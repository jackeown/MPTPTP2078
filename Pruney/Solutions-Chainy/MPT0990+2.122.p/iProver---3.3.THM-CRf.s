%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:22 EST 2020

% Result     : Theorem 7.64s
% Output     : CNFRefutation 7.64s
% Verified   : 
% Statistics : Number of formulae       :  198 ( 886 expanded)
%              Number of clauses        :  118 ( 305 expanded)
%              Number of leaves         :   21 ( 189 expanded)
%              Depth                    :   23
%              Number of atoms          :  571 (5475 expanded)
%              Number of equality atoms :  222 (2027 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f18,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f18])).

fof(f88,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f62,f74])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f21,plain,(
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
    inference(pure_predicate_removal,[],[f20])).

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
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f49,plain,(
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

fof(f48,plain,
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

fof(f50,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f45,f49,f48])).

fof(f76,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f50])).

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

fof(f51,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0] : k4_relat_1(k6_relat_1(X0)) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : k4_relat_1(k6_relat_1(X0)) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f85,plain,(
    ! [X0] : k4_relat_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
    inference(definition_unfolding,[],[f57,f74,f74])).

fof(f78,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f50])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f31,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f59,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f81,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f75,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f60,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f79,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f50])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f35,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f65,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f89,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f65,f74])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f42])).

fof(f73,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f77,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f38])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f80,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f50])).

fof(f16,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f72,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f40])).

fof(f71,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

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

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_partfun1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f58,f74])).

fof(f84,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_12,plain,
    ( v1_relat_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_679,plain,
    ( v1_relat_1(k6_partfun1(X0_51)) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1126,plain,
    ( v1_relat_1(k6_partfun1(X0_51)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_679])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_667,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_31])).

cnf(c_1134,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_667])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_686,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(X1_50))
    | ~ v1_relat_1(X1_50)
    | v1_relat_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1120,plain,
    ( m1_subset_1(X0_50,k1_zfmisc_1(X1_50)) != iProver_top
    | v1_relat_1(X1_50) != iProver_top
    | v1_relat_1(X0_50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_686])).

cnf(c_1681,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1134,c_1120])).

cnf(c_34,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_1183,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0_50))
    | ~ v1_relat_1(X0_50)
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_686])).

cnf(c_1221,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ v1_relat_1(k2_zfmisc_1(X0_51,X1_51))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1183])).

cnf(c_1278,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1221])).

cnf(c_1279,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1278])).

cnf(c_3,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_685,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_51,X1_51)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1288,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_685])).

cnf(c_1289,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1288])).

cnf(c_2010,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1681,c_34,c_1279,c_1289])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_684,plain,
    ( ~ v1_relat_1(X0_50)
    | ~ v1_relat_1(X1_50)
    | k5_relat_1(k4_relat_1(X1_50),k4_relat_1(X0_50)) = k4_relat_1(k5_relat_1(X0_50,X1_50)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1122,plain,
    ( k5_relat_1(k4_relat_1(X0_50),k4_relat_1(X1_50)) = k4_relat_1(k5_relat_1(X1_50,X0_50))
    | v1_relat_1(X1_50) != iProver_top
    | v1_relat_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_684])).

cnf(c_2015,plain,
    ( k5_relat_1(k4_relat_1(sK2),k4_relat_1(X0_50)) = k4_relat_1(k5_relat_1(X0_50,sK2))
    | v1_relat_1(X0_50) != iProver_top ),
    inference(superposition,[status(thm)],[c_2010,c_1122])).

cnf(c_2145,plain,
    ( k5_relat_1(k4_relat_1(sK2),k4_relat_1(k6_partfun1(X0_51))) = k4_relat_1(k5_relat_1(k6_partfun1(X0_51),sK2)) ),
    inference(superposition,[status(thm)],[c_1126,c_2015])).

cnf(c_6,plain,
    ( k4_relat_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_682,plain,
    ( k4_relat_1(k6_partfun1(X0_51)) = k6_partfun1(X0_51) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_2149,plain,
    ( k5_relat_1(k4_relat_1(sK2),k6_partfun1(X0_51)) = k4_relat_1(k5_relat_1(k6_partfun1(X0_51),sK2)) ),
    inference(light_normalisation,[status(thm)],[c_2145,c_682])).

cnf(c_1121,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_51,X1_51)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_685])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_669,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_1132,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_669])).

cnf(c_1680,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1132,c_1120])).

cnf(c_2007,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1121,c_1680])).

cnf(c_8,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_26,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_458,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_26])).

cnf(c_459,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_458])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_461,plain,
    ( ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_459,c_32])).

cnf(c_658,plain,
    ( ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_461])).

cnf(c_1143,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_658])).

cnf(c_1441,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1143,c_31,c_658,c_1278,c_1288])).

cnf(c_10,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_680,plain,
    ( ~ v1_funct_1(X0_50)
    | ~ v1_relat_1(X0_50)
    | v1_relat_1(k2_funct_1(X0_50)) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1125,plain,
    ( v1_funct_1(X0_50) != iProver_top
    | v1_relat_1(X0_50) != iProver_top
    | v1_relat_1(k2_funct_1(X0_50)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_680])).

cnf(c_1677,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k4_relat_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1441,c_1125])).

cnf(c_33,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_2336,plain,
    ( v1_relat_1(k4_relat_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1677,c_33,c_34,c_1279,c_1289])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_683,plain,
    ( ~ v1_relat_1(X0_50)
    | ~ v1_relat_1(X1_50)
    | ~ v1_relat_1(X2_50)
    | k5_relat_1(k5_relat_1(X0_50,X1_50),X2_50) = k5_relat_1(X0_50,k5_relat_1(X1_50,X2_50)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1123,plain,
    ( k5_relat_1(k5_relat_1(X0_50,X1_50),X2_50) = k5_relat_1(X0_50,k5_relat_1(X1_50,X2_50))
    | v1_relat_1(X0_50) != iProver_top
    | v1_relat_1(X1_50) != iProver_top
    | v1_relat_1(X2_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_683])).

cnf(c_2340,plain,
    ( k5_relat_1(k4_relat_1(sK2),k5_relat_1(X0_50,X1_50)) = k5_relat_1(k5_relat_1(k4_relat_1(sK2),X0_50),X1_50)
    | v1_relat_1(X0_50) != iProver_top
    | v1_relat_1(X1_50) != iProver_top ),
    inference(superposition,[status(thm)],[c_2336,c_1123])).

cnf(c_16349,plain,
    ( k5_relat_1(k5_relat_1(k4_relat_1(sK2),sK2),X0_50) = k5_relat_1(k4_relat_1(sK2),k5_relat_1(sK2,X0_50))
    | v1_relat_1(X0_50) != iProver_top ),
    inference(superposition,[status(thm)],[c_2010,c_2340])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_678,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | k2_relset_1(X0_51,X1_51,X0_50) = k2_relat_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1127,plain,
    ( k2_relset_1(X0_51,X1_51,X0_50) = k2_relat_1(X0_50)
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_678])).

cnf(c_1746,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1134,c_1127])).

cnf(c_28,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_670,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_1748,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_1746,c_670])).

cnf(c_13,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_444,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_26])).

cnf(c_445,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(unflattening,[status(thm)],[c_444])).

cnf(c_447,plain,
    ( ~ v1_relat_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_445,c_32])).

cnf(c_659,plain,
    ( ~ v1_relat_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(subtyping,[status(esa)],[c_447])).

cnf(c_1142,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_659])).

cnf(c_1503,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1142,c_31,c_659,c_1278,c_1288])).

cnf(c_1505,plain,
    ( k5_relat_1(k4_relat_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(light_normalisation,[status(thm)],[c_1503,c_1441])).

cnf(c_1750,plain,
    ( k5_relat_1(k4_relat_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(demodulation,[status(thm)],[c_1748,c_1505])).

cnf(c_16361,plain,
    ( k5_relat_1(k4_relat_1(sK2),k5_relat_1(sK2,X0_50)) = k5_relat_1(k6_partfun1(sK1),X0_50)
    | v1_relat_1(X0_50) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_16349,c_1750])).

cnf(c_16910,plain,
    ( k5_relat_1(k4_relat_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
    inference(superposition,[status(thm)],[c_2007,c_16361])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_674,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51)))
    | ~ v1_funct_1(X0_50)
    | ~ v1_funct_1(X1_50)
    | k1_partfun1(X2_51,X3_51,X0_51,X1_51,X1_50,X0_50) = k5_relat_1(X1_50,X0_50) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1131,plain,
    ( k1_partfun1(X0_51,X1_51,X2_51,X3_51,X0_50,X1_50) = k5_relat_1(X0_50,X1_50)
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51))) != iProver_top
    | v1_funct_1(X1_50) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_674])).

cnf(c_2656,plain,
    ( k1_partfun1(X0_51,X1_51,sK1,sK0,X0_50,sK3) = k5_relat_1(X0_50,sK3)
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1132,c_1131])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_35,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_2853,plain,
    ( v1_funct_1(X0_50) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | k1_partfun1(X0_51,X1_51,sK1,sK0,X0_50,sK3) = k5_relat_1(X0_50,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2656,c_35])).

cnf(c_2854,plain,
    ( k1_partfun1(X0_51,X1_51,sK1,sK0,X0_50,sK3) = k5_relat_1(X0_50,sK3)
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(renaming,[status(thm)],[c_2853])).

cnf(c_2860,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1134,c_2854])).

cnf(c_18,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_27,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_359,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_27])).

cnf(c_360,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_359])).

cnf(c_21,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_43,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_362,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_360,c_43])).

cnf(c_664,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_362])).

cnf(c_1137,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_664])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_677,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51)))
    | m1_subset_1(k1_partfun1(X2_51,X3_51,X0_51,X1_51,X1_50,X0_50),k1_zfmisc_1(k2_zfmisc_1(X2_51,X1_51)))
    | ~ v1_funct_1(X0_50)
    | ~ v1_funct_1(X1_50) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1193,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_677])).

cnf(c_1507,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1137,c_32,c_31,c_30,c_29,c_664,c_1193])).

cnf(c_2863,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2860,c_1507])).

cnf(c_3072,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2863,c_33])).

cnf(c_15,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_320,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_15,c_2])).

cnf(c_7,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k6_partfun1(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_339,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k5_relat_1(k6_partfun1(X1),X0) = X0 ),
    inference(resolution,[status(thm)],[c_320,c_7])).

cnf(c_665,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ v1_relat_1(X0_50)
    | k5_relat_1(k6_partfun1(X0_51),X0_50) = X0_50 ),
    inference(subtyping,[status(esa)],[c_339])).

cnf(c_1136,plain,
    ( k5_relat_1(k6_partfun1(X0_51),X0_50) = X0_50
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_relat_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_665])).

cnf(c_724,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_51,X1_51)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_685])).

cnf(c_756,plain,
    ( k5_relat_1(k6_partfun1(X0_51),X0_50) = X0_50
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_relat_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_665])).

cnf(c_1273,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | v1_relat_1(X0_50)
    | ~ v1_relat_1(k2_zfmisc_1(X0_51,X1_51)) ),
    inference(instantiation,[status(thm)],[c_686])).

cnf(c_1274,plain,
    ( m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_relat_1(X0_50) = iProver_top
    | v1_relat_1(k2_zfmisc_1(X0_51,X1_51)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1273])).

cnf(c_3230,plain,
    ( m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | k5_relat_1(k6_partfun1(X0_51),X0_50) = X0_50 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1136,c_724,c_756,c_1274])).

cnf(c_3231,plain,
    ( k5_relat_1(k6_partfun1(X0_51),X0_50) = X0_50
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3230])).

cnf(c_3236,plain,
    ( k5_relat_1(k6_partfun1(sK1),sK3) = sK3 ),
    inference(superposition,[status(thm)],[c_1132,c_3231])).

cnf(c_16920,plain,
    ( k5_relat_1(k4_relat_1(sK2),k6_partfun1(sK0)) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_16910,c_3072,c_3236])).

cnf(c_17229,plain,
    ( k4_relat_1(k5_relat_1(k6_partfun1(sK0),sK2)) = sK3 ),
    inference(superposition,[status(thm)],[c_2149,c_16920])).

cnf(c_3237,plain,
    ( k5_relat_1(k6_partfun1(sK0),sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_1134,c_3231])).

cnf(c_17231,plain,
    ( k4_relat_1(sK2) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_17229,c_3237])).

cnf(c_23,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_673,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1443,plain,
    ( k4_relat_1(sK2) != sK3 ),
    inference(demodulation,[status(thm)],[c_1441,c_673])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_17231,c_1443])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:35:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 7.64/1.52  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.64/1.52  
% 7.64/1.52  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.64/1.52  
% 7.64/1.52  ------  iProver source info
% 7.64/1.52  
% 7.64/1.52  git: date: 2020-06-30 10:37:57 +0100
% 7.64/1.52  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.64/1.52  git: non_committed_changes: false
% 7.64/1.52  git: last_make_outside_of_git: false
% 7.64/1.52  
% 7.64/1.52  ------ 
% 7.64/1.52  
% 7.64/1.52  ------ Input Options
% 7.64/1.52  
% 7.64/1.52  --out_options                           all
% 7.64/1.52  --tptp_safe_out                         true
% 7.64/1.52  --problem_path                          ""
% 7.64/1.52  --include_path                          ""
% 7.64/1.52  --clausifier                            res/vclausify_rel
% 7.64/1.52  --clausifier_options                    ""
% 7.64/1.52  --stdin                                 false
% 7.64/1.52  --stats_out                             all
% 7.64/1.52  
% 7.64/1.52  ------ General Options
% 7.64/1.52  
% 7.64/1.52  --fof                                   false
% 7.64/1.52  --time_out_real                         305.
% 7.64/1.52  --time_out_virtual                      -1.
% 7.64/1.52  --symbol_type_check                     false
% 7.64/1.52  --clausify_out                          false
% 7.64/1.52  --sig_cnt_out                           false
% 7.64/1.52  --trig_cnt_out                          false
% 7.64/1.52  --trig_cnt_out_tolerance                1.
% 7.64/1.52  --trig_cnt_out_sk_spl                   false
% 7.64/1.52  --abstr_cl_out                          false
% 7.64/1.52  
% 7.64/1.52  ------ Global Options
% 7.64/1.52  
% 7.64/1.52  --schedule                              default
% 7.64/1.52  --add_important_lit                     false
% 7.64/1.52  --prop_solver_per_cl                    1000
% 7.64/1.52  --min_unsat_core                        false
% 7.64/1.52  --soft_assumptions                      false
% 7.64/1.52  --soft_lemma_size                       3
% 7.64/1.52  --prop_impl_unit_size                   0
% 7.64/1.52  --prop_impl_unit                        []
% 7.64/1.52  --share_sel_clauses                     true
% 7.64/1.52  --reset_solvers                         false
% 7.64/1.52  --bc_imp_inh                            [conj_cone]
% 7.64/1.52  --conj_cone_tolerance                   3.
% 7.64/1.52  --extra_neg_conj                        none
% 7.64/1.52  --large_theory_mode                     true
% 7.64/1.52  --prolific_symb_bound                   200
% 7.64/1.52  --lt_threshold                          2000
% 7.64/1.52  --clause_weak_htbl                      true
% 7.64/1.52  --gc_record_bc_elim                     false
% 7.64/1.52  
% 7.64/1.52  ------ Preprocessing Options
% 7.64/1.52  
% 7.64/1.52  --preprocessing_flag                    true
% 7.64/1.52  --time_out_prep_mult                    0.1
% 7.64/1.52  --splitting_mode                        input
% 7.64/1.52  --splitting_grd                         true
% 7.64/1.52  --splitting_cvd                         false
% 7.64/1.52  --splitting_cvd_svl                     false
% 7.64/1.52  --splitting_nvd                         32
% 7.64/1.52  --sub_typing                            true
% 7.64/1.52  --prep_gs_sim                           true
% 7.64/1.52  --prep_unflatten                        true
% 7.64/1.52  --prep_res_sim                          true
% 7.64/1.52  --prep_upred                            true
% 7.64/1.52  --prep_sem_filter                       exhaustive
% 7.64/1.52  --prep_sem_filter_out                   false
% 7.64/1.52  --pred_elim                             true
% 7.64/1.52  --res_sim_input                         true
% 7.64/1.52  --eq_ax_congr_red                       true
% 7.64/1.52  --pure_diseq_elim                       true
% 7.64/1.52  --brand_transform                       false
% 7.64/1.52  --non_eq_to_eq                          false
% 7.64/1.52  --prep_def_merge                        true
% 7.64/1.52  --prep_def_merge_prop_impl              false
% 7.64/1.52  --prep_def_merge_mbd                    true
% 7.64/1.52  --prep_def_merge_tr_red                 false
% 7.64/1.52  --prep_def_merge_tr_cl                  false
% 7.64/1.52  --smt_preprocessing                     true
% 7.64/1.52  --smt_ac_axioms                         fast
% 7.64/1.52  --preprocessed_out                      false
% 7.64/1.52  --preprocessed_stats                    false
% 7.64/1.52  
% 7.64/1.52  ------ Abstraction refinement Options
% 7.64/1.52  
% 7.64/1.52  --abstr_ref                             []
% 7.64/1.52  --abstr_ref_prep                        false
% 7.64/1.52  --abstr_ref_until_sat                   false
% 7.64/1.52  --abstr_ref_sig_restrict                funpre
% 7.64/1.52  --abstr_ref_af_restrict_to_split_sk     false
% 7.64/1.52  --abstr_ref_under                       []
% 7.64/1.52  
% 7.64/1.52  ------ SAT Options
% 7.64/1.52  
% 7.64/1.52  --sat_mode                              false
% 7.64/1.52  --sat_fm_restart_options                ""
% 7.64/1.52  --sat_gr_def                            false
% 7.64/1.52  --sat_epr_types                         true
% 7.64/1.52  --sat_non_cyclic_types                  false
% 7.64/1.52  --sat_finite_models                     false
% 7.64/1.52  --sat_fm_lemmas                         false
% 7.64/1.52  --sat_fm_prep                           false
% 7.64/1.52  --sat_fm_uc_incr                        true
% 7.64/1.52  --sat_out_model                         small
% 7.64/1.52  --sat_out_clauses                       false
% 7.64/1.52  
% 7.64/1.52  ------ QBF Options
% 7.64/1.52  
% 7.64/1.52  --qbf_mode                              false
% 7.64/1.52  --qbf_elim_univ                         false
% 7.64/1.52  --qbf_dom_inst                          none
% 7.64/1.52  --qbf_dom_pre_inst                      false
% 7.64/1.52  --qbf_sk_in                             false
% 7.64/1.52  --qbf_pred_elim                         true
% 7.64/1.52  --qbf_split                             512
% 7.64/1.52  
% 7.64/1.52  ------ BMC1 Options
% 7.64/1.52  
% 7.64/1.52  --bmc1_incremental                      false
% 7.64/1.52  --bmc1_axioms                           reachable_all
% 7.64/1.52  --bmc1_min_bound                        0
% 7.64/1.52  --bmc1_max_bound                        -1
% 7.64/1.52  --bmc1_max_bound_default                -1
% 7.64/1.52  --bmc1_symbol_reachability              true
% 7.64/1.52  --bmc1_property_lemmas                  false
% 7.64/1.52  --bmc1_k_induction                      false
% 7.64/1.52  --bmc1_non_equiv_states                 false
% 7.64/1.52  --bmc1_deadlock                         false
% 7.64/1.52  --bmc1_ucm                              false
% 7.64/1.52  --bmc1_add_unsat_core                   none
% 7.64/1.52  --bmc1_unsat_core_children              false
% 7.64/1.52  --bmc1_unsat_core_extrapolate_axioms    false
% 7.64/1.52  --bmc1_out_stat                         full
% 7.64/1.52  --bmc1_ground_init                      false
% 7.64/1.52  --bmc1_pre_inst_next_state              false
% 7.64/1.52  --bmc1_pre_inst_state                   false
% 7.64/1.52  --bmc1_pre_inst_reach_state             false
% 7.64/1.52  --bmc1_out_unsat_core                   false
% 7.64/1.52  --bmc1_aig_witness_out                  false
% 7.64/1.52  --bmc1_verbose                          false
% 7.64/1.52  --bmc1_dump_clauses_tptp                false
% 7.64/1.52  --bmc1_dump_unsat_core_tptp             false
% 7.64/1.52  --bmc1_dump_file                        -
% 7.64/1.52  --bmc1_ucm_expand_uc_limit              128
% 7.64/1.52  --bmc1_ucm_n_expand_iterations          6
% 7.64/1.52  --bmc1_ucm_extend_mode                  1
% 7.64/1.52  --bmc1_ucm_init_mode                    2
% 7.64/1.52  --bmc1_ucm_cone_mode                    none
% 7.64/1.52  --bmc1_ucm_reduced_relation_type        0
% 7.64/1.52  --bmc1_ucm_relax_model                  4
% 7.64/1.52  --bmc1_ucm_full_tr_after_sat            true
% 7.64/1.52  --bmc1_ucm_expand_neg_assumptions       false
% 7.64/1.52  --bmc1_ucm_layered_model                none
% 7.64/1.52  --bmc1_ucm_max_lemma_size               10
% 7.64/1.52  
% 7.64/1.52  ------ AIG Options
% 7.64/1.52  
% 7.64/1.52  --aig_mode                              false
% 7.64/1.52  
% 7.64/1.52  ------ Instantiation Options
% 7.64/1.52  
% 7.64/1.52  --instantiation_flag                    true
% 7.64/1.52  --inst_sos_flag                         true
% 7.64/1.52  --inst_sos_phase                        true
% 7.64/1.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.64/1.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.64/1.52  --inst_lit_sel_side                     num_symb
% 7.64/1.52  --inst_solver_per_active                1400
% 7.64/1.52  --inst_solver_calls_frac                1.
% 7.64/1.52  --inst_passive_queue_type               priority_queues
% 7.64/1.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.64/1.52  --inst_passive_queues_freq              [25;2]
% 7.64/1.52  --inst_dismatching                      true
% 7.64/1.52  --inst_eager_unprocessed_to_passive     true
% 7.64/1.52  --inst_prop_sim_given                   true
% 7.64/1.52  --inst_prop_sim_new                     false
% 7.64/1.52  --inst_subs_new                         false
% 7.64/1.52  --inst_eq_res_simp                      false
% 7.64/1.52  --inst_subs_given                       false
% 7.64/1.52  --inst_orphan_elimination               true
% 7.64/1.52  --inst_learning_loop_flag               true
% 7.64/1.52  --inst_learning_start                   3000
% 7.64/1.52  --inst_learning_factor                  2
% 7.64/1.52  --inst_start_prop_sim_after_learn       3
% 7.64/1.52  --inst_sel_renew                        solver
% 7.64/1.52  --inst_lit_activity_flag                true
% 7.64/1.52  --inst_restr_to_given                   false
% 7.64/1.52  --inst_activity_threshold               500
% 7.64/1.52  --inst_out_proof                        true
% 7.64/1.52  
% 7.64/1.52  ------ Resolution Options
% 7.64/1.52  
% 7.64/1.52  --resolution_flag                       true
% 7.64/1.52  --res_lit_sel                           adaptive
% 7.64/1.52  --res_lit_sel_side                      none
% 7.64/1.52  --res_ordering                          kbo
% 7.64/1.52  --res_to_prop_solver                    active
% 7.64/1.52  --res_prop_simpl_new                    false
% 7.64/1.52  --res_prop_simpl_given                  true
% 7.64/1.52  --res_passive_queue_type                priority_queues
% 7.64/1.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.64/1.52  --res_passive_queues_freq               [15;5]
% 7.64/1.52  --res_forward_subs                      full
% 7.64/1.52  --res_backward_subs                     full
% 7.64/1.52  --res_forward_subs_resolution           true
% 7.64/1.52  --res_backward_subs_resolution          true
% 7.64/1.52  --res_orphan_elimination                true
% 7.64/1.52  --res_time_limit                        2.
% 7.64/1.52  --res_out_proof                         true
% 7.64/1.52  
% 7.64/1.52  ------ Superposition Options
% 7.64/1.52  
% 7.64/1.52  --superposition_flag                    true
% 7.64/1.52  --sup_passive_queue_type                priority_queues
% 7.64/1.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.64/1.52  --sup_passive_queues_freq               [8;1;4]
% 7.64/1.52  --demod_completeness_check              fast
% 7.64/1.52  --demod_use_ground                      true
% 7.64/1.52  --sup_to_prop_solver                    passive
% 7.64/1.52  --sup_prop_simpl_new                    true
% 7.64/1.52  --sup_prop_simpl_given                  true
% 7.64/1.52  --sup_fun_splitting                     true
% 7.64/1.52  --sup_smt_interval                      50000
% 7.64/1.52  
% 7.64/1.52  ------ Superposition Simplification Setup
% 7.64/1.52  
% 7.64/1.52  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.64/1.52  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.64/1.52  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.64/1.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.64/1.52  --sup_full_triv                         [TrivRules;PropSubs]
% 7.64/1.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.64/1.52  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.64/1.52  --sup_immed_triv                        [TrivRules]
% 7.64/1.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.64/1.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.64/1.52  --sup_immed_bw_main                     []
% 7.64/1.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.64/1.52  --sup_input_triv                        [Unflattening;TrivRules]
% 7.64/1.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.64/1.52  --sup_input_bw                          []
% 7.64/1.52  
% 7.64/1.52  ------ Combination Options
% 7.64/1.52  
% 7.64/1.52  --comb_res_mult                         3
% 7.64/1.52  --comb_sup_mult                         2
% 7.64/1.52  --comb_inst_mult                        10
% 7.64/1.52  
% 7.64/1.52  ------ Debug Options
% 7.64/1.52  
% 7.64/1.52  --dbg_backtrace                         false
% 7.64/1.52  --dbg_dump_prop_clauses                 false
% 7.64/1.52  --dbg_dump_prop_clauses_file            -
% 7.64/1.52  --dbg_out_stat                          false
% 7.64/1.52  ------ Parsing...
% 7.64/1.52  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.64/1.52  
% 7.64/1.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 7.64/1.52  
% 7.64/1.52  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.64/1.52  
% 7.64/1.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.64/1.52  ------ Proving...
% 7.64/1.52  ------ Problem Properties 
% 7.64/1.52  
% 7.64/1.52  
% 7.64/1.52  clauses                                 29
% 7.64/1.52  conjectures                             8
% 7.64/1.52  EPR                                     4
% 7.64/1.52  Horn                                    29
% 7.64/1.52  unary                                   12
% 7.64/1.52  binary                                  8
% 7.64/1.52  lits                                    62
% 7.64/1.52  lits eq                                 17
% 7.64/1.52  fd_pure                                 0
% 7.64/1.52  fd_pseudo                               0
% 7.64/1.52  fd_cond                                 0
% 7.64/1.52  fd_pseudo_cond                          0
% 7.64/1.52  AC symbols                              0
% 7.64/1.52  
% 7.64/1.52  ------ Schedule dynamic 5 is on 
% 7.64/1.52  
% 7.64/1.52  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.64/1.52  
% 7.64/1.52  
% 7.64/1.52  ------ 
% 7.64/1.52  Current options:
% 7.64/1.52  ------ 
% 7.64/1.52  
% 7.64/1.52  ------ Input Options
% 7.64/1.52  
% 7.64/1.52  --out_options                           all
% 7.64/1.52  --tptp_safe_out                         true
% 7.64/1.52  --problem_path                          ""
% 7.64/1.52  --include_path                          ""
% 7.64/1.52  --clausifier                            res/vclausify_rel
% 7.64/1.52  --clausifier_options                    ""
% 7.64/1.52  --stdin                                 false
% 7.64/1.52  --stats_out                             all
% 7.64/1.52  
% 7.64/1.52  ------ General Options
% 7.64/1.52  
% 7.64/1.52  --fof                                   false
% 7.64/1.52  --time_out_real                         305.
% 7.64/1.52  --time_out_virtual                      -1.
% 7.64/1.52  --symbol_type_check                     false
% 7.64/1.52  --clausify_out                          false
% 7.64/1.52  --sig_cnt_out                           false
% 7.64/1.52  --trig_cnt_out                          false
% 7.64/1.52  --trig_cnt_out_tolerance                1.
% 7.64/1.52  --trig_cnt_out_sk_spl                   false
% 7.64/1.52  --abstr_cl_out                          false
% 7.64/1.52  
% 7.64/1.52  ------ Global Options
% 7.64/1.52  
% 7.64/1.52  --schedule                              default
% 7.64/1.52  --add_important_lit                     false
% 7.64/1.52  --prop_solver_per_cl                    1000
% 7.64/1.52  --min_unsat_core                        false
% 7.64/1.52  --soft_assumptions                      false
% 7.64/1.52  --soft_lemma_size                       3
% 7.64/1.52  --prop_impl_unit_size                   0
% 7.64/1.52  --prop_impl_unit                        []
% 7.64/1.52  --share_sel_clauses                     true
% 7.64/1.52  --reset_solvers                         false
% 7.64/1.52  --bc_imp_inh                            [conj_cone]
% 7.64/1.52  --conj_cone_tolerance                   3.
% 7.64/1.52  --extra_neg_conj                        none
% 7.64/1.52  --large_theory_mode                     true
% 7.64/1.52  --prolific_symb_bound                   200
% 7.64/1.52  --lt_threshold                          2000
% 7.64/1.52  --clause_weak_htbl                      true
% 7.64/1.52  --gc_record_bc_elim                     false
% 7.64/1.52  
% 7.64/1.52  ------ Preprocessing Options
% 7.64/1.52  
% 7.64/1.52  --preprocessing_flag                    true
% 7.64/1.52  --time_out_prep_mult                    0.1
% 7.64/1.52  --splitting_mode                        input
% 7.64/1.52  --splitting_grd                         true
% 7.64/1.52  --splitting_cvd                         false
% 7.64/1.52  --splitting_cvd_svl                     false
% 7.64/1.52  --splitting_nvd                         32
% 7.64/1.52  --sub_typing                            true
% 7.64/1.52  --prep_gs_sim                           true
% 7.64/1.52  --prep_unflatten                        true
% 7.64/1.52  --prep_res_sim                          true
% 7.64/1.52  --prep_upred                            true
% 7.64/1.52  --prep_sem_filter                       exhaustive
% 7.64/1.52  --prep_sem_filter_out                   false
% 7.64/1.52  --pred_elim                             true
% 7.64/1.52  --res_sim_input                         true
% 7.64/1.52  --eq_ax_congr_red                       true
% 7.64/1.52  --pure_diseq_elim                       true
% 7.64/1.52  --brand_transform                       false
% 7.64/1.52  --non_eq_to_eq                          false
% 7.64/1.52  --prep_def_merge                        true
% 7.64/1.52  --prep_def_merge_prop_impl              false
% 7.64/1.52  --prep_def_merge_mbd                    true
% 7.64/1.52  --prep_def_merge_tr_red                 false
% 7.64/1.52  --prep_def_merge_tr_cl                  false
% 7.64/1.52  --smt_preprocessing                     true
% 7.64/1.52  --smt_ac_axioms                         fast
% 7.64/1.52  --preprocessed_out                      false
% 7.64/1.52  --preprocessed_stats                    false
% 7.64/1.52  
% 7.64/1.52  ------ Abstraction refinement Options
% 7.64/1.52  
% 7.64/1.52  --abstr_ref                             []
% 7.64/1.52  --abstr_ref_prep                        false
% 7.64/1.52  --abstr_ref_until_sat                   false
% 7.64/1.52  --abstr_ref_sig_restrict                funpre
% 7.64/1.52  --abstr_ref_af_restrict_to_split_sk     false
% 7.64/1.52  --abstr_ref_under                       []
% 7.64/1.52  
% 7.64/1.52  ------ SAT Options
% 7.64/1.52  
% 7.64/1.52  --sat_mode                              false
% 7.64/1.52  --sat_fm_restart_options                ""
% 7.64/1.52  --sat_gr_def                            false
% 7.64/1.52  --sat_epr_types                         true
% 7.64/1.52  --sat_non_cyclic_types                  false
% 7.64/1.52  --sat_finite_models                     false
% 7.64/1.52  --sat_fm_lemmas                         false
% 7.64/1.52  --sat_fm_prep                           false
% 7.64/1.52  --sat_fm_uc_incr                        true
% 7.64/1.52  --sat_out_model                         small
% 7.64/1.52  --sat_out_clauses                       false
% 7.64/1.52  
% 7.64/1.52  ------ QBF Options
% 7.64/1.52  
% 7.64/1.52  --qbf_mode                              false
% 7.64/1.52  --qbf_elim_univ                         false
% 7.64/1.52  --qbf_dom_inst                          none
% 7.64/1.52  --qbf_dom_pre_inst                      false
% 7.64/1.52  --qbf_sk_in                             false
% 7.64/1.52  --qbf_pred_elim                         true
% 7.64/1.52  --qbf_split                             512
% 7.64/1.52  
% 7.64/1.52  ------ BMC1 Options
% 7.64/1.52  
% 7.64/1.52  --bmc1_incremental                      false
% 7.64/1.52  --bmc1_axioms                           reachable_all
% 7.64/1.52  --bmc1_min_bound                        0
% 7.64/1.52  --bmc1_max_bound                        -1
% 7.64/1.52  --bmc1_max_bound_default                -1
% 7.64/1.52  --bmc1_symbol_reachability              true
% 7.64/1.52  --bmc1_property_lemmas                  false
% 7.64/1.52  --bmc1_k_induction                      false
% 7.64/1.52  --bmc1_non_equiv_states                 false
% 7.64/1.52  --bmc1_deadlock                         false
% 7.64/1.52  --bmc1_ucm                              false
% 7.64/1.52  --bmc1_add_unsat_core                   none
% 7.64/1.52  --bmc1_unsat_core_children              false
% 7.64/1.52  --bmc1_unsat_core_extrapolate_axioms    false
% 7.64/1.52  --bmc1_out_stat                         full
% 7.64/1.52  --bmc1_ground_init                      false
% 7.64/1.52  --bmc1_pre_inst_next_state              false
% 7.64/1.52  --bmc1_pre_inst_state                   false
% 7.64/1.52  --bmc1_pre_inst_reach_state             false
% 7.64/1.52  --bmc1_out_unsat_core                   false
% 7.64/1.52  --bmc1_aig_witness_out                  false
% 7.64/1.52  --bmc1_verbose                          false
% 7.64/1.52  --bmc1_dump_clauses_tptp                false
% 7.64/1.52  --bmc1_dump_unsat_core_tptp             false
% 7.64/1.52  --bmc1_dump_file                        -
% 7.64/1.52  --bmc1_ucm_expand_uc_limit              128
% 7.64/1.52  --bmc1_ucm_n_expand_iterations          6
% 7.64/1.52  --bmc1_ucm_extend_mode                  1
% 7.64/1.52  --bmc1_ucm_init_mode                    2
% 7.64/1.52  --bmc1_ucm_cone_mode                    none
% 7.64/1.52  --bmc1_ucm_reduced_relation_type        0
% 7.64/1.52  --bmc1_ucm_relax_model                  4
% 7.64/1.52  --bmc1_ucm_full_tr_after_sat            true
% 7.64/1.52  --bmc1_ucm_expand_neg_assumptions       false
% 7.64/1.52  --bmc1_ucm_layered_model                none
% 7.64/1.52  --bmc1_ucm_max_lemma_size               10
% 7.64/1.52  
% 7.64/1.52  ------ AIG Options
% 7.64/1.52  
% 7.64/1.52  --aig_mode                              false
% 7.64/1.52  
% 7.64/1.52  ------ Instantiation Options
% 7.64/1.52  
% 7.64/1.52  --instantiation_flag                    true
% 7.64/1.52  --inst_sos_flag                         true
% 7.64/1.52  --inst_sos_phase                        true
% 7.64/1.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.64/1.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.64/1.52  --inst_lit_sel_side                     none
% 7.64/1.52  --inst_solver_per_active                1400
% 7.64/1.52  --inst_solver_calls_frac                1.
% 7.64/1.52  --inst_passive_queue_type               priority_queues
% 7.64/1.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.64/1.52  --inst_passive_queues_freq              [25;2]
% 7.64/1.52  --inst_dismatching                      true
% 7.64/1.52  --inst_eager_unprocessed_to_passive     true
% 7.64/1.52  --inst_prop_sim_given                   true
% 7.64/1.52  --inst_prop_sim_new                     false
% 7.64/1.52  --inst_subs_new                         false
% 7.64/1.52  --inst_eq_res_simp                      false
% 7.64/1.52  --inst_subs_given                       false
% 7.64/1.52  --inst_orphan_elimination               true
% 7.64/1.52  --inst_learning_loop_flag               true
% 7.64/1.52  --inst_learning_start                   3000
% 7.64/1.52  --inst_learning_factor                  2
% 7.64/1.52  --inst_start_prop_sim_after_learn       3
% 7.64/1.52  --inst_sel_renew                        solver
% 7.64/1.52  --inst_lit_activity_flag                true
% 7.64/1.52  --inst_restr_to_given                   false
% 7.64/1.52  --inst_activity_threshold               500
% 7.64/1.52  --inst_out_proof                        true
% 7.64/1.52  
% 7.64/1.52  ------ Resolution Options
% 7.64/1.52  
% 7.64/1.52  --resolution_flag                       false
% 7.64/1.52  --res_lit_sel                           adaptive
% 7.64/1.52  --res_lit_sel_side                      none
% 7.64/1.52  --res_ordering                          kbo
% 7.64/1.52  --res_to_prop_solver                    active
% 7.64/1.52  --res_prop_simpl_new                    false
% 7.64/1.52  --res_prop_simpl_given                  true
% 7.64/1.52  --res_passive_queue_type                priority_queues
% 7.64/1.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.64/1.52  --res_passive_queues_freq               [15;5]
% 7.64/1.52  --res_forward_subs                      full
% 7.64/1.52  --res_backward_subs                     full
% 7.64/1.52  --res_forward_subs_resolution           true
% 7.64/1.52  --res_backward_subs_resolution          true
% 7.64/1.52  --res_orphan_elimination                true
% 7.64/1.52  --res_time_limit                        2.
% 7.64/1.52  --res_out_proof                         true
% 7.64/1.52  
% 7.64/1.52  ------ Superposition Options
% 7.64/1.52  
% 7.64/1.52  --superposition_flag                    true
% 7.64/1.52  --sup_passive_queue_type                priority_queues
% 7.64/1.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.64/1.52  --sup_passive_queues_freq               [8;1;4]
% 7.64/1.52  --demod_completeness_check              fast
% 7.64/1.52  --demod_use_ground                      true
% 7.64/1.52  --sup_to_prop_solver                    passive
% 7.64/1.52  --sup_prop_simpl_new                    true
% 7.64/1.52  --sup_prop_simpl_given                  true
% 7.64/1.52  --sup_fun_splitting                     true
% 7.64/1.52  --sup_smt_interval                      50000
% 7.64/1.52  
% 7.64/1.52  ------ Superposition Simplification Setup
% 7.64/1.52  
% 7.64/1.52  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.64/1.52  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.64/1.52  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.64/1.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.64/1.52  --sup_full_triv                         [TrivRules;PropSubs]
% 7.64/1.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.64/1.52  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.64/1.52  --sup_immed_triv                        [TrivRules]
% 7.64/1.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.64/1.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.64/1.52  --sup_immed_bw_main                     []
% 7.64/1.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.64/1.52  --sup_input_triv                        [Unflattening;TrivRules]
% 7.64/1.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.64/1.52  --sup_input_bw                          []
% 7.64/1.52  
% 7.64/1.52  ------ Combination Options
% 7.64/1.52  
% 7.64/1.52  --comb_res_mult                         3
% 7.64/1.52  --comb_sup_mult                         2
% 7.64/1.52  --comb_inst_mult                        10
% 7.64/1.52  
% 7.64/1.52  ------ Debug Options
% 7.64/1.52  
% 7.64/1.52  --dbg_backtrace                         false
% 7.64/1.52  --dbg_dump_prop_clauses                 false
% 7.64/1.52  --dbg_dump_prop_clauses_file            -
% 7.64/1.52  --dbg_out_stat                          false
% 7.64/1.52  
% 7.64/1.52  
% 7.64/1.52  
% 7.64/1.52  
% 7.64/1.52  ------ Proving...
% 7.64/1.52  
% 7.64/1.52  
% 7.64/1.52  % SZS status Theorem for theBenchmark.p
% 7.64/1.52  
% 7.64/1.52  % SZS output start CNFRefutation for theBenchmark.p
% 7.64/1.52  
% 7.64/1.52  fof(f10,axiom,(
% 7.64/1.52    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 7.64/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.52  
% 7.64/1.52  fof(f62,plain,(
% 7.64/1.52    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 7.64/1.52    inference(cnf_transformation,[],[f10])).
% 7.64/1.52  
% 7.64/1.52  fof(f18,axiom,(
% 7.64/1.52    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 7.64/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.52  
% 7.64/1.52  fof(f74,plain,(
% 7.64/1.52    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 7.64/1.52    inference(cnf_transformation,[],[f18])).
% 7.64/1.52  
% 7.64/1.52  fof(f88,plain,(
% 7.64/1.52    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 7.64/1.52    inference(definition_unfolding,[],[f62,f74])).
% 7.64/1.52  
% 7.64/1.52  fof(f19,conjecture,(
% 7.64/1.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 7.64/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.52  
% 7.64/1.52  fof(f20,negated_conjecture,(
% 7.64/1.52    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 7.64/1.52    inference(negated_conjecture,[],[f19])).
% 7.64/1.52  
% 7.64/1.52  fof(f21,plain,(
% 7.64/1.52    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 7.64/1.52    inference(pure_predicate_removal,[],[f20])).
% 7.64/1.52  
% 7.64/1.52  fof(f44,plain,(
% 7.64/1.52    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 7.64/1.52    inference(ennf_transformation,[],[f21])).
% 7.64/1.52  
% 7.64/1.52  fof(f45,plain,(
% 7.64/1.52    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 7.64/1.52    inference(flattening,[],[f44])).
% 7.64/1.52  
% 7.64/1.52  fof(f49,plain,(
% 7.64/1.52    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(sK3))) )),
% 7.64/1.52    introduced(choice_axiom,[])).
% 7.64/1.52  
% 7.64/1.52  fof(f48,plain,(
% 7.64/1.52    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2))),
% 7.64/1.52    introduced(choice_axiom,[])).
% 7.64/1.52  
% 7.64/1.52  fof(f50,plain,(
% 7.64/1.52    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2)),
% 7.64/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f45,f49,f48])).
% 7.64/1.52  
% 7.64/1.52  fof(f76,plain,(
% 7.64/1.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 7.64/1.52    inference(cnf_transformation,[],[f50])).
% 7.64/1.52  
% 7.64/1.52  fof(f1,axiom,(
% 7.64/1.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 7.64/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.52  
% 7.64/1.52  fof(f24,plain,(
% 7.64/1.52    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 7.64/1.52    inference(ennf_transformation,[],[f1])).
% 7.64/1.52  
% 7.64/1.52  fof(f51,plain,(
% 7.64/1.52    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 7.64/1.52    inference(cnf_transformation,[],[f24])).
% 7.64/1.52  
% 7.64/1.52  fof(f3,axiom,(
% 7.64/1.52    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 7.64/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.52  
% 7.64/1.52  fof(f54,plain,(
% 7.64/1.52    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 7.64/1.52    inference(cnf_transformation,[],[f3])).
% 7.64/1.52  
% 7.64/1.52  fof(f4,axiom,(
% 7.64/1.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1))))),
% 7.64/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.52  
% 7.64/1.52  fof(f26,plain,(
% 7.64/1.52    ! [X0] : (! [X1] : (k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.64/1.52    inference(ennf_transformation,[],[f4])).
% 7.64/1.52  
% 7.64/1.52  fof(f55,plain,(
% 7.64/1.52    ( ! [X0,X1] : (k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.64/1.52    inference(cnf_transformation,[],[f26])).
% 7.64/1.52  
% 7.64/1.52  fof(f6,axiom,(
% 7.64/1.52    ! [X0] : k4_relat_1(k6_relat_1(X0)) = k6_relat_1(X0)),
% 7.64/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.52  
% 7.64/1.52  fof(f57,plain,(
% 7.64/1.52    ( ! [X0] : (k4_relat_1(k6_relat_1(X0)) = k6_relat_1(X0)) )),
% 7.64/1.52    inference(cnf_transformation,[],[f6])).
% 7.64/1.52  
% 7.64/1.52  fof(f85,plain,(
% 7.64/1.52    ( ! [X0] : (k4_relat_1(k6_partfun1(X0)) = k6_partfun1(X0)) )),
% 7.64/1.52    inference(definition_unfolding,[],[f57,f74,f74])).
% 7.64/1.52  
% 7.64/1.52  fof(f78,plain,(
% 7.64/1.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 7.64/1.52    inference(cnf_transformation,[],[f50])).
% 7.64/1.52  
% 7.64/1.52  fof(f8,axiom,(
% 7.64/1.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 7.64/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.52  
% 7.64/1.52  fof(f30,plain,(
% 7.64/1.52    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.64/1.52    inference(ennf_transformation,[],[f8])).
% 7.64/1.52  
% 7.64/1.52  fof(f31,plain,(
% 7.64/1.52    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.64/1.52    inference(flattening,[],[f30])).
% 7.64/1.52  
% 7.64/1.52  fof(f59,plain,(
% 7.64/1.52    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.64/1.52    inference(cnf_transformation,[],[f31])).
% 7.64/1.52  
% 7.64/1.52  fof(f81,plain,(
% 7.64/1.52    v2_funct_1(sK2)),
% 7.64/1.52    inference(cnf_transformation,[],[f50])).
% 7.64/1.52  
% 7.64/1.52  fof(f75,plain,(
% 7.64/1.52    v1_funct_1(sK2)),
% 7.64/1.52    inference(cnf_transformation,[],[f50])).
% 7.64/1.52  
% 7.64/1.52  fof(f9,axiom,(
% 7.64/1.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 7.64/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.52  
% 7.64/1.52  fof(f32,plain,(
% 7.64/1.52    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.64/1.52    inference(ennf_transformation,[],[f9])).
% 7.64/1.52  
% 7.64/1.52  fof(f33,plain,(
% 7.64/1.52    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.64/1.52    inference(flattening,[],[f32])).
% 7.64/1.52  
% 7.64/1.52  fof(f60,plain,(
% 7.64/1.52    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.64/1.52    inference(cnf_transformation,[],[f33])).
% 7.64/1.52  
% 7.64/1.52  fof(f5,axiom,(
% 7.64/1.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2))))),
% 7.64/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.52  
% 7.64/1.52  fof(f27,plain,(
% 7.64/1.52    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.64/1.52    inference(ennf_transformation,[],[f5])).
% 7.64/1.52  
% 7.64/1.52  fof(f56,plain,(
% 7.64/1.52    ( ! [X2,X0,X1] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.64/1.52    inference(cnf_transformation,[],[f27])).
% 7.64/1.52  
% 7.64/1.52  fof(f13,axiom,(
% 7.64/1.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 7.64/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.52  
% 7.64/1.52  fof(f37,plain,(
% 7.64/1.52    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.64/1.52    inference(ennf_transformation,[],[f13])).
% 7.64/1.52  
% 7.64/1.52  fof(f67,plain,(
% 7.64/1.52    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.64/1.52    inference(cnf_transformation,[],[f37])).
% 7.64/1.52  
% 7.64/1.52  fof(f79,plain,(
% 7.64/1.52    k2_relset_1(sK0,sK1,sK2) = sK1),
% 7.64/1.52    inference(cnf_transformation,[],[f50])).
% 7.64/1.52  
% 7.64/1.52  fof(f11,axiom,(
% 7.64/1.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 7.64/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.52  
% 7.64/1.52  fof(f34,plain,(
% 7.64/1.52    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.64/1.52    inference(ennf_transformation,[],[f11])).
% 7.64/1.52  
% 7.64/1.52  fof(f35,plain,(
% 7.64/1.52    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.64/1.52    inference(flattening,[],[f34])).
% 7.64/1.52  
% 7.64/1.52  fof(f65,plain,(
% 7.64/1.52    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.64/1.52    inference(cnf_transformation,[],[f35])).
% 7.64/1.52  
% 7.64/1.52  fof(f89,plain,(
% 7.64/1.52    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.64/1.52    inference(definition_unfolding,[],[f65,f74])).
% 7.64/1.52  
% 7.64/1.52  fof(f17,axiom,(
% 7.64/1.52    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 7.64/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.52  
% 7.64/1.52  fof(f42,plain,(
% 7.64/1.52    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 7.64/1.52    inference(ennf_transformation,[],[f17])).
% 7.64/1.52  
% 7.64/1.52  fof(f43,plain,(
% 7.64/1.52    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 7.64/1.52    inference(flattening,[],[f42])).
% 7.64/1.52  
% 7.64/1.52  fof(f73,plain,(
% 7.64/1.52    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 7.64/1.52    inference(cnf_transformation,[],[f43])).
% 7.64/1.52  
% 7.64/1.52  fof(f77,plain,(
% 7.64/1.52    v1_funct_1(sK3)),
% 7.64/1.52    inference(cnf_transformation,[],[f50])).
% 7.64/1.52  
% 7.64/1.52  fof(f14,axiom,(
% 7.64/1.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 7.64/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.52  
% 7.64/1.52  fof(f38,plain,(
% 7.64/1.52    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 7.64/1.52    inference(ennf_transformation,[],[f14])).
% 7.64/1.52  
% 7.64/1.52  fof(f39,plain,(
% 7.64/1.52    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.64/1.52    inference(flattening,[],[f38])).
% 7.64/1.52  
% 7.64/1.52  fof(f47,plain,(
% 7.64/1.52    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.64/1.52    inference(nnf_transformation,[],[f39])).
% 7.64/1.52  
% 7.64/1.52  fof(f68,plain,(
% 7.64/1.52    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.64/1.52    inference(cnf_transformation,[],[f47])).
% 7.64/1.52  
% 7.64/1.52  fof(f80,plain,(
% 7.64/1.52    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 7.64/1.52    inference(cnf_transformation,[],[f50])).
% 7.64/1.52  
% 7.64/1.52  fof(f16,axiom,(
% 7.64/1.52    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 7.64/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.52  
% 7.64/1.52  fof(f22,plain,(
% 7.64/1.52    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 7.64/1.52    inference(pure_predicate_removal,[],[f16])).
% 7.64/1.52  
% 7.64/1.52  fof(f72,plain,(
% 7.64/1.52    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 7.64/1.52    inference(cnf_transformation,[],[f22])).
% 7.64/1.52  
% 7.64/1.52  fof(f15,axiom,(
% 7.64/1.52    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 7.64/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.52  
% 7.64/1.52  fof(f40,plain,(
% 7.64/1.52    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 7.64/1.52    inference(ennf_transformation,[],[f15])).
% 7.64/1.52  
% 7.64/1.52  fof(f41,plain,(
% 7.64/1.52    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 7.64/1.52    inference(flattening,[],[f40])).
% 7.64/1.52  
% 7.64/1.52  fof(f71,plain,(
% 7.64/1.52    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 7.64/1.52    inference(cnf_transformation,[],[f41])).
% 7.64/1.52  
% 7.64/1.52  fof(f12,axiom,(
% 7.64/1.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.64/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.52  
% 7.64/1.52  fof(f23,plain,(
% 7.64/1.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 7.64/1.52    inference(pure_predicate_removal,[],[f12])).
% 7.64/1.52  
% 7.64/1.52  fof(f36,plain,(
% 7.64/1.52    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.64/1.52    inference(ennf_transformation,[],[f23])).
% 7.64/1.52  
% 7.64/1.52  fof(f66,plain,(
% 7.64/1.52    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.64/1.52    inference(cnf_transformation,[],[f36])).
% 7.64/1.52  
% 7.64/1.52  fof(f2,axiom,(
% 7.64/1.52    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 7.64/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.52  
% 7.64/1.52  fof(f25,plain,(
% 7.64/1.52    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.64/1.52    inference(ennf_transformation,[],[f2])).
% 7.64/1.52  
% 7.64/1.52  fof(f46,plain,(
% 7.64/1.52    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.64/1.52    inference(nnf_transformation,[],[f25])).
% 7.64/1.52  
% 7.64/1.52  fof(f52,plain,(
% 7.64/1.52    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.64/1.52    inference(cnf_transformation,[],[f46])).
% 7.64/1.52  
% 7.64/1.52  fof(f7,axiom,(
% 7.64/1.52    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 7.64/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.52  
% 7.64/1.52  fof(f28,plain,(
% 7.64/1.52    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.64/1.52    inference(ennf_transformation,[],[f7])).
% 7.64/1.52  
% 7.64/1.52  fof(f29,plain,(
% 7.64/1.52    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 7.64/1.52    inference(flattening,[],[f28])).
% 7.64/1.52  
% 7.64/1.52  fof(f58,plain,(
% 7.64/1.52    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 7.64/1.52    inference(cnf_transformation,[],[f29])).
% 7.64/1.52  
% 7.64/1.52  fof(f86,plain,(
% 7.64/1.52    ( ! [X0,X1] : (k5_relat_1(k6_partfun1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 7.64/1.52    inference(definition_unfolding,[],[f58,f74])).
% 7.64/1.52  
% 7.64/1.52  fof(f84,plain,(
% 7.64/1.52    k2_funct_1(sK2) != sK3),
% 7.64/1.52    inference(cnf_transformation,[],[f50])).
% 7.64/1.52  
% 7.64/1.52  cnf(c_12,plain,
% 7.64/1.52      ( v1_relat_1(k6_partfun1(X0)) ),
% 7.64/1.52      inference(cnf_transformation,[],[f88]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_679,plain,
% 7.64/1.52      ( v1_relat_1(k6_partfun1(X0_51)) ),
% 7.64/1.52      inference(subtyping,[status(esa)],[c_12]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_1126,plain,
% 7.64/1.52      ( v1_relat_1(k6_partfun1(X0_51)) = iProver_top ),
% 7.64/1.52      inference(predicate_to_equality,[status(thm)],[c_679]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_31,negated_conjecture,
% 7.64/1.52      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 7.64/1.52      inference(cnf_transformation,[],[f76]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_667,negated_conjecture,
% 7.64/1.52      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 7.64/1.52      inference(subtyping,[status(esa)],[c_31]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_1134,plain,
% 7.64/1.52      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.64/1.52      inference(predicate_to_equality,[status(thm)],[c_667]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_0,plain,
% 7.64/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.64/1.52      | ~ v1_relat_1(X1)
% 7.64/1.52      | v1_relat_1(X0) ),
% 7.64/1.52      inference(cnf_transformation,[],[f51]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_686,plain,
% 7.64/1.52      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(X1_50))
% 7.64/1.52      | ~ v1_relat_1(X1_50)
% 7.64/1.52      | v1_relat_1(X0_50) ),
% 7.64/1.52      inference(subtyping,[status(esa)],[c_0]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_1120,plain,
% 7.64/1.52      ( m1_subset_1(X0_50,k1_zfmisc_1(X1_50)) != iProver_top
% 7.64/1.52      | v1_relat_1(X1_50) != iProver_top
% 7.64/1.52      | v1_relat_1(X0_50) = iProver_top ),
% 7.64/1.52      inference(predicate_to_equality,[status(thm)],[c_686]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_1681,plain,
% 7.64/1.52      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 7.64/1.52      | v1_relat_1(sK2) = iProver_top ),
% 7.64/1.52      inference(superposition,[status(thm)],[c_1134,c_1120]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_34,plain,
% 7.64/1.52      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.64/1.52      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_1183,plain,
% 7.64/1.52      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0_50))
% 7.64/1.52      | ~ v1_relat_1(X0_50)
% 7.64/1.52      | v1_relat_1(sK2) ),
% 7.64/1.52      inference(instantiation,[status(thm)],[c_686]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_1221,plain,
% 7.64/1.52      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 7.64/1.52      | ~ v1_relat_1(k2_zfmisc_1(X0_51,X1_51))
% 7.64/1.52      | v1_relat_1(sK2) ),
% 7.64/1.52      inference(instantiation,[status(thm)],[c_1183]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_1278,plain,
% 7.64/1.52      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.64/1.52      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
% 7.64/1.52      | v1_relat_1(sK2) ),
% 7.64/1.52      inference(instantiation,[status(thm)],[c_1221]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_1279,plain,
% 7.64/1.52      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.64/1.52      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 7.64/1.52      | v1_relat_1(sK2) = iProver_top ),
% 7.64/1.52      inference(predicate_to_equality,[status(thm)],[c_1278]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_3,plain,
% 7.64/1.52      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 7.64/1.52      inference(cnf_transformation,[],[f54]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_685,plain,
% 7.64/1.52      ( v1_relat_1(k2_zfmisc_1(X0_51,X1_51)) ),
% 7.64/1.52      inference(subtyping,[status(esa)],[c_3]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_1288,plain,
% 7.64/1.52      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 7.64/1.52      inference(instantiation,[status(thm)],[c_685]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_1289,plain,
% 7.64/1.52      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 7.64/1.52      inference(predicate_to_equality,[status(thm)],[c_1288]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_2010,plain,
% 7.64/1.52      ( v1_relat_1(sK2) = iProver_top ),
% 7.64/1.52      inference(global_propositional_subsumption,
% 7.64/1.52                [status(thm)],
% 7.64/1.52                [c_1681,c_34,c_1279,c_1289]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_4,plain,
% 7.64/1.52      ( ~ v1_relat_1(X0)
% 7.64/1.52      | ~ v1_relat_1(X1)
% 7.64/1.52      | k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1)) ),
% 7.64/1.52      inference(cnf_transformation,[],[f55]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_684,plain,
% 7.64/1.52      ( ~ v1_relat_1(X0_50)
% 7.64/1.52      | ~ v1_relat_1(X1_50)
% 7.64/1.52      | k5_relat_1(k4_relat_1(X1_50),k4_relat_1(X0_50)) = k4_relat_1(k5_relat_1(X0_50,X1_50)) ),
% 7.64/1.52      inference(subtyping,[status(esa)],[c_4]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_1122,plain,
% 7.64/1.52      ( k5_relat_1(k4_relat_1(X0_50),k4_relat_1(X1_50)) = k4_relat_1(k5_relat_1(X1_50,X0_50))
% 7.64/1.52      | v1_relat_1(X1_50) != iProver_top
% 7.64/1.52      | v1_relat_1(X0_50) != iProver_top ),
% 7.64/1.52      inference(predicate_to_equality,[status(thm)],[c_684]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_2015,plain,
% 7.64/1.52      ( k5_relat_1(k4_relat_1(sK2),k4_relat_1(X0_50)) = k4_relat_1(k5_relat_1(X0_50,sK2))
% 7.64/1.52      | v1_relat_1(X0_50) != iProver_top ),
% 7.64/1.52      inference(superposition,[status(thm)],[c_2010,c_1122]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_2145,plain,
% 7.64/1.52      ( k5_relat_1(k4_relat_1(sK2),k4_relat_1(k6_partfun1(X0_51))) = k4_relat_1(k5_relat_1(k6_partfun1(X0_51),sK2)) ),
% 7.64/1.52      inference(superposition,[status(thm)],[c_1126,c_2015]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_6,plain,
% 7.64/1.52      ( k4_relat_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
% 7.64/1.52      inference(cnf_transformation,[],[f85]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_682,plain,
% 7.64/1.52      ( k4_relat_1(k6_partfun1(X0_51)) = k6_partfun1(X0_51) ),
% 7.64/1.52      inference(subtyping,[status(esa)],[c_6]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_2149,plain,
% 7.64/1.52      ( k5_relat_1(k4_relat_1(sK2),k6_partfun1(X0_51)) = k4_relat_1(k5_relat_1(k6_partfun1(X0_51),sK2)) ),
% 7.64/1.52      inference(light_normalisation,[status(thm)],[c_2145,c_682]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_1121,plain,
% 7.64/1.52      ( v1_relat_1(k2_zfmisc_1(X0_51,X1_51)) = iProver_top ),
% 7.64/1.52      inference(predicate_to_equality,[status(thm)],[c_685]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_29,negated_conjecture,
% 7.64/1.52      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 7.64/1.52      inference(cnf_transformation,[],[f78]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_669,negated_conjecture,
% 7.64/1.52      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 7.64/1.52      inference(subtyping,[status(esa)],[c_29]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_1132,plain,
% 7.64/1.52      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 7.64/1.52      inference(predicate_to_equality,[status(thm)],[c_669]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_1680,plain,
% 7.64/1.52      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 7.64/1.52      | v1_relat_1(sK3) = iProver_top ),
% 7.64/1.52      inference(superposition,[status(thm)],[c_1132,c_1120]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_2007,plain,
% 7.64/1.52      ( v1_relat_1(sK3) = iProver_top ),
% 7.64/1.52      inference(superposition,[status(thm)],[c_1121,c_1680]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_8,plain,
% 7.64/1.52      ( ~ v1_funct_1(X0)
% 7.64/1.52      | ~ v2_funct_1(X0)
% 7.64/1.52      | ~ v1_relat_1(X0)
% 7.64/1.52      | k2_funct_1(X0) = k4_relat_1(X0) ),
% 7.64/1.52      inference(cnf_transformation,[],[f59]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_26,negated_conjecture,
% 7.64/1.52      ( v2_funct_1(sK2) ),
% 7.64/1.52      inference(cnf_transformation,[],[f81]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_458,plain,
% 7.64/1.52      ( ~ v1_funct_1(X0)
% 7.64/1.52      | ~ v1_relat_1(X0)
% 7.64/1.52      | k2_funct_1(X0) = k4_relat_1(X0)
% 7.64/1.52      | sK2 != X0 ),
% 7.64/1.52      inference(resolution_lifted,[status(thm)],[c_8,c_26]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_459,plain,
% 7.64/1.52      ( ~ v1_funct_1(sK2)
% 7.64/1.52      | ~ v1_relat_1(sK2)
% 7.64/1.52      | k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 7.64/1.52      inference(unflattening,[status(thm)],[c_458]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_32,negated_conjecture,
% 7.64/1.52      ( v1_funct_1(sK2) ),
% 7.64/1.52      inference(cnf_transformation,[],[f75]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_461,plain,
% 7.64/1.52      ( ~ v1_relat_1(sK2) | k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 7.64/1.52      inference(global_propositional_subsumption,
% 7.64/1.52                [status(thm)],
% 7.64/1.52                [c_459,c_32]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_658,plain,
% 7.64/1.52      ( ~ v1_relat_1(sK2) | k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 7.64/1.52      inference(subtyping,[status(esa)],[c_461]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_1143,plain,
% 7.64/1.52      ( k2_funct_1(sK2) = k4_relat_1(sK2)
% 7.64/1.52      | v1_relat_1(sK2) != iProver_top ),
% 7.64/1.52      inference(predicate_to_equality,[status(thm)],[c_658]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_1441,plain,
% 7.64/1.52      ( k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 7.64/1.52      inference(global_propositional_subsumption,
% 7.64/1.52                [status(thm)],
% 7.64/1.52                [c_1143,c_31,c_658,c_1278,c_1288]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_10,plain,
% 7.64/1.52      ( ~ v1_funct_1(X0)
% 7.64/1.52      | ~ v1_relat_1(X0)
% 7.64/1.52      | v1_relat_1(k2_funct_1(X0)) ),
% 7.64/1.52      inference(cnf_transformation,[],[f60]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_680,plain,
% 7.64/1.52      ( ~ v1_funct_1(X0_50)
% 7.64/1.52      | ~ v1_relat_1(X0_50)
% 7.64/1.52      | v1_relat_1(k2_funct_1(X0_50)) ),
% 7.64/1.52      inference(subtyping,[status(esa)],[c_10]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_1125,plain,
% 7.64/1.52      ( v1_funct_1(X0_50) != iProver_top
% 7.64/1.52      | v1_relat_1(X0_50) != iProver_top
% 7.64/1.52      | v1_relat_1(k2_funct_1(X0_50)) = iProver_top ),
% 7.64/1.52      inference(predicate_to_equality,[status(thm)],[c_680]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_1677,plain,
% 7.64/1.52      ( v1_funct_1(sK2) != iProver_top
% 7.64/1.52      | v1_relat_1(k4_relat_1(sK2)) = iProver_top
% 7.64/1.52      | v1_relat_1(sK2) != iProver_top ),
% 7.64/1.52      inference(superposition,[status(thm)],[c_1441,c_1125]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_33,plain,
% 7.64/1.52      ( v1_funct_1(sK2) = iProver_top ),
% 7.64/1.52      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_2336,plain,
% 7.64/1.52      ( v1_relat_1(k4_relat_1(sK2)) = iProver_top ),
% 7.64/1.52      inference(global_propositional_subsumption,
% 7.64/1.52                [status(thm)],
% 7.64/1.52                [c_1677,c_33,c_34,c_1279,c_1289]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_5,plain,
% 7.64/1.52      ( ~ v1_relat_1(X0)
% 7.64/1.52      | ~ v1_relat_1(X1)
% 7.64/1.52      | ~ v1_relat_1(X2)
% 7.64/1.52      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ),
% 7.64/1.52      inference(cnf_transformation,[],[f56]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_683,plain,
% 7.64/1.52      ( ~ v1_relat_1(X0_50)
% 7.64/1.52      | ~ v1_relat_1(X1_50)
% 7.64/1.52      | ~ v1_relat_1(X2_50)
% 7.64/1.52      | k5_relat_1(k5_relat_1(X0_50,X1_50),X2_50) = k5_relat_1(X0_50,k5_relat_1(X1_50,X2_50)) ),
% 7.64/1.52      inference(subtyping,[status(esa)],[c_5]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_1123,plain,
% 7.64/1.52      ( k5_relat_1(k5_relat_1(X0_50,X1_50),X2_50) = k5_relat_1(X0_50,k5_relat_1(X1_50,X2_50))
% 7.64/1.52      | v1_relat_1(X0_50) != iProver_top
% 7.64/1.52      | v1_relat_1(X1_50) != iProver_top
% 7.64/1.52      | v1_relat_1(X2_50) != iProver_top ),
% 7.64/1.52      inference(predicate_to_equality,[status(thm)],[c_683]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_2340,plain,
% 7.64/1.52      ( k5_relat_1(k4_relat_1(sK2),k5_relat_1(X0_50,X1_50)) = k5_relat_1(k5_relat_1(k4_relat_1(sK2),X0_50),X1_50)
% 7.64/1.52      | v1_relat_1(X0_50) != iProver_top
% 7.64/1.52      | v1_relat_1(X1_50) != iProver_top ),
% 7.64/1.52      inference(superposition,[status(thm)],[c_2336,c_1123]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_16349,plain,
% 7.64/1.52      ( k5_relat_1(k5_relat_1(k4_relat_1(sK2),sK2),X0_50) = k5_relat_1(k4_relat_1(sK2),k5_relat_1(sK2,X0_50))
% 7.64/1.52      | v1_relat_1(X0_50) != iProver_top ),
% 7.64/1.52      inference(superposition,[status(thm)],[c_2010,c_2340]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_16,plain,
% 7.64/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.64/1.52      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 7.64/1.52      inference(cnf_transformation,[],[f67]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_678,plain,
% 7.64/1.52      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 7.64/1.52      | k2_relset_1(X0_51,X1_51,X0_50) = k2_relat_1(X0_50) ),
% 7.64/1.52      inference(subtyping,[status(esa)],[c_16]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_1127,plain,
% 7.64/1.52      ( k2_relset_1(X0_51,X1_51,X0_50) = k2_relat_1(X0_50)
% 7.64/1.52      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top ),
% 7.64/1.52      inference(predicate_to_equality,[status(thm)],[c_678]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_1746,plain,
% 7.64/1.52      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 7.64/1.52      inference(superposition,[status(thm)],[c_1134,c_1127]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_28,negated_conjecture,
% 7.64/1.52      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 7.64/1.52      inference(cnf_transformation,[],[f79]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_670,negated_conjecture,
% 7.64/1.52      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 7.64/1.52      inference(subtyping,[status(esa)],[c_28]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_1748,plain,
% 7.64/1.52      ( k2_relat_1(sK2) = sK1 ),
% 7.64/1.52      inference(light_normalisation,[status(thm)],[c_1746,c_670]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_13,plain,
% 7.64/1.52      ( ~ v1_funct_1(X0)
% 7.64/1.52      | ~ v2_funct_1(X0)
% 7.64/1.52      | ~ v1_relat_1(X0)
% 7.64/1.52      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
% 7.64/1.52      inference(cnf_transformation,[],[f89]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_444,plain,
% 7.64/1.52      ( ~ v1_funct_1(X0)
% 7.64/1.52      | ~ v1_relat_1(X0)
% 7.64/1.52      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
% 7.64/1.52      | sK2 != X0 ),
% 7.64/1.52      inference(resolution_lifted,[status(thm)],[c_13,c_26]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_445,plain,
% 7.64/1.52      ( ~ v1_funct_1(sK2)
% 7.64/1.52      | ~ v1_relat_1(sK2)
% 7.64/1.52      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 7.64/1.52      inference(unflattening,[status(thm)],[c_444]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_447,plain,
% 7.64/1.52      ( ~ v1_relat_1(sK2)
% 7.64/1.52      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 7.64/1.52      inference(global_propositional_subsumption,
% 7.64/1.52                [status(thm)],
% 7.64/1.52                [c_445,c_32]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_659,plain,
% 7.64/1.52      ( ~ v1_relat_1(sK2)
% 7.64/1.52      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 7.64/1.52      inference(subtyping,[status(esa)],[c_447]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_1142,plain,
% 7.64/1.52      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
% 7.64/1.52      | v1_relat_1(sK2) != iProver_top ),
% 7.64/1.52      inference(predicate_to_equality,[status(thm)],[c_659]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_1503,plain,
% 7.64/1.52      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 7.64/1.52      inference(global_propositional_subsumption,
% 7.64/1.52                [status(thm)],
% 7.64/1.52                [c_1142,c_31,c_659,c_1278,c_1288]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_1505,plain,
% 7.64/1.52      ( k5_relat_1(k4_relat_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 7.64/1.52      inference(light_normalisation,[status(thm)],[c_1503,c_1441]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_1750,plain,
% 7.64/1.52      ( k5_relat_1(k4_relat_1(sK2),sK2) = k6_partfun1(sK1) ),
% 7.64/1.52      inference(demodulation,[status(thm)],[c_1748,c_1505]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_16361,plain,
% 7.64/1.52      ( k5_relat_1(k4_relat_1(sK2),k5_relat_1(sK2,X0_50)) = k5_relat_1(k6_partfun1(sK1),X0_50)
% 7.64/1.52      | v1_relat_1(X0_50) != iProver_top ),
% 7.64/1.52      inference(light_normalisation,[status(thm)],[c_16349,c_1750]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_16910,plain,
% 7.64/1.52      ( k5_relat_1(k4_relat_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
% 7.64/1.52      inference(superposition,[status(thm)],[c_2007,c_16361]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_22,plain,
% 7.64/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.64/1.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.64/1.52      | ~ v1_funct_1(X0)
% 7.64/1.52      | ~ v1_funct_1(X3)
% 7.64/1.52      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 7.64/1.52      inference(cnf_transformation,[],[f73]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_674,plain,
% 7.64/1.52      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 7.64/1.52      | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51)))
% 7.64/1.52      | ~ v1_funct_1(X0_50)
% 7.64/1.52      | ~ v1_funct_1(X1_50)
% 7.64/1.52      | k1_partfun1(X2_51,X3_51,X0_51,X1_51,X1_50,X0_50) = k5_relat_1(X1_50,X0_50) ),
% 7.64/1.52      inference(subtyping,[status(esa)],[c_22]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_1131,plain,
% 7.64/1.52      ( k1_partfun1(X0_51,X1_51,X2_51,X3_51,X0_50,X1_50) = k5_relat_1(X0_50,X1_50)
% 7.64/1.52      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 7.64/1.52      | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51))) != iProver_top
% 7.64/1.52      | v1_funct_1(X1_50) != iProver_top
% 7.64/1.52      | v1_funct_1(X0_50) != iProver_top ),
% 7.64/1.52      inference(predicate_to_equality,[status(thm)],[c_674]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_2656,plain,
% 7.64/1.52      ( k1_partfun1(X0_51,X1_51,sK1,sK0,X0_50,sK3) = k5_relat_1(X0_50,sK3)
% 7.64/1.52      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 7.64/1.52      | v1_funct_1(X0_50) != iProver_top
% 7.64/1.52      | v1_funct_1(sK3) != iProver_top ),
% 7.64/1.52      inference(superposition,[status(thm)],[c_1132,c_1131]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_30,negated_conjecture,
% 7.64/1.52      ( v1_funct_1(sK3) ),
% 7.64/1.52      inference(cnf_transformation,[],[f77]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_35,plain,
% 7.64/1.52      ( v1_funct_1(sK3) = iProver_top ),
% 7.64/1.52      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_2853,plain,
% 7.64/1.52      ( v1_funct_1(X0_50) != iProver_top
% 7.64/1.52      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 7.64/1.52      | k1_partfun1(X0_51,X1_51,sK1,sK0,X0_50,sK3) = k5_relat_1(X0_50,sK3) ),
% 7.64/1.52      inference(global_propositional_subsumption,
% 7.64/1.52                [status(thm)],
% 7.64/1.52                [c_2656,c_35]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_2854,plain,
% 7.64/1.52      ( k1_partfun1(X0_51,X1_51,sK1,sK0,X0_50,sK3) = k5_relat_1(X0_50,sK3)
% 7.64/1.52      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 7.64/1.52      | v1_funct_1(X0_50) != iProver_top ),
% 7.64/1.52      inference(renaming,[status(thm)],[c_2853]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_2860,plain,
% 7.64/1.52      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 7.64/1.52      | v1_funct_1(sK2) != iProver_top ),
% 7.64/1.52      inference(superposition,[status(thm)],[c_1134,c_2854]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_18,plain,
% 7.64/1.52      ( ~ r2_relset_1(X0,X1,X2,X3)
% 7.64/1.52      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.64/1.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.64/1.52      | X3 = X2 ),
% 7.64/1.52      inference(cnf_transformation,[],[f68]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_27,negated_conjecture,
% 7.64/1.52      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 7.64/1.52      inference(cnf_transformation,[],[f80]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_359,plain,
% 7.64/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.64/1.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.64/1.52      | X3 = X0
% 7.64/1.52      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 7.64/1.52      | k6_partfun1(sK0) != X3
% 7.64/1.52      | sK0 != X2
% 7.64/1.52      | sK0 != X1 ),
% 7.64/1.52      inference(resolution_lifted,[status(thm)],[c_18,c_27]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_360,plain,
% 7.64/1.52      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.64/1.52      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.64/1.52      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.64/1.52      inference(unflattening,[status(thm)],[c_359]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_21,plain,
% 7.64/1.52      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 7.64/1.52      inference(cnf_transformation,[],[f72]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_43,plain,
% 7.64/1.52      ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 7.64/1.52      inference(instantiation,[status(thm)],[c_21]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_362,plain,
% 7.64/1.52      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.64/1.52      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.64/1.52      inference(global_propositional_subsumption,
% 7.64/1.52                [status(thm)],
% 7.64/1.52                [c_360,c_43]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_664,plain,
% 7.64/1.52      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.64/1.52      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.64/1.52      inference(subtyping,[status(esa)],[c_362]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_1137,plain,
% 7.64/1.52      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.64/1.52      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 7.64/1.52      inference(predicate_to_equality,[status(thm)],[c_664]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_19,plain,
% 7.64/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.64/1.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.64/1.52      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.64/1.52      | ~ v1_funct_1(X0)
% 7.64/1.52      | ~ v1_funct_1(X3) ),
% 7.64/1.52      inference(cnf_transformation,[],[f71]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_677,plain,
% 7.64/1.52      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 7.64/1.52      | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51)))
% 7.64/1.52      | m1_subset_1(k1_partfun1(X2_51,X3_51,X0_51,X1_51,X1_50,X0_50),k1_zfmisc_1(k2_zfmisc_1(X2_51,X1_51)))
% 7.64/1.52      | ~ v1_funct_1(X0_50)
% 7.64/1.52      | ~ v1_funct_1(X1_50) ),
% 7.64/1.52      inference(subtyping,[status(esa)],[c_19]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_1193,plain,
% 7.64/1.52      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.64/1.52      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 7.64/1.52      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.64/1.52      | ~ v1_funct_1(sK3)
% 7.64/1.52      | ~ v1_funct_1(sK2) ),
% 7.64/1.52      inference(instantiation,[status(thm)],[c_677]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_1507,plain,
% 7.64/1.52      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.64/1.52      inference(global_propositional_subsumption,
% 7.64/1.52                [status(thm)],
% 7.64/1.52                [c_1137,c_32,c_31,c_30,c_29,c_664,c_1193]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_2863,plain,
% 7.64/1.52      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 7.64/1.52      | v1_funct_1(sK2) != iProver_top ),
% 7.64/1.52      inference(light_normalisation,[status(thm)],[c_2860,c_1507]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_3072,plain,
% 7.64/1.52      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 7.64/1.52      inference(global_propositional_subsumption,
% 7.64/1.52                [status(thm)],
% 7.64/1.52                [c_2863,c_33]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_15,plain,
% 7.64/1.52      ( v4_relat_1(X0,X1)
% 7.64/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.64/1.52      inference(cnf_transformation,[],[f66]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_2,plain,
% 7.64/1.52      ( r1_tarski(k1_relat_1(X0),X1)
% 7.64/1.52      | ~ v4_relat_1(X0,X1)
% 7.64/1.52      | ~ v1_relat_1(X0) ),
% 7.64/1.52      inference(cnf_transformation,[],[f52]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_320,plain,
% 7.64/1.52      ( r1_tarski(k1_relat_1(X0),X1)
% 7.64/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.64/1.52      | ~ v1_relat_1(X0) ),
% 7.64/1.52      inference(resolution,[status(thm)],[c_15,c_2]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_7,plain,
% 7.64/1.52      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 7.64/1.52      | ~ v1_relat_1(X0)
% 7.64/1.52      | k5_relat_1(k6_partfun1(X1),X0) = X0 ),
% 7.64/1.52      inference(cnf_transformation,[],[f86]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_339,plain,
% 7.64/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.64/1.52      | ~ v1_relat_1(X0)
% 7.64/1.52      | k5_relat_1(k6_partfun1(X1),X0) = X0 ),
% 7.64/1.52      inference(resolution,[status(thm)],[c_320,c_7]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_665,plain,
% 7.64/1.52      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 7.64/1.52      | ~ v1_relat_1(X0_50)
% 7.64/1.52      | k5_relat_1(k6_partfun1(X0_51),X0_50) = X0_50 ),
% 7.64/1.52      inference(subtyping,[status(esa)],[c_339]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_1136,plain,
% 7.64/1.52      ( k5_relat_1(k6_partfun1(X0_51),X0_50) = X0_50
% 7.64/1.52      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 7.64/1.52      | v1_relat_1(X0_50) != iProver_top ),
% 7.64/1.52      inference(predicate_to_equality,[status(thm)],[c_665]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_724,plain,
% 7.64/1.52      ( v1_relat_1(k2_zfmisc_1(X0_51,X1_51)) = iProver_top ),
% 7.64/1.52      inference(predicate_to_equality,[status(thm)],[c_685]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_756,plain,
% 7.64/1.52      ( k5_relat_1(k6_partfun1(X0_51),X0_50) = X0_50
% 7.64/1.52      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 7.64/1.52      | v1_relat_1(X0_50) != iProver_top ),
% 7.64/1.52      inference(predicate_to_equality,[status(thm)],[c_665]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_1273,plain,
% 7.64/1.52      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 7.64/1.52      | v1_relat_1(X0_50)
% 7.64/1.52      | ~ v1_relat_1(k2_zfmisc_1(X0_51,X1_51)) ),
% 7.64/1.52      inference(instantiation,[status(thm)],[c_686]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_1274,plain,
% 7.64/1.52      ( m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 7.64/1.52      | v1_relat_1(X0_50) = iProver_top
% 7.64/1.52      | v1_relat_1(k2_zfmisc_1(X0_51,X1_51)) != iProver_top ),
% 7.64/1.52      inference(predicate_to_equality,[status(thm)],[c_1273]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_3230,plain,
% 7.64/1.52      ( m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 7.64/1.52      | k5_relat_1(k6_partfun1(X0_51),X0_50) = X0_50 ),
% 7.64/1.52      inference(global_propositional_subsumption,
% 7.64/1.52                [status(thm)],
% 7.64/1.52                [c_1136,c_724,c_756,c_1274]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_3231,plain,
% 7.64/1.52      ( k5_relat_1(k6_partfun1(X0_51),X0_50) = X0_50
% 7.64/1.52      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top ),
% 7.64/1.52      inference(renaming,[status(thm)],[c_3230]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_3236,plain,
% 7.64/1.52      ( k5_relat_1(k6_partfun1(sK1),sK3) = sK3 ),
% 7.64/1.52      inference(superposition,[status(thm)],[c_1132,c_3231]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_16920,plain,
% 7.64/1.52      ( k5_relat_1(k4_relat_1(sK2),k6_partfun1(sK0)) = sK3 ),
% 7.64/1.52      inference(light_normalisation,
% 7.64/1.52                [status(thm)],
% 7.64/1.52                [c_16910,c_3072,c_3236]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_17229,plain,
% 7.64/1.52      ( k4_relat_1(k5_relat_1(k6_partfun1(sK0),sK2)) = sK3 ),
% 7.64/1.52      inference(superposition,[status(thm)],[c_2149,c_16920]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_3237,plain,
% 7.64/1.52      ( k5_relat_1(k6_partfun1(sK0),sK2) = sK2 ),
% 7.64/1.52      inference(superposition,[status(thm)],[c_1134,c_3231]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_17231,plain,
% 7.64/1.52      ( k4_relat_1(sK2) = sK3 ),
% 7.64/1.52      inference(light_normalisation,[status(thm)],[c_17229,c_3237]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_23,negated_conjecture,
% 7.64/1.52      ( k2_funct_1(sK2) != sK3 ),
% 7.64/1.52      inference(cnf_transformation,[],[f84]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_673,negated_conjecture,
% 7.64/1.52      ( k2_funct_1(sK2) != sK3 ),
% 7.64/1.52      inference(subtyping,[status(esa)],[c_23]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(c_1443,plain,
% 7.64/1.52      ( k4_relat_1(sK2) != sK3 ),
% 7.64/1.52      inference(demodulation,[status(thm)],[c_1441,c_673]) ).
% 7.64/1.52  
% 7.64/1.52  cnf(contradiction,plain,
% 7.64/1.52      ( $false ),
% 7.64/1.52      inference(minisat,[status(thm)],[c_17231,c_1443]) ).
% 7.64/1.53  
% 7.64/1.53  
% 7.64/1.53  % SZS output end CNFRefutation for theBenchmark.p
% 7.64/1.53  
% 7.64/1.53  ------                               Statistics
% 7.64/1.53  
% 7.64/1.53  ------ General
% 7.64/1.53  
% 7.64/1.53  abstr_ref_over_cycles:                  0
% 7.64/1.53  abstr_ref_under_cycles:                 0
% 7.64/1.53  gc_basic_clause_elim:                   0
% 7.64/1.53  forced_gc_time:                         0
% 7.64/1.53  parsing_time:                           0.007
% 7.64/1.53  unif_index_cands_time:                  0.
% 7.64/1.53  unif_index_add_time:                    0.
% 7.64/1.53  orderings_time:                         0.
% 7.64/1.53  out_proof_time:                         0.012
% 7.64/1.53  total_time:                             0.574
% 7.64/1.53  num_of_symbols:                         56
% 7.64/1.53  num_of_terms:                           22131
% 7.64/1.53  
% 7.64/1.53  ------ Preprocessing
% 7.64/1.53  
% 7.64/1.53  num_of_splits:                          0
% 7.64/1.53  num_of_split_atoms:                     0
% 7.64/1.53  num_of_reused_defs:                     0
% 7.64/1.53  num_eq_ax_congr_red:                    5
% 7.64/1.53  num_of_sem_filtered_clauses:            1
% 7.64/1.53  num_of_subtypes:                        3
% 7.64/1.53  monotx_restored_types:                  0
% 7.64/1.53  sat_num_of_epr_types:                   0
% 7.64/1.53  sat_num_of_non_cyclic_types:            0
% 7.64/1.53  sat_guarded_non_collapsed_types:        1
% 7.64/1.53  num_pure_diseq_elim:                    0
% 7.64/1.53  simp_replaced_by:                       0
% 7.64/1.53  res_preprocessed:                       157
% 7.64/1.53  prep_upred:                             0
% 7.64/1.53  prep_unflattend:                        14
% 7.64/1.53  smt_new_axioms:                         0
% 7.64/1.53  pred_elim_cands:                        3
% 7.64/1.53  pred_elim:                              4
% 7.64/1.53  pred_elim_cl:                           4
% 7.64/1.53  pred_elim_cycles:                       6
% 7.64/1.53  merged_defs:                            0
% 7.64/1.53  merged_defs_ncl:                        0
% 7.64/1.53  bin_hyper_res:                          0
% 7.64/1.53  prep_cycles:                            4
% 7.64/1.53  pred_elim_time:                         0.002
% 7.64/1.53  splitting_time:                         0.
% 7.64/1.53  sem_filter_time:                        0.
% 7.64/1.53  monotx_time:                            0.
% 7.64/1.53  subtype_inf_time:                       0.
% 7.64/1.53  
% 7.64/1.53  ------ Problem properties
% 7.64/1.53  
% 7.64/1.53  clauses:                                29
% 7.64/1.53  conjectures:                            8
% 7.64/1.53  epr:                                    4
% 7.64/1.53  horn:                                   29
% 7.64/1.53  ground:                                 12
% 7.64/1.53  unary:                                  12
% 7.64/1.53  binary:                                 8
% 7.64/1.53  lits:                                   62
% 7.64/1.53  lits_eq:                                17
% 7.64/1.53  fd_pure:                                0
% 7.64/1.53  fd_pseudo:                              0
% 7.64/1.53  fd_cond:                                0
% 7.64/1.53  fd_pseudo_cond:                         0
% 7.64/1.53  ac_symbols:                             0
% 7.64/1.53  
% 7.64/1.53  ------ Propositional Solver
% 7.64/1.53  
% 7.64/1.53  prop_solver_calls:                      35
% 7.64/1.53  prop_fast_solver_calls:                 1300
% 7.64/1.53  smt_solver_calls:                       0
% 7.64/1.53  smt_fast_solver_calls:                  0
% 7.64/1.53  prop_num_of_clauses:                    7593
% 7.64/1.53  prop_preprocess_simplified:             17415
% 7.64/1.53  prop_fo_subsumed:                       83
% 7.64/1.53  prop_solver_time:                       0.
% 7.64/1.53  smt_solver_time:                        0.
% 7.64/1.53  smt_fast_solver_time:                   0.
% 7.64/1.53  prop_fast_solver_time:                  0.
% 7.64/1.53  prop_unsat_core_time:                   0.001
% 7.64/1.53  
% 7.64/1.53  ------ QBF
% 7.64/1.53  
% 7.64/1.53  qbf_q_res:                              0
% 7.64/1.53  qbf_num_tautologies:                    0
% 7.64/1.53  qbf_prep_cycles:                        0
% 7.64/1.53  
% 7.64/1.53  ------ BMC1
% 7.64/1.53  
% 7.64/1.53  bmc1_current_bound:                     -1
% 7.64/1.53  bmc1_last_solved_bound:                 -1
% 7.64/1.53  bmc1_unsat_core_size:                   -1
% 7.64/1.53  bmc1_unsat_core_parents_size:           -1
% 7.64/1.53  bmc1_merge_next_fun:                    0
% 7.64/1.53  bmc1_unsat_core_clauses_time:           0.
% 7.64/1.53  
% 7.64/1.53  ------ Instantiation
% 7.64/1.53  
% 7.64/1.53  inst_num_of_clauses:                    2644
% 7.64/1.53  inst_num_in_passive:                    966
% 7.64/1.53  inst_num_in_active:                     1118
% 7.64/1.53  inst_num_in_unprocessed:                560
% 7.64/1.53  inst_num_of_loops:                      1200
% 7.64/1.53  inst_num_of_learning_restarts:          0
% 7.64/1.53  inst_num_moves_active_passive:          72
% 7.64/1.53  inst_lit_activity:                      0
% 7.64/1.53  inst_lit_activity_moves:                0
% 7.64/1.53  inst_num_tautologies:                   0
% 7.64/1.53  inst_num_prop_implied:                  0
% 7.64/1.53  inst_num_existing_simplified:           0
% 7.64/1.53  inst_num_eq_res_simplified:             0
% 7.64/1.53  inst_num_child_elim:                    0
% 7.64/1.53  inst_num_of_dismatching_blockings:      2434
% 7.64/1.53  inst_num_of_non_proper_insts:           3392
% 7.64/1.53  inst_num_of_duplicates:                 0
% 7.64/1.53  inst_inst_num_from_inst_to_res:         0
% 7.64/1.53  inst_dismatching_checking_time:         0.
% 7.64/1.53  
% 7.64/1.53  ------ Resolution
% 7.64/1.53  
% 7.64/1.53  res_num_of_clauses:                     0
% 7.64/1.53  res_num_in_passive:                     0
% 7.64/1.53  res_num_in_active:                      0
% 7.64/1.53  res_num_of_loops:                       161
% 7.64/1.53  res_forward_subset_subsumed:            252
% 7.64/1.53  res_backward_subset_subsumed:           14
% 7.64/1.53  res_forward_subsumed:                   0
% 7.64/1.53  res_backward_subsumed:                  0
% 7.64/1.53  res_forward_subsumption_resolution:     0
% 7.64/1.53  res_backward_subsumption_resolution:    0
% 7.64/1.53  res_clause_to_clause_subsumption:       1384
% 7.64/1.53  res_orphan_elimination:                 0
% 7.64/1.53  res_tautology_del:                      389
% 7.64/1.53  res_num_eq_res_simplified:              0
% 7.64/1.53  res_num_sel_changes:                    0
% 7.64/1.53  res_moves_from_active_to_pass:          0
% 7.64/1.53  
% 7.64/1.53  ------ Superposition
% 7.64/1.53  
% 7.64/1.53  sup_time_total:                         0.
% 7.64/1.53  sup_time_generating:                    0.
% 7.64/1.53  sup_time_sim_full:                      0.
% 7.64/1.53  sup_time_sim_immed:                     0.
% 7.64/1.53  
% 7.64/1.53  sup_num_of_clauses:                     567
% 7.64/1.53  sup_num_in_active:                      200
% 7.64/1.53  sup_num_in_passive:                     367
% 7.64/1.53  sup_num_of_loops:                       239
% 7.64/1.53  sup_fw_superposition:                   530
% 7.64/1.53  sup_bw_superposition:                   84
% 7.64/1.53  sup_immediate_simplified:               211
% 7.64/1.53  sup_given_eliminated:                   2
% 7.64/1.53  comparisons_done:                       0
% 7.64/1.53  comparisons_avoided:                    0
% 7.64/1.53  
% 7.64/1.53  ------ Simplifications
% 7.64/1.53  
% 7.64/1.53  
% 7.64/1.53  sim_fw_subset_subsumed:                 7
% 7.64/1.53  sim_bw_subset_subsumed:                 22
% 7.64/1.53  sim_fw_subsumed:                        11
% 7.64/1.53  sim_bw_subsumed:                        3
% 7.64/1.53  sim_fw_subsumption_res:                 0
% 7.64/1.53  sim_bw_subsumption_res:                 0
% 7.64/1.53  sim_tautology_del:                      4
% 7.64/1.53  sim_eq_tautology_del:                   39
% 7.64/1.53  sim_eq_res_simp:                        0
% 7.64/1.53  sim_fw_demodulated:                     31
% 7.64/1.53  sim_bw_demodulated:                     29
% 7.64/1.53  sim_light_normalised:                   207
% 7.64/1.53  sim_joinable_taut:                      0
% 7.64/1.53  sim_joinable_simp:                      0
% 7.64/1.53  sim_ac_normalised:                      0
% 7.64/1.53  sim_smt_subsumption:                    0
% 7.64/1.53  
%------------------------------------------------------------------------------
