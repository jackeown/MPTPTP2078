%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:25 EST 2020

% Result     : Theorem 27.52s
% Output     : CNFRefutation 27.52s
% Verified   : 
% Statistics : Number of formulae       :  222 (1068 expanded)
%              Number of clauses        :  130 ( 328 expanded)
%              Number of leaves         :   25 ( 272 expanded)
%              Depth                    :   21
%              Number of atoms          :  864 (8919 expanded)
%              Number of equality atoms :  424 (3352 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   24 (   3 average)
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
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

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
    inference(flattening,[],[f49])).

fof(f55,plain,(
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

fof(f54,plain,
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

fof(f56,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f50,f55,f54])).

fof(f90,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
          & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f28,plain,(
    ! [X0] :
      ( ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f65,plain,(
    ! [X0] :
      ( k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f96,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f56])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
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
    inference(flattening,[],[f47])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f91,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f56])).

fof(f92,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f56])).

fof(f98,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f100,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f56])).

fof(f3,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f17,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f85,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f17])).

fof(f103,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f59,f85])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

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

fof(f57,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f95,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f56])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f37])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f94,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f56])).

fof(f99,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f56])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => ( v2_funct_1(X0)
              & v2_funct_1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X0)
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f93,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f43])).

fof(f84,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f97,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f56])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f41])).

fof(f82,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f35])).

fof(f51,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f15,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f83,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0)
              & k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f106,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f67,f85])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f39])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f18,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( v2_funct_2(X3,X0)
            & v2_funct_1(X2) )
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( v2_funct_2(X3,X0)
            & v2_funct_1(X2) )
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f45])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_funct_2(X3,X0)
      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f4,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f104,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f62,f85])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f32,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f68,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f107,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f72])).

fof(f101,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1144,plain,
    ( X0 != X1
    | k2_funct_1(X0) = k2_funct_1(X1) ),
    theory(equality)).

cnf(c_71349,plain,
    ( k2_funct_1(sK2) = k2_funct_1(k2_funct_1(sK3))
    | sK2 != k2_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1144])).

cnf(c_1133,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_50349,plain,
    ( k2_funct_1(sK2) != X0
    | k2_funct_1(sK2) = sK3
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_1133])).

cnf(c_61532,plain,
    ( k2_funct_1(sK2) != k2_funct_1(k2_funct_1(sK3))
    | k2_funct_1(sK2) = sK3
    | sK3 != k2_funct_1(k2_funct_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_50349])).

cnf(c_3633,plain,
    ( X0 != X1
    | sK2 != X1
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_1133])).

cnf(c_7011,plain,
    ( X0 != sK2
    | sK2 = X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_3633])).

cnf(c_14718,plain,
    ( k2_funct_1(X0) != sK2
    | sK2 = k2_funct_1(X0)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_7011])).

cnf(c_36112,plain,
    ( k2_funct_1(sK3) != sK2
    | sK2 = k2_funct_1(sK3)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_14718])).

cnf(c_43,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1708,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_9,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1734,plain,
    ( k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4103,plain,
    ( k1_relat_1(k5_relat_1(k2_funct_1(sK2),sK2)) = k2_relat_1(sK2)
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1708,c_1734])).

cnf(c_37,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_30,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1717,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_3426,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_37,c_1717])).

cnf(c_42,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_41,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_35,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_33,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1806,plain,
    ( ~ v1_funct_2(X0,X1,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,sK1,X0) != sK1
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(sK1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_2000,plain,
    ( ~ v1_funct_2(sK2,X0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(X0,sK1,sK2) != sK1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1806])).

cnf(c_2084,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(sK0,sK1,sK2) != sK1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_2000])).

cnf(c_3646,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3426,c_43,c_42,c_41,c_37,c_35,c_33,c_2084])).

cnf(c_4104,plain,
    ( k1_relat_1(k6_partfun1(sK1)) = k2_relat_1(sK2)
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4103,c_3646])).

cnf(c_3,plain,
    ( k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_4105,plain,
    ( k2_relat_1(sK2) = sK1
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4104,c_3])).

cnf(c_51,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1740,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1710,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1741,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2992,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1710,c_1741])).

cnf(c_3364,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1740,c_2992])).

cnf(c_4209,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4105,c_51,c_3364])).

cnf(c_38,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1713,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1723,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4367,plain,
    ( k1_relset_1(sK1,sK0,sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1713,c_1723])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1731,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2859,plain,
    ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1713,c_1731])).

cnf(c_4370,plain,
    ( k1_relat_1(sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4367,c_2859])).

cnf(c_39,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_48,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_34,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1132,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1167,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1132])).

cnf(c_1859,plain,
    ( sK0 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_1133])).

cnf(c_1860,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1859])).

cnf(c_6996,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4370,c_48,c_34,c_1167,c_1860])).

cnf(c_6,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | v2_funct_1(X1)
    | ~ v2_funct_1(k5_relat_1(X0,X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X1) != k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1737,plain,
    ( k1_relat_1(X0) != k2_relat_1(X1)
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) = iProver_top
    | v2_funct_1(k5_relat_1(X1,X0)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_7000,plain,
    ( k2_relat_1(X0) != sK1
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6996,c_1737])).

cnf(c_40,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_47,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_2991,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1713,c_1741])).

cnf(c_3066,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3067,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3066])).

cnf(c_31501,plain,
    ( v1_relat_1(X0) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
    | k2_relat_1(X0) != sK1
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7000,c_47,c_2991,c_3067])).

cnf(c_31502,plain,
    ( k2_relat_1(X0) != sK1
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_31501])).

cnf(c_31508,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4209,c_31502])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1719,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_5325,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1713,c_1719])).

cnf(c_5691,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5325,c_47])).

cnf(c_5692,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_5691])).

cnf(c_5699,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1710,c_5692])).

cnf(c_44,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_5899,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5699,c_44])).

cnf(c_36,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1714,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_5901,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5899,c_1714])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1722,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_6143,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5899,c_1722])).

cnf(c_46,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_49,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_7913,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6143,c_44,c_46,c_47,c_49])).

cnf(c_15,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1729,plain,
    ( X0 = X1
    | r2_relset_1(X2,X3,X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_7924,plain,
    ( k5_relat_1(sK2,sK3) = X0
    | r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7913,c_1729])).

cnf(c_9859,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5901,c_7924])).

cnf(c_26,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2142,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_2143,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2142])).

cnf(c_10314,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9859,c_2143])).

cnf(c_31511,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_31508,c_10314])).

cnf(c_10,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k1_relat_1(X1) != k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_1733,plain,
    ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k1_relat_1(X1) != k2_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v2_funct_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_10330,plain,
    ( k2_funct_1(sK3) = sK2
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_10314,c_1733])).

cnf(c_3296,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2991,c_3067])).

cnf(c_23,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_28,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | v2_funct_2(X3,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_471,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ v5_relat_1(X4,X5)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X4)
    | X3 != X4
    | X0 != X5
    | k2_relat_1(X4) = X5 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_28])).

cnf(c_472,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ v5_relat_1(X3,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X3)
    | k2_relat_1(X3) = X0 ),
    inference(unflattening,[status(thm)],[c_471])).

cnf(c_12,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_496,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X3)
    | k2_relat_1(X3) = X0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_472,c_12])).

cnf(c_1707,plain,
    ( k2_relat_1(X0) = X1
    | r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X0),k6_partfun1(X1)) != iProver_top
    | v1_funct_2(X3,X1,X2) != iProver_top
    | v1_funct_2(X0,X2,X1) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_496])).

cnf(c_2690,plain,
    ( k2_relat_1(sK3) = sK0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1714,c_1707])).

cnf(c_45,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_2693,plain,
    ( k2_relat_1(sK3) = sK0
    | v1_relat_1(sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2690,c_44,c_45,c_46,c_47,c_48,c_49])).

cnf(c_3300,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(superposition,[status(thm)],[c_3296,c_2693])).

cnf(c_10331,plain,
    ( k2_funct_1(sK3) = sK2
    | k6_partfun1(sK0) != k6_partfun1(sK0)
    | sK1 != sK1
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10330,c_3300,c_4209,c_6996])).

cnf(c_10332,plain,
    ( k2_funct_1(sK3) = sK2
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_10331])).

cnf(c_4,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_9060,plain,
    ( v2_funct_1(k6_partfun1(sK0)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_9061,plain,
    ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9060])).

cnf(c_1903,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_1133])).

cnf(c_2211,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1903])).

cnf(c_4020,plain,
    ( k2_funct_1(X0) != sK3
    | sK3 = k2_funct_1(X0)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2211])).

cnf(c_6113,plain,
    ( k2_funct_1(k2_funct_1(sK3)) != sK3
    | sK3 = k2_funct_1(k2_funct_1(sK3))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_4020])).

cnf(c_1711,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_11,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1732,plain,
    ( k2_funct_1(k2_funct_1(X0)) = X0
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3429,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = sK3
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1711,c_1732])).

cnf(c_3397,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1132])).

cnf(c_14,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1730,plain,
    ( r2_relset_1(X0,X1,X2,X2) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2809,plain,
    ( r2_relset_1(sK1,sK0,sK3,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1713,c_1730])).

cnf(c_1897,plain,
    ( ~ r2_relset_1(X0,X1,X2,sK3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | sK3 = X2 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_2283,plain,
    ( ~ r2_relset_1(sK1,sK0,X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_1897])).

cnf(c_2415,plain,
    ( ~ r2_relset_1(sK1,sK0,sK3,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_2283])).

cnf(c_2416,plain,
    ( sK3 = sK3
    | r2_relset_1(sK1,sK0,sK3,sK3) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2415])).

cnf(c_32,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f101])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_71349,c_61532,c_36112,c_31511,c_10332,c_9061,c_6113,c_3429,c_3397,c_3364,c_3067,c_2991,c_2809,c_2416,c_32,c_49,c_47,c_44])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:55:16 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 27.52/4.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.52/4.00  
% 27.52/4.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.52/4.00  
% 27.52/4.00  ------  iProver source info
% 27.52/4.00  
% 27.52/4.00  git: date: 2020-06-30 10:37:57 +0100
% 27.52/4.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.52/4.00  git: non_committed_changes: false
% 27.52/4.00  git: last_make_outside_of_git: false
% 27.52/4.00  
% 27.52/4.00  ------ 
% 27.52/4.00  
% 27.52/4.00  ------ Input Options
% 27.52/4.00  
% 27.52/4.00  --out_options                           all
% 27.52/4.00  --tptp_safe_out                         true
% 27.52/4.00  --problem_path                          ""
% 27.52/4.00  --include_path                          ""
% 27.52/4.00  --clausifier                            res/vclausify_rel
% 27.52/4.00  --clausifier_options                    ""
% 27.52/4.00  --stdin                                 false
% 27.52/4.00  --stats_out                             all
% 27.52/4.00  
% 27.52/4.00  ------ General Options
% 27.52/4.00  
% 27.52/4.00  --fof                                   false
% 27.52/4.00  --time_out_real                         305.
% 27.52/4.00  --time_out_virtual                      -1.
% 27.52/4.00  --symbol_type_check                     false
% 27.52/4.00  --clausify_out                          false
% 27.52/4.00  --sig_cnt_out                           false
% 27.52/4.00  --trig_cnt_out                          false
% 27.52/4.00  --trig_cnt_out_tolerance                1.
% 27.52/4.00  --trig_cnt_out_sk_spl                   false
% 27.52/4.00  --abstr_cl_out                          false
% 27.52/4.00  
% 27.52/4.00  ------ Global Options
% 27.52/4.00  
% 27.52/4.00  --schedule                              default
% 27.52/4.00  --add_important_lit                     false
% 27.52/4.00  --prop_solver_per_cl                    1000
% 27.52/4.00  --min_unsat_core                        false
% 27.52/4.00  --soft_assumptions                      false
% 27.52/4.00  --soft_lemma_size                       3
% 27.52/4.00  --prop_impl_unit_size                   0
% 27.52/4.00  --prop_impl_unit                        []
% 27.52/4.00  --share_sel_clauses                     true
% 27.52/4.00  --reset_solvers                         false
% 27.52/4.00  --bc_imp_inh                            [conj_cone]
% 27.52/4.00  --conj_cone_tolerance                   3.
% 27.52/4.00  --extra_neg_conj                        none
% 27.52/4.00  --large_theory_mode                     true
% 27.52/4.00  --prolific_symb_bound                   200
% 27.52/4.00  --lt_threshold                          2000
% 27.52/4.00  --clause_weak_htbl                      true
% 27.52/4.00  --gc_record_bc_elim                     false
% 27.52/4.00  
% 27.52/4.00  ------ Preprocessing Options
% 27.52/4.00  
% 27.52/4.00  --preprocessing_flag                    true
% 27.52/4.00  --time_out_prep_mult                    0.1
% 27.52/4.00  --splitting_mode                        input
% 27.52/4.00  --splitting_grd                         true
% 27.52/4.00  --splitting_cvd                         false
% 27.52/4.00  --splitting_cvd_svl                     false
% 27.52/4.00  --splitting_nvd                         32
% 27.52/4.00  --sub_typing                            true
% 27.52/4.00  --prep_gs_sim                           true
% 27.52/4.00  --prep_unflatten                        true
% 27.52/4.00  --prep_res_sim                          true
% 27.52/4.00  --prep_upred                            true
% 27.52/4.00  --prep_sem_filter                       exhaustive
% 27.52/4.00  --prep_sem_filter_out                   false
% 27.52/4.00  --pred_elim                             true
% 27.52/4.00  --res_sim_input                         true
% 27.52/4.00  --eq_ax_congr_red                       true
% 27.52/4.00  --pure_diseq_elim                       true
% 27.52/4.00  --brand_transform                       false
% 27.52/4.00  --non_eq_to_eq                          false
% 27.52/4.00  --prep_def_merge                        true
% 27.52/4.00  --prep_def_merge_prop_impl              false
% 27.52/4.00  --prep_def_merge_mbd                    true
% 27.52/4.00  --prep_def_merge_tr_red                 false
% 27.52/4.00  --prep_def_merge_tr_cl                  false
% 27.52/4.00  --smt_preprocessing                     true
% 27.52/4.00  --smt_ac_axioms                         fast
% 27.52/4.00  --preprocessed_out                      false
% 27.52/4.00  --preprocessed_stats                    false
% 27.52/4.00  
% 27.52/4.00  ------ Abstraction refinement Options
% 27.52/4.00  
% 27.52/4.00  --abstr_ref                             []
% 27.52/4.00  --abstr_ref_prep                        false
% 27.52/4.00  --abstr_ref_until_sat                   false
% 27.52/4.00  --abstr_ref_sig_restrict                funpre
% 27.52/4.00  --abstr_ref_af_restrict_to_split_sk     false
% 27.52/4.00  --abstr_ref_under                       []
% 27.52/4.00  
% 27.52/4.00  ------ SAT Options
% 27.52/4.00  
% 27.52/4.00  --sat_mode                              false
% 27.52/4.00  --sat_fm_restart_options                ""
% 27.52/4.00  --sat_gr_def                            false
% 27.52/4.00  --sat_epr_types                         true
% 27.52/4.00  --sat_non_cyclic_types                  false
% 27.52/4.00  --sat_finite_models                     false
% 27.52/4.00  --sat_fm_lemmas                         false
% 27.52/4.00  --sat_fm_prep                           false
% 27.52/4.00  --sat_fm_uc_incr                        true
% 27.52/4.00  --sat_out_model                         small
% 27.52/4.00  --sat_out_clauses                       false
% 27.52/4.00  
% 27.52/4.00  ------ QBF Options
% 27.52/4.00  
% 27.52/4.00  --qbf_mode                              false
% 27.52/4.00  --qbf_elim_univ                         false
% 27.52/4.00  --qbf_dom_inst                          none
% 27.52/4.00  --qbf_dom_pre_inst                      false
% 27.52/4.00  --qbf_sk_in                             false
% 27.52/4.00  --qbf_pred_elim                         true
% 27.52/4.00  --qbf_split                             512
% 27.52/4.00  
% 27.52/4.00  ------ BMC1 Options
% 27.52/4.00  
% 27.52/4.00  --bmc1_incremental                      false
% 27.52/4.00  --bmc1_axioms                           reachable_all
% 27.52/4.00  --bmc1_min_bound                        0
% 27.52/4.00  --bmc1_max_bound                        -1
% 27.52/4.00  --bmc1_max_bound_default                -1
% 27.52/4.00  --bmc1_symbol_reachability              true
% 27.52/4.00  --bmc1_property_lemmas                  false
% 27.52/4.00  --bmc1_k_induction                      false
% 27.52/4.00  --bmc1_non_equiv_states                 false
% 27.52/4.00  --bmc1_deadlock                         false
% 27.52/4.00  --bmc1_ucm                              false
% 27.52/4.00  --bmc1_add_unsat_core                   none
% 27.52/4.00  --bmc1_unsat_core_children              false
% 27.52/4.00  --bmc1_unsat_core_extrapolate_axioms    false
% 27.52/4.00  --bmc1_out_stat                         full
% 27.52/4.00  --bmc1_ground_init                      false
% 27.52/4.00  --bmc1_pre_inst_next_state              false
% 27.52/4.00  --bmc1_pre_inst_state                   false
% 27.52/4.00  --bmc1_pre_inst_reach_state             false
% 27.52/4.00  --bmc1_out_unsat_core                   false
% 27.52/4.00  --bmc1_aig_witness_out                  false
% 27.52/4.00  --bmc1_verbose                          false
% 27.52/4.00  --bmc1_dump_clauses_tptp                false
% 27.52/4.00  --bmc1_dump_unsat_core_tptp             false
% 27.52/4.00  --bmc1_dump_file                        -
% 27.52/4.00  --bmc1_ucm_expand_uc_limit              128
% 27.52/4.00  --bmc1_ucm_n_expand_iterations          6
% 27.52/4.00  --bmc1_ucm_extend_mode                  1
% 27.52/4.00  --bmc1_ucm_init_mode                    2
% 27.52/4.00  --bmc1_ucm_cone_mode                    none
% 27.52/4.00  --bmc1_ucm_reduced_relation_type        0
% 27.52/4.00  --bmc1_ucm_relax_model                  4
% 27.52/4.00  --bmc1_ucm_full_tr_after_sat            true
% 27.52/4.00  --bmc1_ucm_expand_neg_assumptions       false
% 27.52/4.00  --bmc1_ucm_layered_model                none
% 27.52/4.00  --bmc1_ucm_max_lemma_size               10
% 27.52/4.00  
% 27.52/4.00  ------ AIG Options
% 27.52/4.00  
% 27.52/4.00  --aig_mode                              false
% 27.52/4.00  
% 27.52/4.00  ------ Instantiation Options
% 27.52/4.00  
% 27.52/4.00  --instantiation_flag                    true
% 27.52/4.00  --inst_sos_flag                         true
% 27.52/4.00  --inst_sos_phase                        true
% 27.52/4.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.52/4.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.52/4.00  --inst_lit_sel_side                     num_symb
% 27.52/4.00  --inst_solver_per_active                1400
% 27.52/4.00  --inst_solver_calls_frac                1.
% 27.52/4.00  --inst_passive_queue_type               priority_queues
% 27.52/4.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.52/4.00  --inst_passive_queues_freq              [25;2]
% 27.52/4.00  --inst_dismatching                      true
% 27.52/4.00  --inst_eager_unprocessed_to_passive     true
% 27.52/4.00  --inst_prop_sim_given                   true
% 27.52/4.00  --inst_prop_sim_new                     false
% 27.52/4.00  --inst_subs_new                         false
% 27.52/4.00  --inst_eq_res_simp                      false
% 27.52/4.00  --inst_subs_given                       false
% 27.52/4.00  --inst_orphan_elimination               true
% 27.52/4.00  --inst_learning_loop_flag               true
% 27.52/4.00  --inst_learning_start                   3000
% 27.52/4.00  --inst_learning_factor                  2
% 27.52/4.00  --inst_start_prop_sim_after_learn       3
% 27.52/4.00  --inst_sel_renew                        solver
% 27.52/4.00  --inst_lit_activity_flag                true
% 27.52/4.00  --inst_restr_to_given                   false
% 27.52/4.00  --inst_activity_threshold               500
% 27.52/4.00  --inst_out_proof                        true
% 27.52/4.00  
% 27.52/4.00  ------ Resolution Options
% 27.52/4.00  
% 27.52/4.00  --resolution_flag                       true
% 27.52/4.00  --res_lit_sel                           adaptive
% 27.52/4.00  --res_lit_sel_side                      none
% 27.52/4.00  --res_ordering                          kbo
% 27.52/4.00  --res_to_prop_solver                    active
% 27.52/4.00  --res_prop_simpl_new                    false
% 27.52/4.00  --res_prop_simpl_given                  true
% 27.52/4.00  --res_passive_queue_type                priority_queues
% 27.52/4.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.52/4.00  --res_passive_queues_freq               [15;5]
% 27.52/4.00  --res_forward_subs                      full
% 27.52/4.00  --res_backward_subs                     full
% 27.52/4.00  --res_forward_subs_resolution           true
% 27.52/4.00  --res_backward_subs_resolution          true
% 27.52/4.00  --res_orphan_elimination                true
% 27.52/4.00  --res_time_limit                        2.
% 27.52/4.00  --res_out_proof                         true
% 27.52/4.00  
% 27.52/4.00  ------ Superposition Options
% 27.52/4.00  
% 27.52/4.00  --superposition_flag                    true
% 27.52/4.00  --sup_passive_queue_type                priority_queues
% 27.52/4.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.52/4.00  --sup_passive_queues_freq               [8;1;4]
% 27.52/4.00  --demod_completeness_check              fast
% 27.52/4.00  --demod_use_ground                      true
% 27.52/4.00  --sup_to_prop_solver                    passive
% 27.52/4.00  --sup_prop_simpl_new                    true
% 27.52/4.00  --sup_prop_simpl_given                  true
% 27.52/4.00  --sup_fun_splitting                     true
% 27.52/4.00  --sup_smt_interval                      50000
% 27.52/4.00  
% 27.52/4.00  ------ Superposition Simplification Setup
% 27.52/4.00  
% 27.52/4.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 27.52/4.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 27.52/4.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 27.52/4.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 27.52/4.00  --sup_full_triv                         [TrivRules;PropSubs]
% 27.52/4.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 27.52/4.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 27.52/4.00  --sup_immed_triv                        [TrivRules]
% 27.52/4.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.52/4.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.52/4.00  --sup_immed_bw_main                     []
% 27.52/4.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 27.52/4.00  --sup_input_triv                        [Unflattening;TrivRules]
% 27.52/4.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.52/4.00  --sup_input_bw                          []
% 27.52/4.00  
% 27.52/4.00  ------ Combination Options
% 27.52/4.00  
% 27.52/4.00  --comb_res_mult                         3
% 27.52/4.00  --comb_sup_mult                         2
% 27.52/4.00  --comb_inst_mult                        10
% 27.52/4.00  
% 27.52/4.00  ------ Debug Options
% 27.52/4.00  
% 27.52/4.00  --dbg_backtrace                         false
% 27.52/4.00  --dbg_dump_prop_clauses                 false
% 27.52/4.00  --dbg_dump_prop_clauses_file            -
% 27.52/4.00  --dbg_out_stat                          false
% 27.52/4.00  ------ Parsing...
% 27.52/4.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.52/4.00  
% 27.52/4.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 27.52/4.00  
% 27.52/4.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.52/4.00  
% 27.52/4.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.52/4.00  ------ Proving...
% 27.52/4.00  ------ Problem Properties 
% 27.52/4.00  
% 27.52/4.00  
% 27.52/4.00  clauses                                 41
% 27.52/4.00  conjectures                             12
% 27.52/4.00  EPR                                     7
% 27.52/4.00  Horn                                    35
% 27.52/4.00  unary                                   18
% 27.52/4.00  binary                                  2
% 27.52/4.00  lits                                    130
% 27.52/4.00  lits eq                                 33
% 27.52/4.00  fd_pure                                 0
% 27.52/4.00  fd_pseudo                               0
% 27.52/4.00  fd_cond                                 5
% 27.52/4.00  fd_pseudo_cond                          3
% 27.52/4.00  AC symbols                              0
% 27.52/4.00  
% 27.52/4.00  ------ Schedule dynamic 5 is on 
% 27.52/4.00  
% 27.52/4.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 27.52/4.00  
% 27.52/4.00  
% 27.52/4.00  ------ 
% 27.52/4.00  Current options:
% 27.52/4.00  ------ 
% 27.52/4.00  
% 27.52/4.00  ------ Input Options
% 27.52/4.00  
% 27.52/4.00  --out_options                           all
% 27.52/4.00  --tptp_safe_out                         true
% 27.52/4.00  --problem_path                          ""
% 27.52/4.00  --include_path                          ""
% 27.52/4.00  --clausifier                            res/vclausify_rel
% 27.52/4.00  --clausifier_options                    ""
% 27.52/4.00  --stdin                                 false
% 27.52/4.00  --stats_out                             all
% 27.52/4.00  
% 27.52/4.00  ------ General Options
% 27.52/4.00  
% 27.52/4.00  --fof                                   false
% 27.52/4.00  --time_out_real                         305.
% 27.52/4.00  --time_out_virtual                      -1.
% 27.52/4.00  --symbol_type_check                     false
% 27.52/4.00  --clausify_out                          false
% 27.52/4.00  --sig_cnt_out                           false
% 27.52/4.00  --trig_cnt_out                          false
% 27.52/4.00  --trig_cnt_out_tolerance                1.
% 27.52/4.00  --trig_cnt_out_sk_spl                   false
% 27.52/4.00  --abstr_cl_out                          false
% 27.52/4.00  
% 27.52/4.00  ------ Global Options
% 27.52/4.00  
% 27.52/4.00  --schedule                              default
% 27.52/4.00  --add_important_lit                     false
% 27.52/4.00  --prop_solver_per_cl                    1000
% 27.52/4.00  --min_unsat_core                        false
% 27.52/4.00  --soft_assumptions                      false
% 27.52/4.00  --soft_lemma_size                       3
% 27.52/4.00  --prop_impl_unit_size                   0
% 27.52/4.00  --prop_impl_unit                        []
% 27.52/4.00  --share_sel_clauses                     true
% 27.52/4.00  --reset_solvers                         false
% 27.52/4.00  --bc_imp_inh                            [conj_cone]
% 27.52/4.00  --conj_cone_tolerance                   3.
% 27.52/4.00  --extra_neg_conj                        none
% 27.52/4.00  --large_theory_mode                     true
% 27.52/4.00  --prolific_symb_bound                   200
% 27.52/4.01  --lt_threshold                          2000
% 27.52/4.01  --clause_weak_htbl                      true
% 27.52/4.01  --gc_record_bc_elim                     false
% 27.52/4.01  
% 27.52/4.01  ------ Preprocessing Options
% 27.52/4.01  
% 27.52/4.01  --preprocessing_flag                    true
% 27.52/4.01  --time_out_prep_mult                    0.1
% 27.52/4.01  --splitting_mode                        input
% 27.52/4.01  --splitting_grd                         true
% 27.52/4.01  --splitting_cvd                         false
% 27.52/4.01  --splitting_cvd_svl                     false
% 27.52/4.01  --splitting_nvd                         32
% 27.52/4.01  --sub_typing                            true
% 27.52/4.01  --prep_gs_sim                           true
% 27.52/4.01  --prep_unflatten                        true
% 27.52/4.01  --prep_res_sim                          true
% 27.52/4.01  --prep_upred                            true
% 27.52/4.01  --prep_sem_filter                       exhaustive
% 27.52/4.01  --prep_sem_filter_out                   false
% 27.52/4.01  --pred_elim                             true
% 27.52/4.01  --res_sim_input                         true
% 27.52/4.01  --eq_ax_congr_red                       true
% 27.52/4.01  --pure_diseq_elim                       true
% 27.52/4.01  --brand_transform                       false
% 27.52/4.01  --non_eq_to_eq                          false
% 27.52/4.01  --prep_def_merge                        true
% 27.52/4.01  --prep_def_merge_prop_impl              false
% 27.52/4.01  --prep_def_merge_mbd                    true
% 27.52/4.01  --prep_def_merge_tr_red                 false
% 27.52/4.01  --prep_def_merge_tr_cl                  false
% 27.52/4.01  --smt_preprocessing                     true
% 27.52/4.01  --smt_ac_axioms                         fast
% 27.52/4.01  --preprocessed_out                      false
% 27.52/4.01  --preprocessed_stats                    false
% 27.52/4.01  
% 27.52/4.01  ------ Abstraction refinement Options
% 27.52/4.01  
% 27.52/4.01  --abstr_ref                             []
% 27.52/4.01  --abstr_ref_prep                        false
% 27.52/4.01  --abstr_ref_until_sat                   false
% 27.52/4.01  --abstr_ref_sig_restrict                funpre
% 27.52/4.01  --abstr_ref_af_restrict_to_split_sk     false
% 27.52/4.01  --abstr_ref_under                       []
% 27.52/4.01  
% 27.52/4.01  ------ SAT Options
% 27.52/4.01  
% 27.52/4.01  --sat_mode                              false
% 27.52/4.01  --sat_fm_restart_options                ""
% 27.52/4.01  --sat_gr_def                            false
% 27.52/4.01  --sat_epr_types                         true
% 27.52/4.01  --sat_non_cyclic_types                  false
% 27.52/4.01  --sat_finite_models                     false
% 27.52/4.01  --sat_fm_lemmas                         false
% 27.52/4.01  --sat_fm_prep                           false
% 27.52/4.01  --sat_fm_uc_incr                        true
% 27.52/4.01  --sat_out_model                         small
% 27.52/4.01  --sat_out_clauses                       false
% 27.52/4.01  
% 27.52/4.01  ------ QBF Options
% 27.52/4.01  
% 27.52/4.01  --qbf_mode                              false
% 27.52/4.01  --qbf_elim_univ                         false
% 27.52/4.01  --qbf_dom_inst                          none
% 27.52/4.01  --qbf_dom_pre_inst                      false
% 27.52/4.01  --qbf_sk_in                             false
% 27.52/4.01  --qbf_pred_elim                         true
% 27.52/4.01  --qbf_split                             512
% 27.52/4.01  
% 27.52/4.01  ------ BMC1 Options
% 27.52/4.01  
% 27.52/4.01  --bmc1_incremental                      false
% 27.52/4.01  --bmc1_axioms                           reachable_all
% 27.52/4.01  --bmc1_min_bound                        0
% 27.52/4.01  --bmc1_max_bound                        -1
% 27.52/4.01  --bmc1_max_bound_default                -1
% 27.52/4.01  --bmc1_symbol_reachability              true
% 27.52/4.01  --bmc1_property_lemmas                  false
% 27.52/4.01  --bmc1_k_induction                      false
% 27.52/4.01  --bmc1_non_equiv_states                 false
% 27.52/4.01  --bmc1_deadlock                         false
% 27.52/4.01  --bmc1_ucm                              false
% 27.52/4.01  --bmc1_add_unsat_core                   none
% 27.52/4.01  --bmc1_unsat_core_children              false
% 27.52/4.01  --bmc1_unsat_core_extrapolate_axioms    false
% 27.52/4.01  --bmc1_out_stat                         full
% 27.52/4.01  --bmc1_ground_init                      false
% 27.52/4.01  --bmc1_pre_inst_next_state              false
% 27.52/4.01  --bmc1_pre_inst_state                   false
% 27.52/4.01  --bmc1_pre_inst_reach_state             false
% 27.52/4.01  --bmc1_out_unsat_core                   false
% 27.52/4.01  --bmc1_aig_witness_out                  false
% 27.52/4.01  --bmc1_verbose                          false
% 27.52/4.01  --bmc1_dump_clauses_tptp                false
% 27.52/4.01  --bmc1_dump_unsat_core_tptp             false
% 27.52/4.01  --bmc1_dump_file                        -
% 27.52/4.01  --bmc1_ucm_expand_uc_limit              128
% 27.52/4.01  --bmc1_ucm_n_expand_iterations          6
% 27.52/4.01  --bmc1_ucm_extend_mode                  1
% 27.52/4.01  --bmc1_ucm_init_mode                    2
% 27.52/4.01  --bmc1_ucm_cone_mode                    none
% 27.52/4.01  --bmc1_ucm_reduced_relation_type        0
% 27.52/4.01  --bmc1_ucm_relax_model                  4
% 27.52/4.01  --bmc1_ucm_full_tr_after_sat            true
% 27.52/4.01  --bmc1_ucm_expand_neg_assumptions       false
% 27.52/4.01  --bmc1_ucm_layered_model                none
% 27.52/4.01  --bmc1_ucm_max_lemma_size               10
% 27.52/4.01  
% 27.52/4.01  ------ AIG Options
% 27.52/4.01  
% 27.52/4.01  --aig_mode                              false
% 27.52/4.01  
% 27.52/4.01  ------ Instantiation Options
% 27.52/4.01  
% 27.52/4.01  --instantiation_flag                    true
% 27.52/4.01  --inst_sos_flag                         true
% 27.52/4.01  --inst_sos_phase                        true
% 27.52/4.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.52/4.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.52/4.01  --inst_lit_sel_side                     none
% 27.52/4.01  --inst_solver_per_active                1400
% 27.52/4.01  --inst_solver_calls_frac                1.
% 27.52/4.01  --inst_passive_queue_type               priority_queues
% 27.52/4.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.52/4.01  --inst_passive_queues_freq              [25;2]
% 27.52/4.01  --inst_dismatching                      true
% 27.52/4.01  --inst_eager_unprocessed_to_passive     true
% 27.52/4.01  --inst_prop_sim_given                   true
% 27.52/4.01  --inst_prop_sim_new                     false
% 27.52/4.01  --inst_subs_new                         false
% 27.52/4.01  --inst_eq_res_simp                      false
% 27.52/4.01  --inst_subs_given                       false
% 27.52/4.01  --inst_orphan_elimination               true
% 27.52/4.01  --inst_learning_loop_flag               true
% 27.52/4.01  --inst_learning_start                   3000
% 27.52/4.01  --inst_learning_factor                  2
% 27.52/4.01  --inst_start_prop_sim_after_learn       3
% 27.52/4.01  --inst_sel_renew                        solver
% 27.52/4.01  --inst_lit_activity_flag                true
% 27.52/4.01  --inst_restr_to_given                   false
% 27.52/4.01  --inst_activity_threshold               500
% 27.52/4.01  --inst_out_proof                        true
% 27.52/4.01  
% 27.52/4.01  ------ Resolution Options
% 27.52/4.01  
% 27.52/4.01  --resolution_flag                       false
% 27.52/4.01  --res_lit_sel                           adaptive
% 27.52/4.01  --res_lit_sel_side                      none
% 27.52/4.01  --res_ordering                          kbo
% 27.52/4.01  --res_to_prop_solver                    active
% 27.52/4.01  --res_prop_simpl_new                    false
% 27.52/4.01  --res_prop_simpl_given                  true
% 27.52/4.01  --res_passive_queue_type                priority_queues
% 27.52/4.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.52/4.01  --res_passive_queues_freq               [15;5]
% 27.52/4.01  --res_forward_subs                      full
% 27.52/4.01  --res_backward_subs                     full
% 27.52/4.01  --res_forward_subs_resolution           true
% 27.52/4.01  --res_backward_subs_resolution          true
% 27.52/4.01  --res_orphan_elimination                true
% 27.52/4.01  --res_time_limit                        2.
% 27.52/4.01  --res_out_proof                         true
% 27.52/4.01  
% 27.52/4.01  ------ Superposition Options
% 27.52/4.01  
% 27.52/4.01  --superposition_flag                    true
% 27.52/4.01  --sup_passive_queue_type                priority_queues
% 27.52/4.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.52/4.01  --sup_passive_queues_freq               [8;1;4]
% 27.52/4.01  --demod_completeness_check              fast
% 27.52/4.01  --demod_use_ground                      true
% 27.52/4.01  --sup_to_prop_solver                    passive
% 27.52/4.01  --sup_prop_simpl_new                    true
% 27.52/4.01  --sup_prop_simpl_given                  true
% 27.52/4.01  --sup_fun_splitting                     true
% 27.52/4.01  --sup_smt_interval                      50000
% 27.52/4.01  
% 27.52/4.01  ------ Superposition Simplification Setup
% 27.52/4.01  
% 27.52/4.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 27.52/4.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 27.52/4.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 27.52/4.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 27.52/4.01  --sup_full_triv                         [TrivRules;PropSubs]
% 27.52/4.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 27.52/4.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 27.52/4.01  --sup_immed_triv                        [TrivRules]
% 27.52/4.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.52/4.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.52/4.01  --sup_immed_bw_main                     []
% 27.52/4.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 27.52/4.01  --sup_input_triv                        [Unflattening;TrivRules]
% 27.52/4.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.52/4.01  --sup_input_bw                          []
% 27.52/4.01  
% 27.52/4.01  ------ Combination Options
% 27.52/4.01  
% 27.52/4.01  --comb_res_mult                         3
% 27.52/4.01  --comb_sup_mult                         2
% 27.52/4.01  --comb_inst_mult                        10
% 27.52/4.01  
% 27.52/4.01  ------ Debug Options
% 27.52/4.01  
% 27.52/4.01  --dbg_backtrace                         false
% 27.52/4.01  --dbg_dump_prop_clauses                 false
% 27.52/4.01  --dbg_dump_prop_clauses_file            -
% 27.52/4.01  --dbg_out_stat                          false
% 27.52/4.01  
% 27.52/4.01  
% 27.52/4.01  
% 27.52/4.01  
% 27.52/4.01  ------ Proving...
% 27.52/4.01  
% 27.52/4.01  
% 27.52/4.01  % SZS status Theorem for theBenchmark.p
% 27.52/4.01  
% 27.52/4.01  % SZS output start CNFRefutation for theBenchmark.p
% 27.52/4.01  
% 27.52/4.01  fof(f20,conjecture,(
% 27.52/4.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 27.52/4.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.52/4.01  
% 27.52/4.01  fof(f21,negated_conjecture,(
% 27.52/4.01    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 27.52/4.01    inference(negated_conjecture,[],[f20])).
% 27.52/4.01  
% 27.52/4.01  fof(f49,plain,(
% 27.52/4.01    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 27.52/4.01    inference(ennf_transformation,[],[f21])).
% 27.52/4.01  
% 27.52/4.01  fof(f50,plain,(
% 27.52/4.01    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 27.52/4.01    inference(flattening,[],[f49])).
% 27.52/4.01  
% 27.52/4.01  fof(f55,plain,(
% 27.52/4.01    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 27.52/4.01    introduced(choice_axiom,[])).
% 27.52/4.01  
% 27.52/4.01  fof(f54,plain,(
% 27.52/4.01    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 27.52/4.01    introduced(choice_axiom,[])).
% 27.52/4.01  
% 27.52/4.01  fof(f56,plain,(
% 27.52/4.01    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 27.52/4.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f50,f55,f54])).
% 27.52/4.01  
% 27.52/4.01  fof(f90,plain,(
% 27.52/4.01    v1_funct_1(sK2)),
% 27.52/4.01    inference(cnf_transformation,[],[f56])).
% 27.52/4.01  
% 27.52/4.01  fof(f6,axiom,(
% 27.52/4.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0))))),
% 27.52/4.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.52/4.01  
% 27.52/4.01  fof(f27,plain,(
% 27.52/4.01    ! [X0] : (((k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 27.52/4.01    inference(ennf_transformation,[],[f6])).
% 27.52/4.01  
% 27.52/4.01  fof(f28,plain,(
% 27.52/4.01    ! [X0] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 27.52/4.01    inference(flattening,[],[f27])).
% 27.52/4.01  
% 27.52/4.01  fof(f65,plain,(
% 27.52/4.01    ( ! [X0] : (k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 27.52/4.01    inference(cnf_transformation,[],[f28])).
% 27.52/4.01  
% 27.52/4.01  fof(f96,plain,(
% 27.52/4.01    k2_relset_1(sK0,sK1,sK2) = sK1),
% 27.52/4.01    inference(cnf_transformation,[],[f56])).
% 27.52/4.01  
% 27.52/4.01  fof(f19,axiom,(
% 27.52/4.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 27.52/4.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.52/4.01  
% 27.52/4.01  fof(f47,plain,(
% 27.52/4.01    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 27.52/4.01    inference(ennf_transformation,[],[f19])).
% 27.52/4.01  
% 27.52/4.01  fof(f48,plain,(
% 27.52/4.01    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 27.52/4.01    inference(flattening,[],[f47])).
% 27.52/4.01  
% 27.52/4.01  fof(f89,plain,(
% 27.52/4.01    ( ! [X2,X0,X1] : (k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 27.52/4.01    inference(cnf_transformation,[],[f48])).
% 27.52/4.01  
% 27.52/4.01  fof(f91,plain,(
% 27.52/4.01    v1_funct_2(sK2,sK0,sK1)),
% 27.52/4.01    inference(cnf_transformation,[],[f56])).
% 27.52/4.01  
% 27.52/4.01  fof(f92,plain,(
% 27.52/4.01    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 27.52/4.01    inference(cnf_transformation,[],[f56])).
% 27.52/4.01  
% 27.52/4.01  fof(f98,plain,(
% 27.52/4.01    v2_funct_1(sK2)),
% 27.52/4.01    inference(cnf_transformation,[],[f56])).
% 27.52/4.01  
% 27.52/4.01  fof(f100,plain,(
% 27.52/4.01    k1_xboole_0 != sK1),
% 27.52/4.01    inference(cnf_transformation,[],[f56])).
% 27.52/4.01  
% 27.52/4.01  fof(f3,axiom,(
% 27.52/4.01    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 27.52/4.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.52/4.01  
% 27.52/4.01  fof(f59,plain,(
% 27.52/4.01    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 27.52/4.01    inference(cnf_transformation,[],[f3])).
% 27.52/4.01  
% 27.52/4.01  fof(f17,axiom,(
% 27.52/4.01    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 27.52/4.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.52/4.01  
% 27.52/4.01  fof(f85,plain,(
% 27.52/4.01    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 27.52/4.01    inference(cnf_transformation,[],[f17])).
% 27.52/4.01  
% 27.52/4.01  fof(f103,plain,(
% 27.52/4.01    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 27.52/4.01    inference(definition_unfolding,[],[f59,f85])).
% 27.52/4.01  
% 27.52/4.01  fof(f2,axiom,(
% 27.52/4.01    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 27.52/4.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.52/4.01  
% 27.52/4.01  fof(f58,plain,(
% 27.52/4.01    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 27.52/4.01    inference(cnf_transformation,[],[f2])).
% 27.52/4.01  
% 27.52/4.01  fof(f1,axiom,(
% 27.52/4.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 27.52/4.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.52/4.01  
% 27.52/4.01  fof(f24,plain,(
% 27.52/4.01    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 27.52/4.01    inference(ennf_transformation,[],[f1])).
% 27.52/4.01  
% 27.52/4.01  fof(f57,plain,(
% 27.52/4.01    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 27.52/4.01    inference(cnf_transformation,[],[f24])).
% 27.52/4.01  
% 27.52/4.01  fof(f95,plain,(
% 27.52/4.01    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 27.52/4.01    inference(cnf_transformation,[],[f56])).
% 27.52/4.01  
% 27.52/4.01  fof(f12,axiom,(
% 27.52/4.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 27.52/4.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.52/4.01  
% 27.52/4.01  fof(f37,plain,(
% 27.52/4.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 27.52/4.01    inference(ennf_transformation,[],[f12])).
% 27.52/4.01  
% 27.52/4.01  fof(f38,plain,(
% 27.52/4.01    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 27.52/4.01    inference(flattening,[],[f37])).
% 27.52/4.01  
% 27.52/4.01  fof(f52,plain,(
% 27.52/4.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 27.52/4.01    inference(nnf_transformation,[],[f38])).
% 27.52/4.01  
% 27.52/4.01  fof(f73,plain,(
% 27.52/4.01    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 27.52/4.01    inference(cnf_transformation,[],[f52])).
% 27.52/4.01  
% 27.52/4.01  fof(f10,axiom,(
% 27.52/4.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 27.52/4.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.52/4.01  
% 27.52/4.01  fof(f34,plain,(
% 27.52/4.01    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 27.52/4.01    inference(ennf_transformation,[],[f10])).
% 27.52/4.01  
% 27.52/4.01  fof(f70,plain,(
% 27.52/4.01    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 27.52/4.01    inference(cnf_transformation,[],[f34])).
% 27.52/4.01  
% 27.52/4.01  fof(f94,plain,(
% 27.52/4.01    v1_funct_2(sK3,sK1,sK0)),
% 27.52/4.01    inference(cnf_transformation,[],[f56])).
% 27.52/4.01  
% 27.52/4.01  fof(f99,plain,(
% 27.52/4.01    k1_xboole_0 != sK0),
% 27.52/4.01    inference(cnf_transformation,[],[f56])).
% 27.52/4.01  
% 27.52/4.01  fof(f5,axiom,(
% 27.52/4.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 27.52/4.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.52/4.01  
% 27.52/4.01  fof(f25,plain,(
% 27.52/4.01    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 27.52/4.01    inference(ennf_transformation,[],[f5])).
% 27.52/4.01  
% 27.52/4.01  fof(f26,plain,(
% 27.52/4.01    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 27.52/4.01    inference(flattening,[],[f25])).
% 27.52/4.01  
% 27.52/4.01  fof(f64,plain,(
% 27.52/4.01    ( ! [X0,X1] : (v2_funct_1(X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 27.52/4.01    inference(cnf_transformation,[],[f26])).
% 27.52/4.01  
% 27.52/4.01  fof(f93,plain,(
% 27.52/4.01    v1_funct_1(sK3)),
% 27.52/4.01    inference(cnf_transformation,[],[f56])).
% 27.52/4.01  
% 27.52/4.01  fof(f16,axiom,(
% 27.52/4.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 27.52/4.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.52/4.01  
% 27.52/4.01  fof(f43,plain,(
% 27.52/4.01    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 27.52/4.01    inference(ennf_transformation,[],[f16])).
% 27.52/4.01  
% 27.52/4.01  fof(f44,plain,(
% 27.52/4.01    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 27.52/4.01    inference(flattening,[],[f43])).
% 27.52/4.01  
% 27.52/4.01  fof(f84,plain,(
% 27.52/4.01    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 27.52/4.01    inference(cnf_transformation,[],[f44])).
% 27.52/4.01  
% 27.52/4.01  fof(f97,plain,(
% 27.52/4.01    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 27.52/4.01    inference(cnf_transformation,[],[f56])).
% 27.52/4.01  
% 27.52/4.01  fof(f14,axiom,(
% 27.52/4.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 27.52/4.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.52/4.01  
% 27.52/4.01  fof(f41,plain,(
% 27.52/4.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 27.52/4.01    inference(ennf_transformation,[],[f14])).
% 27.52/4.01  
% 27.52/4.01  fof(f42,plain,(
% 27.52/4.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 27.52/4.01    inference(flattening,[],[f41])).
% 27.52/4.01  
% 27.52/4.01  fof(f82,plain,(
% 27.52/4.01    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 27.52/4.01    inference(cnf_transformation,[],[f42])).
% 27.52/4.01  
% 27.52/4.01  fof(f11,axiom,(
% 27.52/4.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 27.52/4.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.52/4.01  
% 27.52/4.01  fof(f35,plain,(
% 27.52/4.01    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 27.52/4.01    inference(ennf_transformation,[],[f11])).
% 27.52/4.01  
% 27.52/4.01  fof(f36,plain,(
% 27.52/4.01    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 27.52/4.01    inference(flattening,[],[f35])).
% 27.52/4.01  
% 27.52/4.01  fof(f51,plain,(
% 27.52/4.01    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 27.52/4.01    inference(nnf_transformation,[],[f36])).
% 27.52/4.01  
% 27.52/4.01  fof(f71,plain,(
% 27.52/4.01    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 27.52/4.01    inference(cnf_transformation,[],[f51])).
% 27.52/4.01  
% 27.52/4.01  fof(f15,axiom,(
% 27.52/4.01    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 27.52/4.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.52/4.01  
% 27.52/4.01  fof(f22,plain,(
% 27.52/4.01    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 27.52/4.01    inference(pure_predicate_removal,[],[f15])).
% 27.52/4.01  
% 27.52/4.01  fof(f83,plain,(
% 27.52/4.01    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 27.52/4.01    inference(cnf_transformation,[],[f22])).
% 27.52/4.01  
% 27.52/4.01  fof(f7,axiom,(
% 27.52/4.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 27.52/4.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.52/4.01  
% 27.52/4.01  fof(f29,plain,(
% 27.52/4.01    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 27.52/4.01    inference(ennf_transformation,[],[f7])).
% 27.52/4.01  
% 27.52/4.01  fof(f30,plain,(
% 27.52/4.01    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 27.52/4.01    inference(flattening,[],[f29])).
% 27.52/4.01  
% 27.52/4.01  fof(f67,plain,(
% 27.52/4.01    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 27.52/4.01    inference(cnf_transformation,[],[f30])).
% 27.52/4.01  
% 27.52/4.01  fof(f106,plain,(
% 27.52/4.01    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 27.52/4.01    inference(definition_unfolding,[],[f67,f85])).
% 27.52/4.01  
% 27.52/4.01  fof(f13,axiom,(
% 27.52/4.01    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 27.52/4.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.52/4.01  
% 27.52/4.01  fof(f39,plain,(
% 27.52/4.01    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 27.52/4.01    inference(ennf_transformation,[],[f13])).
% 27.52/4.01  
% 27.52/4.01  fof(f40,plain,(
% 27.52/4.01    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 27.52/4.01    inference(flattening,[],[f39])).
% 27.52/4.01  
% 27.52/4.01  fof(f53,plain,(
% 27.52/4.01    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 27.52/4.01    inference(nnf_transformation,[],[f40])).
% 27.52/4.01  
% 27.52/4.01  fof(f79,plain,(
% 27.52/4.01    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 27.52/4.01    inference(cnf_transformation,[],[f53])).
% 27.52/4.01  
% 27.52/4.01  fof(f18,axiom,(
% 27.52/4.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 27.52/4.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.52/4.01  
% 27.52/4.01  fof(f45,plain,(
% 27.52/4.01    ! [X0,X1,X2] : (! [X3] : (((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 27.52/4.01    inference(ennf_transformation,[],[f18])).
% 27.52/4.01  
% 27.52/4.01  fof(f46,plain,(
% 27.52/4.01    ! [X0,X1,X2] : (! [X3] : ((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 27.52/4.01    inference(flattening,[],[f45])).
% 27.52/4.01  
% 27.52/4.01  fof(f87,plain,(
% 27.52/4.01    ( ! [X2,X0,X3,X1] : (v2_funct_2(X3,X0) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 27.52/4.01    inference(cnf_transformation,[],[f46])).
% 27.52/4.01  
% 27.52/4.01  fof(f9,axiom,(
% 27.52/4.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 27.52/4.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.52/4.01  
% 27.52/4.01  fof(f23,plain,(
% 27.52/4.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 27.52/4.01    inference(pure_predicate_removal,[],[f9])).
% 27.52/4.01  
% 27.52/4.01  fof(f33,plain,(
% 27.52/4.01    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 27.52/4.01    inference(ennf_transformation,[],[f23])).
% 27.52/4.01  
% 27.52/4.01  fof(f69,plain,(
% 27.52/4.01    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 27.52/4.01    inference(cnf_transformation,[],[f33])).
% 27.52/4.01  
% 27.52/4.01  fof(f4,axiom,(
% 27.52/4.01    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 27.52/4.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.52/4.01  
% 27.52/4.01  fof(f62,plain,(
% 27.52/4.01    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 27.52/4.01    inference(cnf_transformation,[],[f4])).
% 27.52/4.01  
% 27.52/4.01  fof(f104,plain,(
% 27.52/4.01    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 27.52/4.01    inference(definition_unfolding,[],[f62,f85])).
% 27.52/4.01  
% 27.52/4.01  fof(f8,axiom,(
% 27.52/4.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 27.52/4.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.52/4.01  
% 27.52/4.01  fof(f31,plain,(
% 27.52/4.01    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 27.52/4.01    inference(ennf_transformation,[],[f8])).
% 27.52/4.01  
% 27.52/4.01  fof(f32,plain,(
% 27.52/4.01    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 27.52/4.01    inference(flattening,[],[f31])).
% 27.52/4.01  
% 27.52/4.01  fof(f68,plain,(
% 27.52/4.01    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 27.52/4.01    inference(cnf_transformation,[],[f32])).
% 27.52/4.01  
% 27.52/4.01  fof(f72,plain,(
% 27.52/4.01    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 27.52/4.01    inference(cnf_transformation,[],[f51])).
% 27.52/4.01  
% 27.52/4.01  fof(f107,plain,(
% 27.52/4.01    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 27.52/4.01    inference(equality_resolution,[],[f72])).
% 27.52/4.01  
% 27.52/4.01  fof(f101,plain,(
% 27.52/4.01    k2_funct_1(sK2) != sK3),
% 27.52/4.01    inference(cnf_transformation,[],[f56])).
% 27.52/4.01  
% 27.52/4.01  cnf(c_1144,plain,
% 27.52/4.01      ( X0 != X1 | k2_funct_1(X0) = k2_funct_1(X1) ),
% 27.52/4.01      theory(equality) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_71349,plain,
% 27.52/4.01      ( k2_funct_1(sK2) = k2_funct_1(k2_funct_1(sK3))
% 27.52/4.01      | sK2 != k2_funct_1(sK3) ),
% 27.52/4.01      inference(instantiation,[status(thm)],[c_1144]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_1133,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_50349,plain,
% 27.52/4.01      ( k2_funct_1(sK2) != X0 | k2_funct_1(sK2) = sK3 | sK3 != X0 ),
% 27.52/4.01      inference(instantiation,[status(thm)],[c_1133]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_61532,plain,
% 27.52/4.01      ( k2_funct_1(sK2) != k2_funct_1(k2_funct_1(sK3))
% 27.52/4.01      | k2_funct_1(sK2) = sK3
% 27.52/4.01      | sK3 != k2_funct_1(k2_funct_1(sK3)) ),
% 27.52/4.01      inference(instantiation,[status(thm)],[c_50349]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_3633,plain,
% 27.52/4.01      ( X0 != X1 | sK2 != X1 | sK2 = X0 ),
% 27.52/4.01      inference(instantiation,[status(thm)],[c_1133]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_7011,plain,
% 27.52/4.01      ( X0 != sK2 | sK2 = X0 | sK2 != sK2 ),
% 27.52/4.01      inference(instantiation,[status(thm)],[c_3633]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_14718,plain,
% 27.52/4.01      ( k2_funct_1(X0) != sK2 | sK2 = k2_funct_1(X0) | sK2 != sK2 ),
% 27.52/4.01      inference(instantiation,[status(thm)],[c_7011]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_36112,plain,
% 27.52/4.01      ( k2_funct_1(sK3) != sK2 | sK2 = k2_funct_1(sK3) | sK2 != sK2 ),
% 27.52/4.01      inference(instantiation,[status(thm)],[c_14718]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_43,negated_conjecture,
% 27.52/4.01      ( v1_funct_1(sK2) ),
% 27.52/4.01      inference(cnf_transformation,[],[f90]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_1708,plain,
% 27.52/4.01      ( v1_funct_1(sK2) = iProver_top ),
% 27.52/4.01      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_9,plain,
% 27.52/4.01      ( ~ v1_funct_1(X0)
% 27.52/4.01      | ~ v2_funct_1(X0)
% 27.52/4.01      | ~ v1_relat_1(X0)
% 27.52/4.01      | k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) ),
% 27.52/4.01      inference(cnf_transformation,[],[f65]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_1734,plain,
% 27.52/4.01      ( k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0)
% 27.52/4.01      | v1_funct_1(X0) != iProver_top
% 27.52/4.01      | v2_funct_1(X0) != iProver_top
% 27.52/4.01      | v1_relat_1(X0) != iProver_top ),
% 27.52/4.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_4103,plain,
% 27.52/4.01      ( k1_relat_1(k5_relat_1(k2_funct_1(sK2),sK2)) = k2_relat_1(sK2)
% 27.52/4.01      | v2_funct_1(sK2) != iProver_top
% 27.52/4.01      | v1_relat_1(sK2) != iProver_top ),
% 27.52/4.01      inference(superposition,[status(thm)],[c_1708,c_1734]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_37,negated_conjecture,
% 27.52/4.01      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 27.52/4.01      inference(cnf_transformation,[],[f96]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_30,plain,
% 27.52/4.01      ( ~ v1_funct_2(X0,X1,X2)
% 27.52/4.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.52/4.01      | ~ v1_funct_1(X0)
% 27.52/4.01      | ~ v2_funct_1(X0)
% 27.52/4.01      | k2_relset_1(X1,X2,X0) != X2
% 27.52/4.01      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
% 27.52/4.01      | k1_xboole_0 = X2 ),
% 27.52/4.01      inference(cnf_transformation,[],[f89]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_1717,plain,
% 27.52/4.01      ( k2_relset_1(X0,X1,X2) != X1
% 27.52/4.01      | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
% 27.52/4.01      | k1_xboole_0 = X1
% 27.52/4.01      | v1_funct_2(X2,X0,X1) != iProver_top
% 27.52/4.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 27.52/4.01      | v1_funct_1(X2) != iProver_top
% 27.52/4.01      | v2_funct_1(X2) != iProver_top ),
% 27.52/4.01      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_3426,plain,
% 27.52/4.01      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 27.52/4.01      | sK1 = k1_xboole_0
% 27.52/4.01      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 27.52/4.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 27.52/4.01      | v1_funct_1(sK2) != iProver_top
% 27.52/4.01      | v2_funct_1(sK2) != iProver_top ),
% 27.52/4.01      inference(superposition,[status(thm)],[c_37,c_1717]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_42,negated_conjecture,
% 27.52/4.01      ( v1_funct_2(sK2,sK0,sK1) ),
% 27.52/4.01      inference(cnf_transformation,[],[f91]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_41,negated_conjecture,
% 27.52/4.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 27.52/4.01      inference(cnf_transformation,[],[f92]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_35,negated_conjecture,
% 27.52/4.01      ( v2_funct_1(sK2) ),
% 27.52/4.01      inference(cnf_transformation,[],[f98]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_33,negated_conjecture,
% 27.52/4.01      ( k1_xboole_0 != sK1 ),
% 27.52/4.01      inference(cnf_transformation,[],[f100]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_1806,plain,
% 27.52/4.01      ( ~ v1_funct_2(X0,X1,sK1)
% 27.52/4.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 27.52/4.01      | ~ v1_funct_1(X0)
% 27.52/4.01      | ~ v2_funct_1(X0)
% 27.52/4.01      | k2_relset_1(X1,sK1,X0) != sK1
% 27.52/4.01      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(sK1)
% 27.52/4.01      | k1_xboole_0 = sK1 ),
% 27.52/4.01      inference(instantiation,[status(thm)],[c_30]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_2000,plain,
% 27.52/4.01      ( ~ v1_funct_2(sK2,X0,sK1)
% 27.52/4.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
% 27.52/4.01      | ~ v1_funct_1(sK2)
% 27.52/4.01      | ~ v2_funct_1(sK2)
% 27.52/4.01      | k2_relset_1(X0,sK1,sK2) != sK1
% 27.52/4.01      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 27.52/4.01      | k1_xboole_0 = sK1 ),
% 27.52/4.01      inference(instantiation,[status(thm)],[c_1806]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_2084,plain,
% 27.52/4.01      ( ~ v1_funct_2(sK2,sK0,sK1)
% 27.52/4.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 27.52/4.01      | ~ v1_funct_1(sK2)
% 27.52/4.01      | ~ v2_funct_1(sK2)
% 27.52/4.01      | k2_relset_1(sK0,sK1,sK2) != sK1
% 27.52/4.01      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 27.52/4.01      | k1_xboole_0 = sK1 ),
% 27.52/4.01      inference(instantiation,[status(thm)],[c_2000]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_3646,plain,
% 27.52/4.01      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
% 27.52/4.01      inference(global_propositional_subsumption,
% 27.52/4.01                [status(thm)],
% 27.52/4.01                [c_3426,c_43,c_42,c_41,c_37,c_35,c_33,c_2084]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_4104,plain,
% 27.52/4.01      ( k1_relat_1(k6_partfun1(sK1)) = k2_relat_1(sK2)
% 27.52/4.01      | v2_funct_1(sK2) != iProver_top
% 27.52/4.01      | v1_relat_1(sK2) != iProver_top ),
% 27.52/4.01      inference(light_normalisation,[status(thm)],[c_4103,c_3646]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_3,plain,
% 27.52/4.01      ( k1_relat_1(k6_partfun1(X0)) = X0 ),
% 27.52/4.01      inference(cnf_transformation,[],[f103]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_4105,plain,
% 27.52/4.01      ( k2_relat_1(sK2) = sK1
% 27.52/4.01      | v2_funct_1(sK2) != iProver_top
% 27.52/4.01      | v1_relat_1(sK2) != iProver_top ),
% 27.52/4.01      inference(demodulation,[status(thm)],[c_4104,c_3]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_51,plain,
% 27.52/4.01      ( v2_funct_1(sK2) = iProver_top ),
% 27.52/4.01      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_1,plain,
% 27.52/4.01      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 27.52/4.01      inference(cnf_transformation,[],[f58]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_1740,plain,
% 27.52/4.01      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 27.52/4.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_1710,plain,
% 27.52/4.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 27.52/4.01      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_0,plain,
% 27.52/4.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 27.52/4.01      | ~ v1_relat_1(X1)
% 27.52/4.01      | v1_relat_1(X0) ),
% 27.52/4.01      inference(cnf_transformation,[],[f57]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_1741,plain,
% 27.52/4.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 27.52/4.01      | v1_relat_1(X1) != iProver_top
% 27.52/4.01      | v1_relat_1(X0) = iProver_top ),
% 27.52/4.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_2992,plain,
% 27.52/4.01      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 27.52/4.01      | v1_relat_1(sK2) = iProver_top ),
% 27.52/4.01      inference(superposition,[status(thm)],[c_1710,c_1741]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_3364,plain,
% 27.52/4.01      ( v1_relat_1(sK2) = iProver_top ),
% 27.52/4.01      inference(superposition,[status(thm)],[c_1740,c_2992]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_4209,plain,
% 27.52/4.01      ( k2_relat_1(sK2) = sK1 ),
% 27.52/4.01      inference(global_propositional_subsumption,
% 27.52/4.01                [status(thm)],
% 27.52/4.01                [c_4105,c_51,c_3364]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_38,negated_conjecture,
% 27.52/4.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 27.52/4.01      inference(cnf_transformation,[],[f95]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_1713,plain,
% 27.52/4.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 27.52/4.01      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_21,plain,
% 27.52/4.01      ( ~ v1_funct_2(X0,X1,X2)
% 27.52/4.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.52/4.01      | k1_relset_1(X1,X2,X0) = X1
% 27.52/4.01      | k1_xboole_0 = X2 ),
% 27.52/4.01      inference(cnf_transformation,[],[f73]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_1723,plain,
% 27.52/4.01      ( k1_relset_1(X0,X1,X2) = X0
% 27.52/4.01      | k1_xboole_0 = X1
% 27.52/4.01      | v1_funct_2(X2,X0,X1) != iProver_top
% 27.52/4.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 27.52/4.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_4367,plain,
% 27.52/4.01      ( k1_relset_1(sK1,sK0,sK3) = sK1
% 27.52/4.01      | sK0 = k1_xboole_0
% 27.52/4.01      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 27.52/4.01      inference(superposition,[status(thm)],[c_1713,c_1723]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_13,plain,
% 27.52/4.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.52/4.01      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 27.52/4.01      inference(cnf_transformation,[],[f70]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_1731,plain,
% 27.52/4.01      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 27.52/4.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 27.52/4.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_2859,plain,
% 27.52/4.01      ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
% 27.52/4.01      inference(superposition,[status(thm)],[c_1713,c_1731]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_4370,plain,
% 27.52/4.01      ( k1_relat_1(sK3) = sK1
% 27.52/4.01      | sK0 = k1_xboole_0
% 27.52/4.01      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 27.52/4.01      inference(demodulation,[status(thm)],[c_4367,c_2859]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_39,negated_conjecture,
% 27.52/4.01      ( v1_funct_2(sK3,sK1,sK0) ),
% 27.52/4.01      inference(cnf_transformation,[],[f94]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_48,plain,
% 27.52/4.01      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 27.52/4.01      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_34,negated_conjecture,
% 27.52/4.01      ( k1_xboole_0 != sK0 ),
% 27.52/4.01      inference(cnf_transformation,[],[f99]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_1132,plain,( X0 = X0 ),theory(equality) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_1167,plain,
% 27.52/4.01      ( k1_xboole_0 = k1_xboole_0 ),
% 27.52/4.01      inference(instantiation,[status(thm)],[c_1132]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_1859,plain,
% 27.52/4.01      ( sK0 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK0 ),
% 27.52/4.01      inference(instantiation,[status(thm)],[c_1133]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_1860,plain,
% 27.52/4.01      ( sK0 != k1_xboole_0
% 27.52/4.01      | k1_xboole_0 = sK0
% 27.52/4.01      | k1_xboole_0 != k1_xboole_0 ),
% 27.52/4.01      inference(instantiation,[status(thm)],[c_1859]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_6996,plain,
% 27.52/4.01      ( k1_relat_1(sK3) = sK1 ),
% 27.52/4.01      inference(global_propositional_subsumption,
% 27.52/4.01                [status(thm)],
% 27.52/4.01                [c_4370,c_48,c_34,c_1167,c_1860]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_6,plain,
% 27.52/4.01      ( ~ v1_funct_1(X0)
% 27.52/4.01      | ~ v1_funct_1(X1)
% 27.52/4.01      | v2_funct_1(X1)
% 27.52/4.01      | ~ v2_funct_1(k5_relat_1(X0,X1))
% 27.52/4.01      | ~ v1_relat_1(X1)
% 27.52/4.01      | ~ v1_relat_1(X0)
% 27.52/4.01      | k1_relat_1(X1) != k2_relat_1(X0) ),
% 27.52/4.01      inference(cnf_transformation,[],[f64]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_1737,plain,
% 27.52/4.01      ( k1_relat_1(X0) != k2_relat_1(X1)
% 27.52/4.01      | v1_funct_1(X1) != iProver_top
% 27.52/4.01      | v1_funct_1(X0) != iProver_top
% 27.52/4.01      | v2_funct_1(X0) = iProver_top
% 27.52/4.01      | v2_funct_1(k5_relat_1(X1,X0)) != iProver_top
% 27.52/4.01      | v1_relat_1(X1) != iProver_top
% 27.52/4.01      | v1_relat_1(X0) != iProver_top ),
% 27.52/4.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_7000,plain,
% 27.52/4.01      ( k2_relat_1(X0) != sK1
% 27.52/4.01      | v1_funct_1(X0) != iProver_top
% 27.52/4.01      | v1_funct_1(sK3) != iProver_top
% 27.52/4.01      | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
% 27.52/4.01      | v2_funct_1(sK3) = iProver_top
% 27.52/4.01      | v1_relat_1(X0) != iProver_top
% 27.52/4.01      | v1_relat_1(sK3) != iProver_top ),
% 27.52/4.01      inference(superposition,[status(thm)],[c_6996,c_1737]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_40,negated_conjecture,
% 27.52/4.01      ( v1_funct_1(sK3) ),
% 27.52/4.01      inference(cnf_transformation,[],[f93]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_47,plain,
% 27.52/4.01      ( v1_funct_1(sK3) = iProver_top ),
% 27.52/4.01      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_2991,plain,
% 27.52/4.01      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 27.52/4.01      | v1_relat_1(sK3) = iProver_top ),
% 27.52/4.01      inference(superposition,[status(thm)],[c_1713,c_1741]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_3066,plain,
% 27.52/4.01      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
% 27.52/4.01      inference(instantiation,[status(thm)],[c_1]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_3067,plain,
% 27.52/4.01      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
% 27.52/4.01      inference(predicate_to_equality,[status(thm)],[c_3066]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_31501,plain,
% 27.52/4.01      ( v1_relat_1(X0) != iProver_top
% 27.52/4.01      | v2_funct_1(sK3) = iProver_top
% 27.52/4.01      | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
% 27.52/4.01      | k2_relat_1(X0) != sK1
% 27.52/4.01      | v1_funct_1(X0) != iProver_top ),
% 27.52/4.01      inference(global_propositional_subsumption,
% 27.52/4.01                [status(thm)],
% 27.52/4.01                [c_7000,c_47,c_2991,c_3067]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_31502,plain,
% 27.52/4.01      ( k2_relat_1(X0) != sK1
% 27.52/4.01      | v1_funct_1(X0) != iProver_top
% 27.52/4.01      | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
% 27.52/4.01      | v2_funct_1(sK3) = iProver_top
% 27.52/4.01      | v1_relat_1(X0) != iProver_top ),
% 27.52/4.01      inference(renaming,[status(thm)],[c_31501]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_31508,plain,
% 27.52/4.01      ( v1_funct_1(sK2) != iProver_top
% 27.52/4.01      | v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
% 27.52/4.01      | v2_funct_1(sK3) = iProver_top
% 27.52/4.01      | v1_relat_1(sK2) != iProver_top ),
% 27.52/4.01      inference(superposition,[status(thm)],[c_4209,c_31502]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_27,plain,
% 27.52/4.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.52/4.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 27.52/4.01      | ~ v1_funct_1(X0)
% 27.52/4.01      | ~ v1_funct_1(X3)
% 27.52/4.01      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 27.52/4.01      inference(cnf_transformation,[],[f84]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_1719,plain,
% 27.52/4.01      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 27.52/4.01      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 27.52/4.01      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 27.52/4.01      | v1_funct_1(X5) != iProver_top
% 27.52/4.01      | v1_funct_1(X4) != iProver_top ),
% 27.52/4.01      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_5325,plain,
% 27.52/4.01      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 27.52/4.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 27.52/4.01      | v1_funct_1(X2) != iProver_top
% 27.52/4.01      | v1_funct_1(sK3) != iProver_top ),
% 27.52/4.01      inference(superposition,[status(thm)],[c_1713,c_1719]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_5691,plain,
% 27.52/4.01      ( v1_funct_1(X2) != iProver_top
% 27.52/4.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 27.52/4.01      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 27.52/4.01      inference(global_propositional_subsumption,
% 27.52/4.01                [status(thm)],
% 27.52/4.01                [c_5325,c_47]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_5692,plain,
% 27.52/4.01      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 27.52/4.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 27.52/4.01      | v1_funct_1(X2) != iProver_top ),
% 27.52/4.01      inference(renaming,[status(thm)],[c_5691]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_5699,plain,
% 27.52/4.01      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 27.52/4.01      | v1_funct_1(sK2) != iProver_top ),
% 27.52/4.01      inference(superposition,[status(thm)],[c_1710,c_5692]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_44,plain,
% 27.52/4.01      ( v1_funct_1(sK2) = iProver_top ),
% 27.52/4.01      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_5899,plain,
% 27.52/4.01      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 27.52/4.01      inference(global_propositional_subsumption,
% 27.52/4.01                [status(thm)],
% 27.52/4.01                [c_5699,c_44]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_36,negated_conjecture,
% 27.52/4.01      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 27.52/4.01      inference(cnf_transformation,[],[f97]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_1714,plain,
% 27.52/4.01      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) = iProver_top ),
% 27.52/4.01      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_5901,plain,
% 27.52/4.01      ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) = iProver_top ),
% 27.52/4.01      inference(demodulation,[status(thm)],[c_5899,c_1714]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_24,plain,
% 27.52/4.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.52/4.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 27.52/4.01      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 27.52/4.01      | ~ v1_funct_1(X0)
% 27.52/4.01      | ~ v1_funct_1(X3) ),
% 27.52/4.01      inference(cnf_transformation,[],[f82]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_1722,plain,
% 27.52/4.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 27.52/4.01      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 27.52/4.01      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 27.52/4.01      | v1_funct_1(X0) != iProver_top
% 27.52/4.01      | v1_funct_1(X3) != iProver_top ),
% 27.52/4.01      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_6143,plain,
% 27.52/4.01      ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 27.52/4.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 27.52/4.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 27.52/4.01      | v1_funct_1(sK3) != iProver_top
% 27.52/4.01      | v1_funct_1(sK2) != iProver_top ),
% 27.52/4.01      inference(superposition,[status(thm)],[c_5899,c_1722]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_46,plain,
% 27.52/4.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 27.52/4.01      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_49,plain,
% 27.52/4.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 27.52/4.01      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_7913,plain,
% 27.52/4.01      ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 27.52/4.01      inference(global_propositional_subsumption,
% 27.52/4.01                [status(thm)],
% 27.52/4.01                [c_6143,c_44,c_46,c_47,c_49]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_15,plain,
% 27.52/4.01      ( ~ r2_relset_1(X0,X1,X2,X3)
% 27.52/4.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 27.52/4.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 27.52/4.01      | X3 = X2 ),
% 27.52/4.01      inference(cnf_transformation,[],[f71]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_1729,plain,
% 27.52/4.01      ( X0 = X1
% 27.52/4.01      | r2_relset_1(X2,X3,X1,X0) != iProver_top
% 27.52/4.01      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 27.52/4.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top ),
% 27.52/4.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_7924,plain,
% 27.52/4.01      ( k5_relat_1(sK2,sK3) = X0
% 27.52/4.01      | r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),X0) != iProver_top
% 27.52/4.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 27.52/4.01      inference(superposition,[status(thm)],[c_7913,c_1729]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_9859,plain,
% 27.52/4.01      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 27.52/4.01      | m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 27.52/4.01      inference(superposition,[status(thm)],[c_5901,c_7924]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_26,plain,
% 27.52/4.01      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 27.52/4.01      inference(cnf_transformation,[],[f83]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_2142,plain,
% 27.52/4.01      ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 27.52/4.01      inference(instantiation,[status(thm)],[c_26]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_2143,plain,
% 27.52/4.01      ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 27.52/4.01      inference(predicate_to_equality,[status(thm)],[c_2142]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_10314,plain,
% 27.52/4.01      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 27.52/4.01      inference(global_propositional_subsumption,
% 27.52/4.01                [status(thm)],
% 27.52/4.01                [c_9859,c_2143]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_31511,plain,
% 27.52/4.01      ( v1_funct_1(sK2) != iProver_top
% 27.52/4.01      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 27.52/4.01      | v2_funct_1(sK3) = iProver_top
% 27.52/4.01      | v1_relat_1(sK2) != iProver_top ),
% 27.52/4.01      inference(light_normalisation,[status(thm)],[c_31508,c_10314]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_10,plain,
% 27.52/4.01      ( ~ v1_funct_1(X0)
% 27.52/4.01      | ~ v1_funct_1(X1)
% 27.52/4.01      | ~ v2_funct_1(X1)
% 27.52/4.01      | ~ v1_relat_1(X1)
% 27.52/4.01      | ~ v1_relat_1(X0)
% 27.52/4.01      | k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 27.52/4.01      | k2_funct_1(X1) = X0
% 27.52/4.01      | k1_relat_1(X1) != k2_relat_1(X0) ),
% 27.52/4.01      inference(cnf_transformation,[],[f106]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_1733,plain,
% 27.52/4.01      ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 27.52/4.01      | k2_funct_1(X1) = X0
% 27.52/4.01      | k1_relat_1(X1) != k2_relat_1(X0)
% 27.52/4.01      | v1_funct_1(X0) != iProver_top
% 27.52/4.01      | v1_funct_1(X1) != iProver_top
% 27.52/4.01      | v2_funct_1(X1) != iProver_top
% 27.52/4.01      | v1_relat_1(X0) != iProver_top
% 27.52/4.01      | v1_relat_1(X1) != iProver_top ),
% 27.52/4.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_10330,plain,
% 27.52/4.01      ( k2_funct_1(sK3) = sK2
% 27.52/4.01      | k1_relat_1(sK3) != k2_relat_1(sK2)
% 27.52/4.01      | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
% 27.52/4.01      | v1_funct_1(sK3) != iProver_top
% 27.52/4.01      | v1_funct_1(sK2) != iProver_top
% 27.52/4.01      | v2_funct_1(sK3) != iProver_top
% 27.52/4.01      | v1_relat_1(sK3) != iProver_top
% 27.52/4.01      | v1_relat_1(sK2) != iProver_top ),
% 27.52/4.01      inference(superposition,[status(thm)],[c_10314,c_1733]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_3296,plain,
% 27.52/4.01      ( v1_relat_1(sK3) = iProver_top ),
% 27.52/4.01      inference(global_propositional_subsumption,
% 27.52/4.01                [status(thm)],
% 27.52/4.01                [c_2991,c_3067]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_23,plain,
% 27.52/4.01      ( ~ v2_funct_2(X0,X1)
% 27.52/4.01      | ~ v5_relat_1(X0,X1)
% 27.52/4.01      | ~ v1_relat_1(X0)
% 27.52/4.01      | k2_relat_1(X0) = X1 ),
% 27.52/4.01      inference(cnf_transformation,[],[f79]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_28,plain,
% 27.52/4.01      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 27.52/4.01      | ~ v1_funct_2(X2,X0,X1)
% 27.52/4.01      | ~ v1_funct_2(X3,X1,X0)
% 27.52/4.01      | v2_funct_2(X3,X0)
% 27.52/4.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 27.52/4.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 27.52/4.01      | ~ v1_funct_1(X3)
% 27.52/4.01      | ~ v1_funct_1(X2) ),
% 27.52/4.01      inference(cnf_transformation,[],[f87]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_471,plain,
% 27.52/4.01      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 27.52/4.01      | ~ v1_funct_2(X2,X0,X1)
% 27.52/4.01      | ~ v1_funct_2(X3,X1,X0)
% 27.52/4.01      | ~ v5_relat_1(X4,X5)
% 27.52/4.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 27.52/4.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 27.52/4.01      | ~ v1_funct_1(X2)
% 27.52/4.01      | ~ v1_funct_1(X3)
% 27.52/4.01      | ~ v1_relat_1(X4)
% 27.52/4.01      | X3 != X4
% 27.52/4.01      | X0 != X5
% 27.52/4.01      | k2_relat_1(X4) = X5 ),
% 27.52/4.01      inference(resolution_lifted,[status(thm)],[c_23,c_28]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_472,plain,
% 27.52/4.01      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 27.52/4.01      | ~ v1_funct_2(X2,X0,X1)
% 27.52/4.01      | ~ v1_funct_2(X3,X1,X0)
% 27.52/4.01      | ~ v5_relat_1(X3,X0)
% 27.52/4.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 27.52/4.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 27.52/4.01      | ~ v1_funct_1(X3)
% 27.52/4.01      | ~ v1_funct_1(X2)
% 27.52/4.01      | ~ v1_relat_1(X3)
% 27.52/4.01      | k2_relat_1(X3) = X0 ),
% 27.52/4.01      inference(unflattening,[status(thm)],[c_471]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_12,plain,
% 27.52/4.01      ( v5_relat_1(X0,X1)
% 27.52/4.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 27.52/4.01      inference(cnf_transformation,[],[f69]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_496,plain,
% 27.52/4.01      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 27.52/4.01      | ~ v1_funct_2(X2,X0,X1)
% 27.52/4.01      | ~ v1_funct_2(X3,X1,X0)
% 27.52/4.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 27.52/4.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 27.52/4.01      | ~ v1_funct_1(X3)
% 27.52/4.01      | ~ v1_funct_1(X2)
% 27.52/4.01      | ~ v1_relat_1(X3)
% 27.52/4.01      | k2_relat_1(X3) = X0 ),
% 27.52/4.01      inference(forward_subsumption_resolution,
% 27.52/4.01                [status(thm)],
% 27.52/4.01                [c_472,c_12]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_1707,plain,
% 27.52/4.01      ( k2_relat_1(X0) = X1
% 27.52/4.01      | r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X0),k6_partfun1(X1)) != iProver_top
% 27.52/4.01      | v1_funct_2(X3,X1,X2) != iProver_top
% 27.52/4.01      | v1_funct_2(X0,X2,X1) != iProver_top
% 27.52/4.01      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 27.52/4.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
% 27.52/4.01      | v1_funct_1(X3) != iProver_top
% 27.52/4.01      | v1_funct_1(X0) != iProver_top
% 27.52/4.01      | v1_relat_1(X0) != iProver_top ),
% 27.52/4.01      inference(predicate_to_equality,[status(thm)],[c_496]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_2690,plain,
% 27.52/4.01      ( k2_relat_1(sK3) = sK0
% 27.52/4.01      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 27.52/4.01      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 27.52/4.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 27.52/4.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 27.52/4.01      | v1_funct_1(sK3) != iProver_top
% 27.52/4.01      | v1_funct_1(sK2) != iProver_top
% 27.52/4.01      | v1_relat_1(sK3) != iProver_top ),
% 27.52/4.01      inference(superposition,[status(thm)],[c_1714,c_1707]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_45,plain,
% 27.52/4.01      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 27.52/4.01      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_2693,plain,
% 27.52/4.01      ( k2_relat_1(sK3) = sK0 | v1_relat_1(sK3) != iProver_top ),
% 27.52/4.01      inference(global_propositional_subsumption,
% 27.52/4.01                [status(thm)],
% 27.52/4.01                [c_2690,c_44,c_45,c_46,c_47,c_48,c_49]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_3300,plain,
% 27.52/4.01      ( k2_relat_1(sK3) = sK0 ),
% 27.52/4.01      inference(superposition,[status(thm)],[c_3296,c_2693]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_10331,plain,
% 27.52/4.01      ( k2_funct_1(sK3) = sK2
% 27.52/4.01      | k6_partfun1(sK0) != k6_partfun1(sK0)
% 27.52/4.01      | sK1 != sK1
% 27.52/4.01      | v1_funct_1(sK3) != iProver_top
% 27.52/4.01      | v1_funct_1(sK2) != iProver_top
% 27.52/4.01      | v2_funct_1(sK3) != iProver_top
% 27.52/4.01      | v1_relat_1(sK3) != iProver_top
% 27.52/4.01      | v1_relat_1(sK2) != iProver_top ),
% 27.52/4.01      inference(light_normalisation,
% 27.52/4.01                [status(thm)],
% 27.52/4.01                [c_10330,c_3300,c_4209,c_6996]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_10332,plain,
% 27.52/4.01      ( k2_funct_1(sK3) = sK2
% 27.52/4.01      | v1_funct_1(sK3) != iProver_top
% 27.52/4.01      | v1_funct_1(sK2) != iProver_top
% 27.52/4.01      | v2_funct_1(sK3) != iProver_top
% 27.52/4.01      | v1_relat_1(sK3) != iProver_top
% 27.52/4.01      | v1_relat_1(sK2) != iProver_top ),
% 27.52/4.01      inference(equality_resolution_simp,[status(thm)],[c_10331]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_4,plain,
% 27.52/4.01      ( v2_funct_1(k6_partfun1(X0)) ),
% 27.52/4.01      inference(cnf_transformation,[],[f104]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_9060,plain,
% 27.52/4.01      ( v2_funct_1(k6_partfun1(sK0)) ),
% 27.52/4.01      inference(instantiation,[status(thm)],[c_4]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_9061,plain,
% 27.52/4.01      ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
% 27.52/4.01      inference(predicate_to_equality,[status(thm)],[c_9060]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_1903,plain,
% 27.52/4.01      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 27.52/4.01      inference(instantiation,[status(thm)],[c_1133]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_2211,plain,
% 27.52/4.01      ( X0 != sK3 | sK3 = X0 | sK3 != sK3 ),
% 27.52/4.01      inference(instantiation,[status(thm)],[c_1903]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_4020,plain,
% 27.52/4.01      ( k2_funct_1(X0) != sK3 | sK3 = k2_funct_1(X0) | sK3 != sK3 ),
% 27.52/4.01      inference(instantiation,[status(thm)],[c_2211]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_6113,plain,
% 27.52/4.01      ( k2_funct_1(k2_funct_1(sK3)) != sK3
% 27.52/4.01      | sK3 = k2_funct_1(k2_funct_1(sK3))
% 27.52/4.01      | sK3 != sK3 ),
% 27.52/4.01      inference(instantiation,[status(thm)],[c_4020]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_1711,plain,
% 27.52/4.01      ( v1_funct_1(sK3) = iProver_top ),
% 27.52/4.01      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_11,plain,
% 27.52/4.01      ( ~ v1_funct_1(X0)
% 27.52/4.01      | ~ v2_funct_1(X0)
% 27.52/4.01      | ~ v1_relat_1(X0)
% 27.52/4.01      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 27.52/4.01      inference(cnf_transformation,[],[f68]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_1732,plain,
% 27.52/4.01      ( k2_funct_1(k2_funct_1(X0)) = X0
% 27.52/4.01      | v1_funct_1(X0) != iProver_top
% 27.52/4.01      | v2_funct_1(X0) != iProver_top
% 27.52/4.01      | v1_relat_1(X0) != iProver_top ),
% 27.52/4.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_3429,plain,
% 27.52/4.01      ( k2_funct_1(k2_funct_1(sK3)) = sK3
% 27.52/4.01      | v2_funct_1(sK3) != iProver_top
% 27.52/4.01      | v1_relat_1(sK3) != iProver_top ),
% 27.52/4.01      inference(superposition,[status(thm)],[c_1711,c_1732]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_3397,plain,
% 27.52/4.01      ( sK2 = sK2 ),
% 27.52/4.01      inference(instantiation,[status(thm)],[c_1132]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_14,plain,
% 27.52/4.01      ( r2_relset_1(X0,X1,X2,X2)
% 27.52/4.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 27.52/4.01      inference(cnf_transformation,[],[f107]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_1730,plain,
% 27.52/4.01      ( r2_relset_1(X0,X1,X2,X2) = iProver_top
% 27.52/4.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 27.52/4.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_2809,plain,
% 27.52/4.01      ( r2_relset_1(sK1,sK0,sK3,sK3) = iProver_top ),
% 27.52/4.01      inference(superposition,[status(thm)],[c_1713,c_1730]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_1897,plain,
% 27.52/4.01      ( ~ r2_relset_1(X0,X1,X2,sK3)
% 27.52/4.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 27.52/4.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 27.52/4.01      | sK3 = X2 ),
% 27.52/4.01      inference(instantiation,[status(thm)],[c_15]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_2283,plain,
% 27.52/4.01      ( ~ r2_relset_1(sK1,sK0,X0,sK3)
% 27.52/4.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 27.52/4.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 27.52/4.01      | sK3 = X0 ),
% 27.52/4.01      inference(instantiation,[status(thm)],[c_1897]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_2415,plain,
% 27.52/4.01      ( ~ r2_relset_1(sK1,sK0,sK3,sK3)
% 27.52/4.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 27.52/4.01      | sK3 = sK3 ),
% 27.52/4.01      inference(instantiation,[status(thm)],[c_2283]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_2416,plain,
% 27.52/4.01      ( sK3 = sK3
% 27.52/4.01      | r2_relset_1(sK1,sK0,sK3,sK3) != iProver_top
% 27.52/4.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 27.52/4.01      inference(predicate_to_equality,[status(thm)],[c_2415]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(c_32,negated_conjecture,
% 27.52/4.01      ( k2_funct_1(sK2) != sK3 ),
% 27.52/4.01      inference(cnf_transformation,[],[f101]) ).
% 27.52/4.01  
% 27.52/4.01  cnf(contradiction,plain,
% 27.52/4.01      ( $false ),
% 27.52/4.01      inference(minisat,
% 27.52/4.01                [status(thm)],
% 27.52/4.01                [c_71349,c_61532,c_36112,c_31511,c_10332,c_9061,c_6113,
% 27.52/4.01                 c_3429,c_3397,c_3364,c_3067,c_2991,c_2809,c_2416,c_32,
% 27.52/4.01                 c_49,c_47,c_44]) ).
% 27.52/4.01  
% 27.52/4.01  
% 27.52/4.01  % SZS output end CNFRefutation for theBenchmark.p
% 27.52/4.01  
% 27.52/4.01  ------                               Statistics
% 27.52/4.01  
% 27.52/4.01  ------ General
% 27.52/4.01  
% 27.52/4.01  abstr_ref_over_cycles:                  0
% 27.52/4.01  abstr_ref_under_cycles:                 0
% 27.52/4.01  gc_basic_clause_elim:                   0
% 27.52/4.01  forced_gc_time:                         0
% 27.52/4.01  parsing_time:                           0.008
% 27.52/4.01  unif_index_cands_time:                  0.
% 27.52/4.01  unif_index_add_time:                    0.
% 27.52/4.01  orderings_time:                         0.
% 27.52/4.01  out_proof_time:                         0.024
% 27.52/4.01  total_time:                             3.184
% 27.52/4.01  num_of_symbols:                         54
% 27.52/4.01  num_of_terms:                           80423
% 27.52/4.01  
% 27.52/4.01  ------ Preprocessing
% 27.52/4.01  
% 27.52/4.01  num_of_splits:                          0
% 27.52/4.01  num_of_split_atoms:                     0
% 27.52/4.01  num_of_reused_defs:                     0
% 27.52/4.01  num_eq_ax_congr_red:                    8
% 27.52/4.01  num_of_sem_filtered_clauses:            1
% 27.52/4.01  num_of_subtypes:                        0
% 27.52/4.01  monotx_restored_types:                  0
% 27.52/4.01  sat_num_of_epr_types:                   0
% 27.52/4.01  sat_num_of_non_cyclic_types:            0
% 27.52/4.01  sat_guarded_non_collapsed_types:        0
% 27.52/4.01  num_pure_diseq_elim:                    0
% 27.52/4.01  simp_replaced_by:                       0
% 27.52/4.01  res_preprocessed:                       204
% 27.52/4.01  prep_upred:                             0
% 27.52/4.01  prep_unflattend:                        38
% 27.52/4.01  smt_new_axioms:                         0
% 27.52/4.01  pred_elim_cands:                        6
% 27.52/4.01  pred_elim:                              2
% 27.52/4.01  pred_elim_cl:                           3
% 27.52/4.01  pred_elim_cycles:                       5
% 27.52/4.01  merged_defs:                            0
% 27.52/4.01  merged_defs_ncl:                        0
% 27.52/4.01  bin_hyper_res:                          0
% 27.52/4.01  prep_cycles:                            4
% 27.52/4.01  pred_elim_time:                         0.01
% 27.52/4.01  splitting_time:                         0.
% 27.52/4.01  sem_filter_time:                        0.
% 27.52/4.01  monotx_time:                            0.
% 27.52/4.01  subtype_inf_time:                       0.
% 27.52/4.01  
% 27.52/4.01  ------ Problem properties
% 27.52/4.01  
% 27.52/4.01  clauses:                                41
% 27.52/4.01  conjectures:                            12
% 27.52/4.01  epr:                                    7
% 27.52/4.01  horn:                                   35
% 27.52/4.01  ground:                                 12
% 27.52/4.01  unary:                                  18
% 27.52/4.01  binary:                                 2
% 27.52/4.01  lits:                                   130
% 27.52/4.01  lits_eq:                                33
% 27.52/4.01  fd_pure:                                0
% 27.52/4.01  fd_pseudo:                              0
% 27.52/4.01  fd_cond:                                5
% 27.52/4.01  fd_pseudo_cond:                         3
% 27.52/4.01  ac_symbols:                             0
% 27.52/4.01  
% 27.52/4.01  ------ Propositional Solver
% 27.52/4.01  
% 27.52/4.01  prop_solver_calls:                      44
% 27.52/4.01  prop_fast_solver_calls:                 5095
% 27.52/4.01  smt_solver_calls:                       0
% 27.52/4.01  smt_fast_solver_calls:                  0
% 27.52/4.01  prop_num_of_clauses:                    31581
% 27.52/4.01  prop_preprocess_simplified:             61867
% 27.52/4.01  prop_fo_subsumed:                       1388
% 27.52/4.01  prop_solver_time:                       0.
% 27.52/4.01  smt_solver_time:                        0.
% 27.52/4.01  smt_fast_solver_time:                   0.
% 27.52/4.01  prop_fast_solver_time:                  0.
% 27.52/4.01  prop_unsat_core_time:                   0.006
% 27.52/4.01  
% 27.52/4.01  ------ QBF
% 27.52/4.01  
% 27.52/4.01  qbf_q_res:                              0
% 27.52/4.01  qbf_num_tautologies:                    0
% 27.52/4.01  qbf_prep_cycles:                        0
% 27.52/4.01  
% 27.52/4.01  ------ BMC1
% 27.52/4.01  
% 27.52/4.01  bmc1_current_bound:                     -1
% 27.52/4.01  bmc1_last_solved_bound:                 -1
% 27.52/4.01  bmc1_unsat_core_size:                   -1
% 27.52/4.01  bmc1_unsat_core_parents_size:           -1
% 27.52/4.01  bmc1_merge_next_fun:                    0
% 27.52/4.01  bmc1_unsat_core_clauses_time:           0.
% 27.52/4.01  
% 27.52/4.01  ------ Instantiation
% 27.52/4.01  
% 27.52/4.01  inst_num_of_clauses:                    2512
% 27.52/4.01  inst_num_in_passive:                    1449
% 27.52/4.01  inst_num_in_active:                     3605
% 27.52/4.01  inst_num_in_unprocessed:                209
% 27.52/4.01  inst_num_of_loops:                      3855
% 27.52/4.01  inst_num_of_learning_restarts:          1
% 27.52/4.01  inst_num_moves_active_passive:          246
% 27.52/4.01  inst_lit_activity:                      0
% 27.52/4.01  inst_lit_activity_moves:                2
% 27.52/4.01  inst_num_tautologies:                   0
% 27.52/4.01  inst_num_prop_implied:                  0
% 27.52/4.01  inst_num_existing_simplified:           0
% 27.52/4.01  inst_num_eq_res_simplified:             0
% 27.52/4.01  inst_num_child_elim:                    0
% 27.52/4.01  inst_num_of_dismatching_blockings:      3308
% 27.52/4.01  inst_num_of_non_proper_insts:           8675
% 27.52/4.01  inst_num_of_duplicates:                 0
% 27.52/4.01  inst_inst_num_from_inst_to_res:         0
% 27.52/4.01  inst_dismatching_checking_time:         0.
% 27.52/4.01  
% 27.52/4.01  ------ Resolution
% 27.52/4.01  
% 27.52/4.01  res_num_of_clauses:                     59
% 27.52/4.01  res_num_in_passive:                     59
% 27.52/4.01  res_num_in_active:                      0
% 27.52/4.01  res_num_of_loops:                       208
% 27.52/4.01  res_forward_subset_subsumed:            654
% 27.52/4.01  res_backward_subset_subsumed:           4
% 27.52/4.01  res_forward_subsumed:                   0
% 27.52/4.01  res_backward_subsumed:                  0
% 27.52/4.01  res_forward_subsumption_resolution:     4
% 27.52/4.01  res_backward_subsumption_resolution:    0
% 27.52/4.01  res_clause_to_clause_subsumption:       8822
% 27.52/4.01  res_orphan_elimination:                 0
% 27.52/4.01  res_tautology_del:                      251
% 27.52/4.01  res_num_eq_res_simplified:              0
% 27.52/4.01  res_num_sel_changes:                    0
% 27.52/4.01  res_moves_from_active_to_pass:          0
% 27.52/4.01  
% 27.52/4.01  ------ Superposition
% 27.52/4.01  
% 27.52/4.01  sup_time_total:                         0.
% 27.52/4.01  sup_time_generating:                    0.
% 27.52/4.01  sup_time_sim_full:                      0.
% 27.52/4.01  sup_time_sim_immed:                     0.
% 27.52/4.01  
% 27.52/4.01  sup_num_of_clauses:                     3645
% 27.52/4.01  sup_num_in_active:                      735
% 27.52/4.01  sup_num_in_passive:                     2910
% 27.52/4.01  sup_num_of_loops:                       770
% 27.52/4.01  sup_fw_superposition:                   1463
% 27.52/4.01  sup_bw_superposition:                   2759
% 27.52/4.01  sup_immediate_simplified:               2014
% 27.52/4.01  sup_given_eliminated:                   0
% 27.52/4.01  comparisons_done:                       0
% 27.52/4.01  comparisons_avoided:                    1
% 27.52/4.01  
% 27.52/4.01  ------ Simplifications
% 27.52/4.01  
% 27.52/4.01  
% 27.52/4.01  sim_fw_subset_subsumed:                 86
% 27.52/4.01  sim_bw_subset_subsumed:                 192
% 27.52/4.01  sim_fw_subsumed:                        31
% 27.52/4.01  sim_bw_subsumed:                        8
% 27.52/4.01  sim_fw_subsumption_res:                 0
% 27.52/4.01  sim_bw_subsumption_res:                 0
% 27.52/4.01  sim_tautology_del:                      0
% 27.52/4.01  sim_eq_tautology_del:                   77
% 27.52/4.01  sim_eq_res_simp:                        2
% 27.52/4.01  sim_fw_demodulated:                     355
% 27.52/4.01  sim_bw_demodulated:                     14
% 27.52/4.01  sim_light_normalised:                   1648
% 27.52/4.01  sim_joinable_taut:                      0
% 27.52/4.01  sim_joinable_simp:                      0
% 27.52/4.01  sim_ac_normalised:                      0
% 27.52/4.01  sim_smt_subsumption:                    0
% 27.52/4.01  
%------------------------------------------------------------------------------
