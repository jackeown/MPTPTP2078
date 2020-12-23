%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:21 EST 2020

% Result     : Theorem 7.49s
% Output     : CNFRefutation 7.49s
% Verified   : 
% Statistics : Number of formulae       :  199 ( 968 expanded)
%              Number of clauses        :  116 ( 307 expanded)
%              Number of leaves         :   20 ( 217 expanded)
%              Depth                    :   24
%              Number of atoms          :  619 (6567 expanded)
%              Number of equality atoms :  249 (2497 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    6 (   2 average)

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

fof(f57,plain,(
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

fof(f58,plain,(
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
    inference(flattening,[],[f57])).

fof(f64,plain,(
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

fof(f63,plain,
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

fof(f65,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f58,f64,f63])).

fof(f100,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f65])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f98,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f65])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f101,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f65])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f44,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f43])).

fof(f82,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f103,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f65])).

fof(f97,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f65])).

fof(f22,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_1(X0) ) ) ),
    inference(pure_predicate_removal,[],[f22])).

fof(f55,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f56,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f55])).

fof(f96,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f37])).

fof(f79,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f78,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f83,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f46,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f45])).

fof(f85,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f21,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f94,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f21])).

fof(f109,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f85,f94])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f107,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_partfun1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f76,f94])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f54,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f53])).

fof(f93,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f99,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f65])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f50,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f49])).

fof(f62,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f50])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f102,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f65])).

fof(f18,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f90,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f111,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f90,f94])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f52,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f51])).

fof(f92,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f108,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_partfun1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f77,f94])).

fof(f106,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1248,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1264,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3276,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1248,c_1264])).

cnf(c_43,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_1497,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1880,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1497])).

cnf(c_1881,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1880])).

cnf(c_6,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1963,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1964,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1963])).

cnf(c_4079,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3276,c_43,c_1881,c_1964])).

cnf(c_38,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1246,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_3277,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1246,c_1264])).

cnf(c_41,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_1883,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1497])).

cnf(c_1884,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1883])).

cnf(c_1966,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1967,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1966])).

cnf(c_4157,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3277,c_41,c_1884,c_1967])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1254,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2053,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1246,c_1254])).

cnf(c_35,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_2055,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2053,c_35])).

cnf(c_17,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_33,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_464,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_33])).

cnf(c_465,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_464])).

cnf(c_39,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_467,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_465,c_39])).

cnf(c_1240,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_467])).

cnf(c_2064,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = sK1
    | v1_relat_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2055,c_1240])).

cnf(c_2226,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2064,c_41,c_1884,c_1967])).

cnf(c_28,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1249,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_2967,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2))))) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2226,c_1249])).

cnf(c_40,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_12,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1488,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1489,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1488])).

cnf(c_13,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1494,plain,
    ( ~ v1_funct_1(sK2)
    | v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1495,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1494])).

cnf(c_10148,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2))))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2967,c_40,c_41,c_1489,c_1495,c_1884,c_1967])).

cnf(c_16,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_478,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_33])).

cnf(c_479,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_478])).

cnf(c_481,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_479,c_39])).

cnf(c_1239,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_481])).

cnf(c_4166,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_4157,c_1239])).

cnf(c_10152,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10148,c_4166])).

cnf(c_10155,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_10152,c_1264])).

cnf(c_10202,plain,
    ( v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10155,c_40,c_41,c_1495,c_1884,c_1967])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1260,plain,
    ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_10211,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_10202,c_1260])).

cnf(c_28727,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4157,c_10211])).

cnf(c_18,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_450,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_33])).

cnf(c_451,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(unflattening,[status(thm)],[c_450])).

cnf(c_453,plain,
    ( ~ v1_relat_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_451,c_39])).

cnf(c_1241,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_453])).

cnf(c_2063,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | v1_relat_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2055,c_1241])).

cnf(c_2420,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2063,c_41,c_1884,c_1967])).

cnf(c_28773,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k6_partfun1(sK1),X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_28727,c_2420])).

cnf(c_29392,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
    inference(superposition,[status(thm)],[c_4079,c_28773])).

cnf(c_20,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_5,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_398,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_20,c_5])).

cnf(c_1244,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_398])).

cnf(c_1979,plain,
    ( r1_tarski(k1_relat_1(sK3),sK1) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1248,c_1244])).

cnf(c_2378,plain,
    ( r1_tarski(k1_relat_1(sK3),sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1979,c_43,c_1881,c_1964])).

cnf(c_10,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k6_partfun1(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1259,plain,
    ( k5_relat_1(k6_partfun1(X0),X1) = X1
    | r1_tarski(k1_relat_1(X1),X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4042,plain,
    ( k5_relat_1(k6_partfun1(sK1),sK3) = sK3
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2378,c_1259])).

cnf(c_7187,plain,
    ( k5_relat_1(k6_partfun1(sK1),sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4042,c_43,c_1881,c_1964])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1250,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_4953,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1248,c_1250])).

cnf(c_37,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_42,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_5162,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4953,c_42])).

cnf(c_5163,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_5162])).

cnf(c_5175,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1246,c_5163])).

cnf(c_1632,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(X1,X2,X3,X4,X0,sK3) = k5_relat_1(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_1834,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(X2,X3,X0,X1,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1632])).

cnf(c_2023,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(X0,X1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1834])).

cnf(c_2398,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_2023])).

cnf(c_5395,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5175,c_39,c_38,c_37,c_36,c_2398])).

cnf(c_23,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_34,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_419,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_34])).

cnf(c_420,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_419])).

cnf(c_24,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_60,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_422,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_420,c_60])).

cnf(c_1243,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_422])).

cnf(c_5398,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5395,c_1243])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1252,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_5400,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5395,c_1252])).

cnf(c_8288,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5398,c_40,c_41,c_42,c_43,c_5400])).

cnf(c_1980,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1246,c_1244])).

cnf(c_2384,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1980,c_41,c_1884,c_1967])).

cnf(c_11,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_partfun1(X1)) = X0 ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1258,plain,
    ( k5_relat_1(X0,k6_partfun1(X1)) = X0
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4458,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0)) = k2_funct_1(sK2)
    | r1_tarski(k1_relat_1(sK2),X0) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4166,c_1258])).

cnf(c_12513,plain,
    ( r1_tarski(k1_relat_1(sK2),X0) != iProver_top
    | k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0)) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4458,c_40,c_41,c_1495,c_1884,c_1967])).

cnf(c_12514,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0)) = k2_funct_1(sK2)
    | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_12513])).

cnf(c_12522,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k2_funct_1(sK2) ),
    inference(superposition,[status(thm)],[c_2384,c_12514])).

cnf(c_29420,plain,
    ( k2_funct_1(sK2) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_29392,c_7187,c_8288,c_12522])).

cnf(c_30,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f106])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_29420,c_30])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:35:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.49/1.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.49/1.48  
% 7.49/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.49/1.48  
% 7.49/1.48  ------  iProver source info
% 7.49/1.48  
% 7.49/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.49/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.49/1.48  git: non_committed_changes: false
% 7.49/1.48  git: last_make_outside_of_git: false
% 7.49/1.48  
% 7.49/1.48  ------ 
% 7.49/1.48  
% 7.49/1.48  ------ Input Options
% 7.49/1.48  
% 7.49/1.48  --out_options                           all
% 7.49/1.48  --tptp_safe_out                         true
% 7.49/1.48  --problem_path                          ""
% 7.49/1.48  --include_path                          ""
% 7.49/1.48  --clausifier                            res/vclausify_rel
% 7.49/1.48  --clausifier_options                    --mode clausify
% 7.49/1.48  --stdin                                 false
% 7.49/1.48  --stats_out                             all
% 7.49/1.48  
% 7.49/1.48  ------ General Options
% 7.49/1.48  
% 7.49/1.48  --fof                                   false
% 7.49/1.48  --time_out_real                         305.
% 7.49/1.48  --time_out_virtual                      -1.
% 7.49/1.48  --symbol_type_check                     false
% 7.49/1.48  --clausify_out                          false
% 7.49/1.48  --sig_cnt_out                           false
% 7.49/1.48  --trig_cnt_out                          false
% 7.49/1.48  --trig_cnt_out_tolerance                1.
% 7.49/1.48  --trig_cnt_out_sk_spl                   false
% 7.49/1.48  --abstr_cl_out                          false
% 7.49/1.48  
% 7.49/1.48  ------ Global Options
% 7.49/1.48  
% 7.49/1.48  --schedule                              default
% 7.49/1.48  --add_important_lit                     false
% 7.49/1.48  --prop_solver_per_cl                    1000
% 7.49/1.48  --min_unsat_core                        false
% 7.49/1.48  --soft_assumptions                      false
% 7.49/1.48  --soft_lemma_size                       3
% 7.49/1.48  --prop_impl_unit_size                   0
% 7.49/1.48  --prop_impl_unit                        []
% 7.49/1.48  --share_sel_clauses                     true
% 7.49/1.48  --reset_solvers                         false
% 7.49/1.48  --bc_imp_inh                            [conj_cone]
% 7.49/1.48  --conj_cone_tolerance                   3.
% 7.49/1.48  --extra_neg_conj                        none
% 7.49/1.48  --large_theory_mode                     true
% 7.49/1.48  --prolific_symb_bound                   200
% 7.49/1.48  --lt_threshold                          2000
% 7.49/1.48  --clause_weak_htbl                      true
% 7.49/1.48  --gc_record_bc_elim                     false
% 7.49/1.48  
% 7.49/1.48  ------ Preprocessing Options
% 7.49/1.48  
% 7.49/1.48  --preprocessing_flag                    true
% 7.49/1.48  --time_out_prep_mult                    0.1
% 7.49/1.48  --splitting_mode                        input
% 7.49/1.48  --splitting_grd                         true
% 7.49/1.48  --splitting_cvd                         false
% 7.49/1.48  --splitting_cvd_svl                     false
% 7.49/1.48  --splitting_nvd                         32
% 7.49/1.48  --sub_typing                            true
% 7.49/1.48  --prep_gs_sim                           true
% 7.49/1.48  --prep_unflatten                        true
% 7.49/1.48  --prep_res_sim                          true
% 7.49/1.48  --prep_upred                            true
% 7.49/1.48  --prep_sem_filter                       exhaustive
% 7.49/1.48  --prep_sem_filter_out                   false
% 7.49/1.48  --pred_elim                             true
% 7.49/1.48  --res_sim_input                         true
% 7.49/1.48  --eq_ax_congr_red                       true
% 7.49/1.48  --pure_diseq_elim                       true
% 7.49/1.48  --brand_transform                       false
% 7.49/1.48  --non_eq_to_eq                          false
% 7.49/1.48  --prep_def_merge                        true
% 7.49/1.48  --prep_def_merge_prop_impl              false
% 7.49/1.48  --prep_def_merge_mbd                    true
% 7.49/1.48  --prep_def_merge_tr_red                 false
% 7.49/1.48  --prep_def_merge_tr_cl                  false
% 7.49/1.48  --smt_preprocessing                     true
% 7.49/1.48  --smt_ac_axioms                         fast
% 7.49/1.48  --preprocessed_out                      false
% 7.49/1.48  --preprocessed_stats                    false
% 7.49/1.48  
% 7.49/1.48  ------ Abstraction refinement Options
% 7.49/1.48  
% 7.49/1.48  --abstr_ref                             []
% 7.49/1.48  --abstr_ref_prep                        false
% 7.49/1.48  --abstr_ref_until_sat                   false
% 7.49/1.48  --abstr_ref_sig_restrict                funpre
% 7.49/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.49/1.48  --abstr_ref_under                       []
% 7.49/1.48  
% 7.49/1.48  ------ SAT Options
% 7.49/1.48  
% 7.49/1.48  --sat_mode                              false
% 7.49/1.48  --sat_fm_restart_options                ""
% 7.49/1.48  --sat_gr_def                            false
% 7.49/1.48  --sat_epr_types                         true
% 7.49/1.48  --sat_non_cyclic_types                  false
% 7.49/1.48  --sat_finite_models                     false
% 7.49/1.48  --sat_fm_lemmas                         false
% 7.49/1.48  --sat_fm_prep                           false
% 7.49/1.48  --sat_fm_uc_incr                        true
% 7.49/1.48  --sat_out_model                         small
% 7.49/1.48  --sat_out_clauses                       false
% 7.49/1.48  
% 7.49/1.48  ------ QBF Options
% 7.49/1.48  
% 7.49/1.48  --qbf_mode                              false
% 7.49/1.48  --qbf_elim_univ                         false
% 7.49/1.48  --qbf_dom_inst                          none
% 7.49/1.48  --qbf_dom_pre_inst                      false
% 7.49/1.48  --qbf_sk_in                             false
% 7.49/1.48  --qbf_pred_elim                         true
% 7.49/1.48  --qbf_split                             512
% 7.49/1.48  
% 7.49/1.48  ------ BMC1 Options
% 7.49/1.48  
% 7.49/1.48  --bmc1_incremental                      false
% 7.49/1.48  --bmc1_axioms                           reachable_all
% 7.49/1.48  --bmc1_min_bound                        0
% 7.49/1.48  --bmc1_max_bound                        -1
% 7.49/1.48  --bmc1_max_bound_default                -1
% 7.49/1.48  --bmc1_symbol_reachability              true
% 7.49/1.48  --bmc1_property_lemmas                  false
% 7.49/1.48  --bmc1_k_induction                      false
% 7.49/1.48  --bmc1_non_equiv_states                 false
% 7.49/1.48  --bmc1_deadlock                         false
% 7.49/1.48  --bmc1_ucm                              false
% 7.49/1.48  --bmc1_add_unsat_core                   none
% 7.49/1.48  --bmc1_unsat_core_children              false
% 7.49/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.49/1.48  --bmc1_out_stat                         full
% 7.49/1.48  --bmc1_ground_init                      false
% 7.49/1.48  --bmc1_pre_inst_next_state              false
% 7.49/1.48  --bmc1_pre_inst_state                   false
% 7.49/1.48  --bmc1_pre_inst_reach_state             false
% 7.49/1.48  --bmc1_out_unsat_core                   false
% 7.49/1.48  --bmc1_aig_witness_out                  false
% 7.49/1.48  --bmc1_verbose                          false
% 7.49/1.48  --bmc1_dump_clauses_tptp                false
% 7.49/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.49/1.48  --bmc1_dump_file                        -
% 7.49/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.49/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.49/1.48  --bmc1_ucm_extend_mode                  1
% 7.49/1.48  --bmc1_ucm_init_mode                    2
% 7.49/1.48  --bmc1_ucm_cone_mode                    none
% 7.49/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.49/1.48  --bmc1_ucm_relax_model                  4
% 7.49/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.49/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.49/1.48  --bmc1_ucm_layered_model                none
% 7.49/1.48  --bmc1_ucm_max_lemma_size               10
% 7.49/1.48  
% 7.49/1.48  ------ AIG Options
% 7.49/1.48  
% 7.49/1.48  --aig_mode                              false
% 7.49/1.48  
% 7.49/1.48  ------ Instantiation Options
% 7.49/1.48  
% 7.49/1.48  --instantiation_flag                    true
% 7.49/1.48  --inst_sos_flag                         false
% 7.49/1.48  --inst_sos_phase                        true
% 7.49/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.49/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.49/1.48  --inst_lit_sel_side                     num_symb
% 7.49/1.48  --inst_solver_per_active                1400
% 7.49/1.48  --inst_solver_calls_frac                1.
% 7.49/1.48  --inst_passive_queue_type               priority_queues
% 7.49/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.49/1.48  --inst_passive_queues_freq              [25;2]
% 7.49/1.48  --inst_dismatching                      true
% 7.49/1.48  --inst_eager_unprocessed_to_passive     true
% 7.49/1.48  --inst_prop_sim_given                   true
% 7.49/1.48  --inst_prop_sim_new                     false
% 7.49/1.48  --inst_subs_new                         false
% 7.49/1.48  --inst_eq_res_simp                      false
% 7.49/1.48  --inst_subs_given                       false
% 7.49/1.48  --inst_orphan_elimination               true
% 7.49/1.48  --inst_learning_loop_flag               true
% 7.49/1.48  --inst_learning_start                   3000
% 7.49/1.48  --inst_learning_factor                  2
% 7.49/1.48  --inst_start_prop_sim_after_learn       3
% 7.49/1.48  --inst_sel_renew                        solver
% 7.49/1.48  --inst_lit_activity_flag                true
% 7.49/1.48  --inst_restr_to_given                   false
% 7.49/1.48  --inst_activity_threshold               500
% 7.49/1.48  --inst_out_proof                        true
% 7.49/1.48  
% 7.49/1.48  ------ Resolution Options
% 7.49/1.48  
% 7.49/1.48  --resolution_flag                       true
% 7.49/1.48  --res_lit_sel                           adaptive
% 7.49/1.48  --res_lit_sel_side                      none
% 7.49/1.48  --res_ordering                          kbo
% 7.49/1.48  --res_to_prop_solver                    active
% 7.49/1.48  --res_prop_simpl_new                    false
% 7.49/1.48  --res_prop_simpl_given                  true
% 7.49/1.48  --res_passive_queue_type                priority_queues
% 7.49/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.49/1.48  --res_passive_queues_freq               [15;5]
% 7.49/1.48  --res_forward_subs                      full
% 7.49/1.48  --res_backward_subs                     full
% 7.49/1.48  --res_forward_subs_resolution           true
% 7.49/1.48  --res_backward_subs_resolution          true
% 7.49/1.48  --res_orphan_elimination                true
% 7.49/1.48  --res_time_limit                        2.
% 7.49/1.48  --res_out_proof                         true
% 7.49/1.48  
% 7.49/1.48  ------ Superposition Options
% 7.49/1.48  
% 7.49/1.48  --superposition_flag                    true
% 7.49/1.48  --sup_passive_queue_type                priority_queues
% 7.49/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.49/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.49/1.48  --demod_completeness_check              fast
% 7.49/1.48  --demod_use_ground                      true
% 7.49/1.48  --sup_to_prop_solver                    passive
% 7.49/1.48  --sup_prop_simpl_new                    true
% 7.49/1.48  --sup_prop_simpl_given                  true
% 7.49/1.48  --sup_fun_splitting                     false
% 7.49/1.48  --sup_smt_interval                      50000
% 7.49/1.48  
% 7.49/1.48  ------ Superposition Simplification Setup
% 7.49/1.48  
% 7.49/1.48  --sup_indices_passive                   []
% 7.49/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.49/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.49/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.49/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.49/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.49/1.48  --sup_full_bw                           [BwDemod]
% 7.49/1.48  --sup_immed_triv                        [TrivRules]
% 7.49/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.49/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.49/1.48  --sup_immed_bw_main                     []
% 7.49/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.49/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.49/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.49/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.49/1.48  
% 7.49/1.48  ------ Combination Options
% 7.49/1.48  
% 7.49/1.48  --comb_res_mult                         3
% 7.49/1.48  --comb_sup_mult                         2
% 7.49/1.48  --comb_inst_mult                        10
% 7.49/1.48  
% 7.49/1.48  ------ Debug Options
% 7.49/1.48  
% 7.49/1.48  --dbg_backtrace                         false
% 7.49/1.48  --dbg_dump_prop_clauses                 false
% 7.49/1.48  --dbg_dump_prop_clauses_file            -
% 7.49/1.48  --dbg_out_stat                          false
% 7.49/1.48  ------ Parsing...
% 7.49/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.49/1.48  
% 7.49/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 7.49/1.48  
% 7.49/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.49/1.48  
% 7.49/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.49/1.48  ------ Proving...
% 7.49/1.48  ------ Problem Properties 
% 7.49/1.48  
% 7.49/1.48  
% 7.49/1.48  clauses                                 33
% 7.49/1.48  conjectures                             8
% 7.49/1.48  EPR                                     6
% 7.49/1.48  Horn                                    33
% 7.49/1.48  unary                                   11
% 7.49/1.48  binary                                  8
% 7.49/1.48  lits                                    77
% 7.49/1.48  lits eq                                 19
% 7.49/1.48  fd_pure                                 0
% 7.49/1.48  fd_pseudo                               0
% 7.49/1.48  fd_cond                                 0
% 7.49/1.48  fd_pseudo_cond                          1
% 7.49/1.48  AC symbols                              0
% 7.49/1.48  
% 7.49/1.48  ------ Schedule dynamic 5 is on 
% 7.49/1.48  
% 7.49/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.49/1.48  
% 7.49/1.48  
% 7.49/1.48  ------ 
% 7.49/1.48  Current options:
% 7.49/1.48  ------ 
% 7.49/1.48  
% 7.49/1.48  ------ Input Options
% 7.49/1.48  
% 7.49/1.48  --out_options                           all
% 7.49/1.48  --tptp_safe_out                         true
% 7.49/1.48  --problem_path                          ""
% 7.49/1.48  --include_path                          ""
% 7.49/1.48  --clausifier                            res/vclausify_rel
% 7.49/1.48  --clausifier_options                    --mode clausify
% 7.49/1.48  --stdin                                 false
% 7.49/1.48  --stats_out                             all
% 7.49/1.48  
% 7.49/1.48  ------ General Options
% 7.49/1.48  
% 7.49/1.48  --fof                                   false
% 7.49/1.48  --time_out_real                         305.
% 7.49/1.48  --time_out_virtual                      -1.
% 7.49/1.48  --symbol_type_check                     false
% 7.49/1.48  --clausify_out                          false
% 7.49/1.48  --sig_cnt_out                           false
% 7.49/1.48  --trig_cnt_out                          false
% 7.49/1.48  --trig_cnt_out_tolerance                1.
% 7.49/1.48  --trig_cnt_out_sk_spl                   false
% 7.49/1.48  --abstr_cl_out                          false
% 7.49/1.48  
% 7.49/1.48  ------ Global Options
% 7.49/1.48  
% 7.49/1.48  --schedule                              default
% 7.49/1.48  --add_important_lit                     false
% 7.49/1.48  --prop_solver_per_cl                    1000
% 7.49/1.48  --min_unsat_core                        false
% 7.49/1.48  --soft_assumptions                      false
% 7.49/1.48  --soft_lemma_size                       3
% 7.49/1.48  --prop_impl_unit_size                   0
% 7.49/1.48  --prop_impl_unit                        []
% 7.49/1.48  --share_sel_clauses                     true
% 7.49/1.48  --reset_solvers                         false
% 7.49/1.48  --bc_imp_inh                            [conj_cone]
% 7.49/1.48  --conj_cone_tolerance                   3.
% 7.49/1.48  --extra_neg_conj                        none
% 7.49/1.48  --large_theory_mode                     true
% 7.49/1.48  --prolific_symb_bound                   200
% 7.49/1.48  --lt_threshold                          2000
% 7.49/1.48  --clause_weak_htbl                      true
% 7.49/1.48  --gc_record_bc_elim                     false
% 7.49/1.48  
% 7.49/1.48  ------ Preprocessing Options
% 7.49/1.48  
% 7.49/1.48  --preprocessing_flag                    true
% 7.49/1.48  --time_out_prep_mult                    0.1
% 7.49/1.48  --splitting_mode                        input
% 7.49/1.48  --splitting_grd                         true
% 7.49/1.48  --splitting_cvd                         false
% 7.49/1.48  --splitting_cvd_svl                     false
% 7.49/1.48  --splitting_nvd                         32
% 7.49/1.48  --sub_typing                            true
% 7.49/1.48  --prep_gs_sim                           true
% 7.49/1.48  --prep_unflatten                        true
% 7.49/1.48  --prep_res_sim                          true
% 7.49/1.48  --prep_upred                            true
% 7.49/1.48  --prep_sem_filter                       exhaustive
% 7.49/1.48  --prep_sem_filter_out                   false
% 7.49/1.48  --pred_elim                             true
% 7.49/1.48  --res_sim_input                         true
% 7.49/1.48  --eq_ax_congr_red                       true
% 7.49/1.48  --pure_diseq_elim                       true
% 7.49/1.48  --brand_transform                       false
% 7.49/1.48  --non_eq_to_eq                          false
% 7.49/1.48  --prep_def_merge                        true
% 7.49/1.48  --prep_def_merge_prop_impl              false
% 7.49/1.48  --prep_def_merge_mbd                    true
% 7.49/1.48  --prep_def_merge_tr_red                 false
% 7.49/1.48  --prep_def_merge_tr_cl                  false
% 7.49/1.48  --smt_preprocessing                     true
% 7.49/1.48  --smt_ac_axioms                         fast
% 7.49/1.48  --preprocessed_out                      false
% 7.49/1.48  --preprocessed_stats                    false
% 7.49/1.48  
% 7.49/1.48  ------ Abstraction refinement Options
% 7.49/1.48  
% 7.49/1.48  --abstr_ref                             []
% 7.49/1.48  --abstr_ref_prep                        false
% 7.49/1.48  --abstr_ref_until_sat                   false
% 7.49/1.48  --abstr_ref_sig_restrict                funpre
% 7.49/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.49/1.48  --abstr_ref_under                       []
% 7.49/1.48  
% 7.49/1.48  ------ SAT Options
% 7.49/1.48  
% 7.49/1.48  --sat_mode                              false
% 7.49/1.48  --sat_fm_restart_options                ""
% 7.49/1.48  --sat_gr_def                            false
% 7.49/1.48  --sat_epr_types                         true
% 7.49/1.48  --sat_non_cyclic_types                  false
% 7.49/1.48  --sat_finite_models                     false
% 7.49/1.48  --sat_fm_lemmas                         false
% 7.49/1.48  --sat_fm_prep                           false
% 7.49/1.48  --sat_fm_uc_incr                        true
% 7.49/1.48  --sat_out_model                         small
% 7.49/1.48  --sat_out_clauses                       false
% 7.49/1.48  
% 7.49/1.48  ------ QBF Options
% 7.49/1.48  
% 7.49/1.48  --qbf_mode                              false
% 7.49/1.48  --qbf_elim_univ                         false
% 7.49/1.48  --qbf_dom_inst                          none
% 7.49/1.48  --qbf_dom_pre_inst                      false
% 7.49/1.48  --qbf_sk_in                             false
% 7.49/1.48  --qbf_pred_elim                         true
% 7.49/1.48  --qbf_split                             512
% 7.49/1.48  
% 7.49/1.48  ------ BMC1 Options
% 7.49/1.48  
% 7.49/1.48  --bmc1_incremental                      false
% 7.49/1.48  --bmc1_axioms                           reachable_all
% 7.49/1.48  --bmc1_min_bound                        0
% 7.49/1.48  --bmc1_max_bound                        -1
% 7.49/1.48  --bmc1_max_bound_default                -1
% 7.49/1.48  --bmc1_symbol_reachability              true
% 7.49/1.48  --bmc1_property_lemmas                  false
% 7.49/1.48  --bmc1_k_induction                      false
% 7.49/1.48  --bmc1_non_equiv_states                 false
% 7.49/1.48  --bmc1_deadlock                         false
% 7.49/1.48  --bmc1_ucm                              false
% 7.49/1.48  --bmc1_add_unsat_core                   none
% 7.49/1.48  --bmc1_unsat_core_children              false
% 7.49/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.49/1.48  --bmc1_out_stat                         full
% 7.49/1.48  --bmc1_ground_init                      false
% 7.49/1.48  --bmc1_pre_inst_next_state              false
% 7.49/1.48  --bmc1_pre_inst_state                   false
% 7.49/1.48  --bmc1_pre_inst_reach_state             false
% 7.49/1.48  --bmc1_out_unsat_core                   false
% 7.49/1.48  --bmc1_aig_witness_out                  false
% 7.49/1.48  --bmc1_verbose                          false
% 7.49/1.48  --bmc1_dump_clauses_tptp                false
% 7.49/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.49/1.48  --bmc1_dump_file                        -
% 7.49/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.49/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.49/1.48  --bmc1_ucm_extend_mode                  1
% 7.49/1.48  --bmc1_ucm_init_mode                    2
% 7.49/1.48  --bmc1_ucm_cone_mode                    none
% 7.49/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.49/1.48  --bmc1_ucm_relax_model                  4
% 7.49/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.49/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.49/1.48  --bmc1_ucm_layered_model                none
% 7.49/1.48  --bmc1_ucm_max_lemma_size               10
% 7.49/1.48  
% 7.49/1.48  ------ AIG Options
% 7.49/1.48  
% 7.49/1.48  --aig_mode                              false
% 7.49/1.48  
% 7.49/1.48  ------ Instantiation Options
% 7.49/1.48  
% 7.49/1.48  --instantiation_flag                    true
% 7.49/1.48  --inst_sos_flag                         false
% 7.49/1.48  --inst_sos_phase                        true
% 7.49/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.49/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.49/1.48  --inst_lit_sel_side                     none
% 7.49/1.48  --inst_solver_per_active                1400
% 7.49/1.48  --inst_solver_calls_frac                1.
% 7.49/1.48  --inst_passive_queue_type               priority_queues
% 7.49/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.49/1.48  --inst_passive_queues_freq              [25;2]
% 7.49/1.48  --inst_dismatching                      true
% 7.49/1.48  --inst_eager_unprocessed_to_passive     true
% 7.49/1.48  --inst_prop_sim_given                   true
% 7.49/1.48  --inst_prop_sim_new                     false
% 7.49/1.48  --inst_subs_new                         false
% 7.49/1.48  --inst_eq_res_simp                      false
% 7.49/1.48  --inst_subs_given                       false
% 7.49/1.48  --inst_orphan_elimination               true
% 7.49/1.48  --inst_learning_loop_flag               true
% 7.49/1.48  --inst_learning_start                   3000
% 7.49/1.48  --inst_learning_factor                  2
% 7.49/1.48  --inst_start_prop_sim_after_learn       3
% 7.49/1.48  --inst_sel_renew                        solver
% 7.49/1.48  --inst_lit_activity_flag                true
% 7.49/1.48  --inst_restr_to_given                   false
% 7.49/1.48  --inst_activity_threshold               500
% 7.49/1.48  --inst_out_proof                        true
% 7.49/1.48  
% 7.49/1.48  ------ Resolution Options
% 7.49/1.48  
% 7.49/1.48  --resolution_flag                       false
% 7.49/1.48  --res_lit_sel                           adaptive
% 7.49/1.48  --res_lit_sel_side                      none
% 7.49/1.48  --res_ordering                          kbo
% 7.49/1.48  --res_to_prop_solver                    active
% 7.49/1.48  --res_prop_simpl_new                    false
% 7.49/1.48  --res_prop_simpl_given                  true
% 7.49/1.48  --res_passive_queue_type                priority_queues
% 7.49/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.49/1.48  --res_passive_queues_freq               [15;5]
% 7.49/1.48  --res_forward_subs                      full
% 7.49/1.48  --res_backward_subs                     full
% 7.49/1.48  --res_forward_subs_resolution           true
% 7.49/1.48  --res_backward_subs_resolution          true
% 7.49/1.48  --res_orphan_elimination                true
% 7.49/1.48  --res_time_limit                        2.
% 7.49/1.48  --res_out_proof                         true
% 7.49/1.48  
% 7.49/1.48  ------ Superposition Options
% 7.49/1.48  
% 7.49/1.48  --superposition_flag                    true
% 7.49/1.48  --sup_passive_queue_type                priority_queues
% 7.49/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.49/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.49/1.48  --demod_completeness_check              fast
% 7.49/1.48  --demod_use_ground                      true
% 7.49/1.48  --sup_to_prop_solver                    passive
% 7.49/1.48  --sup_prop_simpl_new                    true
% 7.49/1.48  --sup_prop_simpl_given                  true
% 7.49/1.48  --sup_fun_splitting                     false
% 7.49/1.48  --sup_smt_interval                      50000
% 7.49/1.48  
% 7.49/1.48  ------ Superposition Simplification Setup
% 7.49/1.48  
% 7.49/1.48  --sup_indices_passive                   []
% 7.49/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.49/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.49/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.49/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.49/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.49/1.48  --sup_full_bw                           [BwDemod]
% 7.49/1.48  --sup_immed_triv                        [TrivRules]
% 7.49/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.49/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.49/1.48  --sup_immed_bw_main                     []
% 7.49/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.49/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.49/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.49/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.49/1.48  
% 7.49/1.48  ------ Combination Options
% 7.49/1.48  
% 7.49/1.48  --comb_res_mult                         3
% 7.49/1.48  --comb_sup_mult                         2
% 7.49/1.48  --comb_inst_mult                        10
% 7.49/1.48  
% 7.49/1.48  ------ Debug Options
% 7.49/1.48  
% 7.49/1.48  --dbg_backtrace                         false
% 7.49/1.48  --dbg_dump_prop_clauses                 false
% 7.49/1.48  --dbg_dump_prop_clauses_file            -
% 7.49/1.48  --dbg_out_stat                          false
% 7.49/1.48  
% 7.49/1.48  
% 7.49/1.48  
% 7.49/1.48  
% 7.49/1.48  ------ Proving...
% 7.49/1.48  
% 7.49/1.48  
% 7.49/1.48  % SZS status Theorem for theBenchmark.p
% 7.49/1.48  
% 7.49/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.49/1.48  
% 7.49/1.48  fof(f23,conjecture,(
% 7.49/1.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 7.49/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.48  
% 7.49/1.48  fof(f24,negated_conjecture,(
% 7.49/1.48    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 7.49/1.48    inference(negated_conjecture,[],[f23])).
% 7.49/1.48  
% 7.49/1.48  fof(f25,plain,(
% 7.49/1.48    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 7.49/1.48    inference(pure_predicate_removal,[],[f24])).
% 7.49/1.48  
% 7.49/1.48  fof(f57,plain,(
% 7.49/1.48    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 7.49/1.48    inference(ennf_transformation,[],[f25])).
% 7.49/1.48  
% 7.49/1.48  fof(f58,plain,(
% 7.49/1.48    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 7.49/1.48    inference(flattening,[],[f57])).
% 7.49/1.48  
% 7.49/1.48  fof(f64,plain,(
% 7.49/1.48    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(sK3))) )),
% 7.49/1.48    introduced(choice_axiom,[])).
% 7.49/1.48  
% 7.49/1.48  fof(f63,plain,(
% 7.49/1.48    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2))),
% 7.49/1.48    introduced(choice_axiom,[])).
% 7.49/1.48  
% 7.49/1.48  fof(f65,plain,(
% 7.49/1.48    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2)),
% 7.49/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f58,f64,f63])).
% 7.49/1.48  
% 7.49/1.48  fof(f100,plain,(
% 7.49/1.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 7.49/1.48    inference(cnf_transformation,[],[f65])).
% 7.49/1.48  
% 7.49/1.48  fof(f2,axiom,(
% 7.49/1.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 7.49/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.48  
% 7.49/1.48  fof(f28,plain,(
% 7.49/1.48    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 7.49/1.48    inference(ennf_transformation,[],[f2])).
% 7.49/1.48  
% 7.49/1.48  fof(f69,plain,(
% 7.49/1.48    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 7.49/1.48    inference(cnf_transformation,[],[f28])).
% 7.49/1.48  
% 7.49/1.48  fof(f4,axiom,(
% 7.49/1.48    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 7.49/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.48  
% 7.49/1.48  fof(f72,plain,(
% 7.49/1.48    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 7.49/1.48    inference(cnf_transformation,[],[f4])).
% 7.49/1.48  
% 7.49/1.48  fof(f98,plain,(
% 7.49/1.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 7.49/1.48    inference(cnf_transformation,[],[f65])).
% 7.49/1.48  
% 7.49/1.48  fof(f16,axiom,(
% 7.49/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 7.49/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.48  
% 7.49/1.48  fof(f48,plain,(
% 7.49/1.48    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.49/1.48    inference(ennf_transformation,[],[f16])).
% 7.49/1.48  
% 7.49/1.48  fof(f87,plain,(
% 7.49/1.48    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.49/1.48    inference(cnf_transformation,[],[f48])).
% 7.49/1.48  
% 7.49/1.48  fof(f101,plain,(
% 7.49/1.48    k2_relset_1(sK0,sK1,sK2) = sK1),
% 7.49/1.48    inference(cnf_transformation,[],[f65])).
% 7.49/1.48  
% 7.49/1.48  fof(f13,axiom,(
% 7.49/1.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 7.49/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.48  
% 7.49/1.48  fof(f43,plain,(
% 7.49/1.48    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.49/1.48    inference(ennf_transformation,[],[f13])).
% 7.49/1.48  
% 7.49/1.48  fof(f44,plain,(
% 7.49/1.48    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.49/1.48    inference(flattening,[],[f43])).
% 7.49/1.48  
% 7.49/1.48  fof(f82,plain,(
% 7.49/1.48    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.49/1.48    inference(cnf_transformation,[],[f44])).
% 7.49/1.48  
% 7.49/1.48  fof(f103,plain,(
% 7.49/1.48    v2_funct_1(sK2)),
% 7.49/1.48    inference(cnf_transformation,[],[f65])).
% 7.49/1.48  
% 7.49/1.48  fof(f97,plain,(
% 7.49/1.48    v1_funct_1(sK2)),
% 7.49/1.48    inference(cnf_transformation,[],[f65])).
% 7.49/1.48  
% 7.49/1.48  fof(f22,axiom,(
% 7.49/1.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 7.49/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.48  
% 7.49/1.48  fof(f26,plain,(
% 7.49/1.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_1(X0)))),
% 7.49/1.48    inference(pure_predicate_removal,[],[f22])).
% 7.49/1.48  
% 7.49/1.48  fof(f55,plain,(
% 7.49/1.48    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.49/1.48    inference(ennf_transformation,[],[f26])).
% 7.49/1.48  
% 7.49/1.48  fof(f56,plain,(
% 7.49/1.48    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.49/1.48    inference(flattening,[],[f55])).
% 7.49/1.48  
% 7.49/1.48  fof(f96,plain,(
% 7.49/1.48    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.49/1.48    inference(cnf_transformation,[],[f56])).
% 7.49/1.48  
% 7.49/1.48  fof(f10,axiom,(
% 7.49/1.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 7.49/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.48  
% 7.49/1.48  fof(f37,plain,(
% 7.49/1.48    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.49/1.48    inference(ennf_transformation,[],[f10])).
% 7.49/1.48  
% 7.49/1.48  fof(f38,plain,(
% 7.49/1.48    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.49/1.48    inference(flattening,[],[f37])).
% 7.49/1.48  
% 7.49/1.48  fof(f79,plain,(
% 7.49/1.48    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.49/1.48    inference(cnf_transformation,[],[f38])).
% 7.49/1.48  
% 7.49/1.48  fof(f78,plain,(
% 7.49/1.48    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.49/1.48    inference(cnf_transformation,[],[f38])).
% 7.49/1.48  
% 7.49/1.48  fof(f83,plain,(
% 7.49/1.48    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.49/1.48    inference(cnf_transformation,[],[f44])).
% 7.49/1.48  
% 7.49/1.48  fof(f7,axiom,(
% 7.49/1.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2))))),
% 7.49/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.48  
% 7.49/1.48  fof(f32,plain,(
% 7.49/1.48    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.49/1.48    inference(ennf_transformation,[],[f7])).
% 7.49/1.48  
% 7.49/1.48  fof(f75,plain,(
% 7.49/1.48    ( ! [X2,X0,X1] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.49/1.48    inference(cnf_transformation,[],[f32])).
% 7.49/1.48  
% 7.49/1.48  fof(f14,axiom,(
% 7.49/1.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 7.49/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.48  
% 7.49/1.48  fof(f45,plain,(
% 7.49/1.48    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.49/1.48    inference(ennf_transformation,[],[f14])).
% 7.49/1.48  
% 7.49/1.48  fof(f46,plain,(
% 7.49/1.48    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.49/1.48    inference(flattening,[],[f45])).
% 7.49/1.48  
% 7.49/1.48  fof(f85,plain,(
% 7.49/1.48    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.49/1.48    inference(cnf_transformation,[],[f46])).
% 7.49/1.48  
% 7.49/1.48  fof(f21,axiom,(
% 7.49/1.48    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 7.49/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.48  
% 7.49/1.48  fof(f94,plain,(
% 7.49/1.48    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 7.49/1.48    inference(cnf_transformation,[],[f21])).
% 7.49/1.48  
% 7.49/1.48  fof(f109,plain,(
% 7.49/1.48    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.49/1.48    inference(definition_unfolding,[],[f85,f94])).
% 7.49/1.48  
% 7.49/1.48  fof(f15,axiom,(
% 7.49/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.49/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.48  
% 7.49/1.48  fof(f27,plain,(
% 7.49/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 7.49/1.48    inference(pure_predicate_removal,[],[f15])).
% 7.49/1.48  
% 7.49/1.48  fof(f47,plain,(
% 7.49/1.48    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.49/1.48    inference(ennf_transformation,[],[f27])).
% 7.49/1.48  
% 7.49/1.48  fof(f86,plain,(
% 7.49/1.48    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.49/1.48    inference(cnf_transformation,[],[f47])).
% 7.49/1.48  
% 7.49/1.48  fof(f3,axiom,(
% 7.49/1.48    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 7.49/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.48  
% 7.49/1.48  fof(f29,plain,(
% 7.49/1.48    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.49/1.48    inference(ennf_transformation,[],[f3])).
% 7.49/1.48  
% 7.49/1.48  fof(f61,plain,(
% 7.49/1.48    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.49/1.48    inference(nnf_transformation,[],[f29])).
% 7.49/1.48  
% 7.49/1.48  fof(f70,plain,(
% 7.49/1.48    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.49/1.48    inference(cnf_transformation,[],[f61])).
% 7.49/1.48  
% 7.49/1.48  fof(f8,axiom,(
% 7.49/1.48    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 7.49/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.48  
% 7.49/1.48  fof(f33,plain,(
% 7.49/1.48    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.49/1.48    inference(ennf_transformation,[],[f8])).
% 7.49/1.48  
% 7.49/1.48  fof(f34,plain,(
% 7.49/1.48    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 7.49/1.48    inference(flattening,[],[f33])).
% 7.49/1.48  
% 7.49/1.48  fof(f76,plain,(
% 7.49/1.48    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 7.49/1.48    inference(cnf_transformation,[],[f34])).
% 7.49/1.48  
% 7.49/1.48  fof(f107,plain,(
% 7.49/1.48    ( ! [X0,X1] : (k5_relat_1(k6_partfun1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 7.49/1.48    inference(definition_unfolding,[],[f76,f94])).
% 7.49/1.48  
% 7.49/1.48  fof(f20,axiom,(
% 7.49/1.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 7.49/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.48  
% 7.49/1.48  fof(f53,plain,(
% 7.49/1.48    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 7.49/1.48    inference(ennf_transformation,[],[f20])).
% 7.49/1.48  
% 7.49/1.48  fof(f54,plain,(
% 7.49/1.48    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 7.49/1.48    inference(flattening,[],[f53])).
% 7.49/1.48  
% 7.49/1.48  fof(f93,plain,(
% 7.49/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 7.49/1.48    inference(cnf_transformation,[],[f54])).
% 7.49/1.48  
% 7.49/1.48  fof(f99,plain,(
% 7.49/1.48    v1_funct_1(sK3)),
% 7.49/1.48    inference(cnf_transformation,[],[f65])).
% 7.49/1.48  
% 7.49/1.48  fof(f17,axiom,(
% 7.49/1.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 7.49/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.48  
% 7.49/1.48  fof(f49,plain,(
% 7.49/1.48    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 7.49/1.48    inference(ennf_transformation,[],[f17])).
% 7.49/1.48  
% 7.49/1.48  fof(f50,plain,(
% 7.49/1.48    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.49/1.48    inference(flattening,[],[f49])).
% 7.49/1.48  
% 7.49/1.48  fof(f62,plain,(
% 7.49/1.48    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.49/1.48    inference(nnf_transformation,[],[f50])).
% 7.49/1.48  
% 7.49/1.48  fof(f88,plain,(
% 7.49/1.48    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.49/1.48    inference(cnf_transformation,[],[f62])).
% 7.49/1.48  
% 7.49/1.48  fof(f102,plain,(
% 7.49/1.48    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 7.49/1.48    inference(cnf_transformation,[],[f65])).
% 7.49/1.48  
% 7.49/1.48  fof(f18,axiom,(
% 7.49/1.48    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 7.49/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.48  
% 7.49/1.48  fof(f90,plain,(
% 7.49/1.48    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 7.49/1.48    inference(cnf_transformation,[],[f18])).
% 7.49/1.48  
% 7.49/1.48  fof(f111,plain,(
% 7.49/1.48    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 7.49/1.48    inference(definition_unfolding,[],[f90,f94])).
% 7.49/1.48  
% 7.49/1.48  fof(f19,axiom,(
% 7.49/1.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 7.49/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.48  
% 7.49/1.48  fof(f51,plain,(
% 7.49/1.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 7.49/1.48    inference(ennf_transformation,[],[f19])).
% 7.49/1.48  
% 7.49/1.48  fof(f52,plain,(
% 7.49/1.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 7.49/1.48    inference(flattening,[],[f51])).
% 7.49/1.48  
% 7.49/1.48  fof(f92,plain,(
% 7.49/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 7.49/1.48    inference(cnf_transformation,[],[f52])).
% 7.49/1.48  
% 7.49/1.48  fof(f9,axiom,(
% 7.49/1.48    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 7.49/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.48  
% 7.49/1.48  fof(f35,plain,(
% 7.49/1.48    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.49/1.48    inference(ennf_transformation,[],[f9])).
% 7.49/1.48  
% 7.49/1.48  fof(f36,plain,(
% 7.49/1.48    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 7.49/1.48    inference(flattening,[],[f35])).
% 7.49/1.48  
% 7.49/1.48  fof(f77,plain,(
% 7.49/1.48    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 7.49/1.48    inference(cnf_transformation,[],[f36])).
% 7.49/1.48  
% 7.49/1.48  fof(f108,plain,(
% 7.49/1.48    ( ! [X0,X1] : (k5_relat_1(X1,k6_partfun1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 7.49/1.48    inference(definition_unfolding,[],[f77,f94])).
% 7.49/1.48  
% 7.49/1.48  fof(f106,plain,(
% 7.49/1.48    k2_funct_1(sK2) != sK3),
% 7.49/1.48    inference(cnf_transformation,[],[f65])).
% 7.49/1.48  
% 7.49/1.48  cnf(c_36,negated_conjecture,
% 7.49/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 7.49/1.48      inference(cnf_transformation,[],[f100]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_1248,plain,
% 7.49/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 7.49/1.48      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_3,plain,
% 7.49/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.49/1.48      | ~ v1_relat_1(X1)
% 7.49/1.48      | v1_relat_1(X0) ),
% 7.49/1.48      inference(cnf_transformation,[],[f69]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_1264,plain,
% 7.49/1.48      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.49/1.48      | v1_relat_1(X1) != iProver_top
% 7.49/1.48      | v1_relat_1(X0) = iProver_top ),
% 7.49/1.48      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_3276,plain,
% 7.49/1.48      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 7.49/1.48      | v1_relat_1(sK3) = iProver_top ),
% 7.49/1.48      inference(superposition,[status(thm)],[c_1248,c_1264]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_43,plain,
% 7.49/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 7.49/1.48      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_1497,plain,
% 7.49/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.49/1.48      | v1_relat_1(X0)
% 7.49/1.48      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 7.49/1.48      inference(instantiation,[status(thm)],[c_3]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_1880,plain,
% 7.49/1.48      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 7.49/1.48      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
% 7.49/1.48      | v1_relat_1(sK3) ),
% 7.49/1.48      inference(instantiation,[status(thm)],[c_1497]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_1881,plain,
% 7.49/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 7.49/1.48      | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 7.49/1.48      | v1_relat_1(sK3) = iProver_top ),
% 7.49/1.48      inference(predicate_to_equality,[status(thm)],[c_1880]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_6,plain,
% 7.49/1.48      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 7.49/1.48      inference(cnf_transformation,[],[f72]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_1963,plain,
% 7.49/1.48      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
% 7.49/1.48      inference(instantiation,[status(thm)],[c_6]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_1964,plain,
% 7.49/1.48      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
% 7.49/1.48      inference(predicate_to_equality,[status(thm)],[c_1963]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_4079,plain,
% 7.49/1.48      ( v1_relat_1(sK3) = iProver_top ),
% 7.49/1.48      inference(global_propositional_subsumption,
% 7.49/1.48                [status(thm)],
% 7.49/1.48                [c_3276,c_43,c_1881,c_1964]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_38,negated_conjecture,
% 7.49/1.48      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 7.49/1.48      inference(cnf_transformation,[],[f98]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_1246,plain,
% 7.49/1.48      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.49/1.48      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_3277,plain,
% 7.49/1.48      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 7.49/1.48      | v1_relat_1(sK2) = iProver_top ),
% 7.49/1.48      inference(superposition,[status(thm)],[c_1246,c_1264]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_41,plain,
% 7.49/1.48      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.49/1.48      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_1883,plain,
% 7.49/1.48      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.49/1.48      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
% 7.49/1.48      | v1_relat_1(sK2) ),
% 7.49/1.48      inference(instantiation,[status(thm)],[c_1497]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_1884,plain,
% 7.49/1.48      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.49/1.48      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 7.49/1.48      | v1_relat_1(sK2) = iProver_top ),
% 7.49/1.48      inference(predicate_to_equality,[status(thm)],[c_1883]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_1966,plain,
% 7.49/1.48      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 7.49/1.48      inference(instantiation,[status(thm)],[c_6]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_1967,plain,
% 7.49/1.48      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 7.49/1.48      inference(predicate_to_equality,[status(thm)],[c_1966]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_4157,plain,
% 7.49/1.48      ( v1_relat_1(sK2) = iProver_top ),
% 7.49/1.48      inference(global_propositional_subsumption,
% 7.49/1.48                [status(thm)],
% 7.49/1.48                [c_3277,c_41,c_1884,c_1967]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_21,plain,
% 7.49/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.49/1.48      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 7.49/1.48      inference(cnf_transformation,[],[f87]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_1254,plain,
% 7.49/1.48      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 7.49/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.49/1.48      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_2053,plain,
% 7.49/1.48      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 7.49/1.48      inference(superposition,[status(thm)],[c_1246,c_1254]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_35,negated_conjecture,
% 7.49/1.48      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 7.49/1.48      inference(cnf_transformation,[],[f101]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_2055,plain,
% 7.49/1.48      ( k2_relat_1(sK2) = sK1 ),
% 7.49/1.48      inference(light_normalisation,[status(thm)],[c_2053,c_35]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_17,plain,
% 7.49/1.48      ( ~ v2_funct_1(X0)
% 7.49/1.48      | ~ v1_funct_1(X0)
% 7.49/1.48      | ~ v1_relat_1(X0)
% 7.49/1.48      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 7.49/1.48      inference(cnf_transformation,[],[f82]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_33,negated_conjecture,
% 7.49/1.48      ( v2_funct_1(sK2) ),
% 7.49/1.48      inference(cnf_transformation,[],[f103]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_464,plain,
% 7.49/1.48      ( ~ v1_funct_1(X0)
% 7.49/1.48      | ~ v1_relat_1(X0)
% 7.49/1.48      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 7.49/1.48      | sK2 != X0 ),
% 7.49/1.48      inference(resolution_lifted,[status(thm)],[c_17,c_33]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_465,plain,
% 7.49/1.48      ( ~ v1_funct_1(sK2)
% 7.49/1.48      | ~ v1_relat_1(sK2)
% 7.49/1.48      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 7.49/1.48      inference(unflattening,[status(thm)],[c_464]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_39,negated_conjecture,
% 7.49/1.48      ( v1_funct_1(sK2) ),
% 7.49/1.48      inference(cnf_transformation,[],[f97]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_467,plain,
% 7.49/1.48      ( ~ v1_relat_1(sK2)
% 7.49/1.48      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 7.49/1.48      inference(global_propositional_subsumption,
% 7.49/1.48                [status(thm)],
% 7.49/1.48                [c_465,c_39]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_1240,plain,
% 7.49/1.48      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 7.49/1.48      | v1_relat_1(sK2) != iProver_top ),
% 7.49/1.48      inference(predicate_to_equality,[status(thm)],[c_467]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_2064,plain,
% 7.49/1.48      ( k1_relat_1(k2_funct_1(sK2)) = sK1
% 7.49/1.48      | v1_relat_1(sK2) != iProver_top ),
% 7.49/1.48      inference(demodulation,[status(thm)],[c_2055,c_1240]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_2226,plain,
% 7.49/1.48      ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
% 7.49/1.48      inference(global_propositional_subsumption,
% 7.49/1.48                [status(thm)],
% 7.49/1.48                [c_2064,c_41,c_1884,c_1967]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_28,plain,
% 7.49/1.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 7.49/1.48      | ~ v1_funct_1(X0)
% 7.49/1.48      | ~ v1_relat_1(X0) ),
% 7.49/1.48      inference(cnf_transformation,[],[f96]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_1249,plain,
% 7.49/1.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 7.49/1.48      | v1_funct_1(X0) != iProver_top
% 7.49/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.49/1.48      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_2967,plain,
% 7.49/1.48      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2))))) = iProver_top
% 7.49/1.48      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 7.49/1.48      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 7.49/1.48      inference(superposition,[status(thm)],[c_2226,c_1249]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_40,plain,
% 7.49/1.48      ( v1_funct_1(sK2) = iProver_top ),
% 7.49/1.48      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_12,plain,
% 7.49/1.48      ( ~ v1_funct_1(X0)
% 7.49/1.48      | v1_funct_1(k2_funct_1(X0))
% 7.49/1.48      | ~ v1_relat_1(X0) ),
% 7.49/1.48      inference(cnf_transformation,[],[f79]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_1488,plain,
% 7.49/1.48      ( v1_funct_1(k2_funct_1(sK2))
% 7.49/1.48      | ~ v1_funct_1(sK2)
% 7.49/1.48      | ~ v1_relat_1(sK2) ),
% 7.49/1.48      inference(instantiation,[status(thm)],[c_12]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_1489,plain,
% 7.49/1.48      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 7.49/1.48      | v1_funct_1(sK2) != iProver_top
% 7.49/1.48      | v1_relat_1(sK2) != iProver_top ),
% 7.49/1.48      inference(predicate_to_equality,[status(thm)],[c_1488]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_13,plain,
% 7.49/1.48      ( ~ v1_funct_1(X0)
% 7.49/1.48      | ~ v1_relat_1(X0)
% 7.49/1.48      | v1_relat_1(k2_funct_1(X0)) ),
% 7.49/1.48      inference(cnf_transformation,[],[f78]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_1494,plain,
% 7.49/1.48      ( ~ v1_funct_1(sK2)
% 7.49/1.48      | v1_relat_1(k2_funct_1(sK2))
% 7.49/1.48      | ~ v1_relat_1(sK2) ),
% 7.49/1.48      inference(instantiation,[status(thm)],[c_13]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_1495,plain,
% 7.49/1.48      ( v1_funct_1(sK2) != iProver_top
% 7.49/1.48      | v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 7.49/1.48      | v1_relat_1(sK2) != iProver_top ),
% 7.49/1.48      inference(predicate_to_equality,[status(thm)],[c_1494]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_10148,plain,
% 7.49/1.48      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2))))) = iProver_top ),
% 7.49/1.48      inference(global_propositional_subsumption,
% 7.49/1.48                [status(thm)],
% 7.49/1.48                [c_2967,c_40,c_41,c_1489,c_1495,c_1884,c_1967]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_16,plain,
% 7.49/1.48      ( ~ v2_funct_1(X0)
% 7.49/1.48      | ~ v1_funct_1(X0)
% 7.49/1.48      | ~ v1_relat_1(X0)
% 7.49/1.48      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 7.49/1.48      inference(cnf_transformation,[],[f83]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_478,plain,
% 7.49/1.48      ( ~ v1_funct_1(X0)
% 7.49/1.48      | ~ v1_relat_1(X0)
% 7.49/1.48      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 7.49/1.48      | sK2 != X0 ),
% 7.49/1.48      inference(resolution_lifted,[status(thm)],[c_16,c_33]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_479,plain,
% 7.49/1.48      ( ~ v1_funct_1(sK2)
% 7.49/1.48      | ~ v1_relat_1(sK2)
% 7.49/1.48      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 7.49/1.48      inference(unflattening,[status(thm)],[c_478]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_481,plain,
% 7.49/1.48      ( ~ v1_relat_1(sK2)
% 7.49/1.48      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 7.49/1.48      inference(global_propositional_subsumption,
% 7.49/1.48                [status(thm)],
% 7.49/1.48                [c_479,c_39]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_1239,plain,
% 7.49/1.48      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 7.49/1.48      | v1_relat_1(sK2) != iProver_top ),
% 7.49/1.48      inference(predicate_to_equality,[status(thm)],[c_481]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_4166,plain,
% 7.49/1.48      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 7.49/1.48      inference(superposition,[status(thm)],[c_4157,c_1239]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_10152,plain,
% 7.49/1.48      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top ),
% 7.49/1.48      inference(light_normalisation,[status(thm)],[c_10148,c_4166]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_10155,plain,
% 7.49/1.48      ( v1_relat_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))) != iProver_top
% 7.49/1.48      | v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
% 7.49/1.48      inference(superposition,[status(thm)],[c_10152,c_1264]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_10202,plain,
% 7.49/1.48      ( v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
% 7.49/1.48      inference(global_propositional_subsumption,
% 7.49/1.48                [status(thm)],
% 7.49/1.48                [c_10155,c_40,c_41,c_1495,c_1884,c_1967]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_9,plain,
% 7.49/1.48      ( ~ v1_relat_1(X0)
% 7.49/1.48      | ~ v1_relat_1(X1)
% 7.49/1.48      | ~ v1_relat_1(X2)
% 7.49/1.48      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ),
% 7.49/1.48      inference(cnf_transformation,[],[f75]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_1260,plain,
% 7.49/1.48      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
% 7.49/1.48      | v1_relat_1(X0) != iProver_top
% 7.49/1.48      | v1_relat_1(X1) != iProver_top
% 7.49/1.48      | v1_relat_1(X2) != iProver_top ),
% 7.49/1.48      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_10211,plain,
% 7.49/1.48      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1)
% 7.49/1.48      | v1_relat_1(X0) != iProver_top
% 7.49/1.48      | v1_relat_1(X1) != iProver_top ),
% 7.49/1.48      inference(superposition,[status(thm)],[c_10202,c_1260]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_28727,plain,
% 7.49/1.48      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),X0)
% 7.49/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.49/1.48      inference(superposition,[status(thm)],[c_4157,c_10211]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_18,plain,
% 7.49/1.48      ( ~ v2_funct_1(X0)
% 7.49/1.48      | ~ v1_funct_1(X0)
% 7.49/1.48      | ~ v1_relat_1(X0)
% 7.49/1.48      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
% 7.49/1.48      inference(cnf_transformation,[],[f109]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_450,plain,
% 7.49/1.48      ( ~ v1_funct_1(X0)
% 7.49/1.48      | ~ v1_relat_1(X0)
% 7.49/1.48      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
% 7.49/1.48      | sK2 != X0 ),
% 7.49/1.48      inference(resolution_lifted,[status(thm)],[c_18,c_33]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_451,plain,
% 7.49/1.48      ( ~ v1_funct_1(sK2)
% 7.49/1.48      | ~ v1_relat_1(sK2)
% 7.49/1.48      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 7.49/1.48      inference(unflattening,[status(thm)],[c_450]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_453,plain,
% 7.49/1.48      ( ~ v1_relat_1(sK2)
% 7.49/1.48      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 7.49/1.48      inference(global_propositional_subsumption,
% 7.49/1.48                [status(thm)],
% 7.49/1.48                [c_451,c_39]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_1241,plain,
% 7.49/1.48      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
% 7.49/1.48      | v1_relat_1(sK2) != iProver_top ),
% 7.49/1.48      inference(predicate_to_equality,[status(thm)],[c_453]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_2063,plain,
% 7.49/1.48      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 7.49/1.48      | v1_relat_1(sK2) != iProver_top ),
% 7.49/1.48      inference(demodulation,[status(thm)],[c_2055,c_1241]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_2420,plain,
% 7.49/1.48      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
% 7.49/1.48      inference(global_propositional_subsumption,
% 7.49/1.48                [status(thm)],
% 7.49/1.48                [c_2063,c_41,c_1884,c_1967]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_28773,plain,
% 7.49/1.48      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k6_partfun1(sK1),X0)
% 7.49/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.49/1.48      inference(light_normalisation,[status(thm)],[c_28727,c_2420]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_29392,plain,
% 7.49/1.48      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
% 7.49/1.48      inference(superposition,[status(thm)],[c_4079,c_28773]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_20,plain,
% 7.49/1.48      ( v4_relat_1(X0,X1)
% 7.49/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.49/1.48      inference(cnf_transformation,[],[f86]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_5,plain,
% 7.49/1.48      ( ~ v4_relat_1(X0,X1)
% 7.49/1.48      | r1_tarski(k1_relat_1(X0),X1)
% 7.49/1.48      | ~ v1_relat_1(X0) ),
% 7.49/1.48      inference(cnf_transformation,[],[f70]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_398,plain,
% 7.49/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.49/1.48      | r1_tarski(k1_relat_1(X0),X1)
% 7.49/1.48      | ~ v1_relat_1(X0) ),
% 7.49/1.48      inference(resolution,[status(thm)],[c_20,c_5]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_1244,plain,
% 7.49/1.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.49/1.48      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 7.49/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.49/1.48      inference(predicate_to_equality,[status(thm)],[c_398]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_1979,plain,
% 7.49/1.48      ( r1_tarski(k1_relat_1(sK3),sK1) = iProver_top
% 7.49/1.48      | v1_relat_1(sK3) != iProver_top ),
% 7.49/1.48      inference(superposition,[status(thm)],[c_1248,c_1244]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_2378,plain,
% 7.49/1.48      ( r1_tarski(k1_relat_1(sK3),sK1) = iProver_top ),
% 7.49/1.48      inference(global_propositional_subsumption,
% 7.49/1.48                [status(thm)],
% 7.49/1.48                [c_1979,c_43,c_1881,c_1964]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_10,plain,
% 7.49/1.48      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 7.49/1.48      | ~ v1_relat_1(X0)
% 7.49/1.48      | k5_relat_1(k6_partfun1(X1),X0) = X0 ),
% 7.49/1.48      inference(cnf_transformation,[],[f107]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_1259,plain,
% 7.49/1.48      ( k5_relat_1(k6_partfun1(X0),X1) = X1
% 7.49/1.48      | r1_tarski(k1_relat_1(X1),X0) != iProver_top
% 7.49/1.48      | v1_relat_1(X1) != iProver_top ),
% 7.49/1.48      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_4042,plain,
% 7.49/1.48      ( k5_relat_1(k6_partfun1(sK1),sK3) = sK3
% 7.49/1.48      | v1_relat_1(sK3) != iProver_top ),
% 7.49/1.48      inference(superposition,[status(thm)],[c_2378,c_1259]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_7187,plain,
% 7.49/1.48      ( k5_relat_1(k6_partfun1(sK1),sK3) = sK3 ),
% 7.49/1.48      inference(global_propositional_subsumption,
% 7.49/1.48                [status(thm)],
% 7.49/1.48                [c_4042,c_43,c_1881,c_1964]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_27,plain,
% 7.49/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.49/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.49/1.48      | ~ v1_funct_1(X0)
% 7.49/1.48      | ~ v1_funct_1(X3)
% 7.49/1.48      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 7.49/1.48      inference(cnf_transformation,[],[f93]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_1250,plain,
% 7.49/1.48      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 7.49/1.48      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 7.49/1.48      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.49/1.48      | v1_funct_1(X5) != iProver_top
% 7.49/1.48      | v1_funct_1(X4) != iProver_top ),
% 7.49/1.48      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_4953,plain,
% 7.49/1.48      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 7.49/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.49/1.48      | v1_funct_1(X2) != iProver_top
% 7.49/1.48      | v1_funct_1(sK3) != iProver_top ),
% 7.49/1.48      inference(superposition,[status(thm)],[c_1248,c_1250]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_37,negated_conjecture,
% 7.49/1.48      ( v1_funct_1(sK3) ),
% 7.49/1.48      inference(cnf_transformation,[],[f99]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_42,plain,
% 7.49/1.48      ( v1_funct_1(sK3) = iProver_top ),
% 7.49/1.48      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_5162,plain,
% 7.49/1.48      ( v1_funct_1(X2) != iProver_top
% 7.49/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.49/1.48      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 7.49/1.48      inference(global_propositional_subsumption,
% 7.49/1.48                [status(thm)],
% 7.49/1.48                [c_4953,c_42]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_5163,plain,
% 7.49/1.48      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 7.49/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.49/1.48      | v1_funct_1(X2) != iProver_top ),
% 7.49/1.48      inference(renaming,[status(thm)],[c_5162]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_5175,plain,
% 7.49/1.48      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 7.49/1.48      | v1_funct_1(sK2) != iProver_top ),
% 7.49/1.48      inference(superposition,[status(thm)],[c_1246,c_5163]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_1632,plain,
% 7.49/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.49/1.48      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 7.49/1.48      | ~ v1_funct_1(X0)
% 7.49/1.48      | ~ v1_funct_1(sK3)
% 7.49/1.48      | k1_partfun1(X1,X2,X3,X4,X0,sK3) = k5_relat_1(X0,sK3) ),
% 7.49/1.48      inference(instantiation,[status(thm)],[c_27]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_1834,plain,
% 7.49/1.48      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.49/1.48      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 7.49/1.48      | ~ v1_funct_1(sK3)
% 7.49/1.48      | ~ v1_funct_1(sK2)
% 7.49/1.48      | k1_partfun1(X2,X3,X0,X1,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 7.49/1.48      inference(instantiation,[status(thm)],[c_1632]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_2023,plain,
% 7.49/1.48      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 7.49/1.48      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.49/1.48      | ~ v1_funct_1(sK3)
% 7.49/1.48      | ~ v1_funct_1(sK2)
% 7.49/1.48      | k1_partfun1(X0,X1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 7.49/1.48      inference(instantiation,[status(thm)],[c_1834]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_2398,plain,
% 7.49/1.48      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 7.49/1.48      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.49/1.48      | ~ v1_funct_1(sK3)
% 7.49/1.48      | ~ v1_funct_1(sK2)
% 7.49/1.48      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 7.49/1.48      inference(instantiation,[status(thm)],[c_2023]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_5395,plain,
% 7.49/1.48      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 7.49/1.48      inference(global_propositional_subsumption,
% 7.49/1.48                [status(thm)],
% 7.49/1.48                [c_5175,c_39,c_38,c_37,c_36,c_2398]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_23,plain,
% 7.49/1.48      ( ~ r2_relset_1(X0,X1,X2,X3)
% 7.49/1.48      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.49/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.49/1.48      | X3 = X2 ),
% 7.49/1.48      inference(cnf_transformation,[],[f88]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_34,negated_conjecture,
% 7.49/1.48      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 7.49/1.48      inference(cnf_transformation,[],[f102]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_419,plain,
% 7.49/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.49/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.49/1.48      | X3 = X0
% 7.49/1.48      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 7.49/1.48      | k6_partfun1(sK0) != X3
% 7.49/1.48      | sK0 != X2
% 7.49/1.48      | sK0 != X1 ),
% 7.49/1.48      inference(resolution_lifted,[status(thm)],[c_23,c_34]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_420,plain,
% 7.49/1.48      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.49/1.48      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.49/1.48      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.49/1.48      inference(unflattening,[status(thm)],[c_419]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_24,plain,
% 7.49/1.48      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 7.49/1.48      inference(cnf_transformation,[],[f111]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_60,plain,
% 7.49/1.48      ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 7.49/1.48      inference(instantiation,[status(thm)],[c_24]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_422,plain,
% 7.49/1.48      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.49/1.48      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.49/1.48      inference(global_propositional_subsumption,
% 7.49/1.48                [status(thm)],
% 7.49/1.48                [c_420,c_60]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_1243,plain,
% 7.49/1.48      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.49/1.48      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 7.49/1.48      inference(predicate_to_equality,[status(thm)],[c_422]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_5398,plain,
% 7.49/1.48      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 7.49/1.48      | m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 7.49/1.48      inference(demodulation,[status(thm)],[c_5395,c_1243]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_25,plain,
% 7.49/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.49/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.49/1.48      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.49/1.48      | ~ v1_funct_1(X0)
% 7.49/1.48      | ~ v1_funct_1(X3) ),
% 7.49/1.48      inference(cnf_transformation,[],[f92]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_1252,plain,
% 7.49/1.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.49/1.48      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 7.49/1.48      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 7.49/1.48      | v1_funct_1(X0) != iProver_top
% 7.49/1.48      | v1_funct_1(X3) != iProver_top ),
% 7.49/1.48      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_5400,plain,
% 7.49/1.48      ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 7.49/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 7.49/1.48      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.49/1.48      | v1_funct_1(sK3) != iProver_top
% 7.49/1.48      | v1_funct_1(sK2) != iProver_top ),
% 7.49/1.48      inference(superposition,[status(thm)],[c_5395,c_1252]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_8288,plain,
% 7.49/1.48      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 7.49/1.48      inference(global_propositional_subsumption,
% 7.49/1.48                [status(thm)],
% 7.49/1.48                [c_5398,c_40,c_41,c_42,c_43,c_5400]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_1980,plain,
% 7.49/1.48      ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top
% 7.49/1.48      | v1_relat_1(sK2) != iProver_top ),
% 7.49/1.48      inference(superposition,[status(thm)],[c_1246,c_1244]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_2384,plain,
% 7.49/1.48      ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
% 7.49/1.48      inference(global_propositional_subsumption,
% 7.49/1.48                [status(thm)],
% 7.49/1.48                [c_1980,c_41,c_1884,c_1967]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_11,plain,
% 7.49/1.48      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 7.49/1.48      | ~ v1_relat_1(X0)
% 7.49/1.48      | k5_relat_1(X0,k6_partfun1(X1)) = X0 ),
% 7.49/1.48      inference(cnf_transformation,[],[f108]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_1258,plain,
% 7.49/1.48      ( k5_relat_1(X0,k6_partfun1(X1)) = X0
% 7.49/1.48      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 7.49/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.49/1.48      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_4458,plain,
% 7.49/1.48      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0)) = k2_funct_1(sK2)
% 7.49/1.48      | r1_tarski(k1_relat_1(sK2),X0) != iProver_top
% 7.49/1.48      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 7.49/1.48      inference(superposition,[status(thm)],[c_4166,c_1258]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_12513,plain,
% 7.49/1.48      ( r1_tarski(k1_relat_1(sK2),X0) != iProver_top
% 7.49/1.48      | k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0)) = k2_funct_1(sK2) ),
% 7.49/1.48      inference(global_propositional_subsumption,
% 7.49/1.48                [status(thm)],
% 7.49/1.48                [c_4458,c_40,c_41,c_1495,c_1884,c_1967]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_12514,plain,
% 7.49/1.48      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0)) = k2_funct_1(sK2)
% 7.49/1.48      | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
% 7.49/1.48      inference(renaming,[status(thm)],[c_12513]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_12522,plain,
% 7.49/1.48      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k2_funct_1(sK2) ),
% 7.49/1.48      inference(superposition,[status(thm)],[c_2384,c_12514]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_29420,plain,
% 7.49/1.48      ( k2_funct_1(sK2) = sK3 ),
% 7.49/1.48      inference(light_normalisation,
% 7.49/1.48                [status(thm)],
% 7.49/1.48                [c_29392,c_7187,c_8288,c_12522]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(c_30,negated_conjecture,
% 7.49/1.48      ( k2_funct_1(sK2) != sK3 ),
% 7.49/1.48      inference(cnf_transformation,[],[f106]) ).
% 7.49/1.48  
% 7.49/1.48  cnf(contradiction,plain,
% 7.49/1.48      ( $false ),
% 7.49/1.48      inference(minisat,[status(thm)],[c_29420,c_30]) ).
% 7.49/1.48  
% 7.49/1.48  
% 7.49/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.49/1.48  
% 7.49/1.48  ------                               Statistics
% 7.49/1.48  
% 7.49/1.48  ------ General
% 7.49/1.48  
% 7.49/1.48  abstr_ref_over_cycles:                  0
% 7.49/1.48  abstr_ref_under_cycles:                 0
% 7.49/1.48  gc_basic_clause_elim:                   0
% 7.49/1.48  forced_gc_time:                         0
% 7.49/1.48  parsing_time:                           0.018
% 7.49/1.48  unif_index_cands_time:                  0.
% 7.49/1.48  unif_index_add_time:                    0.
% 7.49/1.48  orderings_time:                         0.
% 7.49/1.48  out_proof_time:                         0.017
% 7.49/1.48  total_time:                             0.925
% 7.49/1.48  num_of_symbols:                         54
% 7.49/1.48  num_of_terms:                           35884
% 7.49/1.48  
% 7.49/1.48  ------ Preprocessing
% 7.49/1.48  
% 7.49/1.48  num_of_splits:                          0
% 7.49/1.48  num_of_split_atoms:                     0
% 7.49/1.48  num_of_reused_defs:                     0
% 7.49/1.48  num_eq_ax_congr_red:                    5
% 7.49/1.48  num_of_sem_filtered_clauses:            1
% 7.49/1.48  num_of_subtypes:                        0
% 7.49/1.48  monotx_restored_types:                  0
% 7.49/1.48  sat_num_of_epr_types:                   0
% 7.49/1.48  sat_num_of_non_cyclic_types:            0
% 7.49/1.48  sat_guarded_non_collapsed_types:        0
% 7.49/1.48  num_pure_diseq_elim:                    0
% 7.49/1.48  simp_replaced_by:                       0
% 7.49/1.48  res_preprocessed:                       172
% 7.49/1.48  prep_upred:                             0
% 7.49/1.48  prep_unflattend:                        13
% 7.49/1.48  smt_new_axioms:                         0
% 7.49/1.48  pred_elim_cands:                        4
% 7.49/1.48  pred_elim:                              3
% 7.49/1.48  pred_elim_cl:                           5
% 7.49/1.48  pred_elim_cycles:                       5
% 7.49/1.48  merged_defs:                            0
% 7.49/1.48  merged_defs_ncl:                        0
% 7.49/1.48  bin_hyper_res:                          0
% 7.49/1.48  prep_cycles:                            4
% 7.49/1.48  pred_elim_time:                         0.003
% 7.49/1.48  splitting_time:                         0.
% 7.49/1.48  sem_filter_time:                        0.
% 7.49/1.48  monotx_time:                            0.
% 7.49/1.48  subtype_inf_time:                       0.
% 7.49/1.48  
% 7.49/1.48  ------ Problem properties
% 7.49/1.48  
% 7.49/1.48  clauses:                                33
% 7.49/1.48  conjectures:                            8
% 7.49/1.48  epr:                                    6
% 7.49/1.48  horn:                                   33
% 7.49/1.48  ground:                                 13
% 7.49/1.48  unary:                                  11
% 7.49/1.48  binary:                                 8
% 7.49/1.48  lits:                                   77
% 7.49/1.48  lits_eq:                                19
% 7.49/1.48  fd_pure:                                0
% 7.49/1.48  fd_pseudo:                              0
% 7.49/1.48  fd_cond:                                0
% 7.49/1.48  fd_pseudo_cond:                         1
% 7.49/1.48  ac_symbols:                             0
% 7.49/1.48  
% 7.49/1.48  ------ Propositional Solver
% 7.49/1.48  
% 7.49/1.48  prop_solver_calls:                      32
% 7.49/1.48  prop_fast_solver_calls:                 1541
% 7.49/1.48  smt_solver_calls:                       0
% 7.49/1.48  smt_fast_solver_calls:                  0
% 7.49/1.48  prop_num_of_clauses:                    14891
% 7.49/1.48  prop_preprocess_simplified:             29230
% 7.49/1.48  prop_fo_subsumed:                       114
% 7.49/1.48  prop_solver_time:                       0.
% 7.49/1.48  smt_solver_time:                        0.
% 7.49/1.48  smt_fast_solver_time:                   0.
% 7.49/1.48  prop_fast_solver_time:                  0.
% 7.49/1.48  prop_unsat_core_time:                   0.002
% 7.49/1.48  
% 7.49/1.48  ------ QBF
% 7.49/1.48  
% 7.49/1.48  qbf_q_res:                              0
% 7.49/1.48  qbf_num_tautologies:                    0
% 7.49/1.48  qbf_prep_cycles:                        0
% 7.49/1.48  
% 7.49/1.48  ------ BMC1
% 7.49/1.48  
% 7.49/1.48  bmc1_current_bound:                     -1
% 7.49/1.48  bmc1_last_solved_bound:                 -1
% 7.49/1.48  bmc1_unsat_core_size:                   -1
% 7.49/1.48  bmc1_unsat_core_parents_size:           -1
% 7.49/1.48  bmc1_merge_next_fun:                    0
% 7.49/1.48  bmc1_unsat_core_clauses_time:           0.
% 7.49/1.48  
% 7.49/1.48  ------ Instantiation
% 7.49/1.48  
% 7.49/1.48  inst_num_of_clauses:                    3886
% 7.49/1.48  inst_num_in_passive:                    2433
% 7.49/1.48  inst_num_in_active:                     1038
% 7.49/1.48  inst_num_in_unprocessed:                415
% 7.49/1.48  inst_num_of_loops:                      1210
% 7.49/1.48  inst_num_of_learning_restarts:          0
% 7.49/1.48  inst_num_moves_active_passive:          170
% 7.49/1.48  inst_lit_activity:                      0
% 7.49/1.48  inst_lit_activity_moves:                3
% 7.49/1.48  inst_num_tautologies:                   0
% 7.49/1.48  inst_num_prop_implied:                  0
% 7.49/1.48  inst_num_existing_simplified:           0
% 7.49/1.48  inst_num_eq_res_simplified:             0
% 7.49/1.48  inst_num_child_elim:                    0
% 7.49/1.48  inst_num_of_dismatching_blockings:      321
% 7.49/1.48  inst_num_of_non_proper_insts:           2754
% 7.49/1.48  inst_num_of_duplicates:                 0
% 7.49/1.48  inst_inst_num_from_inst_to_res:         0
% 7.49/1.48  inst_dismatching_checking_time:         0.
% 7.49/1.48  
% 7.49/1.48  ------ Resolution
% 7.49/1.48  
% 7.49/1.48  res_num_of_clauses:                     0
% 7.49/1.48  res_num_in_passive:                     0
% 7.49/1.48  res_num_in_active:                      0
% 7.49/1.48  res_num_of_loops:                       176
% 7.49/1.48  res_forward_subset_subsumed:            29
% 7.49/1.48  res_backward_subset_subsumed:           0
% 7.49/1.48  res_forward_subsumed:                   0
% 7.49/1.48  res_backward_subsumed:                  0
% 7.49/1.48  res_forward_subsumption_resolution:     0
% 7.49/1.48  res_backward_subsumption_resolution:    0
% 7.49/1.48  res_clause_to_clause_subsumption:       1381
% 7.49/1.48  res_orphan_elimination:                 0
% 7.49/1.48  res_tautology_del:                      27
% 7.49/1.48  res_num_eq_res_simplified:              0
% 7.49/1.48  res_num_sel_changes:                    0
% 7.49/1.48  res_moves_from_active_to_pass:          0
% 7.49/1.48  
% 7.49/1.48  ------ Superposition
% 7.49/1.48  
% 7.49/1.48  sup_time_total:                         0.
% 7.49/1.48  sup_time_generating:                    0.
% 7.49/1.48  sup_time_sim_full:                      0.
% 7.49/1.48  sup_time_sim_immed:                     0.
% 7.49/1.48  
% 7.49/1.48  sup_num_of_clauses:                     690
% 7.49/1.48  sup_num_in_active:                      233
% 7.49/1.48  sup_num_in_passive:                     457
% 7.49/1.48  sup_num_of_loops:                       241
% 7.49/1.48  sup_fw_superposition:                   537
% 7.49/1.48  sup_bw_superposition:                   205
% 7.49/1.48  sup_immediate_simplified:               127
% 7.49/1.48  sup_given_eliminated:                   1
% 7.49/1.48  comparisons_done:                       0
% 7.49/1.48  comparisons_avoided:                    0
% 7.49/1.48  
% 7.49/1.48  ------ Simplifications
% 7.49/1.48  
% 7.49/1.48  
% 7.49/1.48  sim_fw_subset_subsumed:                 23
% 7.49/1.48  sim_bw_subset_subsumed:                 8
% 7.49/1.48  sim_fw_subsumed:                        12
% 7.49/1.48  sim_bw_subsumed:                        2
% 7.49/1.48  sim_fw_subsumption_res:                 5
% 7.49/1.48  sim_bw_subsumption_res:                 0
% 7.49/1.48  sim_tautology_del:                      1
% 7.49/1.48  sim_eq_tautology_del:                   22
% 7.49/1.48  sim_eq_res_simp:                        0
% 7.49/1.48  sim_fw_demodulated:                     3
% 7.49/1.48  sim_bw_demodulated:                     13
% 7.49/1.48  sim_light_normalised:                   95
% 7.49/1.48  sim_joinable_taut:                      0
% 7.49/1.48  sim_joinable_simp:                      0
% 7.49/1.48  sim_ac_normalised:                      0
% 7.49/1.48  sim_smt_subsumption:                    0
% 7.49/1.48  
%------------------------------------------------------------------------------
