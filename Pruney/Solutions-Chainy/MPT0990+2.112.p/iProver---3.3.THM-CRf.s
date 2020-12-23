%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:20 EST 2020

% Result     : Theorem 3.22s
% Output     : CNFRefutation 3.22s
% Verified   : 
% Statistics : Number of formulae       :  203 ( 957 expanded)
%              Number of clauses        :  115 ( 308 expanded)
%              Number of leaves         :   23 ( 213 expanded)
%              Depth                    :   22
%              Number of atoms          :  599 (6284 expanded)
%              Number of equality atoms :  256 (2389 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   2 average)

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

fof(f23,plain,(
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
    inference(pure_predicate_removal,[],[f22])).

fof(f48,plain,(
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
    inference(ennf_transformation,[],[f23])).

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
    inference(flattening,[],[f48])).

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

fof(f56,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f49,f55,f54])).

fof(f89,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f56])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f87,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f56])).

fof(f86,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f71,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f90,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f56])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f39,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f38])).

fof(f76,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f20,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f85,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f20])).

fof(f100,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f76,f85])).

fof(f92,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f98,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_partfun1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f69,f85])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f47,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f46])).

fof(f84,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f88,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f42])).

fof(f53,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f91,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f56])).

fof(f18,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f83,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f45,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f44])).

fof(f82,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f70,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f99,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f70,f85])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f37,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f36])).

fof(f74,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f8,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f97,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f67,f85])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f50])).

fof(f59,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f95,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1104,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1118,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2878,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1104,c_1118])).

cnf(c_41,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_1435,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1998,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1435])).

cnf(c_1999,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1998])).

cnf(c_6,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2103,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2104,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2103])).

cnf(c_3087,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2878,c_41,c_1999,c_2104])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1102,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_2879,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1102,c_1118])).

cnf(c_39,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_1177,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
    | ~ v1_relat_1(X0)
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1231,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1177])).

cnf(c_1402,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1231])).

cnf(c_1403,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1402])).

cnf(c_1468,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1469,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1468])).

cnf(c_3093,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2879,c_39,c_1403,c_1469])).

cnf(c_37,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1101,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_15,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1110,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1114,plain,
    ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3863,plain,
    ( k5_relat_1(k2_funct_1(X0),k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(k2_funct_1(X0),X1),X2)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1110,c_1114])).

cnf(c_15517,plain,
    ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1101,c_3863])).

cnf(c_15897,plain,
    ( v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15517,c_39,c_1403,c_1469])).

cnf(c_15898,plain,
    ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_15897])).

cnf(c_15905,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3093,c_15898])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1109,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1912,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1102,c_1109])).

cnf(c_33,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1913,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_1912,c_33])).

cnf(c_18,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_31,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_416,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_31])).

cnf(c_417,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(unflattening,[status(thm)],[c_416])).

cnf(c_419,plain,
    ( ~ v1_relat_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_417,c_37])).

cnf(c_1097,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_419])).

cnf(c_1559,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1097,c_37,c_36,c_417,c_1402,c_1468])).

cnf(c_1981,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(demodulation,[status(thm)],[c_1913,c_1559])).

cnf(c_15912,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k6_partfun1(sK1),X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_15905,c_1981])).

cnf(c_16025,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
    inference(superposition,[status(thm)],[c_3087,c_15912])).

cnf(c_20,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_5,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_364,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_20,c_5])).

cnf(c_1100,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_364])).

cnf(c_1833,plain,
    ( r1_tarski(k1_relat_1(sK3),sK1) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1104,c_1100])).

cnf(c_2162,plain,
    ( r1_tarski(k1_relat_1(sK3),sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1833,c_41,c_1999,c_2104])).

cnf(c_12,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k6_partfun1(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1113,plain,
    ( k5_relat_1(k6_partfun1(X0),X1) = X1
    | r1_tarski(k1_relat_1(X1),X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2887,plain,
    ( k5_relat_1(k6_partfun1(sK1),sK3) = sK3
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2162,c_1113])).

cnf(c_3681,plain,
    ( k5_relat_1(k6_partfun1(sK1),sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2887,c_41,c_1999,c_2104])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1105,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3940,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1104,c_1105])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_40,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_3955,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3940,c_40])).

cnf(c_3956,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_3955])).

cnf(c_3964,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1102,c_3956])).

cnf(c_23,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_32,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_385,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_32])).

cnf(c_386,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_385])).

cnf(c_26,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_48,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_388,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_386,c_48])).

cnf(c_1099,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_388])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1169,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_1658,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1099,c_37,c_36,c_35,c_34,c_48,c_386,c_1169])).

cnf(c_3965,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3964,c_1658])).

cnf(c_38,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_4300,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3965,c_38])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1112,plain,
    ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2471,plain,
    ( k5_relat_1(k2_funct_1(X0),k6_partfun1(k2_relat_1(k2_funct_1(X0)))) = k2_funct_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1110,c_1112])).

cnf(c_4354,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(k2_relat_1(k2_funct_1(sK2)))) = k2_funct_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1101,c_2471])).

cnf(c_16,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_444,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_31])).

cnf(c_445,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_444])).

cnf(c_447,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_445,c_37])).

cnf(c_1095,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_447])).

cnf(c_3098,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_3093,c_1095])).

cnf(c_4355,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(k1_relat_1(sK2))) = k2_funct_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4354,c_3098])).

cnf(c_5132,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(k1_relat_1(sK2))) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4355,c_39,c_1403,c_1469])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1115,plain,
    ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3759,plain,
    ( k10_relat_1(sK2,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(sK2,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3093,c_1115])).

cnf(c_4343,plain,
    ( k10_relat_1(sK2,k1_relat_1(sK3)) = k1_relat_1(k5_relat_1(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_3087,c_3759])).

cnf(c_4344,plain,
    ( k10_relat_1(sK2,k1_relat_1(sK3)) = k1_relat_1(k6_partfun1(sK0)) ),
    inference(light_normalisation,[status(thm)],[c_4343,c_4300])).

cnf(c_11,plain,
    ( k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_4345,plain,
    ( k10_relat_1(sK2,k1_relat_1(sK3)) = sK0 ),
    inference(demodulation,[status(thm)],[c_4344,c_11])).

cnf(c_7,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1116,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4517,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4345,c_1116])).

cnf(c_4520,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4517,c_39,c_1403,c_1469])).

cnf(c_1834,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1102,c_1100])).

cnf(c_2196,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1834,c_39,c_1403,c_1469])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1120,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2689,plain,
    ( k1_relat_1(sK2) = sK0
    | r1_tarski(sK0,k1_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2196,c_1120])).

cnf(c_4526,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(superposition,[status(thm)],[c_4520,c_2689])).

cnf(c_5134,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k2_funct_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_5132,c_4526])).

cnf(c_16032,plain,
    ( k2_funct_1(sK2) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_16025,c_3681,c_4300,c_5134])).

cnf(c_28,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f95])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_16032,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.33  % Computer   : n003.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 11:56:27 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.22/1.09  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.09  
% 3.22/1.09  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.22/1.09  
% 3.22/1.09  ------  iProver source info
% 3.22/1.09  
% 3.22/1.09  git: date: 2020-06-30 10:37:57 +0100
% 3.22/1.09  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.22/1.09  git: non_committed_changes: false
% 3.22/1.09  git: last_make_outside_of_git: false
% 3.22/1.09  
% 3.22/1.09  ------ 
% 3.22/1.09  
% 3.22/1.09  ------ Input Options
% 3.22/1.09  
% 3.22/1.09  --out_options                           all
% 3.22/1.09  --tptp_safe_out                         true
% 3.22/1.09  --problem_path                          ""
% 3.22/1.09  --include_path                          ""
% 3.22/1.09  --clausifier                            res/vclausify_rel
% 3.22/1.09  --clausifier_options                    ""
% 3.22/1.09  --stdin                                 false
% 3.22/1.09  --stats_out                             all
% 3.22/1.09  
% 3.22/1.09  ------ General Options
% 3.22/1.09  
% 3.22/1.09  --fof                                   false
% 3.22/1.09  --time_out_real                         305.
% 3.22/1.09  --time_out_virtual                      -1.
% 3.22/1.09  --symbol_type_check                     false
% 3.22/1.09  --clausify_out                          false
% 3.22/1.09  --sig_cnt_out                           false
% 3.22/1.09  --trig_cnt_out                          false
% 3.22/1.09  --trig_cnt_out_tolerance                1.
% 3.22/1.09  --trig_cnt_out_sk_spl                   false
% 3.22/1.09  --abstr_cl_out                          false
% 3.22/1.09  
% 3.22/1.09  ------ Global Options
% 3.22/1.09  
% 3.22/1.09  --schedule                              default
% 3.22/1.09  --add_important_lit                     false
% 3.22/1.09  --prop_solver_per_cl                    1000
% 3.22/1.09  --min_unsat_core                        false
% 3.22/1.09  --soft_assumptions                      false
% 3.22/1.09  --soft_lemma_size                       3
% 3.22/1.09  --prop_impl_unit_size                   0
% 3.22/1.09  --prop_impl_unit                        []
% 3.22/1.09  --share_sel_clauses                     true
% 3.22/1.09  --reset_solvers                         false
% 3.22/1.09  --bc_imp_inh                            [conj_cone]
% 3.22/1.09  --conj_cone_tolerance                   3.
% 3.22/1.09  --extra_neg_conj                        none
% 3.22/1.09  --large_theory_mode                     true
% 3.22/1.09  --prolific_symb_bound                   200
% 3.22/1.09  --lt_threshold                          2000
% 3.22/1.09  --clause_weak_htbl                      true
% 3.22/1.09  --gc_record_bc_elim                     false
% 3.22/1.09  
% 3.22/1.09  ------ Preprocessing Options
% 3.22/1.09  
% 3.22/1.09  --preprocessing_flag                    true
% 3.22/1.09  --time_out_prep_mult                    0.1
% 3.22/1.09  --splitting_mode                        input
% 3.22/1.09  --splitting_grd                         true
% 3.22/1.09  --splitting_cvd                         false
% 3.22/1.09  --splitting_cvd_svl                     false
% 3.22/1.09  --splitting_nvd                         32
% 3.22/1.09  --sub_typing                            true
% 3.22/1.09  --prep_gs_sim                           true
% 3.22/1.09  --prep_unflatten                        true
% 3.22/1.09  --prep_res_sim                          true
% 3.22/1.09  --prep_upred                            true
% 3.22/1.09  --prep_sem_filter                       exhaustive
% 3.22/1.09  --prep_sem_filter_out                   false
% 3.22/1.09  --pred_elim                             true
% 3.22/1.09  --res_sim_input                         true
% 3.22/1.09  --eq_ax_congr_red                       true
% 3.22/1.09  --pure_diseq_elim                       true
% 3.22/1.09  --brand_transform                       false
% 3.22/1.09  --non_eq_to_eq                          false
% 3.22/1.09  --prep_def_merge                        true
% 3.22/1.09  --prep_def_merge_prop_impl              false
% 3.22/1.09  --prep_def_merge_mbd                    true
% 3.22/1.09  --prep_def_merge_tr_red                 false
% 3.22/1.09  --prep_def_merge_tr_cl                  false
% 3.22/1.09  --smt_preprocessing                     true
% 3.22/1.09  --smt_ac_axioms                         fast
% 3.22/1.09  --preprocessed_out                      false
% 3.22/1.09  --preprocessed_stats                    false
% 3.22/1.09  
% 3.22/1.09  ------ Abstraction refinement Options
% 3.22/1.09  
% 3.22/1.09  --abstr_ref                             []
% 3.22/1.09  --abstr_ref_prep                        false
% 3.22/1.09  --abstr_ref_until_sat                   false
% 3.22/1.09  --abstr_ref_sig_restrict                funpre
% 3.22/1.09  --abstr_ref_af_restrict_to_split_sk     false
% 3.22/1.09  --abstr_ref_under                       []
% 3.22/1.09  
% 3.22/1.09  ------ SAT Options
% 3.22/1.09  
% 3.22/1.09  --sat_mode                              false
% 3.22/1.09  --sat_fm_restart_options                ""
% 3.22/1.09  --sat_gr_def                            false
% 3.22/1.09  --sat_epr_types                         true
% 3.22/1.09  --sat_non_cyclic_types                  false
% 3.22/1.09  --sat_finite_models                     false
% 3.22/1.09  --sat_fm_lemmas                         false
% 3.22/1.09  --sat_fm_prep                           false
% 3.22/1.09  --sat_fm_uc_incr                        true
% 3.22/1.09  --sat_out_model                         small
% 3.22/1.09  --sat_out_clauses                       false
% 3.22/1.09  
% 3.22/1.09  ------ QBF Options
% 3.22/1.09  
% 3.22/1.09  --qbf_mode                              false
% 3.22/1.09  --qbf_elim_univ                         false
% 3.22/1.09  --qbf_dom_inst                          none
% 3.22/1.09  --qbf_dom_pre_inst                      false
% 3.22/1.09  --qbf_sk_in                             false
% 3.22/1.09  --qbf_pred_elim                         true
% 3.22/1.09  --qbf_split                             512
% 3.22/1.09  
% 3.22/1.09  ------ BMC1 Options
% 3.22/1.09  
% 3.22/1.09  --bmc1_incremental                      false
% 3.22/1.09  --bmc1_axioms                           reachable_all
% 3.22/1.09  --bmc1_min_bound                        0
% 3.22/1.09  --bmc1_max_bound                        -1
% 3.22/1.09  --bmc1_max_bound_default                -1
% 3.22/1.09  --bmc1_symbol_reachability              true
% 3.22/1.09  --bmc1_property_lemmas                  false
% 3.22/1.09  --bmc1_k_induction                      false
% 3.22/1.09  --bmc1_non_equiv_states                 false
% 3.22/1.09  --bmc1_deadlock                         false
% 3.22/1.09  --bmc1_ucm                              false
% 3.22/1.09  --bmc1_add_unsat_core                   none
% 3.22/1.09  --bmc1_unsat_core_children              false
% 3.22/1.09  --bmc1_unsat_core_extrapolate_axioms    false
% 3.22/1.09  --bmc1_out_stat                         full
% 3.22/1.09  --bmc1_ground_init                      false
% 3.22/1.09  --bmc1_pre_inst_next_state              false
% 3.22/1.09  --bmc1_pre_inst_state                   false
% 3.22/1.09  --bmc1_pre_inst_reach_state             false
% 3.22/1.09  --bmc1_out_unsat_core                   false
% 3.22/1.09  --bmc1_aig_witness_out                  false
% 3.22/1.09  --bmc1_verbose                          false
% 3.22/1.09  --bmc1_dump_clauses_tptp                false
% 3.22/1.09  --bmc1_dump_unsat_core_tptp             false
% 3.22/1.09  --bmc1_dump_file                        -
% 3.22/1.09  --bmc1_ucm_expand_uc_limit              128
% 3.22/1.09  --bmc1_ucm_n_expand_iterations          6
% 3.22/1.09  --bmc1_ucm_extend_mode                  1
% 3.22/1.09  --bmc1_ucm_init_mode                    2
% 3.22/1.09  --bmc1_ucm_cone_mode                    none
% 3.22/1.09  --bmc1_ucm_reduced_relation_type        0
% 3.22/1.09  --bmc1_ucm_relax_model                  4
% 3.22/1.09  --bmc1_ucm_full_tr_after_sat            true
% 3.22/1.09  --bmc1_ucm_expand_neg_assumptions       false
% 3.22/1.09  --bmc1_ucm_layered_model                none
% 3.22/1.09  --bmc1_ucm_max_lemma_size               10
% 3.22/1.09  
% 3.22/1.09  ------ AIG Options
% 3.22/1.09  
% 3.22/1.09  --aig_mode                              false
% 3.22/1.09  
% 3.22/1.09  ------ Instantiation Options
% 3.22/1.09  
% 3.22/1.09  --instantiation_flag                    true
% 3.22/1.09  --inst_sos_flag                         true
% 3.22/1.09  --inst_sos_phase                        true
% 3.22/1.09  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.22/1.09  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.22/1.09  --inst_lit_sel_side                     num_symb
% 3.22/1.09  --inst_solver_per_active                1400
% 3.22/1.09  --inst_solver_calls_frac                1.
% 3.22/1.09  --inst_passive_queue_type               priority_queues
% 3.22/1.09  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.22/1.09  --inst_passive_queues_freq              [25;2]
% 3.22/1.09  --inst_dismatching                      true
% 3.22/1.09  --inst_eager_unprocessed_to_passive     true
% 3.22/1.09  --inst_prop_sim_given                   true
% 3.22/1.09  --inst_prop_sim_new                     false
% 3.22/1.09  --inst_subs_new                         false
% 3.22/1.09  --inst_eq_res_simp                      false
% 3.22/1.09  --inst_subs_given                       false
% 3.22/1.09  --inst_orphan_elimination               true
% 3.22/1.09  --inst_learning_loop_flag               true
% 3.22/1.09  --inst_learning_start                   3000
% 3.22/1.09  --inst_learning_factor                  2
% 3.22/1.09  --inst_start_prop_sim_after_learn       3
% 3.22/1.09  --inst_sel_renew                        solver
% 3.22/1.09  --inst_lit_activity_flag                true
% 3.22/1.09  --inst_restr_to_given                   false
% 3.22/1.09  --inst_activity_threshold               500
% 3.22/1.09  --inst_out_proof                        true
% 3.22/1.09  
% 3.22/1.09  ------ Resolution Options
% 3.22/1.09  
% 3.22/1.09  --resolution_flag                       true
% 3.22/1.09  --res_lit_sel                           adaptive
% 3.22/1.09  --res_lit_sel_side                      none
% 3.22/1.09  --res_ordering                          kbo
% 3.22/1.09  --res_to_prop_solver                    active
% 3.22/1.09  --res_prop_simpl_new                    false
% 3.22/1.09  --res_prop_simpl_given                  true
% 3.22/1.09  --res_passive_queue_type                priority_queues
% 3.22/1.09  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.22/1.09  --res_passive_queues_freq               [15;5]
% 3.22/1.09  --res_forward_subs                      full
% 3.22/1.09  --res_backward_subs                     full
% 3.22/1.09  --res_forward_subs_resolution           true
% 3.22/1.09  --res_backward_subs_resolution          true
% 3.22/1.09  --res_orphan_elimination                true
% 3.22/1.09  --res_time_limit                        2.
% 3.22/1.09  --res_out_proof                         true
% 3.22/1.09  
% 3.22/1.09  ------ Superposition Options
% 3.22/1.09  
% 3.22/1.09  --superposition_flag                    true
% 3.22/1.09  --sup_passive_queue_type                priority_queues
% 3.22/1.09  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.22/1.09  --sup_passive_queues_freq               [8;1;4]
% 3.22/1.09  --demod_completeness_check              fast
% 3.22/1.09  --demod_use_ground                      true
% 3.22/1.09  --sup_to_prop_solver                    passive
% 3.22/1.09  --sup_prop_simpl_new                    true
% 3.22/1.09  --sup_prop_simpl_given                  true
% 3.22/1.09  --sup_fun_splitting                     true
% 3.22/1.09  --sup_smt_interval                      50000
% 3.22/1.09  
% 3.22/1.09  ------ Superposition Simplification Setup
% 3.22/1.09  
% 3.22/1.09  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.22/1.09  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.22/1.09  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.22/1.09  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.22/1.09  --sup_full_triv                         [TrivRules;PropSubs]
% 3.22/1.09  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.22/1.09  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.22/1.09  --sup_immed_triv                        [TrivRules]
% 3.22/1.09  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.22/1.09  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.22/1.09  --sup_immed_bw_main                     []
% 3.22/1.09  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.22/1.09  --sup_input_triv                        [Unflattening;TrivRules]
% 3.22/1.09  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.22/1.09  --sup_input_bw                          []
% 3.22/1.09  
% 3.22/1.09  ------ Combination Options
% 3.22/1.09  
% 3.22/1.09  --comb_res_mult                         3
% 3.22/1.09  --comb_sup_mult                         2
% 3.22/1.09  --comb_inst_mult                        10
% 3.22/1.09  
% 3.22/1.09  ------ Debug Options
% 3.22/1.09  
% 3.22/1.09  --dbg_backtrace                         false
% 3.22/1.09  --dbg_dump_prop_clauses                 false
% 3.22/1.09  --dbg_dump_prop_clauses_file            -
% 3.22/1.09  --dbg_out_stat                          false
% 3.22/1.09  ------ Parsing...
% 3.22/1.09  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.22/1.09  
% 3.22/1.09  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.22/1.09  
% 3.22/1.09  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.22/1.09  
% 3.22/1.09  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.22/1.09  ------ Proving...
% 3.22/1.09  ------ Problem Properties 
% 3.22/1.09  
% 3.22/1.09  
% 3.22/1.09  clauses                                 32
% 3.22/1.09  conjectures                             8
% 3.22/1.09  EPR                                     6
% 3.22/1.09  Horn                                    32
% 3.22/1.09  unary                                   13
% 3.22/1.09  binary                                  8
% 3.22/1.09  lits                                    69
% 3.22/1.09  lits eq                                 18
% 3.22/1.09  fd_pure                                 0
% 3.22/1.09  fd_pseudo                               0
% 3.22/1.09  fd_cond                                 0
% 3.22/1.09  fd_pseudo_cond                          1
% 3.22/1.09  AC symbols                              0
% 3.22/1.09  
% 3.22/1.09  ------ Schedule dynamic 5 is on 
% 3.22/1.09  
% 3.22/1.09  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.22/1.09  
% 3.22/1.09  
% 3.22/1.09  ------ 
% 3.22/1.09  Current options:
% 3.22/1.09  ------ 
% 3.22/1.09  
% 3.22/1.09  ------ Input Options
% 3.22/1.09  
% 3.22/1.09  --out_options                           all
% 3.22/1.09  --tptp_safe_out                         true
% 3.22/1.09  --problem_path                          ""
% 3.22/1.09  --include_path                          ""
% 3.22/1.09  --clausifier                            res/vclausify_rel
% 3.22/1.09  --clausifier_options                    ""
% 3.22/1.09  --stdin                                 false
% 3.22/1.09  --stats_out                             all
% 3.22/1.09  
% 3.22/1.09  ------ General Options
% 3.22/1.09  
% 3.22/1.09  --fof                                   false
% 3.22/1.09  --time_out_real                         305.
% 3.22/1.09  --time_out_virtual                      -1.
% 3.22/1.09  --symbol_type_check                     false
% 3.22/1.09  --clausify_out                          false
% 3.22/1.09  --sig_cnt_out                           false
% 3.22/1.09  --trig_cnt_out                          false
% 3.22/1.09  --trig_cnt_out_tolerance                1.
% 3.22/1.09  --trig_cnt_out_sk_spl                   false
% 3.22/1.09  --abstr_cl_out                          false
% 3.22/1.09  
% 3.22/1.09  ------ Global Options
% 3.22/1.09  
% 3.22/1.09  --schedule                              default
% 3.22/1.09  --add_important_lit                     false
% 3.22/1.09  --prop_solver_per_cl                    1000
% 3.22/1.09  --min_unsat_core                        false
% 3.22/1.09  --soft_assumptions                      false
% 3.22/1.09  --soft_lemma_size                       3
% 3.22/1.09  --prop_impl_unit_size                   0
% 3.22/1.09  --prop_impl_unit                        []
% 3.22/1.09  --share_sel_clauses                     true
% 3.22/1.09  --reset_solvers                         false
% 3.22/1.09  --bc_imp_inh                            [conj_cone]
% 3.22/1.09  --conj_cone_tolerance                   3.
% 3.22/1.09  --extra_neg_conj                        none
% 3.22/1.09  --large_theory_mode                     true
% 3.22/1.09  --prolific_symb_bound                   200
% 3.22/1.09  --lt_threshold                          2000
% 3.22/1.09  --clause_weak_htbl                      true
% 3.22/1.09  --gc_record_bc_elim                     false
% 3.22/1.09  
% 3.22/1.09  ------ Preprocessing Options
% 3.22/1.09  
% 3.22/1.09  --preprocessing_flag                    true
% 3.22/1.09  --time_out_prep_mult                    0.1
% 3.22/1.09  --splitting_mode                        input
% 3.22/1.09  --splitting_grd                         true
% 3.22/1.09  --splitting_cvd                         false
% 3.22/1.09  --splitting_cvd_svl                     false
% 3.22/1.09  --splitting_nvd                         32
% 3.22/1.09  --sub_typing                            true
% 3.22/1.09  --prep_gs_sim                           true
% 3.22/1.09  --prep_unflatten                        true
% 3.22/1.09  --prep_res_sim                          true
% 3.22/1.09  --prep_upred                            true
% 3.22/1.09  --prep_sem_filter                       exhaustive
% 3.22/1.09  --prep_sem_filter_out                   false
% 3.22/1.09  --pred_elim                             true
% 3.22/1.09  --res_sim_input                         true
% 3.22/1.09  --eq_ax_congr_red                       true
% 3.22/1.09  --pure_diseq_elim                       true
% 3.22/1.09  --brand_transform                       false
% 3.22/1.09  --non_eq_to_eq                          false
% 3.22/1.09  --prep_def_merge                        true
% 3.22/1.09  --prep_def_merge_prop_impl              false
% 3.22/1.09  --prep_def_merge_mbd                    true
% 3.22/1.09  --prep_def_merge_tr_red                 false
% 3.22/1.09  --prep_def_merge_tr_cl                  false
% 3.22/1.09  --smt_preprocessing                     true
% 3.22/1.09  --smt_ac_axioms                         fast
% 3.22/1.09  --preprocessed_out                      false
% 3.22/1.09  --preprocessed_stats                    false
% 3.22/1.09  
% 3.22/1.09  ------ Abstraction refinement Options
% 3.22/1.09  
% 3.22/1.09  --abstr_ref                             []
% 3.22/1.09  --abstr_ref_prep                        false
% 3.22/1.09  --abstr_ref_until_sat                   false
% 3.22/1.09  --abstr_ref_sig_restrict                funpre
% 3.22/1.09  --abstr_ref_af_restrict_to_split_sk     false
% 3.22/1.09  --abstr_ref_under                       []
% 3.22/1.09  
% 3.22/1.09  ------ SAT Options
% 3.22/1.09  
% 3.22/1.09  --sat_mode                              false
% 3.22/1.09  --sat_fm_restart_options                ""
% 3.22/1.09  --sat_gr_def                            false
% 3.22/1.09  --sat_epr_types                         true
% 3.22/1.09  --sat_non_cyclic_types                  false
% 3.22/1.09  --sat_finite_models                     false
% 3.22/1.09  --sat_fm_lemmas                         false
% 3.22/1.09  --sat_fm_prep                           false
% 3.22/1.09  --sat_fm_uc_incr                        true
% 3.22/1.09  --sat_out_model                         small
% 3.22/1.09  --sat_out_clauses                       false
% 3.22/1.09  
% 3.22/1.09  ------ QBF Options
% 3.22/1.09  
% 3.22/1.09  --qbf_mode                              false
% 3.22/1.09  --qbf_elim_univ                         false
% 3.22/1.09  --qbf_dom_inst                          none
% 3.22/1.09  --qbf_dom_pre_inst                      false
% 3.22/1.09  --qbf_sk_in                             false
% 3.22/1.09  --qbf_pred_elim                         true
% 3.22/1.09  --qbf_split                             512
% 3.22/1.09  
% 3.22/1.09  ------ BMC1 Options
% 3.22/1.09  
% 3.22/1.09  --bmc1_incremental                      false
% 3.22/1.09  --bmc1_axioms                           reachable_all
% 3.22/1.09  --bmc1_min_bound                        0
% 3.22/1.09  --bmc1_max_bound                        -1
% 3.22/1.09  --bmc1_max_bound_default                -1
% 3.22/1.09  --bmc1_symbol_reachability              true
% 3.22/1.09  --bmc1_property_lemmas                  false
% 3.22/1.09  --bmc1_k_induction                      false
% 3.22/1.09  --bmc1_non_equiv_states                 false
% 3.22/1.09  --bmc1_deadlock                         false
% 3.22/1.09  --bmc1_ucm                              false
% 3.22/1.09  --bmc1_add_unsat_core                   none
% 3.22/1.09  --bmc1_unsat_core_children              false
% 3.22/1.09  --bmc1_unsat_core_extrapolate_axioms    false
% 3.22/1.09  --bmc1_out_stat                         full
% 3.22/1.09  --bmc1_ground_init                      false
% 3.22/1.09  --bmc1_pre_inst_next_state              false
% 3.22/1.09  --bmc1_pre_inst_state                   false
% 3.22/1.09  --bmc1_pre_inst_reach_state             false
% 3.22/1.09  --bmc1_out_unsat_core                   false
% 3.22/1.09  --bmc1_aig_witness_out                  false
% 3.22/1.09  --bmc1_verbose                          false
% 3.22/1.09  --bmc1_dump_clauses_tptp                false
% 3.22/1.09  --bmc1_dump_unsat_core_tptp             false
% 3.22/1.09  --bmc1_dump_file                        -
% 3.22/1.09  --bmc1_ucm_expand_uc_limit              128
% 3.22/1.09  --bmc1_ucm_n_expand_iterations          6
% 3.22/1.09  --bmc1_ucm_extend_mode                  1
% 3.22/1.09  --bmc1_ucm_init_mode                    2
% 3.22/1.09  --bmc1_ucm_cone_mode                    none
% 3.22/1.09  --bmc1_ucm_reduced_relation_type        0
% 3.22/1.09  --bmc1_ucm_relax_model                  4
% 3.22/1.09  --bmc1_ucm_full_tr_after_sat            true
% 3.22/1.09  --bmc1_ucm_expand_neg_assumptions       false
% 3.22/1.09  --bmc1_ucm_layered_model                none
% 3.22/1.09  --bmc1_ucm_max_lemma_size               10
% 3.22/1.09  
% 3.22/1.09  ------ AIG Options
% 3.22/1.09  
% 3.22/1.09  --aig_mode                              false
% 3.22/1.09  
% 3.22/1.09  ------ Instantiation Options
% 3.22/1.09  
% 3.22/1.09  --instantiation_flag                    true
% 3.22/1.09  --inst_sos_flag                         true
% 3.22/1.09  --inst_sos_phase                        true
% 3.22/1.09  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.22/1.09  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.22/1.09  --inst_lit_sel_side                     none
% 3.22/1.09  --inst_solver_per_active                1400
% 3.22/1.09  --inst_solver_calls_frac                1.
% 3.22/1.09  --inst_passive_queue_type               priority_queues
% 3.22/1.09  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.22/1.09  --inst_passive_queues_freq              [25;2]
% 3.22/1.09  --inst_dismatching                      true
% 3.22/1.09  --inst_eager_unprocessed_to_passive     true
% 3.22/1.09  --inst_prop_sim_given                   true
% 3.22/1.09  --inst_prop_sim_new                     false
% 3.22/1.09  --inst_subs_new                         false
% 3.22/1.09  --inst_eq_res_simp                      false
% 3.22/1.09  --inst_subs_given                       false
% 3.22/1.09  --inst_orphan_elimination               true
% 3.22/1.09  --inst_learning_loop_flag               true
% 3.22/1.09  --inst_learning_start                   3000
% 3.22/1.09  --inst_learning_factor                  2
% 3.22/1.09  --inst_start_prop_sim_after_learn       3
% 3.22/1.09  --inst_sel_renew                        solver
% 3.22/1.09  --inst_lit_activity_flag                true
% 3.22/1.09  --inst_restr_to_given                   false
% 3.22/1.09  --inst_activity_threshold               500
% 3.22/1.09  --inst_out_proof                        true
% 3.22/1.09  
% 3.22/1.09  ------ Resolution Options
% 3.22/1.09  
% 3.22/1.09  --resolution_flag                       false
% 3.22/1.09  --res_lit_sel                           adaptive
% 3.22/1.09  --res_lit_sel_side                      none
% 3.22/1.09  --res_ordering                          kbo
% 3.22/1.09  --res_to_prop_solver                    active
% 3.22/1.09  --res_prop_simpl_new                    false
% 3.22/1.09  --res_prop_simpl_given                  true
% 3.22/1.09  --res_passive_queue_type                priority_queues
% 3.22/1.09  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.22/1.09  --res_passive_queues_freq               [15;5]
% 3.22/1.09  --res_forward_subs                      full
% 3.22/1.09  --res_backward_subs                     full
% 3.22/1.09  --res_forward_subs_resolution           true
% 3.22/1.09  --res_backward_subs_resolution          true
% 3.22/1.09  --res_orphan_elimination                true
% 3.22/1.09  --res_time_limit                        2.
% 3.22/1.09  --res_out_proof                         true
% 3.22/1.09  
% 3.22/1.09  ------ Superposition Options
% 3.22/1.09  
% 3.22/1.09  --superposition_flag                    true
% 3.22/1.09  --sup_passive_queue_type                priority_queues
% 3.22/1.09  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.22/1.09  --sup_passive_queues_freq               [8;1;4]
% 3.22/1.09  --demod_completeness_check              fast
% 3.22/1.09  --demod_use_ground                      true
% 3.22/1.09  --sup_to_prop_solver                    passive
% 3.22/1.09  --sup_prop_simpl_new                    true
% 3.22/1.09  --sup_prop_simpl_given                  true
% 3.22/1.09  --sup_fun_splitting                     true
% 3.22/1.09  --sup_smt_interval                      50000
% 3.22/1.09  
% 3.22/1.09  ------ Superposition Simplification Setup
% 3.22/1.09  
% 3.22/1.09  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.22/1.09  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.22/1.09  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.22/1.09  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.22/1.09  --sup_full_triv                         [TrivRules;PropSubs]
% 3.22/1.09  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.22/1.09  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.22/1.09  --sup_immed_triv                        [TrivRules]
% 3.22/1.09  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.22/1.09  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.22/1.09  --sup_immed_bw_main                     []
% 3.22/1.09  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.22/1.09  --sup_input_triv                        [Unflattening;TrivRules]
% 3.22/1.09  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.22/1.09  --sup_input_bw                          []
% 3.22/1.09  
% 3.22/1.09  ------ Combination Options
% 3.22/1.09  
% 3.22/1.09  --comb_res_mult                         3
% 3.22/1.09  --comb_sup_mult                         2
% 3.22/1.09  --comb_inst_mult                        10
% 3.22/1.09  
% 3.22/1.09  ------ Debug Options
% 3.22/1.09  
% 3.22/1.09  --dbg_backtrace                         false
% 3.22/1.09  --dbg_dump_prop_clauses                 false
% 3.22/1.09  --dbg_dump_prop_clauses_file            -
% 3.22/1.09  --dbg_out_stat                          false
% 3.22/1.09  
% 3.22/1.09  
% 3.22/1.09  
% 3.22/1.09  
% 3.22/1.09  ------ Proving...
% 3.22/1.09  
% 3.22/1.09  
% 3.22/1.09  % SZS status Theorem for theBenchmark.p
% 3.22/1.09  
% 3.22/1.09  % SZS output start CNFRefutation for theBenchmark.p
% 3.22/1.09  
% 3.22/1.09  fof(f21,conjecture,(
% 3.22/1.09    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 3.22/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/1.09  
% 3.22/1.09  fof(f22,negated_conjecture,(
% 3.22/1.09    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 3.22/1.09    inference(negated_conjecture,[],[f21])).
% 3.22/1.09  
% 3.22/1.09  fof(f23,plain,(
% 3.22/1.09    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 3.22/1.09    inference(pure_predicate_removal,[],[f22])).
% 3.22/1.09  
% 3.22/1.09  fof(f48,plain,(
% 3.22/1.09    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 3.22/1.09    inference(ennf_transformation,[],[f23])).
% 3.22/1.09  
% 3.22/1.09  fof(f49,plain,(
% 3.22/1.09    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 3.22/1.09    inference(flattening,[],[f48])).
% 3.22/1.09  
% 3.22/1.09  fof(f55,plain,(
% 3.22/1.09    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(sK3))) )),
% 3.22/1.09    introduced(choice_axiom,[])).
% 3.22/1.09  
% 3.22/1.09  fof(f54,plain,(
% 3.22/1.09    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2))),
% 3.22/1.09    introduced(choice_axiom,[])).
% 3.22/1.09  
% 3.22/1.09  fof(f56,plain,(
% 3.22/1.09    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2)),
% 3.22/1.09    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f49,f55,f54])).
% 3.22/1.09  
% 3.22/1.09  fof(f89,plain,(
% 3.22/1.09    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 3.22/1.09    inference(cnf_transformation,[],[f56])).
% 3.22/1.09  
% 3.22/1.09  fof(f2,axiom,(
% 3.22/1.09    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.22/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/1.09  
% 3.22/1.09  fof(f26,plain,(
% 3.22/1.09    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.22/1.09    inference(ennf_transformation,[],[f2])).
% 3.22/1.09  
% 3.22/1.09  fof(f60,plain,(
% 3.22/1.09    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.22/1.09    inference(cnf_transformation,[],[f26])).
% 3.22/1.09  
% 3.22/1.09  fof(f4,axiom,(
% 3.22/1.09    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.22/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/1.09  
% 3.22/1.09  fof(f63,plain,(
% 3.22/1.09    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.22/1.09    inference(cnf_transformation,[],[f4])).
% 3.22/1.09  
% 3.22/1.09  fof(f87,plain,(
% 3.22/1.09    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.22/1.09    inference(cnf_transformation,[],[f56])).
% 3.22/1.09  
% 3.22/1.09  fof(f86,plain,(
% 3.22/1.09    v1_funct_1(sK2)),
% 3.22/1.09    inference(cnf_transformation,[],[f56])).
% 3.22/1.09  
% 3.22/1.09  fof(f11,axiom,(
% 3.22/1.09    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.22/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/1.09  
% 3.22/1.09  fof(f34,plain,(
% 3.22/1.09    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.22/1.09    inference(ennf_transformation,[],[f11])).
% 3.22/1.09  
% 3.22/1.09  fof(f35,plain,(
% 3.22/1.09    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.22/1.09    inference(flattening,[],[f34])).
% 3.22/1.09  
% 3.22/1.09  fof(f71,plain,(
% 3.22/1.09    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.22/1.09    inference(cnf_transformation,[],[f35])).
% 3.22/1.09  
% 3.22/1.09  fof(f7,axiom,(
% 3.22/1.09    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2))))),
% 3.22/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/1.09  
% 3.22/1.09  fof(f30,plain,(
% 3.22/1.09    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.22/1.09    inference(ennf_transformation,[],[f7])).
% 3.22/1.09  
% 3.22/1.09  fof(f66,plain,(
% 3.22/1.09    ( ! [X2,X0,X1] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.22/1.09    inference(cnf_transformation,[],[f30])).
% 3.22/1.09  
% 3.22/1.09  fof(f15,axiom,(
% 3.22/1.09    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.22/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/1.09  
% 3.22/1.09  fof(f41,plain,(
% 3.22/1.09    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.22/1.09    inference(ennf_transformation,[],[f15])).
% 3.22/1.09  
% 3.22/1.09  fof(f78,plain,(
% 3.22/1.09    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.22/1.09    inference(cnf_transformation,[],[f41])).
% 3.22/1.09  
% 3.22/1.09  fof(f90,plain,(
% 3.22/1.09    k2_relset_1(sK0,sK1,sK2) = sK1),
% 3.22/1.09    inference(cnf_transformation,[],[f56])).
% 3.22/1.09  
% 3.22/1.09  fof(f13,axiom,(
% 3.22/1.09    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 3.22/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/1.09  
% 3.22/1.09  fof(f38,plain,(
% 3.22/1.09    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.22/1.09    inference(ennf_transformation,[],[f13])).
% 3.22/1.09  
% 3.22/1.09  fof(f39,plain,(
% 3.22/1.09    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.22/1.09    inference(flattening,[],[f38])).
% 3.22/1.09  
% 3.22/1.09  fof(f76,plain,(
% 3.22/1.09    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.22/1.09    inference(cnf_transformation,[],[f39])).
% 3.22/1.09  
% 3.22/1.09  fof(f20,axiom,(
% 3.22/1.09    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.22/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/1.09  
% 3.22/1.09  fof(f85,plain,(
% 3.22/1.09    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.22/1.09    inference(cnf_transformation,[],[f20])).
% 3.22/1.09  
% 3.22/1.09  fof(f100,plain,(
% 3.22/1.09    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.22/1.09    inference(definition_unfolding,[],[f76,f85])).
% 3.22/1.09  
% 3.22/1.09  fof(f92,plain,(
% 3.22/1.09    v2_funct_1(sK2)),
% 3.22/1.09    inference(cnf_transformation,[],[f56])).
% 3.22/1.09  
% 3.22/1.09  fof(f14,axiom,(
% 3.22/1.09    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.22/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/1.09  
% 3.22/1.09  fof(f25,plain,(
% 3.22/1.09    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.22/1.09    inference(pure_predicate_removal,[],[f14])).
% 3.22/1.09  
% 3.22/1.09  fof(f40,plain,(
% 3.22/1.09    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.22/1.09    inference(ennf_transformation,[],[f25])).
% 3.22/1.09  
% 3.22/1.09  fof(f77,plain,(
% 3.22/1.09    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.22/1.09    inference(cnf_transformation,[],[f40])).
% 3.22/1.09  
% 3.22/1.09  fof(f3,axiom,(
% 3.22/1.09    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.22/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/1.09  
% 3.22/1.09  fof(f27,plain,(
% 3.22/1.09    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.22/1.09    inference(ennf_transformation,[],[f3])).
% 3.22/1.09  
% 3.22/1.09  fof(f52,plain,(
% 3.22/1.09    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.22/1.09    inference(nnf_transformation,[],[f27])).
% 3.22/1.09  
% 3.22/1.09  fof(f61,plain,(
% 3.22/1.09    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.22/1.09    inference(cnf_transformation,[],[f52])).
% 3.22/1.09  
% 3.22/1.09  fof(f9,axiom,(
% 3.22/1.09    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 3.22/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/1.09  
% 3.22/1.09  fof(f31,plain,(
% 3.22/1.09    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.22/1.09    inference(ennf_transformation,[],[f9])).
% 3.22/1.09  
% 3.22/1.09  fof(f32,plain,(
% 3.22/1.09    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 3.22/1.09    inference(flattening,[],[f31])).
% 3.22/1.09  
% 3.22/1.09  fof(f69,plain,(
% 3.22/1.09    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.22/1.09    inference(cnf_transformation,[],[f32])).
% 3.22/1.09  
% 3.22/1.09  fof(f98,plain,(
% 3.22/1.09    ( ! [X0,X1] : (k5_relat_1(k6_partfun1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.22/1.09    inference(definition_unfolding,[],[f69,f85])).
% 3.22/1.09  
% 3.22/1.09  fof(f19,axiom,(
% 3.22/1.09    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.22/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/1.09  
% 3.22/1.09  fof(f46,plain,(
% 3.22/1.09    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.22/1.09    inference(ennf_transformation,[],[f19])).
% 3.22/1.09  
% 3.22/1.09  fof(f47,plain,(
% 3.22/1.09    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.22/1.09    inference(flattening,[],[f46])).
% 3.22/1.09  
% 3.22/1.09  fof(f84,plain,(
% 3.22/1.09    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.22/1.09    inference(cnf_transformation,[],[f47])).
% 3.22/1.09  
% 3.22/1.09  fof(f88,plain,(
% 3.22/1.09    v1_funct_1(sK3)),
% 3.22/1.09    inference(cnf_transformation,[],[f56])).
% 3.22/1.09  
% 3.22/1.09  fof(f16,axiom,(
% 3.22/1.09    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.22/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/1.09  
% 3.22/1.09  fof(f42,plain,(
% 3.22/1.09    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.22/1.09    inference(ennf_transformation,[],[f16])).
% 3.22/1.09  
% 3.22/1.09  fof(f43,plain,(
% 3.22/1.09    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.22/1.09    inference(flattening,[],[f42])).
% 3.22/1.09  
% 3.22/1.09  fof(f53,plain,(
% 3.22/1.09    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.22/1.09    inference(nnf_transformation,[],[f43])).
% 3.22/1.09  
% 3.22/1.09  fof(f79,plain,(
% 3.22/1.09    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.22/1.09    inference(cnf_transformation,[],[f53])).
% 3.22/1.09  
% 3.22/1.09  fof(f91,plain,(
% 3.22/1.09    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 3.22/1.09    inference(cnf_transformation,[],[f56])).
% 3.22/1.09  
% 3.22/1.09  fof(f18,axiom,(
% 3.22/1.09    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 3.22/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/1.09  
% 3.22/1.09  fof(f24,plain,(
% 3.22/1.09    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.22/1.09    inference(pure_predicate_removal,[],[f18])).
% 3.22/1.09  
% 3.22/1.09  fof(f83,plain,(
% 3.22/1.09    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.22/1.09    inference(cnf_transformation,[],[f24])).
% 3.22/1.09  
% 3.22/1.09  fof(f17,axiom,(
% 3.22/1.09    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 3.22/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/1.09  
% 3.22/1.09  fof(f44,plain,(
% 3.22/1.09    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.22/1.09    inference(ennf_transformation,[],[f17])).
% 3.22/1.09  
% 3.22/1.09  fof(f45,plain,(
% 3.22/1.09    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.22/1.09    inference(flattening,[],[f44])).
% 3.22/1.09  
% 3.22/1.09  fof(f82,plain,(
% 3.22/1.09    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.22/1.09    inference(cnf_transformation,[],[f45])).
% 3.22/1.09  
% 3.22/1.09  fof(f10,axiom,(
% 3.22/1.09    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 3.22/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/1.09  
% 3.22/1.09  fof(f33,plain,(
% 3.22/1.09    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 3.22/1.09    inference(ennf_transformation,[],[f10])).
% 3.22/1.09  
% 3.22/1.09  fof(f70,plain,(
% 3.22/1.09    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 3.22/1.09    inference(cnf_transformation,[],[f33])).
% 3.22/1.09  
% 3.22/1.09  fof(f99,plain,(
% 3.22/1.09    ( ! [X0] : (k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 3.22/1.09    inference(definition_unfolding,[],[f70,f85])).
% 3.22/1.09  
% 3.22/1.09  fof(f12,axiom,(
% 3.22/1.09    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 3.22/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/1.09  
% 3.22/1.09  fof(f36,plain,(
% 3.22/1.09    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.22/1.09    inference(ennf_transformation,[],[f12])).
% 3.22/1.09  
% 3.22/1.09  fof(f37,plain,(
% 3.22/1.09    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.22/1.09    inference(flattening,[],[f36])).
% 3.22/1.09  
% 3.22/1.09  fof(f74,plain,(
% 3.22/1.09    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.22/1.09    inference(cnf_transformation,[],[f37])).
% 3.22/1.09  
% 3.22/1.09  fof(f6,axiom,(
% 3.22/1.09    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 3.22/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/1.09  
% 3.22/1.09  fof(f29,plain,(
% 3.22/1.09    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.22/1.09    inference(ennf_transformation,[],[f6])).
% 3.22/1.09  
% 3.22/1.09  fof(f65,plain,(
% 3.22/1.09    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.22/1.09    inference(cnf_transformation,[],[f29])).
% 3.22/1.09  
% 3.22/1.09  fof(f8,axiom,(
% 3.22/1.09    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.22/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/1.09  
% 3.22/1.09  fof(f67,plain,(
% 3.22/1.09    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 3.22/1.09    inference(cnf_transformation,[],[f8])).
% 3.22/1.09  
% 3.22/1.09  fof(f97,plain,(
% 3.22/1.09    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 3.22/1.09    inference(definition_unfolding,[],[f67,f85])).
% 3.22/1.09  
% 3.22/1.09  fof(f5,axiom,(
% 3.22/1.09    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 3.22/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/1.09  
% 3.22/1.09  fof(f28,plain,(
% 3.22/1.09    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.22/1.09    inference(ennf_transformation,[],[f5])).
% 3.22/1.09  
% 3.22/1.09  fof(f64,plain,(
% 3.22/1.09    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.22/1.09    inference(cnf_transformation,[],[f28])).
% 3.22/1.09  
% 3.22/1.09  fof(f1,axiom,(
% 3.22/1.09    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.22/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/1.09  
% 3.22/1.09  fof(f50,plain,(
% 3.22/1.09    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.22/1.09    inference(nnf_transformation,[],[f1])).
% 3.22/1.09  
% 3.22/1.09  fof(f51,plain,(
% 3.22/1.09    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.22/1.09    inference(flattening,[],[f50])).
% 3.22/1.09  
% 3.22/1.09  fof(f59,plain,(
% 3.22/1.09    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.22/1.09    inference(cnf_transformation,[],[f51])).
% 3.22/1.09  
% 3.22/1.09  fof(f95,plain,(
% 3.22/1.09    k2_funct_1(sK2) != sK3),
% 3.22/1.09    inference(cnf_transformation,[],[f56])).
% 3.22/1.09  
% 3.22/1.09  cnf(c_34,negated_conjecture,
% 3.22/1.09      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 3.22/1.09      inference(cnf_transformation,[],[f89]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_1104,plain,
% 3.22/1.09      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.22/1.09      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_3,plain,
% 3.22/1.09      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.22/1.09      | ~ v1_relat_1(X1)
% 3.22/1.09      | v1_relat_1(X0) ),
% 3.22/1.09      inference(cnf_transformation,[],[f60]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_1118,plain,
% 3.22/1.09      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.22/1.09      | v1_relat_1(X1) != iProver_top
% 3.22/1.09      | v1_relat_1(X0) = iProver_top ),
% 3.22/1.09      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_2878,plain,
% 3.22/1.09      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 3.22/1.09      | v1_relat_1(sK3) = iProver_top ),
% 3.22/1.09      inference(superposition,[status(thm)],[c_1104,c_1118]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_41,plain,
% 3.22/1.09      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.22/1.09      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_1435,plain,
% 3.22/1.09      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.22/1.09      | v1_relat_1(X0)
% 3.22/1.09      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 3.22/1.09      inference(instantiation,[status(thm)],[c_3]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_1998,plain,
% 3.22/1.09      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.22/1.09      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
% 3.22/1.09      | v1_relat_1(sK3) ),
% 3.22/1.09      inference(instantiation,[status(thm)],[c_1435]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_1999,plain,
% 3.22/1.09      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.22/1.09      | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 3.22/1.09      | v1_relat_1(sK3) = iProver_top ),
% 3.22/1.09      inference(predicate_to_equality,[status(thm)],[c_1998]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_6,plain,
% 3.22/1.09      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.22/1.09      inference(cnf_transformation,[],[f63]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_2103,plain,
% 3.22/1.09      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
% 3.22/1.09      inference(instantiation,[status(thm)],[c_6]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_2104,plain,
% 3.22/1.09      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
% 3.22/1.09      inference(predicate_to_equality,[status(thm)],[c_2103]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_3087,plain,
% 3.22/1.09      ( v1_relat_1(sK3) = iProver_top ),
% 3.22/1.09      inference(global_propositional_subsumption,
% 3.22/1.09                [status(thm)],
% 3.22/1.09                [c_2878,c_41,c_1999,c_2104]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_36,negated_conjecture,
% 3.22/1.09      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.22/1.09      inference(cnf_transformation,[],[f87]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_1102,plain,
% 3.22/1.09      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.22/1.09      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_2879,plain,
% 3.22/1.09      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 3.22/1.09      | v1_relat_1(sK2) = iProver_top ),
% 3.22/1.09      inference(superposition,[status(thm)],[c_1102,c_1118]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_39,plain,
% 3.22/1.09      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.22/1.09      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_1177,plain,
% 3.22/1.09      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
% 3.22/1.09      | ~ v1_relat_1(X0)
% 3.22/1.09      | v1_relat_1(sK2) ),
% 3.22/1.09      inference(instantiation,[status(thm)],[c_3]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_1231,plain,
% 3.22/1.09      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.22/1.09      | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
% 3.22/1.09      | v1_relat_1(sK2) ),
% 3.22/1.09      inference(instantiation,[status(thm)],[c_1177]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_1402,plain,
% 3.22/1.09      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.22/1.09      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
% 3.22/1.09      | v1_relat_1(sK2) ),
% 3.22/1.09      inference(instantiation,[status(thm)],[c_1231]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_1403,plain,
% 3.22/1.09      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.22/1.09      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 3.22/1.09      | v1_relat_1(sK2) = iProver_top ),
% 3.22/1.09      inference(predicate_to_equality,[status(thm)],[c_1402]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_1468,plain,
% 3.22/1.09      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 3.22/1.09      inference(instantiation,[status(thm)],[c_6]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_1469,plain,
% 3.22/1.09      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 3.22/1.09      inference(predicate_to_equality,[status(thm)],[c_1468]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_3093,plain,
% 3.22/1.09      ( v1_relat_1(sK2) = iProver_top ),
% 3.22/1.09      inference(global_propositional_subsumption,
% 3.22/1.09                [status(thm)],
% 3.22/1.09                [c_2879,c_39,c_1403,c_1469]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_37,negated_conjecture,
% 3.22/1.09      ( v1_funct_1(sK2) ),
% 3.22/1.09      inference(cnf_transformation,[],[f86]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_1101,plain,
% 3.22/1.09      ( v1_funct_1(sK2) = iProver_top ),
% 3.22/1.09      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_15,plain,
% 3.22/1.09      ( ~ v1_funct_1(X0)
% 3.22/1.09      | ~ v1_relat_1(X0)
% 3.22/1.09      | v1_relat_1(k2_funct_1(X0)) ),
% 3.22/1.09      inference(cnf_transformation,[],[f71]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_1110,plain,
% 3.22/1.09      ( v1_funct_1(X0) != iProver_top
% 3.22/1.09      | v1_relat_1(X0) != iProver_top
% 3.22/1.09      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 3.22/1.09      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_9,plain,
% 3.22/1.09      ( ~ v1_relat_1(X0)
% 3.22/1.09      | ~ v1_relat_1(X1)
% 3.22/1.09      | ~ v1_relat_1(X2)
% 3.22/1.09      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ),
% 3.22/1.09      inference(cnf_transformation,[],[f66]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_1114,plain,
% 3.22/1.09      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
% 3.22/1.09      | v1_relat_1(X0) != iProver_top
% 3.22/1.09      | v1_relat_1(X1) != iProver_top
% 3.22/1.09      | v1_relat_1(X2) != iProver_top ),
% 3.22/1.09      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_3863,plain,
% 3.22/1.09      ( k5_relat_1(k2_funct_1(X0),k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(k2_funct_1(X0),X1),X2)
% 3.22/1.09      | v1_funct_1(X0) != iProver_top
% 3.22/1.09      | v1_relat_1(X0) != iProver_top
% 3.22/1.09      | v1_relat_1(X1) != iProver_top
% 3.22/1.09      | v1_relat_1(X2) != iProver_top ),
% 3.22/1.09      inference(superposition,[status(thm)],[c_1110,c_1114]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_15517,plain,
% 3.22/1.09      ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1))
% 3.22/1.09      | v1_relat_1(X0) != iProver_top
% 3.22/1.09      | v1_relat_1(X1) != iProver_top
% 3.22/1.09      | v1_relat_1(sK2) != iProver_top ),
% 3.22/1.09      inference(superposition,[status(thm)],[c_1101,c_3863]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_15897,plain,
% 3.22/1.09      ( v1_relat_1(X1) != iProver_top
% 3.22/1.09      | v1_relat_1(X0) != iProver_top
% 3.22/1.09      | k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1)) ),
% 3.22/1.09      inference(global_propositional_subsumption,
% 3.22/1.09                [status(thm)],
% 3.22/1.09                [c_15517,c_39,c_1403,c_1469]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_15898,plain,
% 3.22/1.09      ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1))
% 3.22/1.09      | v1_relat_1(X0) != iProver_top
% 3.22/1.09      | v1_relat_1(X1) != iProver_top ),
% 3.22/1.09      inference(renaming,[status(thm)],[c_15897]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_15905,plain,
% 3.22/1.09      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),X0)
% 3.22/1.09      | v1_relat_1(X0) != iProver_top ),
% 3.22/1.09      inference(superposition,[status(thm)],[c_3093,c_15898]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_21,plain,
% 3.22/1.09      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.22/1.09      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.22/1.09      inference(cnf_transformation,[],[f78]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_1109,plain,
% 3.22/1.09      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.22/1.09      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.22/1.09      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_1912,plain,
% 3.22/1.09      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 3.22/1.09      inference(superposition,[status(thm)],[c_1102,c_1109]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_33,negated_conjecture,
% 3.22/1.09      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 3.22/1.09      inference(cnf_transformation,[],[f90]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_1913,plain,
% 3.22/1.09      ( k2_relat_1(sK2) = sK1 ),
% 3.22/1.09      inference(light_normalisation,[status(thm)],[c_1912,c_33]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_18,plain,
% 3.22/1.09      ( ~ v2_funct_1(X0)
% 3.22/1.09      | ~ v1_funct_1(X0)
% 3.22/1.09      | ~ v1_relat_1(X0)
% 3.22/1.09      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
% 3.22/1.09      inference(cnf_transformation,[],[f100]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_31,negated_conjecture,
% 3.22/1.09      ( v2_funct_1(sK2) ),
% 3.22/1.09      inference(cnf_transformation,[],[f92]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_416,plain,
% 3.22/1.09      ( ~ v1_funct_1(X0)
% 3.22/1.09      | ~ v1_relat_1(X0)
% 3.22/1.09      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
% 3.22/1.09      | sK2 != X0 ),
% 3.22/1.09      inference(resolution_lifted,[status(thm)],[c_18,c_31]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_417,plain,
% 3.22/1.09      ( ~ v1_funct_1(sK2)
% 3.22/1.09      | ~ v1_relat_1(sK2)
% 3.22/1.09      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 3.22/1.09      inference(unflattening,[status(thm)],[c_416]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_419,plain,
% 3.22/1.09      ( ~ v1_relat_1(sK2)
% 3.22/1.09      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 3.22/1.09      inference(global_propositional_subsumption,
% 3.22/1.09                [status(thm)],
% 3.22/1.09                [c_417,c_37]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_1097,plain,
% 3.22/1.09      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
% 3.22/1.09      | v1_relat_1(sK2) != iProver_top ),
% 3.22/1.09      inference(predicate_to_equality,[status(thm)],[c_419]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_1559,plain,
% 3.22/1.09      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 3.22/1.09      inference(global_propositional_subsumption,
% 3.22/1.09                [status(thm)],
% 3.22/1.09                [c_1097,c_37,c_36,c_417,c_1402,c_1468]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_1981,plain,
% 3.22/1.09      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
% 3.22/1.09      inference(demodulation,[status(thm)],[c_1913,c_1559]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_15912,plain,
% 3.22/1.09      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k6_partfun1(sK1),X0)
% 3.22/1.09      | v1_relat_1(X0) != iProver_top ),
% 3.22/1.09      inference(light_normalisation,[status(thm)],[c_15905,c_1981]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_16025,plain,
% 3.22/1.09      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
% 3.22/1.09      inference(superposition,[status(thm)],[c_3087,c_15912]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_20,plain,
% 3.22/1.09      ( v4_relat_1(X0,X1)
% 3.22/1.09      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.22/1.09      inference(cnf_transformation,[],[f77]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_5,plain,
% 3.22/1.09      ( ~ v4_relat_1(X0,X1)
% 3.22/1.09      | r1_tarski(k1_relat_1(X0),X1)
% 3.22/1.09      | ~ v1_relat_1(X0) ),
% 3.22/1.09      inference(cnf_transformation,[],[f61]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_364,plain,
% 3.22/1.09      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.22/1.09      | r1_tarski(k1_relat_1(X0),X1)
% 3.22/1.09      | ~ v1_relat_1(X0) ),
% 3.22/1.09      inference(resolution,[status(thm)],[c_20,c_5]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_1100,plain,
% 3.22/1.09      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.22/1.09      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 3.22/1.09      | v1_relat_1(X0) != iProver_top ),
% 3.22/1.09      inference(predicate_to_equality,[status(thm)],[c_364]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_1833,plain,
% 3.22/1.09      ( r1_tarski(k1_relat_1(sK3),sK1) = iProver_top
% 3.22/1.09      | v1_relat_1(sK3) != iProver_top ),
% 3.22/1.09      inference(superposition,[status(thm)],[c_1104,c_1100]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_2162,plain,
% 3.22/1.09      ( r1_tarski(k1_relat_1(sK3),sK1) = iProver_top ),
% 3.22/1.09      inference(global_propositional_subsumption,
% 3.22/1.09                [status(thm)],
% 3.22/1.09                [c_1833,c_41,c_1999,c_2104]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_12,plain,
% 3.22/1.09      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 3.22/1.09      | ~ v1_relat_1(X0)
% 3.22/1.09      | k5_relat_1(k6_partfun1(X1),X0) = X0 ),
% 3.22/1.09      inference(cnf_transformation,[],[f98]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_1113,plain,
% 3.22/1.09      ( k5_relat_1(k6_partfun1(X0),X1) = X1
% 3.22/1.09      | r1_tarski(k1_relat_1(X1),X0) != iProver_top
% 3.22/1.09      | v1_relat_1(X1) != iProver_top ),
% 3.22/1.09      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_2887,plain,
% 3.22/1.09      ( k5_relat_1(k6_partfun1(sK1),sK3) = sK3
% 3.22/1.09      | v1_relat_1(sK3) != iProver_top ),
% 3.22/1.09      inference(superposition,[status(thm)],[c_2162,c_1113]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_3681,plain,
% 3.22/1.09      ( k5_relat_1(k6_partfun1(sK1),sK3) = sK3 ),
% 3.22/1.09      inference(global_propositional_subsumption,
% 3.22/1.09                [status(thm)],
% 3.22/1.09                [c_2887,c_41,c_1999,c_2104]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_27,plain,
% 3.22/1.09      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.22/1.09      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.22/1.09      | ~ v1_funct_1(X0)
% 3.22/1.09      | ~ v1_funct_1(X3)
% 3.22/1.09      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.22/1.09      inference(cnf_transformation,[],[f84]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_1105,plain,
% 3.22/1.09      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 3.22/1.09      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 3.22/1.09      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.22/1.09      | v1_funct_1(X5) != iProver_top
% 3.22/1.09      | v1_funct_1(X4) != iProver_top ),
% 3.22/1.09      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_3940,plain,
% 3.22/1.09      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 3.22/1.09      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.22/1.09      | v1_funct_1(X2) != iProver_top
% 3.22/1.09      | v1_funct_1(sK3) != iProver_top ),
% 3.22/1.09      inference(superposition,[status(thm)],[c_1104,c_1105]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_35,negated_conjecture,
% 3.22/1.09      ( v1_funct_1(sK3) ),
% 3.22/1.09      inference(cnf_transformation,[],[f88]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_40,plain,
% 3.22/1.09      ( v1_funct_1(sK3) = iProver_top ),
% 3.22/1.09      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_3955,plain,
% 3.22/1.09      ( v1_funct_1(X2) != iProver_top
% 3.22/1.09      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.22/1.09      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 3.22/1.09      inference(global_propositional_subsumption,
% 3.22/1.09                [status(thm)],
% 3.22/1.09                [c_3940,c_40]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_3956,plain,
% 3.22/1.09      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 3.22/1.09      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.22/1.09      | v1_funct_1(X2) != iProver_top ),
% 3.22/1.09      inference(renaming,[status(thm)],[c_3955]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_3964,plain,
% 3.22/1.09      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 3.22/1.09      | v1_funct_1(sK2) != iProver_top ),
% 3.22/1.09      inference(superposition,[status(thm)],[c_1102,c_3956]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_23,plain,
% 3.22/1.09      ( ~ r2_relset_1(X0,X1,X2,X3)
% 3.22/1.09      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.22/1.09      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.22/1.09      | X3 = X2 ),
% 3.22/1.09      inference(cnf_transformation,[],[f79]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_32,negated_conjecture,
% 3.22/1.09      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 3.22/1.09      inference(cnf_transformation,[],[f91]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_385,plain,
% 3.22/1.09      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.22/1.09      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.22/1.09      | X3 = X0
% 3.22/1.09      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 3.22/1.09      | k6_partfun1(sK0) != X3
% 3.22/1.09      | sK0 != X2
% 3.22/1.09      | sK0 != X1 ),
% 3.22/1.09      inference(resolution_lifted,[status(thm)],[c_23,c_32]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_386,plain,
% 3.22/1.09      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.22/1.09      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.22/1.09      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.22/1.09      inference(unflattening,[status(thm)],[c_385]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_26,plain,
% 3.22/1.09      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.22/1.09      inference(cnf_transformation,[],[f83]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_48,plain,
% 3.22/1.09      ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.22/1.09      inference(instantiation,[status(thm)],[c_26]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_388,plain,
% 3.22/1.09      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.22/1.09      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.22/1.09      inference(global_propositional_subsumption,
% 3.22/1.09                [status(thm)],
% 3.22/1.09                [c_386,c_48]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_1099,plain,
% 3.22/1.09      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.22/1.09      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.22/1.09      inference(predicate_to_equality,[status(thm)],[c_388]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_24,plain,
% 3.22/1.09      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.22/1.09      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.22/1.09      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.22/1.09      | ~ v1_funct_1(X0)
% 3.22/1.09      | ~ v1_funct_1(X3) ),
% 3.22/1.09      inference(cnf_transformation,[],[f82]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_1169,plain,
% 3.22/1.09      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.22/1.09      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.22/1.09      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.22/1.09      | ~ v1_funct_1(sK3)
% 3.22/1.09      | ~ v1_funct_1(sK2) ),
% 3.22/1.09      inference(instantiation,[status(thm)],[c_24]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_1658,plain,
% 3.22/1.09      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.22/1.09      inference(global_propositional_subsumption,
% 3.22/1.09                [status(thm)],
% 3.22/1.09                [c_1099,c_37,c_36,c_35,c_34,c_48,c_386,c_1169]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_3965,plain,
% 3.22/1.09      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 3.22/1.09      | v1_funct_1(sK2) != iProver_top ),
% 3.22/1.09      inference(light_normalisation,[status(thm)],[c_3964,c_1658]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_38,plain,
% 3.22/1.09      ( v1_funct_1(sK2) = iProver_top ),
% 3.22/1.09      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_4300,plain,
% 3.22/1.09      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 3.22/1.09      inference(global_propositional_subsumption,
% 3.22/1.09                [status(thm)],
% 3.22/1.09                [c_3965,c_38]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_13,plain,
% 3.22/1.09      ( ~ v1_relat_1(X0)
% 3.22/1.09      | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ),
% 3.22/1.09      inference(cnf_transformation,[],[f99]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_1112,plain,
% 3.22/1.09      ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
% 3.22/1.09      | v1_relat_1(X0) != iProver_top ),
% 3.22/1.09      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_2471,plain,
% 3.22/1.09      ( k5_relat_1(k2_funct_1(X0),k6_partfun1(k2_relat_1(k2_funct_1(X0)))) = k2_funct_1(X0)
% 3.22/1.09      | v1_funct_1(X0) != iProver_top
% 3.22/1.09      | v1_relat_1(X0) != iProver_top ),
% 3.22/1.09      inference(superposition,[status(thm)],[c_1110,c_1112]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_4354,plain,
% 3.22/1.09      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(k2_relat_1(k2_funct_1(sK2)))) = k2_funct_1(sK2)
% 3.22/1.09      | v1_relat_1(sK2) != iProver_top ),
% 3.22/1.09      inference(superposition,[status(thm)],[c_1101,c_2471]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_16,plain,
% 3.22/1.09      ( ~ v2_funct_1(X0)
% 3.22/1.09      | ~ v1_funct_1(X0)
% 3.22/1.09      | ~ v1_relat_1(X0)
% 3.22/1.09      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 3.22/1.09      inference(cnf_transformation,[],[f74]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_444,plain,
% 3.22/1.09      ( ~ v1_funct_1(X0)
% 3.22/1.09      | ~ v1_relat_1(X0)
% 3.22/1.09      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 3.22/1.09      | sK2 != X0 ),
% 3.22/1.09      inference(resolution_lifted,[status(thm)],[c_16,c_31]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_445,plain,
% 3.22/1.09      ( ~ v1_funct_1(sK2)
% 3.22/1.09      | ~ v1_relat_1(sK2)
% 3.22/1.09      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.22/1.09      inference(unflattening,[status(thm)],[c_444]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_447,plain,
% 3.22/1.09      ( ~ v1_relat_1(sK2)
% 3.22/1.09      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.22/1.09      inference(global_propositional_subsumption,
% 3.22/1.09                [status(thm)],
% 3.22/1.09                [c_445,c_37]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_1095,plain,
% 3.22/1.09      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 3.22/1.09      | v1_relat_1(sK2) != iProver_top ),
% 3.22/1.09      inference(predicate_to_equality,[status(thm)],[c_447]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_3098,plain,
% 3.22/1.09      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.22/1.09      inference(superposition,[status(thm)],[c_3093,c_1095]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_4355,plain,
% 3.22/1.09      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(k1_relat_1(sK2))) = k2_funct_1(sK2)
% 3.22/1.09      | v1_relat_1(sK2) != iProver_top ),
% 3.22/1.09      inference(light_normalisation,[status(thm)],[c_4354,c_3098]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_5132,plain,
% 3.22/1.09      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(k1_relat_1(sK2))) = k2_funct_1(sK2) ),
% 3.22/1.09      inference(global_propositional_subsumption,
% 3.22/1.09                [status(thm)],
% 3.22/1.09                [c_4355,c_39,c_1403,c_1469]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_8,plain,
% 3.22/1.09      ( ~ v1_relat_1(X0)
% 3.22/1.09      | ~ v1_relat_1(X1)
% 3.22/1.09      | k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) ),
% 3.22/1.09      inference(cnf_transformation,[],[f65]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_1115,plain,
% 3.22/1.09      ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
% 3.22/1.09      | v1_relat_1(X0) != iProver_top
% 3.22/1.09      | v1_relat_1(X1) != iProver_top ),
% 3.22/1.09      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_3759,plain,
% 3.22/1.09      ( k10_relat_1(sK2,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(sK2,X0))
% 3.22/1.09      | v1_relat_1(X0) != iProver_top ),
% 3.22/1.09      inference(superposition,[status(thm)],[c_3093,c_1115]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_4343,plain,
% 3.22/1.09      ( k10_relat_1(sK2,k1_relat_1(sK3)) = k1_relat_1(k5_relat_1(sK2,sK3)) ),
% 3.22/1.09      inference(superposition,[status(thm)],[c_3087,c_3759]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_4344,plain,
% 3.22/1.09      ( k10_relat_1(sK2,k1_relat_1(sK3)) = k1_relat_1(k6_partfun1(sK0)) ),
% 3.22/1.09      inference(light_normalisation,[status(thm)],[c_4343,c_4300]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_11,plain,
% 3.22/1.09      ( k1_relat_1(k6_partfun1(X0)) = X0 ),
% 3.22/1.09      inference(cnf_transformation,[],[f97]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_4345,plain,
% 3.22/1.09      ( k10_relat_1(sK2,k1_relat_1(sK3)) = sK0 ),
% 3.22/1.09      inference(demodulation,[status(thm)],[c_4344,c_11]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_7,plain,
% 3.22/1.09      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 3.22/1.09      inference(cnf_transformation,[],[f64]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_1116,plain,
% 3.22/1.09      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) = iProver_top
% 3.22/1.09      | v1_relat_1(X0) != iProver_top ),
% 3.22/1.09      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_4517,plain,
% 3.22/1.09      ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top
% 3.22/1.09      | v1_relat_1(sK2) != iProver_top ),
% 3.22/1.09      inference(superposition,[status(thm)],[c_4345,c_1116]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_4520,plain,
% 3.22/1.09      ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top ),
% 3.22/1.09      inference(global_propositional_subsumption,
% 3.22/1.09                [status(thm)],
% 3.22/1.09                [c_4517,c_39,c_1403,c_1469]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_1834,plain,
% 3.22/1.09      ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top
% 3.22/1.09      | v1_relat_1(sK2) != iProver_top ),
% 3.22/1.09      inference(superposition,[status(thm)],[c_1102,c_1100]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_2196,plain,
% 3.22/1.09      ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
% 3.22/1.09      inference(global_propositional_subsumption,
% 3.22/1.09                [status(thm)],
% 3.22/1.09                [c_1834,c_39,c_1403,c_1469]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_0,plain,
% 3.22/1.09      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.22/1.09      inference(cnf_transformation,[],[f59]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_1120,plain,
% 3.22/1.09      ( X0 = X1
% 3.22/1.09      | r1_tarski(X0,X1) != iProver_top
% 3.22/1.09      | r1_tarski(X1,X0) != iProver_top ),
% 3.22/1.09      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_2689,plain,
% 3.22/1.09      ( k1_relat_1(sK2) = sK0
% 3.22/1.09      | r1_tarski(sK0,k1_relat_1(sK2)) != iProver_top ),
% 3.22/1.09      inference(superposition,[status(thm)],[c_2196,c_1120]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_4526,plain,
% 3.22/1.09      ( k1_relat_1(sK2) = sK0 ),
% 3.22/1.09      inference(superposition,[status(thm)],[c_4520,c_2689]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_5134,plain,
% 3.22/1.09      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k2_funct_1(sK2) ),
% 3.22/1.09      inference(light_normalisation,[status(thm)],[c_5132,c_4526]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_16032,plain,
% 3.22/1.09      ( k2_funct_1(sK2) = sK3 ),
% 3.22/1.09      inference(light_normalisation,
% 3.22/1.09                [status(thm)],
% 3.22/1.09                [c_16025,c_3681,c_4300,c_5134]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(c_28,negated_conjecture,
% 3.22/1.09      ( k2_funct_1(sK2) != sK3 ),
% 3.22/1.09      inference(cnf_transformation,[],[f95]) ).
% 3.22/1.09  
% 3.22/1.09  cnf(contradiction,plain,
% 3.22/1.09      ( $false ),
% 3.22/1.09      inference(minisat,[status(thm)],[c_16032,c_28]) ).
% 3.22/1.09  
% 3.22/1.09  
% 3.22/1.09  % SZS output end CNFRefutation for theBenchmark.p
% 3.22/1.09  
% 3.22/1.09  ------                               Statistics
% 3.22/1.09  
% 3.22/1.09  ------ General
% 3.22/1.09  
% 3.22/1.09  abstr_ref_over_cycles:                  0
% 3.22/1.09  abstr_ref_under_cycles:                 0
% 3.22/1.09  gc_basic_clause_elim:                   0
% 3.22/1.09  forced_gc_time:                         0
% 3.22/1.09  parsing_time:                           0.041
% 3.22/1.09  unif_index_cands_time:                  0.
% 3.22/1.09  unif_index_add_time:                    0.
% 3.22/1.09  orderings_time:                         0.
% 3.22/1.09  out_proof_time:                         0.013
% 3.22/1.09  total_time:                             0.574
% 3.22/1.09  num_of_symbols:                         53
% 3.22/1.09  num_of_terms:                           23744
% 3.22/1.09  
% 3.22/1.09  ------ Preprocessing
% 3.22/1.09  
% 3.22/1.09  num_of_splits:                          0
% 3.22/1.09  num_of_split_atoms:                     0
% 3.22/1.09  num_of_reused_defs:                     0
% 3.22/1.09  num_eq_ax_congr_red:                    5
% 3.22/1.09  num_of_sem_filtered_clauses:            1
% 3.22/1.09  num_of_subtypes:                        0
% 3.22/1.09  monotx_restored_types:                  0
% 3.22/1.09  sat_num_of_epr_types:                   0
% 3.22/1.09  sat_num_of_non_cyclic_types:            0
% 3.22/1.09  sat_guarded_non_collapsed_types:        0
% 3.22/1.09  num_pure_diseq_elim:                    0
% 3.22/1.09  simp_replaced_by:                       0
% 3.22/1.10  res_preprocessed:                       166
% 3.22/1.10  prep_upred:                             0
% 3.22/1.10  prep_unflattend:                        12
% 3.22/1.10  smt_new_axioms:                         0
% 3.22/1.10  pred_elim_cands:                        4
% 3.22/1.10  pred_elim:                              3
% 3.22/1.10  pred_elim_cl:                           5
% 3.22/1.10  pred_elim_cycles:                       5
% 3.22/1.10  merged_defs:                            0
% 3.22/1.10  merged_defs_ncl:                        0
% 3.22/1.10  bin_hyper_res:                          0
% 3.22/1.10  prep_cycles:                            4
% 3.22/1.10  pred_elim_time:                         0.002
% 3.22/1.10  splitting_time:                         0.
% 3.22/1.10  sem_filter_time:                        0.
% 3.22/1.10  monotx_time:                            0.
% 3.22/1.10  subtype_inf_time:                       0.
% 3.22/1.10  
% 3.22/1.10  ------ Problem properties
% 3.22/1.10  
% 3.22/1.10  clauses:                                32
% 3.22/1.10  conjectures:                            8
% 3.22/1.10  epr:                                    6
% 3.22/1.10  horn:                                   32
% 3.22/1.10  ground:                                 13
% 3.22/1.10  unary:                                  13
% 3.22/1.10  binary:                                 8
% 3.22/1.10  lits:                                   69
% 3.22/1.10  lits_eq:                                18
% 3.22/1.10  fd_pure:                                0
% 3.22/1.10  fd_pseudo:                              0
% 3.22/1.10  fd_cond:                                0
% 3.22/1.10  fd_pseudo_cond:                         1
% 3.22/1.10  ac_symbols:                             0
% 3.22/1.10  
% 3.22/1.10  ------ Propositional Solver
% 3.22/1.10  
% 3.22/1.10  prop_solver_calls:                      34
% 3.22/1.10  prop_fast_solver_calls:                 1473
% 3.22/1.10  smt_solver_calls:                       0
% 3.22/1.10  smt_fast_solver_calls:                  0
% 3.22/1.10  prop_num_of_clauses:                    8667
% 3.22/1.10  prop_preprocess_simplified:             17545
% 3.22/1.10  prop_fo_subsumed:                       140
% 3.22/1.10  prop_solver_time:                       0.
% 3.22/1.10  smt_solver_time:                        0.
% 3.22/1.10  smt_fast_solver_time:                   0.
% 3.22/1.10  prop_fast_solver_time:                  0.
% 3.22/1.10  prop_unsat_core_time:                   0.001
% 3.22/1.10  
% 3.22/1.10  ------ QBF
% 3.22/1.10  
% 3.22/1.10  qbf_q_res:                              0
% 3.22/1.10  qbf_num_tautologies:                    0
% 3.22/1.10  qbf_prep_cycles:                        0
% 3.22/1.10  
% 3.22/1.10  ------ BMC1
% 3.22/1.10  
% 3.22/1.10  bmc1_current_bound:                     -1
% 3.22/1.10  bmc1_last_solved_bound:                 -1
% 3.22/1.10  bmc1_unsat_core_size:                   -1
% 3.22/1.10  bmc1_unsat_core_parents_size:           -1
% 3.22/1.10  bmc1_merge_next_fun:                    0
% 3.22/1.10  bmc1_unsat_core_clauses_time:           0.
% 3.22/1.10  
% 3.22/1.10  ------ Instantiation
% 3.22/1.10  
% 3.22/1.10  inst_num_of_clauses:                    2142
% 3.22/1.10  inst_num_in_passive:                    839
% 3.22/1.10  inst_num_in_active:                     1095
% 3.22/1.10  inst_num_in_unprocessed:                208
% 3.22/1.10  inst_num_of_loops:                      1170
% 3.22/1.10  inst_num_of_learning_restarts:          0
% 3.22/1.10  inst_num_moves_active_passive:          71
% 3.22/1.10  inst_lit_activity:                      0
% 3.22/1.10  inst_lit_activity_moves:                1
% 3.22/1.10  inst_num_tautologies:                   0
% 3.22/1.10  inst_num_prop_implied:                  0
% 3.22/1.10  inst_num_existing_simplified:           0
% 3.22/1.10  inst_num_eq_res_simplified:             0
% 3.22/1.10  inst_num_child_elim:                    0
% 3.22/1.10  inst_num_of_dismatching_blockings:      828
% 3.22/1.10  inst_num_of_non_proper_insts:           2507
% 3.22/1.10  inst_num_of_duplicates:                 0
% 3.22/1.10  inst_inst_num_from_inst_to_res:         0
% 3.22/1.10  inst_dismatching_checking_time:         0.
% 3.22/1.10  
% 3.22/1.10  ------ Resolution
% 3.22/1.10  
% 3.22/1.10  res_num_of_clauses:                     0
% 3.22/1.10  res_num_in_passive:                     0
% 3.22/1.10  res_num_in_active:                      0
% 3.22/1.10  res_num_of_loops:                       170
% 3.22/1.10  res_forward_subset_subsumed:            167
% 3.22/1.10  res_backward_subset_subsumed:           0
% 3.22/1.10  res_forward_subsumed:                   0
% 3.22/1.10  res_backward_subsumed:                  0
% 3.22/1.10  res_forward_subsumption_resolution:     0
% 3.22/1.10  res_backward_subsumption_resolution:    0
% 3.22/1.10  res_clause_to_clause_subsumption:       1440
% 3.22/1.10  res_orphan_elimination:                 0
% 3.22/1.10  res_tautology_del:                      255
% 3.22/1.10  res_num_eq_res_simplified:              0
% 3.22/1.10  res_num_sel_changes:                    0
% 3.22/1.10  res_moves_from_active_to_pass:          0
% 3.22/1.10  
% 3.22/1.10  ------ Superposition
% 3.22/1.10  
% 3.22/1.10  sup_time_total:                         0.
% 3.22/1.10  sup_time_generating:                    0.
% 3.22/1.10  sup_time_sim_full:                      0.
% 3.22/1.10  sup_time_sim_immed:                     0.
% 3.22/1.10  
% 3.22/1.10  sup_num_of_clauses:                     552
% 3.22/1.10  sup_num_in_active:                      207
% 3.22/1.10  sup_num_in_passive:                     345
% 3.22/1.10  sup_num_of_loops:                       232
% 3.22/1.10  sup_fw_superposition:                   438
% 3.22/1.10  sup_bw_superposition:                   223
% 3.22/1.10  sup_immediate_simplified:               255
% 3.22/1.10  sup_given_eliminated:                   5
% 3.22/1.10  comparisons_done:                       0
% 3.22/1.10  comparisons_avoided:                    0
% 3.22/1.10  
% 3.22/1.10  ------ Simplifications
% 3.22/1.10  
% 3.22/1.10  
% 3.22/1.10  sim_fw_subset_subsumed:                 16
% 3.22/1.10  sim_bw_subset_subsumed:                 51
% 3.22/1.10  sim_fw_subsumed:                        20
% 3.22/1.10  sim_bw_subsumed:                        3
% 3.22/1.10  sim_fw_subsumption_res:                 0
% 3.22/1.10  sim_bw_subsumption_res:                 0
% 3.22/1.10  sim_tautology_del:                      2
% 3.22/1.10  sim_eq_tautology_del:                   39
% 3.22/1.10  sim_eq_res_simp:                        0
% 3.22/1.10  sim_fw_demodulated:                     36
% 3.22/1.10  sim_bw_demodulated:                     12
% 3.22/1.10  sim_light_normalised:                   231
% 3.22/1.10  sim_joinable_taut:                      0
% 3.22/1.10  sim_joinable_simp:                      0
% 3.22/1.10  sim_ac_normalised:                      0
% 3.22/1.10  sim_smt_subsumption:                    0
% 3.22/1.10  
%------------------------------------------------------------------------------
