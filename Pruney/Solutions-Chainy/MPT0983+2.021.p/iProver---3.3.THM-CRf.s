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
% DateTime   : Thu Dec  3 12:01:49 EST 2020

% Result     : Theorem 7.81s
% Output     : CNFRefutation 7.81s
% Verified   : 
% Statistics : Number of formulae       :  185 ( 947 expanded)
%              Number of clauses        :  111 ( 291 expanded)
%              Number of leaves         :   22 ( 233 expanded)
%              Depth                    :   18
%              Number of atoms          :  590 (5863 expanded)
%              Number of equality atoms :  229 ( 492 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
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
           => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
             => ( v2_funct_2(X3,X0)
                & v2_funct_1(X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f43,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
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
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f43])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
     => ( ( ~ v2_funct_2(sK4,X0)
          | ~ v2_funct_1(X2) )
        & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK4),k6_partfun1(X0))
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(sK4,X1,X0)
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ( ~ v2_funct_2(X3,X0)
              | ~ v2_funct_1(X2) )
            & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ( ~ v2_funct_2(X3,sK1)
            | ~ v2_funct_1(sK3) )
          & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,X3),k6_partfun1(sK1))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
          & v1_funct_2(X3,sK2,sK1)
          & v1_funct_1(X3) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ( ~ v2_funct_2(sK4,sK1)
      | ~ v2_funct_1(sK3) )
    & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1))
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    & v1_funct_2(sK4,sK2,sK1)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f44,f50,f49])).

fof(f77,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f51])).

fof(f80,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f51])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f37])).

fof(f70,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f78,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f75,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f81,plain,(
    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f51])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f31])).

fof(f64,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f28])).

fof(f62,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f33])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f13,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f16,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f85,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f67,f71])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
           => ( v2_funct_1(X3)
              | ( k1_xboole_0 != X1
                & k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f41])).

fof(f73,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v2_funct_1(X3)
      | k1_xboole_0 = X2
      | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f83,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f58,f71])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f86,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f66])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f17,axiom,(
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

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f76,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f79,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f87,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f69])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f82,plain,
    ( ~ v2_funct_2(sK4,sK1)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1227,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1230,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1235,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2779,plain,
    ( k1_partfun1(X0,X1,sK2,sK1,X2,sK4) = k5_relat_1(X2,sK4)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1230,c_1235])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_33,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3071,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK2,sK1,X2,sK4) = k5_relat_1(X2,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2779,c_33])).

cnf(c_3072,plain,
    ( k1_partfun1(X0,X1,sK2,sK1,X2,sK4) = k5_relat_1(X2,sK4)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_3071])).

cnf(c_3081,plain,
    ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k5_relat_1(sK3,sK4)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1227,c_3072])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_30,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3383,plain,
    ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3081,c_30])).

cnf(c_23,negated_conjecture,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1231,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3385,plain,
    ( r2_relset_1(sK1,sK1,k5_relat_1(sK3,sK4),k6_partfun1(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3383,c_1231])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | k4_relset_1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1239,plain,
    ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2306,plain,
    ( k4_relset_1(X0,X1,sK2,sK1,X2,sK4) = k5_relat_1(X2,sK4)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1230,c_1239])).

cnf(c_2569,plain,
    ( k4_relset_1(sK1,sK2,sK2,sK1,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(superposition,[status(thm)],[c_1227,c_2306])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1241,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2878,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2569,c_1241])).

cnf(c_32,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_35,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_5401,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2878,c_32,c_35])).

cnf(c_14,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1237,plain,
    ( X0 = X1
    | r2_relset_1(X2,X3,X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_5415,plain,
    ( k5_relat_1(sK3,sK4) = X0
    | r2_relset_1(sK1,sK1,k5_relat_1(sK3,sK4),X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5401,c_1237])).

cnf(c_19144,plain,
    ( k5_relat_1(sK3,sK4) = k6_partfun1(sK1)
    | m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3385,c_5415])).

cnf(c_15,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_56,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_58,plain,
    ( m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_56])).

cnf(c_19583,plain,
    ( k5_relat_1(sK3,sK4) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19144,c_58])).

cnf(c_19600,plain,
    ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k6_partfun1(sK1) ),
    inference(demodulation,[status(thm)],[c_19583,c_3383])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ v2_funct_1(k1_partfun1(X1,X2,X2,X4,X0,X3))
    | k1_xboole_0 = X4 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1232,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X3) != iProver_top
    | v1_funct_2(X4,X3,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(X2,X3,X3,X0,X1,X4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_19678,plain,
    ( sK1 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK2) != iProver_top
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_funct_1(k6_partfun1(sK1)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_19600,c_1232])).

cnf(c_1236,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2305,plain,
    ( k4_relset_1(X0,X1,X2,X2,X3,k6_partfun1(X2)) = k5_relat_1(X3,k6_partfun1(X2))
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1236,c_1239])).

cnf(c_7875,plain,
    ( k4_relset_1(sK1,sK2,X0,X0,sK3,k6_partfun1(X0)) = k5_relat_1(sK3,k6_partfun1(X0)) ),
    inference(superposition,[status(thm)],[c_1227,c_2305])).

cnf(c_8190,plain,
    ( m1_subset_1(k5_relat_1(sK3,k6_partfun1(X0)),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
    | m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7875,c_1241])).

cnf(c_11142,plain,
    ( m1_subset_1(k5_relat_1(sK3,k6_partfun1(X0)),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8190,c_32,c_56])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1242,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_11149,plain,
    ( v1_xboole_0(k5_relat_1(sK3,k6_partfun1(X0))) = iProver_top
    | v1_xboole_0(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_11142,c_1242])).

cnf(c_5,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_84,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_86,plain,
    ( v2_funct_1(k6_partfun1(sK1)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_84])).

cnf(c_772,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1294,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(sK3)
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_772])).

cnf(c_1301,plain,
    ( ~ v2_funct_1(k6_partfun1(X0))
    | v2_funct_1(sK3)
    | sK3 != k6_partfun1(X0) ),
    inference(instantiation,[status(thm)],[c_1294])).

cnf(c_1302,plain,
    ( sK3 != k6_partfun1(X0)
    | v2_funct_1(k6_partfun1(X0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1301])).

cnf(c_1304,plain,
    ( sK3 != k6_partfun1(sK1)
    | v2_funct_1(k6_partfun1(sK1)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1302])).

cnf(c_767,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1375,plain,
    ( k6_partfun1(X0) != X1
    | sK3 != X1
    | sK3 = k6_partfun1(X0) ),
    inference(instantiation,[status(thm)],[c_767])).

cnf(c_1637,plain,
    ( k6_partfun1(X0) != sK3
    | sK3 = k6_partfun1(X0)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1375])).

cnf(c_1638,plain,
    ( k6_partfun1(sK1) != sK3
    | sK3 = k6_partfun1(sK1)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1637])).

cnf(c_1688,plain,
    ( ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(k6_partfun1(X0)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1704,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1688])).

cnf(c_1706,plain,
    ( m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_xboole_0(k6_partfun1(sK1)) = iProver_top
    | v1_xboole_0(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1704])).

cnf(c_1437,plain,
    ( ~ r2_relset_1(X0,X1,sK3,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X2 = sK3 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1614,plain,
    ( ~ r2_relset_1(sK1,sK2,sK3,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | X0 = sK3 ),
    inference(instantiation,[status(thm)],[c_1437])).

cnf(c_1723,plain,
    ( ~ r2_relset_1(sK1,sK2,sK3,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1614])).

cnf(c_13,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1806,plain,
    ( r2_relset_1(sK1,sK2,sK3,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1432,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(sK3)
    | X0 = sK3 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2037,plain,
    ( ~ v1_xboole_0(k6_partfun1(X0))
    | ~ v1_xboole_0(sK3)
    | k6_partfun1(X0) = sK3 ),
    inference(instantiation,[status(thm)],[c_1432])).

cnf(c_2043,plain,
    ( k6_partfun1(X0) = sK3
    | v1_xboole_0(k6_partfun1(X0)) != iProver_top
    | v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2037])).

cnf(c_2045,plain,
    ( k6_partfun1(sK1) = sK3
    | v1_xboole_0(k6_partfun1(sK1)) != iProver_top
    | v1_xboole_0(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2043])).

cnf(c_2229,plain,
    ( v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1227,c_1242])).

cnf(c_19,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1234,plain,
    ( k2_relset_1(X0,X1,X2) = X1
    | r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) != iProver_top
    | v1_funct_2(X3,X1,X0) != iProver_top
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2797,plain,
    ( k2_relset_1(sK2,sK1,sK4) = sK1
    | v1_funct_2(sK3,sK1,sK2) != iProver_top
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1231,c_1234])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1240,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2062,plain,
    ( k2_relset_1(sK2,sK1,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1230,c_1240])).

cnf(c_2798,plain,
    ( k2_relat_1(sK4) = sK1
    | v1_funct_2(sK3,sK1,sK2) != iProver_top
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2797,c_2062])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_31,plain,
    ( v1_funct_2(sK3,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_25,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_34,plain,
    ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_7860,plain,
    ( k2_relat_1(sK4) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2798,c_30,c_31,c_32,c_33,c_34,c_35])).

cnf(c_8,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_16,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_350,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X0)
    | X0 != X1
    | k2_relat_1(X0) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_16])).

cnf(c_351,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_350])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_361,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0)))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_351,c_7])).

cnf(c_22,negated_conjecture,
    ( ~ v2_funct_2(sK4,sK1)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_376,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
    | ~ v2_funct_1(sK3)
    | k2_relat_1(X0) != sK1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_361,c_22])).

cnf(c_377,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK4))))
    | ~ v2_funct_1(sK3)
    | k2_relat_1(sK4) != sK1 ),
    inference(unflattening,[status(thm)],[c_376])).

cnf(c_764,plain,
    ( ~ v2_funct_1(sK3)
    | sP0_iProver_split
    | k2_relat_1(sK4) != sK1 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_377])).

cnf(c_1223,plain,
    ( k2_relat_1(sK4) != sK1
    | v2_funct_1(sK3) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_764])).

cnf(c_7864,plain,
    ( sK1 != sK1
    | v2_funct_1(sK3) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_7860,c_1223])).

cnf(c_7865,plain,
    ( v2_funct_1(sK3) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_7864])).

cnf(c_763,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK4))))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_377])).

cnf(c_1224,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK4)))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_763])).

cnf(c_7863,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(demodulation,[status(thm)],[c_7860,c_1224])).

cnf(c_9076,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_1230,c_7863])).

cnf(c_11442,plain,
    ( v1_xboole_0(sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11149,c_27,c_58,c_86,c_1304,c_1638,c_1706,c_1723,c_1806,c_2045,c_2229,c_7865,c_9076])).

cnf(c_768,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2593,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(k1_xboole_0)
    | X0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_768])).

cnf(c_2594,plain,
    ( X0 != k1_xboole_0
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2593])).

cnf(c_2596,plain,
    ( sK1 != k1_xboole_0
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2594])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_97,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_19678,c_11442,c_9076,c_7865,c_2596,c_97,c_86,c_35,c_34,c_33,c_32,c_31,c_30])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:27:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.81/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.81/1.49  
% 7.81/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.81/1.49  
% 7.81/1.49  ------  iProver source info
% 7.81/1.49  
% 7.81/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.81/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.81/1.49  git: non_committed_changes: false
% 7.81/1.49  git: last_make_outside_of_git: false
% 7.81/1.49  
% 7.81/1.49  ------ 
% 7.81/1.49  
% 7.81/1.49  ------ Input Options
% 7.81/1.49  
% 7.81/1.49  --out_options                           all
% 7.81/1.49  --tptp_safe_out                         true
% 7.81/1.49  --problem_path                          ""
% 7.81/1.49  --include_path                          ""
% 7.81/1.49  --clausifier                            res/vclausify_rel
% 7.81/1.49  --clausifier_options                    ""
% 7.81/1.49  --stdin                                 false
% 7.81/1.49  --stats_out                             all
% 7.81/1.49  
% 7.81/1.49  ------ General Options
% 7.81/1.49  
% 7.81/1.49  --fof                                   false
% 7.81/1.49  --time_out_real                         305.
% 7.81/1.49  --time_out_virtual                      -1.
% 7.81/1.49  --symbol_type_check                     false
% 7.81/1.49  --clausify_out                          false
% 7.81/1.49  --sig_cnt_out                           false
% 7.81/1.49  --trig_cnt_out                          false
% 7.81/1.49  --trig_cnt_out_tolerance                1.
% 7.81/1.49  --trig_cnt_out_sk_spl                   false
% 7.81/1.49  --abstr_cl_out                          false
% 7.81/1.49  
% 7.81/1.49  ------ Global Options
% 7.81/1.49  
% 7.81/1.49  --schedule                              default
% 7.81/1.49  --add_important_lit                     false
% 7.81/1.49  --prop_solver_per_cl                    1000
% 7.81/1.49  --min_unsat_core                        false
% 7.81/1.49  --soft_assumptions                      false
% 7.81/1.49  --soft_lemma_size                       3
% 7.81/1.49  --prop_impl_unit_size                   0
% 7.81/1.49  --prop_impl_unit                        []
% 7.81/1.49  --share_sel_clauses                     true
% 7.81/1.49  --reset_solvers                         false
% 7.81/1.49  --bc_imp_inh                            [conj_cone]
% 7.81/1.49  --conj_cone_tolerance                   3.
% 7.81/1.49  --extra_neg_conj                        none
% 7.81/1.49  --large_theory_mode                     true
% 7.81/1.49  --prolific_symb_bound                   200
% 7.81/1.49  --lt_threshold                          2000
% 7.81/1.49  --clause_weak_htbl                      true
% 7.81/1.49  --gc_record_bc_elim                     false
% 7.81/1.49  
% 7.81/1.49  ------ Preprocessing Options
% 7.81/1.49  
% 7.81/1.49  --preprocessing_flag                    true
% 7.81/1.49  --time_out_prep_mult                    0.1
% 7.81/1.49  --splitting_mode                        input
% 7.81/1.49  --splitting_grd                         true
% 7.81/1.49  --splitting_cvd                         false
% 7.81/1.49  --splitting_cvd_svl                     false
% 7.81/1.49  --splitting_nvd                         32
% 7.81/1.49  --sub_typing                            true
% 7.81/1.49  --prep_gs_sim                           true
% 7.81/1.49  --prep_unflatten                        true
% 7.81/1.49  --prep_res_sim                          true
% 7.81/1.49  --prep_upred                            true
% 7.81/1.49  --prep_sem_filter                       exhaustive
% 7.81/1.49  --prep_sem_filter_out                   false
% 7.81/1.49  --pred_elim                             true
% 7.81/1.49  --res_sim_input                         true
% 7.81/1.49  --eq_ax_congr_red                       true
% 7.81/1.49  --pure_diseq_elim                       true
% 7.81/1.49  --brand_transform                       false
% 7.81/1.49  --non_eq_to_eq                          false
% 7.81/1.49  --prep_def_merge                        true
% 7.81/1.49  --prep_def_merge_prop_impl              false
% 7.81/1.49  --prep_def_merge_mbd                    true
% 7.81/1.49  --prep_def_merge_tr_red                 false
% 7.81/1.49  --prep_def_merge_tr_cl                  false
% 7.81/1.49  --smt_preprocessing                     true
% 7.81/1.49  --smt_ac_axioms                         fast
% 7.81/1.49  --preprocessed_out                      false
% 7.81/1.49  --preprocessed_stats                    false
% 7.81/1.49  
% 7.81/1.49  ------ Abstraction refinement Options
% 7.81/1.49  
% 7.81/1.49  --abstr_ref                             []
% 7.81/1.49  --abstr_ref_prep                        false
% 7.81/1.49  --abstr_ref_until_sat                   false
% 7.81/1.49  --abstr_ref_sig_restrict                funpre
% 7.81/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.81/1.49  --abstr_ref_under                       []
% 7.81/1.49  
% 7.81/1.49  ------ SAT Options
% 7.81/1.49  
% 7.81/1.49  --sat_mode                              false
% 7.81/1.49  --sat_fm_restart_options                ""
% 7.81/1.49  --sat_gr_def                            false
% 7.81/1.49  --sat_epr_types                         true
% 7.81/1.49  --sat_non_cyclic_types                  false
% 7.81/1.49  --sat_finite_models                     false
% 7.81/1.49  --sat_fm_lemmas                         false
% 7.81/1.49  --sat_fm_prep                           false
% 7.81/1.49  --sat_fm_uc_incr                        true
% 7.81/1.49  --sat_out_model                         small
% 7.81/1.49  --sat_out_clauses                       false
% 7.81/1.49  
% 7.81/1.49  ------ QBF Options
% 7.81/1.49  
% 7.81/1.49  --qbf_mode                              false
% 7.81/1.49  --qbf_elim_univ                         false
% 7.81/1.49  --qbf_dom_inst                          none
% 7.81/1.49  --qbf_dom_pre_inst                      false
% 7.81/1.49  --qbf_sk_in                             false
% 7.81/1.49  --qbf_pred_elim                         true
% 7.81/1.49  --qbf_split                             512
% 7.81/1.49  
% 7.81/1.49  ------ BMC1 Options
% 7.81/1.49  
% 7.81/1.49  --bmc1_incremental                      false
% 7.81/1.49  --bmc1_axioms                           reachable_all
% 7.81/1.49  --bmc1_min_bound                        0
% 7.81/1.49  --bmc1_max_bound                        -1
% 7.81/1.49  --bmc1_max_bound_default                -1
% 7.81/1.49  --bmc1_symbol_reachability              true
% 7.81/1.49  --bmc1_property_lemmas                  false
% 7.81/1.49  --bmc1_k_induction                      false
% 7.81/1.49  --bmc1_non_equiv_states                 false
% 7.81/1.49  --bmc1_deadlock                         false
% 7.81/1.49  --bmc1_ucm                              false
% 7.81/1.49  --bmc1_add_unsat_core                   none
% 7.81/1.49  --bmc1_unsat_core_children              false
% 7.81/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.81/1.49  --bmc1_out_stat                         full
% 7.81/1.49  --bmc1_ground_init                      false
% 7.81/1.49  --bmc1_pre_inst_next_state              false
% 7.81/1.49  --bmc1_pre_inst_state                   false
% 7.81/1.49  --bmc1_pre_inst_reach_state             false
% 7.81/1.49  --bmc1_out_unsat_core                   false
% 7.81/1.49  --bmc1_aig_witness_out                  false
% 7.81/1.49  --bmc1_verbose                          false
% 7.81/1.49  --bmc1_dump_clauses_tptp                false
% 7.81/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.81/1.49  --bmc1_dump_file                        -
% 7.81/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.81/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.81/1.49  --bmc1_ucm_extend_mode                  1
% 7.81/1.49  --bmc1_ucm_init_mode                    2
% 7.81/1.49  --bmc1_ucm_cone_mode                    none
% 7.81/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.81/1.49  --bmc1_ucm_relax_model                  4
% 7.81/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.81/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.81/1.49  --bmc1_ucm_layered_model                none
% 7.81/1.49  --bmc1_ucm_max_lemma_size               10
% 7.81/1.49  
% 7.81/1.49  ------ AIG Options
% 7.81/1.49  
% 7.81/1.49  --aig_mode                              false
% 7.81/1.49  
% 7.81/1.49  ------ Instantiation Options
% 7.81/1.49  
% 7.81/1.49  --instantiation_flag                    true
% 7.81/1.49  --inst_sos_flag                         true
% 7.81/1.49  --inst_sos_phase                        true
% 7.81/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.81/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.81/1.49  --inst_lit_sel_side                     num_symb
% 7.81/1.49  --inst_solver_per_active                1400
% 7.81/1.49  --inst_solver_calls_frac                1.
% 7.81/1.49  --inst_passive_queue_type               priority_queues
% 7.81/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.81/1.49  --inst_passive_queues_freq              [25;2]
% 7.81/1.49  --inst_dismatching                      true
% 7.81/1.49  --inst_eager_unprocessed_to_passive     true
% 7.81/1.49  --inst_prop_sim_given                   true
% 7.81/1.49  --inst_prop_sim_new                     false
% 7.81/1.49  --inst_subs_new                         false
% 7.81/1.49  --inst_eq_res_simp                      false
% 7.81/1.49  --inst_subs_given                       false
% 7.81/1.49  --inst_orphan_elimination               true
% 7.81/1.49  --inst_learning_loop_flag               true
% 7.81/1.49  --inst_learning_start                   3000
% 7.81/1.49  --inst_learning_factor                  2
% 7.81/1.49  --inst_start_prop_sim_after_learn       3
% 7.81/1.49  --inst_sel_renew                        solver
% 7.81/1.49  --inst_lit_activity_flag                true
% 7.81/1.49  --inst_restr_to_given                   false
% 7.81/1.49  --inst_activity_threshold               500
% 7.81/1.49  --inst_out_proof                        true
% 7.81/1.49  
% 7.81/1.49  ------ Resolution Options
% 7.81/1.49  
% 7.81/1.49  --resolution_flag                       true
% 7.81/1.49  --res_lit_sel                           adaptive
% 7.81/1.49  --res_lit_sel_side                      none
% 7.81/1.49  --res_ordering                          kbo
% 7.81/1.49  --res_to_prop_solver                    active
% 7.81/1.49  --res_prop_simpl_new                    false
% 7.81/1.49  --res_prop_simpl_given                  true
% 7.81/1.49  --res_passive_queue_type                priority_queues
% 7.81/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.81/1.49  --res_passive_queues_freq               [15;5]
% 7.81/1.49  --res_forward_subs                      full
% 7.81/1.49  --res_backward_subs                     full
% 7.81/1.49  --res_forward_subs_resolution           true
% 7.81/1.49  --res_backward_subs_resolution          true
% 7.81/1.49  --res_orphan_elimination                true
% 7.81/1.49  --res_time_limit                        2.
% 7.81/1.49  --res_out_proof                         true
% 7.81/1.49  
% 7.81/1.49  ------ Superposition Options
% 7.81/1.49  
% 7.81/1.49  --superposition_flag                    true
% 7.81/1.49  --sup_passive_queue_type                priority_queues
% 7.81/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.81/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.81/1.49  --demod_completeness_check              fast
% 7.81/1.49  --demod_use_ground                      true
% 7.81/1.49  --sup_to_prop_solver                    passive
% 7.81/1.49  --sup_prop_simpl_new                    true
% 7.81/1.49  --sup_prop_simpl_given                  true
% 7.81/1.49  --sup_fun_splitting                     true
% 7.81/1.49  --sup_smt_interval                      50000
% 7.81/1.49  
% 7.81/1.49  ------ Superposition Simplification Setup
% 7.81/1.49  
% 7.81/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.81/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.81/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.81/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.81/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.81/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.81/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.81/1.49  --sup_immed_triv                        [TrivRules]
% 7.81/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.81/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.81/1.49  --sup_immed_bw_main                     []
% 7.81/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.81/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.81/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.81/1.49  --sup_input_bw                          []
% 7.81/1.49  
% 7.81/1.49  ------ Combination Options
% 7.81/1.49  
% 7.81/1.49  --comb_res_mult                         3
% 7.81/1.49  --comb_sup_mult                         2
% 7.81/1.49  --comb_inst_mult                        10
% 7.81/1.49  
% 7.81/1.49  ------ Debug Options
% 7.81/1.49  
% 7.81/1.49  --dbg_backtrace                         false
% 7.81/1.49  --dbg_dump_prop_clauses                 false
% 7.81/1.49  --dbg_dump_prop_clauses_file            -
% 7.81/1.49  --dbg_out_stat                          false
% 7.81/1.49  ------ Parsing...
% 7.81/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.81/1.49  
% 7.81/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 7.81/1.49  
% 7.81/1.49  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.81/1.49  
% 7.81/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.81/1.49  ------ Proving...
% 7.81/1.49  ------ Problem Properties 
% 7.81/1.49  
% 7.81/1.49  
% 7.81/1.49  clauses                                 26
% 7.81/1.49  conjectures                             7
% 7.81/1.49  EPR                                     6
% 7.81/1.49  Horn                                    24
% 7.81/1.49  unary                                   10
% 7.81/1.49  binary                                  5
% 7.81/1.49  lits                                    72
% 7.81/1.49  lits eq                                 8
% 7.81/1.49  fd_pure                                 0
% 7.81/1.49  fd_pseudo                               0
% 7.81/1.49  fd_cond                                 1
% 7.81/1.49  fd_pseudo_cond                          2
% 7.81/1.49  AC symbols                              0
% 7.81/1.49  
% 7.81/1.49  ------ Schedule dynamic 5 is on 
% 7.81/1.49  
% 7.81/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.81/1.49  
% 7.81/1.49  
% 7.81/1.49  ------ 
% 7.81/1.49  Current options:
% 7.81/1.49  ------ 
% 7.81/1.49  
% 7.81/1.49  ------ Input Options
% 7.81/1.49  
% 7.81/1.49  --out_options                           all
% 7.81/1.49  --tptp_safe_out                         true
% 7.81/1.49  --problem_path                          ""
% 7.81/1.49  --include_path                          ""
% 7.81/1.49  --clausifier                            res/vclausify_rel
% 7.81/1.49  --clausifier_options                    ""
% 7.81/1.49  --stdin                                 false
% 7.81/1.49  --stats_out                             all
% 7.81/1.49  
% 7.81/1.49  ------ General Options
% 7.81/1.49  
% 7.81/1.49  --fof                                   false
% 7.81/1.49  --time_out_real                         305.
% 7.81/1.49  --time_out_virtual                      -1.
% 7.81/1.49  --symbol_type_check                     false
% 7.81/1.49  --clausify_out                          false
% 7.81/1.49  --sig_cnt_out                           false
% 7.81/1.49  --trig_cnt_out                          false
% 7.81/1.49  --trig_cnt_out_tolerance                1.
% 7.81/1.49  --trig_cnt_out_sk_spl                   false
% 7.81/1.49  --abstr_cl_out                          false
% 7.81/1.49  
% 7.81/1.49  ------ Global Options
% 7.81/1.49  
% 7.81/1.49  --schedule                              default
% 7.81/1.49  --add_important_lit                     false
% 7.81/1.49  --prop_solver_per_cl                    1000
% 7.81/1.49  --min_unsat_core                        false
% 7.81/1.49  --soft_assumptions                      false
% 7.81/1.49  --soft_lemma_size                       3
% 7.81/1.49  --prop_impl_unit_size                   0
% 7.81/1.49  --prop_impl_unit                        []
% 7.81/1.49  --share_sel_clauses                     true
% 7.81/1.49  --reset_solvers                         false
% 7.81/1.49  --bc_imp_inh                            [conj_cone]
% 7.81/1.49  --conj_cone_tolerance                   3.
% 7.81/1.49  --extra_neg_conj                        none
% 7.81/1.49  --large_theory_mode                     true
% 7.81/1.49  --prolific_symb_bound                   200
% 7.81/1.49  --lt_threshold                          2000
% 7.81/1.49  --clause_weak_htbl                      true
% 7.81/1.49  --gc_record_bc_elim                     false
% 7.81/1.49  
% 7.81/1.49  ------ Preprocessing Options
% 7.81/1.49  
% 7.81/1.49  --preprocessing_flag                    true
% 7.81/1.49  --time_out_prep_mult                    0.1
% 7.81/1.49  --splitting_mode                        input
% 7.81/1.49  --splitting_grd                         true
% 7.81/1.49  --splitting_cvd                         false
% 7.81/1.49  --splitting_cvd_svl                     false
% 7.81/1.49  --splitting_nvd                         32
% 7.81/1.49  --sub_typing                            true
% 7.81/1.49  --prep_gs_sim                           true
% 7.81/1.49  --prep_unflatten                        true
% 7.81/1.49  --prep_res_sim                          true
% 7.81/1.49  --prep_upred                            true
% 7.81/1.49  --prep_sem_filter                       exhaustive
% 7.81/1.49  --prep_sem_filter_out                   false
% 7.81/1.49  --pred_elim                             true
% 7.81/1.49  --res_sim_input                         true
% 7.81/1.49  --eq_ax_congr_red                       true
% 7.81/1.49  --pure_diseq_elim                       true
% 7.81/1.49  --brand_transform                       false
% 7.81/1.49  --non_eq_to_eq                          false
% 7.81/1.49  --prep_def_merge                        true
% 7.81/1.49  --prep_def_merge_prop_impl              false
% 7.81/1.49  --prep_def_merge_mbd                    true
% 7.81/1.49  --prep_def_merge_tr_red                 false
% 7.81/1.49  --prep_def_merge_tr_cl                  false
% 7.81/1.49  --smt_preprocessing                     true
% 7.81/1.49  --smt_ac_axioms                         fast
% 7.81/1.49  --preprocessed_out                      false
% 7.81/1.49  --preprocessed_stats                    false
% 7.81/1.49  
% 7.81/1.49  ------ Abstraction refinement Options
% 7.81/1.49  
% 7.81/1.49  --abstr_ref                             []
% 7.81/1.49  --abstr_ref_prep                        false
% 7.81/1.49  --abstr_ref_until_sat                   false
% 7.81/1.49  --abstr_ref_sig_restrict                funpre
% 7.81/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.81/1.49  --abstr_ref_under                       []
% 7.81/1.49  
% 7.81/1.49  ------ SAT Options
% 7.81/1.49  
% 7.81/1.49  --sat_mode                              false
% 7.81/1.49  --sat_fm_restart_options                ""
% 7.81/1.49  --sat_gr_def                            false
% 7.81/1.49  --sat_epr_types                         true
% 7.81/1.49  --sat_non_cyclic_types                  false
% 7.81/1.49  --sat_finite_models                     false
% 7.81/1.49  --sat_fm_lemmas                         false
% 7.81/1.49  --sat_fm_prep                           false
% 7.81/1.49  --sat_fm_uc_incr                        true
% 7.81/1.49  --sat_out_model                         small
% 7.81/1.49  --sat_out_clauses                       false
% 7.81/1.49  
% 7.81/1.49  ------ QBF Options
% 7.81/1.49  
% 7.81/1.49  --qbf_mode                              false
% 7.81/1.49  --qbf_elim_univ                         false
% 7.81/1.49  --qbf_dom_inst                          none
% 7.81/1.49  --qbf_dom_pre_inst                      false
% 7.81/1.49  --qbf_sk_in                             false
% 7.81/1.49  --qbf_pred_elim                         true
% 7.81/1.49  --qbf_split                             512
% 7.81/1.49  
% 7.81/1.49  ------ BMC1 Options
% 7.81/1.49  
% 7.81/1.49  --bmc1_incremental                      false
% 7.81/1.49  --bmc1_axioms                           reachable_all
% 7.81/1.49  --bmc1_min_bound                        0
% 7.81/1.49  --bmc1_max_bound                        -1
% 7.81/1.49  --bmc1_max_bound_default                -1
% 7.81/1.49  --bmc1_symbol_reachability              true
% 7.81/1.49  --bmc1_property_lemmas                  false
% 7.81/1.49  --bmc1_k_induction                      false
% 7.81/1.49  --bmc1_non_equiv_states                 false
% 7.81/1.49  --bmc1_deadlock                         false
% 7.81/1.49  --bmc1_ucm                              false
% 7.81/1.49  --bmc1_add_unsat_core                   none
% 7.81/1.49  --bmc1_unsat_core_children              false
% 7.81/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.81/1.49  --bmc1_out_stat                         full
% 7.81/1.49  --bmc1_ground_init                      false
% 7.81/1.49  --bmc1_pre_inst_next_state              false
% 7.81/1.49  --bmc1_pre_inst_state                   false
% 7.81/1.49  --bmc1_pre_inst_reach_state             false
% 7.81/1.49  --bmc1_out_unsat_core                   false
% 7.81/1.49  --bmc1_aig_witness_out                  false
% 7.81/1.49  --bmc1_verbose                          false
% 7.81/1.49  --bmc1_dump_clauses_tptp                false
% 7.81/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.81/1.49  --bmc1_dump_file                        -
% 7.81/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.81/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.81/1.49  --bmc1_ucm_extend_mode                  1
% 7.81/1.49  --bmc1_ucm_init_mode                    2
% 7.81/1.49  --bmc1_ucm_cone_mode                    none
% 7.81/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.81/1.49  --bmc1_ucm_relax_model                  4
% 7.81/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.81/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.81/1.49  --bmc1_ucm_layered_model                none
% 7.81/1.49  --bmc1_ucm_max_lemma_size               10
% 7.81/1.49  
% 7.81/1.49  ------ AIG Options
% 7.81/1.49  
% 7.81/1.49  --aig_mode                              false
% 7.81/1.49  
% 7.81/1.49  ------ Instantiation Options
% 7.81/1.49  
% 7.81/1.49  --instantiation_flag                    true
% 7.81/1.49  --inst_sos_flag                         true
% 7.81/1.49  --inst_sos_phase                        true
% 7.81/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.81/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.81/1.49  --inst_lit_sel_side                     none
% 7.81/1.49  --inst_solver_per_active                1400
% 7.81/1.49  --inst_solver_calls_frac                1.
% 7.81/1.49  --inst_passive_queue_type               priority_queues
% 7.81/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.81/1.49  --inst_passive_queues_freq              [25;2]
% 7.81/1.49  --inst_dismatching                      true
% 7.81/1.49  --inst_eager_unprocessed_to_passive     true
% 7.81/1.49  --inst_prop_sim_given                   true
% 7.81/1.49  --inst_prop_sim_new                     false
% 7.81/1.49  --inst_subs_new                         false
% 7.81/1.49  --inst_eq_res_simp                      false
% 7.81/1.49  --inst_subs_given                       false
% 7.81/1.49  --inst_orphan_elimination               true
% 7.81/1.49  --inst_learning_loop_flag               true
% 7.81/1.49  --inst_learning_start                   3000
% 7.81/1.49  --inst_learning_factor                  2
% 7.81/1.49  --inst_start_prop_sim_after_learn       3
% 7.81/1.49  --inst_sel_renew                        solver
% 7.81/1.49  --inst_lit_activity_flag                true
% 7.81/1.49  --inst_restr_to_given                   false
% 7.81/1.49  --inst_activity_threshold               500
% 7.81/1.49  --inst_out_proof                        true
% 7.81/1.49  
% 7.81/1.49  ------ Resolution Options
% 7.81/1.49  
% 7.81/1.49  --resolution_flag                       false
% 7.81/1.49  --res_lit_sel                           adaptive
% 7.81/1.49  --res_lit_sel_side                      none
% 7.81/1.49  --res_ordering                          kbo
% 7.81/1.49  --res_to_prop_solver                    active
% 7.81/1.49  --res_prop_simpl_new                    false
% 7.81/1.49  --res_prop_simpl_given                  true
% 7.81/1.49  --res_passive_queue_type                priority_queues
% 7.81/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.81/1.49  --res_passive_queues_freq               [15;5]
% 7.81/1.49  --res_forward_subs                      full
% 7.81/1.49  --res_backward_subs                     full
% 7.81/1.49  --res_forward_subs_resolution           true
% 7.81/1.49  --res_backward_subs_resolution          true
% 7.81/1.49  --res_orphan_elimination                true
% 7.81/1.49  --res_time_limit                        2.
% 7.81/1.49  --res_out_proof                         true
% 7.81/1.49  
% 7.81/1.49  ------ Superposition Options
% 7.81/1.49  
% 7.81/1.49  --superposition_flag                    true
% 7.81/1.49  --sup_passive_queue_type                priority_queues
% 7.81/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.81/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.81/1.49  --demod_completeness_check              fast
% 7.81/1.49  --demod_use_ground                      true
% 7.81/1.49  --sup_to_prop_solver                    passive
% 7.81/1.49  --sup_prop_simpl_new                    true
% 7.81/1.49  --sup_prop_simpl_given                  true
% 7.81/1.49  --sup_fun_splitting                     true
% 7.81/1.49  --sup_smt_interval                      50000
% 7.81/1.49  
% 7.81/1.49  ------ Superposition Simplification Setup
% 7.81/1.49  
% 7.81/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.81/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.81/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.81/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.81/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.81/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.81/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.81/1.49  --sup_immed_triv                        [TrivRules]
% 7.81/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.81/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.81/1.49  --sup_immed_bw_main                     []
% 7.81/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.81/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.81/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.81/1.49  --sup_input_bw                          []
% 7.81/1.49  
% 7.81/1.49  ------ Combination Options
% 7.81/1.49  
% 7.81/1.49  --comb_res_mult                         3
% 7.81/1.49  --comb_sup_mult                         2
% 7.81/1.49  --comb_inst_mult                        10
% 7.81/1.49  
% 7.81/1.49  ------ Debug Options
% 7.81/1.49  
% 7.81/1.49  --dbg_backtrace                         false
% 7.81/1.49  --dbg_dump_prop_clauses                 false
% 7.81/1.49  --dbg_dump_prop_clauses_file            -
% 7.81/1.49  --dbg_out_stat                          false
% 7.81/1.49  
% 7.81/1.49  
% 7.81/1.49  
% 7.81/1.49  
% 7.81/1.49  ------ Proving...
% 7.81/1.49  
% 7.81/1.49  
% 7.81/1.49  % SZS status Theorem for theBenchmark.p
% 7.81/1.49  
% 7.81/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.81/1.49  
% 7.81/1.49  fof(f19,conjecture,(
% 7.81/1.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 7.81/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.49  
% 7.81/1.49  fof(f20,negated_conjecture,(
% 7.81/1.49    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 7.81/1.49    inference(negated_conjecture,[],[f19])).
% 7.81/1.49  
% 7.81/1.49  fof(f43,plain,(
% 7.81/1.49    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 7.81/1.49    inference(ennf_transformation,[],[f20])).
% 7.81/1.49  
% 7.81/1.49  fof(f44,plain,(
% 7.81/1.49    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 7.81/1.49    inference(flattening,[],[f43])).
% 7.81/1.49  
% 7.81/1.49  fof(f50,plain,(
% 7.81/1.49    ( ! [X2,X0,X1] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((~v2_funct_2(sK4,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK4),k6_partfun1(X0)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK4,X1,X0) & v1_funct_1(sK4))) )),
% 7.81/1.49    introduced(choice_axiom,[])).
% 7.81/1.49  
% 7.81/1.49  fof(f49,plain,(
% 7.81/1.49    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK1) | ~v2_funct_1(sK3)) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,X3),k6_partfun1(sK1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(X3,sK2,sK1) & v1_funct_1(X3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 7.81/1.49    introduced(choice_axiom,[])).
% 7.81/1.49  
% 7.81/1.49  fof(f51,plain,(
% 7.81/1.49    ((~v2_funct_2(sK4,sK1) | ~v2_funct_1(sK3)) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 7.81/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f44,f50,f49])).
% 7.81/1.49  
% 7.81/1.49  fof(f77,plain,(
% 7.81/1.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 7.81/1.49    inference(cnf_transformation,[],[f51])).
% 7.81/1.49  
% 7.81/1.49  fof(f80,plain,(
% 7.81/1.49    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 7.81/1.49    inference(cnf_transformation,[],[f51])).
% 7.81/1.49  
% 7.81/1.49  fof(f15,axiom,(
% 7.81/1.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 7.81/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.49  
% 7.81/1.49  fof(f37,plain,(
% 7.81/1.49    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 7.81/1.49    inference(ennf_transformation,[],[f15])).
% 7.81/1.49  
% 7.81/1.49  fof(f38,plain,(
% 7.81/1.49    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 7.81/1.49    inference(flattening,[],[f37])).
% 7.81/1.49  
% 7.81/1.49  fof(f70,plain,(
% 7.81/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 7.81/1.49    inference(cnf_transformation,[],[f38])).
% 7.81/1.49  
% 7.81/1.49  fof(f78,plain,(
% 7.81/1.49    v1_funct_1(sK4)),
% 7.81/1.49    inference(cnf_transformation,[],[f51])).
% 7.81/1.49  
% 7.81/1.49  fof(f75,plain,(
% 7.81/1.49    v1_funct_1(sK3)),
% 7.81/1.49    inference(cnf_transformation,[],[f51])).
% 7.81/1.49  
% 7.81/1.49  fof(f81,plain,(
% 7.81/1.49    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1))),
% 7.81/1.49    inference(cnf_transformation,[],[f51])).
% 7.81/1.49  
% 7.81/1.49  fof(f11,axiom,(
% 7.81/1.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 7.81/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.49  
% 7.81/1.49  fof(f31,plain,(
% 7.81/1.49    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 7.81/1.49    inference(ennf_transformation,[],[f11])).
% 7.81/1.49  
% 7.81/1.49  fof(f32,plain,(
% 7.81/1.49    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.81/1.49    inference(flattening,[],[f31])).
% 7.81/1.49  
% 7.81/1.49  fof(f64,plain,(
% 7.81/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.81/1.49    inference(cnf_transformation,[],[f32])).
% 7.81/1.49  
% 7.81/1.49  fof(f9,axiom,(
% 7.81/1.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))))),
% 7.81/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.49  
% 7.81/1.49  fof(f28,plain,(
% 7.81/1.49    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 7.81/1.49    inference(ennf_transformation,[],[f9])).
% 7.81/1.49  
% 7.81/1.49  fof(f29,plain,(
% 7.81/1.49    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.81/1.49    inference(flattening,[],[f28])).
% 7.81/1.49  
% 7.81/1.49  fof(f62,plain,(
% 7.81/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.81/1.49    inference(cnf_transformation,[],[f29])).
% 7.81/1.49  
% 7.81/1.49  fof(f12,axiom,(
% 7.81/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 7.81/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.49  
% 7.81/1.49  fof(f33,plain,(
% 7.81/1.49    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 7.81/1.49    inference(ennf_transformation,[],[f12])).
% 7.81/1.49  
% 7.81/1.49  fof(f34,plain,(
% 7.81/1.49    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.81/1.49    inference(flattening,[],[f33])).
% 7.81/1.49  
% 7.81/1.49  fof(f47,plain,(
% 7.81/1.49    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.81/1.49    inference(nnf_transformation,[],[f34])).
% 7.81/1.49  
% 7.81/1.49  fof(f65,plain,(
% 7.81/1.49    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.81/1.49    inference(cnf_transformation,[],[f47])).
% 7.81/1.49  
% 7.81/1.49  fof(f13,axiom,(
% 7.81/1.49    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 7.81/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.49  
% 7.81/1.49  fof(f67,plain,(
% 7.81/1.49    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 7.81/1.49    inference(cnf_transformation,[],[f13])).
% 7.81/1.49  
% 7.81/1.49  fof(f16,axiom,(
% 7.81/1.49    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 7.81/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.49  
% 7.81/1.49  fof(f71,plain,(
% 7.81/1.49    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 7.81/1.49    inference(cnf_transformation,[],[f16])).
% 7.81/1.49  
% 7.81/1.49  fof(f85,plain,(
% 7.81/1.49    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 7.81/1.49    inference(definition_unfolding,[],[f67,f71])).
% 7.81/1.49  
% 7.81/1.49  fof(f18,axiom,(
% 7.81/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 7.81/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.49  
% 7.81/1.49  fof(f41,plain,(
% 7.81/1.49    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 7.81/1.49    inference(ennf_transformation,[],[f18])).
% 7.81/1.49  
% 7.81/1.49  fof(f42,plain,(
% 7.81/1.49    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 7.81/1.49    inference(flattening,[],[f41])).
% 7.81/1.49  
% 7.81/1.49  fof(f73,plain,(
% 7.81/1.49    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X3) | k1_xboole_0 = X2 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 7.81/1.49    inference(cnf_transformation,[],[f42])).
% 7.81/1.49  
% 7.81/1.49  fof(f8,axiom,(
% 7.81/1.49    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 7.81/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.49  
% 7.81/1.49  fof(f27,plain,(
% 7.81/1.49    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 7.81/1.49    inference(ennf_transformation,[],[f8])).
% 7.81/1.49  
% 7.81/1.49  fof(f61,plain,(
% 7.81/1.49    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 7.81/1.49    inference(cnf_transformation,[],[f27])).
% 7.81/1.49  
% 7.81/1.49  fof(f5,axiom,(
% 7.81/1.49    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 7.81/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.49  
% 7.81/1.49  fof(f58,plain,(
% 7.81/1.49    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 7.81/1.49    inference(cnf_transformation,[],[f5])).
% 7.81/1.49  
% 7.81/1.49  fof(f83,plain,(
% 7.81/1.49    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 7.81/1.49    inference(definition_unfolding,[],[f58,f71])).
% 7.81/1.49  
% 7.81/1.49  fof(f66,plain,(
% 7.81/1.49    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.81/1.49    inference(cnf_transformation,[],[f47])).
% 7.81/1.49  
% 7.81/1.49  fof(f86,plain,(
% 7.81/1.49    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.81/1.49    inference(equality_resolution,[],[f66])).
% 7.81/1.49  
% 7.81/1.49  fof(f2,axiom,(
% 7.81/1.49    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 7.81/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.49  
% 7.81/1.49  fof(f22,plain,(
% 7.81/1.49    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 7.81/1.49    inference(ennf_transformation,[],[f2])).
% 7.81/1.49  
% 7.81/1.49  fof(f53,plain,(
% 7.81/1.49    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 7.81/1.49    inference(cnf_transformation,[],[f22])).
% 7.81/1.49  
% 7.81/1.49  fof(f17,axiom,(
% 7.81/1.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 7.81/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.49  
% 7.81/1.49  fof(f39,plain,(
% 7.81/1.49    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 7.81/1.49    inference(ennf_transformation,[],[f17])).
% 7.81/1.49  
% 7.81/1.49  fof(f40,plain,(
% 7.81/1.49    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.81/1.49    inference(flattening,[],[f39])).
% 7.81/1.49  
% 7.81/1.49  fof(f72,plain,(
% 7.81/1.49    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.81/1.49    inference(cnf_transformation,[],[f40])).
% 7.81/1.49  
% 7.81/1.49  fof(f10,axiom,(
% 7.81/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 7.81/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.49  
% 7.81/1.49  fof(f30,plain,(
% 7.81/1.49    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.81/1.49    inference(ennf_transformation,[],[f10])).
% 7.81/1.49  
% 7.81/1.49  fof(f63,plain,(
% 7.81/1.49    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.81/1.49    inference(cnf_transformation,[],[f30])).
% 7.81/1.49  
% 7.81/1.49  fof(f76,plain,(
% 7.81/1.49    v1_funct_2(sK3,sK1,sK2)),
% 7.81/1.49    inference(cnf_transformation,[],[f51])).
% 7.81/1.49  
% 7.81/1.49  fof(f79,plain,(
% 7.81/1.49    v1_funct_2(sK4,sK2,sK1)),
% 7.81/1.49    inference(cnf_transformation,[],[f51])).
% 7.81/1.49  
% 7.81/1.49  fof(f7,axiom,(
% 7.81/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.81/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.49  
% 7.81/1.49  fof(f21,plain,(
% 7.81/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 7.81/1.49    inference(pure_predicate_removal,[],[f7])).
% 7.81/1.49  
% 7.81/1.49  fof(f26,plain,(
% 7.81/1.49    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.81/1.49    inference(ennf_transformation,[],[f21])).
% 7.81/1.49  
% 7.81/1.49  fof(f60,plain,(
% 7.81/1.49    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.81/1.49    inference(cnf_transformation,[],[f26])).
% 7.81/1.49  
% 7.81/1.49  fof(f14,axiom,(
% 7.81/1.49    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 7.81/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.49  
% 7.81/1.49  fof(f35,plain,(
% 7.81/1.49    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 7.81/1.49    inference(ennf_transformation,[],[f14])).
% 7.81/1.49  
% 7.81/1.49  fof(f36,plain,(
% 7.81/1.49    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.81/1.49    inference(flattening,[],[f35])).
% 7.81/1.49  
% 7.81/1.49  fof(f48,plain,(
% 7.81/1.49    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.81/1.49    inference(nnf_transformation,[],[f36])).
% 7.81/1.49  
% 7.81/1.49  fof(f69,plain,(
% 7.81/1.49    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.81/1.49    inference(cnf_transformation,[],[f48])).
% 7.81/1.49  
% 7.81/1.49  fof(f87,plain,(
% 7.81/1.49    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 7.81/1.49    inference(equality_resolution,[],[f69])).
% 7.81/1.49  
% 7.81/1.49  fof(f6,axiom,(
% 7.81/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.81/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.49  
% 7.81/1.49  fof(f25,plain,(
% 7.81/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.81/1.49    inference(ennf_transformation,[],[f6])).
% 7.81/1.49  
% 7.81/1.49  fof(f59,plain,(
% 7.81/1.49    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.81/1.49    inference(cnf_transformation,[],[f25])).
% 7.81/1.49  
% 7.81/1.49  fof(f82,plain,(
% 7.81/1.49    ~v2_funct_2(sK4,sK1) | ~v2_funct_1(sK3)),
% 7.81/1.49    inference(cnf_transformation,[],[f51])).
% 7.81/1.49  
% 7.81/1.49  fof(f1,axiom,(
% 7.81/1.49    v1_xboole_0(k1_xboole_0)),
% 7.81/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.49  
% 7.81/1.49  fof(f52,plain,(
% 7.81/1.49    v1_xboole_0(k1_xboole_0)),
% 7.81/1.49    inference(cnf_transformation,[],[f1])).
% 7.81/1.49  
% 7.81/1.49  cnf(c_27,negated_conjecture,
% 7.81/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 7.81/1.49      inference(cnf_transformation,[],[f77]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1227,plain,
% 7.81/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 7.81/1.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_24,negated_conjecture,
% 7.81/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 7.81/1.49      inference(cnf_transformation,[],[f80]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1230,plain,
% 7.81/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 7.81/1.49      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_18,plain,
% 7.81/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.81/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.81/1.49      | ~ v1_funct_1(X0)
% 7.81/1.49      | ~ v1_funct_1(X3)
% 7.81/1.49      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 7.81/1.49      inference(cnf_transformation,[],[f70]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1235,plain,
% 7.81/1.49      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 7.81/1.49      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 7.81/1.49      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.81/1.49      | v1_funct_1(X4) != iProver_top
% 7.81/1.49      | v1_funct_1(X5) != iProver_top ),
% 7.81/1.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_2779,plain,
% 7.81/1.49      ( k1_partfun1(X0,X1,sK2,sK1,X2,sK4) = k5_relat_1(X2,sK4)
% 7.81/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.81/1.49      | v1_funct_1(X2) != iProver_top
% 7.81/1.49      | v1_funct_1(sK4) != iProver_top ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_1230,c_1235]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_26,negated_conjecture,
% 7.81/1.49      ( v1_funct_1(sK4) ),
% 7.81/1.49      inference(cnf_transformation,[],[f78]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_33,plain,
% 7.81/1.49      ( v1_funct_1(sK4) = iProver_top ),
% 7.81/1.49      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_3071,plain,
% 7.81/1.49      ( v1_funct_1(X2) != iProver_top
% 7.81/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.81/1.49      | k1_partfun1(X0,X1,sK2,sK1,X2,sK4) = k5_relat_1(X2,sK4) ),
% 7.81/1.49      inference(global_propositional_subsumption,
% 7.81/1.49                [status(thm)],
% 7.81/1.49                [c_2779,c_33]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_3072,plain,
% 7.81/1.49      ( k1_partfun1(X0,X1,sK2,sK1,X2,sK4) = k5_relat_1(X2,sK4)
% 7.81/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.81/1.49      | v1_funct_1(X2) != iProver_top ),
% 7.81/1.49      inference(renaming,[status(thm)],[c_3071]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_3081,plain,
% 7.81/1.49      ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k5_relat_1(sK3,sK4)
% 7.81/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_1227,c_3072]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_29,negated_conjecture,
% 7.81/1.49      ( v1_funct_1(sK3) ),
% 7.81/1.49      inference(cnf_transformation,[],[f75]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_30,plain,
% 7.81/1.49      ( v1_funct_1(sK3) = iProver_top ),
% 7.81/1.49      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_3383,plain,
% 7.81/1.49      ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 7.81/1.49      inference(global_propositional_subsumption,
% 7.81/1.49                [status(thm)],
% 7.81/1.49                [c_3081,c_30]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_23,negated_conjecture,
% 7.81/1.49      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) ),
% 7.81/1.49      inference(cnf_transformation,[],[f81]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1231,plain,
% 7.81/1.49      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) = iProver_top ),
% 7.81/1.49      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_3385,plain,
% 7.81/1.49      ( r2_relset_1(sK1,sK1,k5_relat_1(sK3,sK4),k6_partfun1(sK1)) = iProver_top ),
% 7.81/1.49      inference(demodulation,[status(thm)],[c_3383,c_1231]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_12,plain,
% 7.81/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.81/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.81/1.49      | k4_relset_1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 7.81/1.49      inference(cnf_transformation,[],[f64]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1239,plain,
% 7.81/1.49      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 7.81/1.49      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 7.81/1.49      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.81/1.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_2306,plain,
% 7.81/1.49      ( k4_relset_1(X0,X1,sK2,sK1,X2,sK4) = k5_relat_1(X2,sK4)
% 7.81/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_1230,c_1239]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_2569,plain,
% 7.81/1.49      ( k4_relset_1(sK1,sK2,sK2,sK1,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_1227,c_2306]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_10,plain,
% 7.81/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.81/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.81/1.49      | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) ),
% 7.81/1.49      inference(cnf_transformation,[],[f62]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1241,plain,
% 7.81/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.81/1.49      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 7.81/1.49      | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top ),
% 7.81/1.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_2878,plain,
% 7.81/1.49      ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
% 7.81/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 7.81/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_2569,c_1241]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_32,plain,
% 7.81/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 7.81/1.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_35,plain,
% 7.81/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 7.81/1.49      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_5401,plain,
% 7.81/1.49      ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 7.81/1.49      inference(global_propositional_subsumption,
% 7.81/1.49                [status(thm)],
% 7.81/1.49                [c_2878,c_32,c_35]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_14,plain,
% 7.81/1.49      ( ~ r2_relset_1(X0,X1,X2,X3)
% 7.81/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.81/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.81/1.49      | X3 = X2 ),
% 7.81/1.49      inference(cnf_transformation,[],[f65]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1237,plain,
% 7.81/1.49      ( X0 = X1
% 7.81/1.49      | r2_relset_1(X2,X3,X1,X0) != iProver_top
% 7.81/1.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 7.81/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top ),
% 7.81/1.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_5415,plain,
% 7.81/1.49      ( k5_relat_1(sK3,sK4) = X0
% 7.81/1.49      | r2_relset_1(sK1,sK1,k5_relat_1(sK3,sK4),X0) != iProver_top
% 7.81/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_5401,c_1237]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_19144,plain,
% 7.81/1.49      ( k5_relat_1(sK3,sK4) = k6_partfun1(sK1)
% 7.81/1.49      | m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_3385,c_5415]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_15,plain,
% 7.81/1.49      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 7.81/1.49      inference(cnf_transformation,[],[f85]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_56,plain,
% 7.81/1.49      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 7.81/1.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_58,plain,
% 7.81/1.49      ( m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 7.81/1.49      inference(instantiation,[status(thm)],[c_56]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_19583,plain,
% 7.81/1.49      ( k5_relat_1(sK3,sK4) = k6_partfun1(sK1) ),
% 7.81/1.49      inference(global_propositional_subsumption,
% 7.81/1.49                [status(thm)],
% 7.81/1.49                [c_19144,c_58]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_19600,plain,
% 7.81/1.49      ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k6_partfun1(sK1) ),
% 7.81/1.49      inference(demodulation,[status(thm)],[c_19583,c_3383]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_21,plain,
% 7.81/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.81/1.49      | ~ v1_funct_2(X3,X2,X4)
% 7.81/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.81/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
% 7.81/1.49      | ~ v1_funct_1(X3)
% 7.81/1.49      | ~ v1_funct_1(X0)
% 7.81/1.49      | v2_funct_1(X0)
% 7.81/1.49      | ~ v2_funct_1(k1_partfun1(X1,X2,X2,X4,X0,X3))
% 7.81/1.49      | k1_xboole_0 = X4 ),
% 7.81/1.49      inference(cnf_transformation,[],[f73]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1232,plain,
% 7.81/1.49      ( k1_xboole_0 = X0
% 7.81/1.49      | v1_funct_2(X1,X2,X3) != iProver_top
% 7.81/1.49      | v1_funct_2(X4,X3,X0) != iProver_top
% 7.81/1.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 7.81/1.49      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) != iProver_top
% 7.81/1.49      | v1_funct_1(X4) != iProver_top
% 7.81/1.49      | v1_funct_1(X1) != iProver_top
% 7.81/1.49      | v2_funct_1(X1) = iProver_top
% 7.81/1.49      | v2_funct_1(k1_partfun1(X2,X3,X3,X0,X1,X4)) != iProver_top ),
% 7.81/1.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_19678,plain,
% 7.81/1.49      ( sK1 = k1_xboole_0
% 7.81/1.49      | v1_funct_2(sK3,sK1,sK2) != iProver_top
% 7.81/1.49      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.81/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 7.81/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.81/1.49      | v1_funct_1(sK3) != iProver_top
% 7.81/1.49      | v1_funct_1(sK4) != iProver_top
% 7.81/1.49      | v2_funct_1(k6_partfun1(sK1)) != iProver_top
% 7.81/1.49      | v2_funct_1(sK3) = iProver_top ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_19600,c_1232]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1236,plain,
% 7.81/1.49      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 7.81/1.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_2305,plain,
% 7.81/1.49      ( k4_relset_1(X0,X1,X2,X2,X3,k6_partfun1(X2)) = k5_relat_1(X3,k6_partfun1(X2))
% 7.81/1.49      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_1236,c_1239]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_7875,plain,
% 7.81/1.49      ( k4_relset_1(sK1,sK2,X0,X0,sK3,k6_partfun1(X0)) = k5_relat_1(sK3,k6_partfun1(X0)) ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_1227,c_2305]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_8190,plain,
% 7.81/1.49      ( m1_subset_1(k5_relat_1(sK3,k6_partfun1(X0)),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
% 7.81/1.49      | m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 7.81/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_7875,c_1241]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_11142,plain,
% 7.81/1.49      ( m1_subset_1(k5_relat_1(sK3,k6_partfun1(X0)),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top ),
% 7.81/1.49      inference(global_propositional_subsumption,
% 7.81/1.49                [status(thm)],
% 7.81/1.49                [c_8190,c_32,c_56]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_9,plain,
% 7.81/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.81/1.49      | ~ v1_xboole_0(X1)
% 7.81/1.49      | v1_xboole_0(X0) ),
% 7.81/1.49      inference(cnf_transformation,[],[f61]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1242,plain,
% 7.81/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.81/1.49      | v1_xboole_0(X1) != iProver_top
% 7.81/1.49      | v1_xboole_0(X0) = iProver_top ),
% 7.81/1.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_11149,plain,
% 7.81/1.49      ( v1_xboole_0(k5_relat_1(sK3,k6_partfun1(X0))) = iProver_top
% 7.81/1.49      | v1_xboole_0(sK1) != iProver_top ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_11142,c_1242]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_5,plain,
% 7.81/1.49      ( v2_funct_1(k6_partfun1(X0)) ),
% 7.81/1.49      inference(cnf_transformation,[],[f83]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_84,plain,
% 7.81/1.49      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 7.81/1.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_86,plain,
% 7.81/1.49      ( v2_funct_1(k6_partfun1(sK1)) = iProver_top ),
% 7.81/1.49      inference(instantiation,[status(thm)],[c_84]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_772,plain,
% 7.81/1.49      ( ~ v2_funct_1(X0) | v2_funct_1(X1) | X1 != X0 ),
% 7.81/1.49      theory(equality) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1294,plain,
% 7.81/1.49      ( ~ v2_funct_1(X0) | v2_funct_1(sK3) | sK3 != X0 ),
% 7.81/1.49      inference(instantiation,[status(thm)],[c_772]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1301,plain,
% 7.81/1.49      ( ~ v2_funct_1(k6_partfun1(X0))
% 7.81/1.49      | v2_funct_1(sK3)
% 7.81/1.49      | sK3 != k6_partfun1(X0) ),
% 7.81/1.49      inference(instantiation,[status(thm)],[c_1294]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1302,plain,
% 7.81/1.49      ( sK3 != k6_partfun1(X0)
% 7.81/1.49      | v2_funct_1(k6_partfun1(X0)) != iProver_top
% 7.81/1.49      | v2_funct_1(sK3) = iProver_top ),
% 7.81/1.49      inference(predicate_to_equality,[status(thm)],[c_1301]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1304,plain,
% 7.81/1.49      ( sK3 != k6_partfun1(sK1)
% 7.81/1.49      | v2_funct_1(k6_partfun1(sK1)) != iProver_top
% 7.81/1.49      | v2_funct_1(sK3) = iProver_top ),
% 7.81/1.49      inference(instantiation,[status(thm)],[c_1302]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_767,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1375,plain,
% 7.81/1.49      ( k6_partfun1(X0) != X1 | sK3 != X1 | sK3 = k6_partfun1(X0) ),
% 7.81/1.49      inference(instantiation,[status(thm)],[c_767]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1637,plain,
% 7.81/1.49      ( k6_partfun1(X0) != sK3 | sK3 = k6_partfun1(X0) | sK3 != sK3 ),
% 7.81/1.49      inference(instantiation,[status(thm)],[c_1375]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1638,plain,
% 7.81/1.49      ( k6_partfun1(sK1) != sK3 | sK3 = k6_partfun1(sK1) | sK3 != sK3 ),
% 7.81/1.49      inference(instantiation,[status(thm)],[c_1637]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1688,plain,
% 7.81/1.49      ( ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.81/1.49      | ~ v1_xboole_0(X1)
% 7.81/1.49      | v1_xboole_0(k6_partfun1(X0)) ),
% 7.81/1.49      inference(instantiation,[status(thm)],[c_9]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1704,plain,
% 7.81/1.49      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.81/1.49      | v1_xboole_0(X1) != iProver_top
% 7.81/1.49      | v1_xboole_0(k6_partfun1(X0)) = iProver_top ),
% 7.81/1.49      inference(predicate_to_equality,[status(thm)],[c_1688]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1706,plain,
% 7.81/1.49      ( m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 7.81/1.49      | v1_xboole_0(k6_partfun1(sK1)) = iProver_top
% 7.81/1.49      | v1_xboole_0(sK1) != iProver_top ),
% 7.81/1.49      inference(instantiation,[status(thm)],[c_1704]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1437,plain,
% 7.81/1.49      ( ~ r2_relset_1(X0,X1,sK3,X2)
% 7.81/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.81/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.81/1.49      | X2 = sK3 ),
% 7.81/1.49      inference(instantiation,[status(thm)],[c_14]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1614,plain,
% 7.81/1.49      ( ~ r2_relset_1(sK1,sK2,sK3,X0)
% 7.81/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 7.81/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 7.81/1.49      | X0 = sK3 ),
% 7.81/1.49      inference(instantiation,[status(thm)],[c_1437]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1723,plain,
% 7.81/1.49      ( ~ r2_relset_1(sK1,sK2,sK3,sK3)
% 7.81/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 7.81/1.49      | sK3 = sK3 ),
% 7.81/1.49      inference(instantiation,[status(thm)],[c_1614]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_13,plain,
% 7.81/1.49      ( r2_relset_1(X0,X1,X2,X2)
% 7.81/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 7.81/1.49      inference(cnf_transformation,[],[f86]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1806,plain,
% 7.81/1.49      ( r2_relset_1(sK1,sK2,sK3,sK3)
% 7.81/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 7.81/1.49      inference(instantiation,[status(thm)],[c_13]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1,plain,
% 7.81/1.49      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X1 = X0 ),
% 7.81/1.49      inference(cnf_transformation,[],[f53]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1432,plain,
% 7.81/1.49      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(sK3) | X0 = sK3 ),
% 7.81/1.49      inference(instantiation,[status(thm)],[c_1]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_2037,plain,
% 7.81/1.49      ( ~ v1_xboole_0(k6_partfun1(X0))
% 7.81/1.49      | ~ v1_xboole_0(sK3)
% 7.81/1.49      | k6_partfun1(X0) = sK3 ),
% 7.81/1.49      inference(instantiation,[status(thm)],[c_1432]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_2043,plain,
% 7.81/1.49      ( k6_partfun1(X0) = sK3
% 7.81/1.49      | v1_xboole_0(k6_partfun1(X0)) != iProver_top
% 7.81/1.49      | v1_xboole_0(sK3) != iProver_top ),
% 7.81/1.49      inference(predicate_to_equality,[status(thm)],[c_2037]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_2045,plain,
% 7.81/1.49      ( k6_partfun1(sK1) = sK3
% 7.81/1.49      | v1_xboole_0(k6_partfun1(sK1)) != iProver_top
% 7.81/1.49      | v1_xboole_0(sK3) != iProver_top ),
% 7.81/1.49      inference(instantiation,[status(thm)],[c_2043]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_2229,plain,
% 7.81/1.49      ( v1_xboole_0(sK3) = iProver_top
% 7.81/1.49      | v1_xboole_0(sK1) != iProver_top ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_1227,c_1242]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_19,plain,
% 7.81/1.49      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 7.81/1.49      | ~ v1_funct_2(X2,X0,X1)
% 7.81/1.49      | ~ v1_funct_2(X3,X1,X0)
% 7.81/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 7.81/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.81/1.49      | ~ v1_funct_1(X2)
% 7.81/1.49      | ~ v1_funct_1(X3)
% 7.81/1.49      | k2_relset_1(X1,X0,X3) = X0 ),
% 7.81/1.49      inference(cnf_transformation,[],[f72]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1234,plain,
% 7.81/1.49      ( k2_relset_1(X0,X1,X2) = X1
% 7.81/1.49      | r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) != iProver_top
% 7.81/1.49      | v1_funct_2(X3,X1,X0) != iProver_top
% 7.81/1.49      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.81/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.81/1.49      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
% 7.81/1.49      | v1_funct_1(X2) != iProver_top
% 7.81/1.49      | v1_funct_1(X3) != iProver_top ),
% 7.81/1.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_2797,plain,
% 7.81/1.49      ( k2_relset_1(sK2,sK1,sK4) = sK1
% 7.81/1.49      | v1_funct_2(sK3,sK1,sK2) != iProver_top
% 7.81/1.49      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.81/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 7.81/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.81/1.49      | v1_funct_1(sK3) != iProver_top
% 7.81/1.49      | v1_funct_1(sK4) != iProver_top ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_1231,c_1234]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_11,plain,
% 7.81/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.81/1.49      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 7.81/1.49      inference(cnf_transformation,[],[f63]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1240,plain,
% 7.81/1.49      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 7.81/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.81/1.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_2062,plain,
% 7.81/1.49      ( k2_relset_1(sK2,sK1,sK4) = k2_relat_1(sK4) ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_1230,c_1240]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_2798,plain,
% 7.81/1.49      ( k2_relat_1(sK4) = sK1
% 7.81/1.49      | v1_funct_2(sK3,sK1,sK2) != iProver_top
% 7.81/1.49      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.81/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 7.81/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.81/1.49      | v1_funct_1(sK3) != iProver_top
% 7.81/1.49      | v1_funct_1(sK4) != iProver_top ),
% 7.81/1.49      inference(demodulation,[status(thm)],[c_2797,c_2062]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_28,negated_conjecture,
% 7.81/1.49      ( v1_funct_2(sK3,sK1,sK2) ),
% 7.81/1.49      inference(cnf_transformation,[],[f76]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_31,plain,
% 7.81/1.49      ( v1_funct_2(sK3,sK1,sK2) = iProver_top ),
% 7.81/1.49      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_25,negated_conjecture,
% 7.81/1.49      ( v1_funct_2(sK4,sK2,sK1) ),
% 7.81/1.49      inference(cnf_transformation,[],[f79]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_34,plain,
% 7.81/1.49      ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
% 7.81/1.49      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_7860,plain,
% 7.81/1.49      ( k2_relat_1(sK4) = sK1 ),
% 7.81/1.49      inference(global_propositional_subsumption,
% 7.81/1.49                [status(thm)],
% 7.81/1.49                [c_2798,c_30,c_31,c_32,c_33,c_34,c_35]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_8,plain,
% 7.81/1.49      ( v5_relat_1(X0,X1)
% 7.81/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 7.81/1.49      inference(cnf_transformation,[],[f60]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_16,plain,
% 7.81/1.49      ( v2_funct_2(X0,k2_relat_1(X0))
% 7.81/1.49      | ~ v5_relat_1(X0,k2_relat_1(X0))
% 7.81/1.49      | ~ v1_relat_1(X0) ),
% 7.81/1.49      inference(cnf_transformation,[],[f87]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_350,plain,
% 7.81/1.49      ( v2_funct_2(X0,k2_relat_1(X0))
% 7.81/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 7.81/1.49      | ~ v1_relat_1(X0)
% 7.81/1.49      | X0 != X1
% 7.81/1.49      | k2_relat_1(X0) != X3 ),
% 7.81/1.49      inference(resolution_lifted,[status(thm)],[c_8,c_16]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_351,plain,
% 7.81/1.49      ( v2_funct_2(X0,k2_relat_1(X0))
% 7.81/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
% 7.81/1.49      | ~ v1_relat_1(X0) ),
% 7.81/1.49      inference(unflattening,[status(thm)],[c_350]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_7,plain,
% 7.81/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.81/1.49      | v1_relat_1(X0) ),
% 7.81/1.49      inference(cnf_transformation,[],[f59]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_361,plain,
% 7.81/1.49      ( v2_funct_2(X0,k2_relat_1(X0))
% 7.81/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0)))) ),
% 7.81/1.49      inference(forward_subsumption_resolution,[status(thm)],[c_351,c_7]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_22,negated_conjecture,
% 7.81/1.49      ( ~ v2_funct_2(sK4,sK1) | ~ v2_funct_1(sK3) ),
% 7.81/1.49      inference(cnf_transformation,[],[f82]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_376,plain,
% 7.81/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
% 7.81/1.49      | ~ v2_funct_1(sK3)
% 7.81/1.49      | k2_relat_1(X0) != sK1
% 7.81/1.49      | sK4 != X0 ),
% 7.81/1.49      inference(resolution_lifted,[status(thm)],[c_361,c_22]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_377,plain,
% 7.81/1.49      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK4))))
% 7.81/1.49      | ~ v2_funct_1(sK3)
% 7.81/1.49      | k2_relat_1(sK4) != sK1 ),
% 7.81/1.49      inference(unflattening,[status(thm)],[c_376]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_764,plain,
% 7.81/1.49      ( ~ v2_funct_1(sK3) | sP0_iProver_split | k2_relat_1(sK4) != sK1 ),
% 7.81/1.49      inference(splitting,
% 7.81/1.49                [splitting(split),new_symbols(definition,[])],
% 7.81/1.49                [c_377]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1223,plain,
% 7.81/1.49      ( k2_relat_1(sK4) != sK1
% 7.81/1.49      | v2_funct_1(sK3) != iProver_top
% 7.81/1.49      | sP0_iProver_split = iProver_top ),
% 7.81/1.49      inference(predicate_to_equality,[status(thm)],[c_764]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_7864,plain,
% 7.81/1.49      ( sK1 != sK1
% 7.81/1.49      | v2_funct_1(sK3) != iProver_top
% 7.81/1.49      | sP0_iProver_split = iProver_top ),
% 7.81/1.49      inference(demodulation,[status(thm)],[c_7860,c_1223]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_7865,plain,
% 7.81/1.49      ( v2_funct_1(sK3) != iProver_top
% 7.81/1.49      | sP0_iProver_split = iProver_top ),
% 7.81/1.49      inference(equality_resolution_simp,[status(thm)],[c_7864]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_763,plain,
% 7.81/1.49      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK4))))
% 7.81/1.49      | ~ sP0_iProver_split ),
% 7.81/1.49      inference(splitting,
% 7.81/1.49                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 7.81/1.49                [c_377]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_1224,plain,
% 7.81/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK4)))) != iProver_top
% 7.81/1.49      | sP0_iProver_split != iProver_top ),
% 7.81/1.49      inference(predicate_to_equality,[status(thm)],[c_763]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_7863,plain,
% 7.81/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 7.81/1.49      | sP0_iProver_split != iProver_top ),
% 7.81/1.49      inference(demodulation,[status(thm)],[c_7860,c_1224]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_9076,plain,
% 7.81/1.49      ( sP0_iProver_split != iProver_top ),
% 7.81/1.49      inference(superposition,[status(thm)],[c_1230,c_7863]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_11442,plain,
% 7.81/1.49      ( v1_xboole_0(sK1) != iProver_top ),
% 7.81/1.49      inference(global_propositional_subsumption,
% 7.81/1.49                [status(thm)],
% 7.81/1.49                [c_11149,c_27,c_58,c_86,c_1304,c_1638,c_1706,c_1723,
% 7.81/1.49                 c_1806,c_2045,c_2229,c_7865,c_9076]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_768,plain,
% 7.81/1.49      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 7.81/1.49      theory(equality) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_2593,plain,
% 7.81/1.49      ( v1_xboole_0(X0)
% 7.81/1.49      | ~ v1_xboole_0(k1_xboole_0)
% 7.81/1.49      | X0 != k1_xboole_0 ),
% 7.81/1.49      inference(instantiation,[status(thm)],[c_768]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_2594,plain,
% 7.81/1.49      ( X0 != k1_xboole_0
% 7.81/1.49      | v1_xboole_0(X0) = iProver_top
% 7.81/1.49      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 7.81/1.49      inference(predicate_to_equality,[status(thm)],[c_2593]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_2596,plain,
% 7.81/1.49      ( sK1 != k1_xboole_0
% 7.81/1.49      | v1_xboole_0(sK1) = iProver_top
% 7.81/1.49      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 7.81/1.49      inference(instantiation,[status(thm)],[c_2594]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_0,plain,
% 7.81/1.49      ( v1_xboole_0(k1_xboole_0) ),
% 7.81/1.49      inference(cnf_transformation,[],[f52]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(c_97,plain,
% 7.81/1.49      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 7.81/1.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.81/1.49  
% 7.81/1.49  cnf(contradiction,plain,
% 7.81/1.49      ( $false ),
% 7.81/1.49      inference(minisat,
% 7.81/1.49                [status(thm)],
% 7.81/1.49                [c_19678,c_11442,c_9076,c_7865,c_2596,c_97,c_86,c_35,
% 7.81/1.49                 c_34,c_33,c_32,c_31,c_30]) ).
% 7.81/1.49  
% 7.81/1.49  
% 7.81/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.81/1.49  
% 7.81/1.49  ------                               Statistics
% 7.81/1.49  
% 7.81/1.49  ------ General
% 7.81/1.49  
% 7.81/1.49  abstr_ref_over_cycles:                  0
% 7.81/1.49  abstr_ref_under_cycles:                 0
% 7.81/1.49  gc_basic_clause_elim:                   0
% 7.81/1.49  forced_gc_time:                         0
% 7.81/1.49  parsing_time:                           0.01
% 7.81/1.49  unif_index_cands_time:                  0.
% 7.81/1.49  unif_index_add_time:                    0.
% 7.81/1.49  orderings_time:                         0.
% 7.81/1.49  out_proof_time:                         0.017
% 7.81/1.49  total_time:                             0.703
% 7.81/1.49  num_of_symbols:                         55
% 7.81/1.49  num_of_terms:                           31631
% 7.81/1.49  
% 7.81/1.49  ------ Preprocessing
% 7.81/1.49  
% 7.81/1.49  num_of_splits:                          1
% 7.81/1.49  num_of_split_atoms:                     1
% 7.81/1.49  num_of_reused_defs:                     0
% 7.81/1.49  num_eq_ax_congr_red:                    38
% 7.81/1.49  num_of_sem_filtered_clauses:            1
% 7.81/1.49  num_of_subtypes:                        0
% 7.81/1.49  monotx_restored_types:                  0
% 7.81/1.49  sat_num_of_epr_types:                   0
% 7.81/1.49  sat_num_of_non_cyclic_types:            0
% 7.81/1.49  sat_guarded_non_collapsed_types:        0
% 7.81/1.49  num_pure_diseq_elim:                    0
% 7.81/1.49  simp_replaced_by:                       0
% 7.81/1.49  res_preprocessed:                       134
% 7.81/1.49  prep_upred:                             0
% 7.81/1.49  prep_unflattend:                        29
% 7.81/1.49  smt_new_axioms:                         0
% 7.81/1.49  pred_elim_cands:                        6
% 7.81/1.49  pred_elim:                              3
% 7.81/1.49  pred_elim_cl:                           5
% 7.81/1.49  pred_elim_cycles:                       5
% 7.81/1.49  merged_defs:                            0
% 7.81/1.49  merged_defs_ncl:                        0
% 7.81/1.49  bin_hyper_res:                          0
% 7.81/1.49  prep_cycles:                            4
% 7.81/1.49  pred_elim_time:                         0.007
% 7.81/1.49  splitting_time:                         0.
% 7.81/1.49  sem_filter_time:                        0.
% 7.81/1.49  monotx_time:                            0.
% 7.81/1.49  subtype_inf_time:                       0.
% 7.81/1.49  
% 7.81/1.49  ------ Problem properties
% 7.81/1.49  
% 7.81/1.49  clauses:                                26
% 7.81/1.49  conjectures:                            7
% 7.81/1.49  epr:                                    6
% 7.81/1.49  horn:                                   24
% 7.81/1.49  ground:                                 9
% 7.81/1.49  unary:                                  10
% 7.81/1.49  binary:                                 5
% 7.81/1.49  lits:                                   72
% 7.81/1.49  lits_eq:                                8
% 7.81/1.49  fd_pure:                                0
% 7.81/1.49  fd_pseudo:                              0
% 7.81/1.49  fd_cond:                                1
% 7.81/1.49  fd_pseudo_cond:                         2
% 7.81/1.49  ac_symbols:                             0
% 7.81/1.49  
% 7.81/1.49  ------ Propositional Solver
% 7.81/1.49  
% 7.81/1.49  prop_solver_calls:                      34
% 7.81/1.49  prop_fast_solver_calls:                 1374
% 7.81/1.49  smt_solver_calls:                       0
% 7.81/1.49  smt_fast_solver_calls:                  0
% 7.81/1.49  prop_num_of_clauses:                    9675
% 7.81/1.49  prop_preprocess_simplified:             14850
% 7.81/1.49  prop_fo_subsumed:                       32
% 7.81/1.49  prop_solver_time:                       0.
% 7.81/1.49  smt_solver_time:                        0.
% 7.81/1.49  smt_fast_solver_time:                   0.
% 7.81/1.49  prop_fast_solver_time:                  0.
% 7.81/1.49  prop_unsat_core_time:                   0.001
% 7.81/1.49  
% 7.81/1.49  ------ QBF
% 7.81/1.49  
% 7.81/1.49  qbf_q_res:                              0
% 7.81/1.49  qbf_num_tautologies:                    0
% 7.81/1.49  qbf_prep_cycles:                        0
% 7.81/1.49  
% 7.81/1.49  ------ BMC1
% 7.81/1.49  
% 7.81/1.49  bmc1_current_bound:                     -1
% 7.81/1.49  bmc1_last_solved_bound:                 -1
% 7.81/1.49  bmc1_unsat_core_size:                   -1
% 7.81/1.49  bmc1_unsat_core_parents_size:           -1
% 7.81/1.49  bmc1_merge_next_fun:                    0
% 7.81/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.81/1.49  
% 7.81/1.49  ------ Instantiation
% 7.81/1.49  
% 7.81/1.49  inst_num_of_clauses:                    2025
% 7.81/1.49  inst_num_in_passive:                    626
% 7.81/1.49  inst_num_in_active:                     1038
% 7.81/1.49  inst_num_in_unprocessed:                361
% 7.81/1.49  inst_num_of_loops:                      1230
% 7.81/1.49  inst_num_of_learning_restarts:          0
% 7.81/1.49  inst_num_moves_active_passive:          186
% 7.81/1.49  inst_lit_activity:                      0
% 7.81/1.49  inst_lit_activity_moves:                1
% 7.81/1.49  inst_num_tautologies:                   0
% 7.81/1.49  inst_num_prop_implied:                  0
% 7.81/1.49  inst_num_existing_simplified:           0
% 7.81/1.49  inst_num_eq_res_simplified:             0
% 7.81/1.49  inst_num_child_elim:                    0
% 7.81/1.49  inst_num_of_dismatching_blockings:      2087
% 7.81/1.49  inst_num_of_non_proper_insts:           3298
% 7.81/1.49  inst_num_of_duplicates:                 0
% 7.81/1.49  inst_inst_num_from_inst_to_res:         0
% 7.81/1.49  inst_dismatching_checking_time:         0.
% 7.81/1.49  
% 7.81/1.49  ------ Resolution
% 7.81/1.49  
% 7.81/1.49  res_num_of_clauses:                     0
% 7.81/1.49  res_num_in_passive:                     0
% 7.81/1.49  res_num_in_active:                      0
% 7.81/1.49  res_num_of_loops:                       138
% 7.81/1.49  res_forward_subset_subsumed:            103
% 7.81/1.49  res_backward_subset_subsumed:           0
% 7.81/1.49  res_forward_subsumed:                   0
% 7.81/1.49  res_backward_subsumed:                  0
% 7.81/1.49  res_forward_subsumption_resolution:     2
% 7.81/1.49  res_backward_subsumption_resolution:    0
% 7.81/1.49  res_clause_to_clause_subsumption:       2481
% 7.81/1.49  res_orphan_elimination:                 0
% 7.81/1.49  res_tautology_del:                      124
% 7.81/1.49  res_num_eq_res_simplified:              0
% 7.81/1.49  res_num_sel_changes:                    0
% 7.81/1.49  res_moves_from_active_to_pass:          0
% 7.81/1.49  
% 7.81/1.49  ------ Superposition
% 7.81/1.49  
% 7.81/1.49  sup_time_total:                         0.
% 7.81/1.49  sup_time_generating:                    0.
% 7.81/1.49  sup_time_sim_full:                      0.
% 7.81/1.49  sup_time_sim_immed:                     0.
% 7.81/1.49  
% 7.81/1.49  sup_num_of_clauses:                     1043
% 7.81/1.49  sup_num_in_active:                      217
% 7.81/1.49  sup_num_in_passive:                     826
% 7.81/1.49  sup_num_of_loops:                       244
% 7.81/1.49  sup_fw_superposition:                   845
% 7.81/1.49  sup_bw_superposition:                   414
% 7.81/1.49  sup_immediate_simplified:               473
% 7.81/1.49  sup_given_eliminated:                   1
% 7.81/1.49  comparisons_done:                       0
% 7.81/1.49  comparisons_avoided:                    1
% 7.81/1.49  
% 7.81/1.49  ------ Simplifications
% 7.81/1.49  
% 7.81/1.49  
% 7.81/1.49  sim_fw_subset_subsumed:                 69
% 7.81/1.49  sim_bw_subset_subsumed:                 5
% 7.81/1.49  sim_fw_subsumed:                        38
% 7.81/1.49  sim_bw_subsumed:                        4
% 7.81/1.49  sim_fw_subsumption_res:                 0
% 7.81/1.49  sim_bw_subsumption_res:                 0
% 7.81/1.49  sim_tautology_del:                      2
% 7.81/1.49  sim_eq_tautology_del:                   38
% 7.81/1.49  sim_eq_res_simp:                        1
% 7.81/1.49  sim_fw_demodulated:                     95
% 7.81/1.49  sim_bw_demodulated:                     35
% 7.81/1.49  sim_light_normalised:                   287
% 7.81/1.49  sim_joinable_taut:                      0
% 7.81/1.49  sim_joinable_simp:                      0
% 7.81/1.49  sim_ac_normalised:                      0
% 7.81/1.49  sim_smt_subsumption:                    0
% 7.81/1.49  
%------------------------------------------------------------------------------
