%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:01:49 EST 2020

% Result     : Theorem 7.65s
% Output     : CNFRefutation 7.65s
% Verified   : 
% Statistics : Number of formulae       :  185 ( 947 expanded)
%              Number of clauses        :  111 ( 291 expanded)
%              Number of leaves         :   22 ( 233 expanded)
%              Depth                    :   18
%              Number of atoms          :  589 (5861 expanded)
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

fof(f76,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f51])).

fof(f79,plain,(
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

fof(f69,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f77,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f74,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f80,plain,(
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

fof(f63,plain,(
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

fof(f61,plain,(
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

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f13,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f16,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f83,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f66,f70])).

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

fof(f72,plain,(
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

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f82,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f57,f70])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f84,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f65])).

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

fof(f71,plain,(
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

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f75,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f78,plain,(
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

fof(f59,plain,(
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

fof(f68,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f85,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f68])).

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

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f81,plain,
    ( ~ v2_funct_2(sK4,sK1)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1253,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1256,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1261,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2805,plain,
    ( k1_partfun1(X0,X1,sK2,sK1,X2,sK4) = k5_relat_1(X2,sK4)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1256,c_1261])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_32,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3097,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK2,sK1,X2,sK4) = k5_relat_1(X2,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2805,c_32])).

cnf(c_3098,plain,
    ( k1_partfun1(X0,X1,sK2,sK1,X2,sK4) = k5_relat_1(X2,sK4)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_3097])).

cnf(c_3107,plain,
    ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k5_relat_1(sK3,sK4)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1253,c_3098])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_29,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3409,plain,
    ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3107,c_29])).

cnf(c_22,negated_conjecture,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1257,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3411,plain,
    ( r2_relset_1(sK1,sK1,k5_relat_1(sK3,sK4),k6_partfun1(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3409,c_1257])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | k4_relset_1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1265,plain,
    ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2332,plain,
    ( k4_relset_1(X0,X1,sK2,sK1,X2,sK4) = k5_relat_1(X2,sK4)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1256,c_1265])).

cnf(c_2595,plain,
    ( k4_relset_1(sK1,sK2,sK2,sK1,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(superposition,[status(thm)],[c_1253,c_2332])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1267,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2904,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2595,c_1267])).

cnf(c_31,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_34,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_5427,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2904,c_31,c_34])).

cnf(c_13,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1263,plain,
    ( X0 = X1
    | r2_relset_1(X2,X3,X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_5441,plain,
    ( k5_relat_1(sK3,sK4) = X0
    | r2_relset_1(sK1,sK1,k5_relat_1(sK3,sK4),X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5427,c_1263])).

cnf(c_19170,plain,
    ( k5_relat_1(sK3,sK4) = k6_partfun1(sK1)
    | m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3411,c_5441])).

cnf(c_14,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_55,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_57,plain,
    ( m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_55])).

cnf(c_19609,plain,
    ( k5_relat_1(sK3,sK4) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19170,c_57])).

cnf(c_19626,plain,
    ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k6_partfun1(sK1) ),
    inference(demodulation,[status(thm)],[c_19609,c_3409])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ v2_funct_1(k1_partfun1(X1,X2,X2,X4,X0,X3))
    | k1_xboole_0 = X4 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1258,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X3) != iProver_top
    | v1_funct_2(X4,X3,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(X2,X3,X3,X0,X1,X4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_19704,plain,
    ( sK1 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK2) != iProver_top
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_funct_1(k6_partfun1(sK1)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_19626,c_1258])).

cnf(c_1262,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2331,plain,
    ( k4_relset_1(X0,X1,X2,X2,X3,k6_partfun1(X2)) = k5_relat_1(X3,k6_partfun1(X2))
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1262,c_1265])).

cnf(c_7901,plain,
    ( k4_relset_1(sK1,sK2,X0,X0,sK3,k6_partfun1(X0)) = k5_relat_1(sK3,k6_partfun1(X0)) ),
    inference(superposition,[status(thm)],[c_1253,c_2331])).

cnf(c_8216,plain,
    ( m1_subset_1(k5_relat_1(sK3,k6_partfun1(X0)),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
    | m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7901,c_1267])).

cnf(c_11168,plain,
    ( m1_subset_1(k5_relat_1(sK3,k6_partfun1(X0)),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8216,c_31,c_55])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1268,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_11175,plain,
    ( v1_xboole_0(k5_relat_1(sK3,k6_partfun1(X0))) = iProver_top
    | v1_xboole_0(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_11168,c_1268])).

cnf(c_5,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_80,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_82,plain,
    ( v2_funct_1(k6_partfun1(sK1)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_80])).

cnf(c_798,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1320,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(sK3)
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_798])).

cnf(c_1327,plain,
    ( ~ v2_funct_1(k6_partfun1(X0))
    | v2_funct_1(sK3)
    | sK3 != k6_partfun1(X0) ),
    inference(instantiation,[status(thm)],[c_1320])).

cnf(c_1328,plain,
    ( sK3 != k6_partfun1(X0)
    | v2_funct_1(k6_partfun1(X0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1327])).

cnf(c_1330,plain,
    ( sK3 != k6_partfun1(sK1)
    | v2_funct_1(k6_partfun1(sK1)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1328])).

cnf(c_793,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1401,plain,
    ( k6_partfun1(X0) != X1
    | sK3 != X1
    | sK3 = k6_partfun1(X0) ),
    inference(instantiation,[status(thm)],[c_793])).

cnf(c_1663,plain,
    ( k6_partfun1(X0) != sK3
    | sK3 = k6_partfun1(X0)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1401])).

cnf(c_1664,plain,
    ( k6_partfun1(sK1) != sK3
    | sK3 = k6_partfun1(sK1)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1663])).

cnf(c_1714,plain,
    ( ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(k6_partfun1(X0)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1730,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1714])).

cnf(c_1732,plain,
    ( m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_xboole_0(k6_partfun1(sK1)) = iProver_top
    | v1_xboole_0(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1730])).

cnf(c_1463,plain,
    ( ~ r2_relset_1(X0,X1,sK3,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X2 = sK3 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1640,plain,
    ( ~ r2_relset_1(sK1,sK2,sK3,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | X0 = sK3 ),
    inference(instantiation,[status(thm)],[c_1463])).

cnf(c_1749,plain,
    ( ~ r2_relset_1(sK1,sK2,sK3,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1640])).

cnf(c_12,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1832,plain,
    ( r2_relset_1(sK1,sK2,sK3,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1458,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(sK3)
    | X0 = sK3 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2063,plain,
    ( ~ v1_xboole_0(k6_partfun1(X0))
    | ~ v1_xboole_0(sK3)
    | k6_partfun1(X0) = sK3 ),
    inference(instantiation,[status(thm)],[c_1458])).

cnf(c_2069,plain,
    ( k6_partfun1(X0) = sK3
    | v1_xboole_0(k6_partfun1(X0)) != iProver_top
    | v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2063])).

cnf(c_2071,plain,
    ( k6_partfun1(sK1) = sK3
    | v1_xboole_0(k6_partfun1(sK1)) != iProver_top
    | v1_xboole_0(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2069])).

cnf(c_2255,plain,
    ( v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1253,c_1268])).

cnf(c_18,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1260,plain,
    ( k2_relset_1(X0,X1,X2) = X1
    | r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) != iProver_top
    | v1_funct_2(X3,X1,X0) != iProver_top
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2823,plain,
    ( k2_relset_1(sK2,sK1,sK4) = sK1
    | v1_funct_2(sK3,sK1,sK2) != iProver_top
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1257,c_1260])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1266,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2088,plain,
    ( k2_relset_1(sK2,sK1,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1256,c_1266])).

cnf(c_2824,plain,
    ( k2_relat_1(sK4) = sK1
    | v1_funct_2(sK3,sK1,sK2) != iProver_top
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2823,c_2088])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_30,plain,
    ( v1_funct_2(sK3,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_33,plain,
    ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_7886,plain,
    ( k2_relat_1(sK4) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2824,c_29,c_30,c_31,c_32,c_33,c_34])).

cnf(c_7,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_15,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_376,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X0)
    | X0 != X1
    | k2_relat_1(X0) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_15])).

cnf(c_377,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_376])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_387,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0)))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_377,c_6])).

cnf(c_21,negated_conjecture,
    ( ~ v2_funct_2(sK4,sK1)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_402,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
    | ~ v2_funct_1(sK3)
    | k2_relat_1(X0) != sK1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_387,c_21])).

cnf(c_403,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK4))))
    | ~ v2_funct_1(sK3)
    | k2_relat_1(sK4) != sK1 ),
    inference(unflattening,[status(thm)],[c_402])).

cnf(c_790,plain,
    ( ~ v2_funct_1(sK3)
    | sP0_iProver_split
    | k2_relat_1(sK4) != sK1 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_403])).

cnf(c_1249,plain,
    ( k2_relat_1(sK4) != sK1
    | v2_funct_1(sK3) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_790])).

cnf(c_7890,plain,
    ( sK1 != sK1
    | v2_funct_1(sK3) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_7886,c_1249])).

cnf(c_7891,plain,
    ( v2_funct_1(sK3) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_7890])).

cnf(c_789,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK4))))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_403])).

cnf(c_1250,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK4)))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_789])).

cnf(c_7889,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(demodulation,[status(thm)],[c_7886,c_1250])).

cnf(c_9102,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_1256,c_7889])).

cnf(c_11468,plain,
    ( v1_xboole_0(sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11175,c_26,c_57,c_82,c_1330,c_1664,c_1732,c_1749,c_1832,c_2071,c_2255,c_7891,c_9102])).

cnf(c_794,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2619,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(k1_xboole_0)
    | X0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_794])).

cnf(c_2620,plain,
    ( X0 != k1_xboole_0
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2619])).

cnf(c_2622,plain,
    ( sK1 != k1_xboole_0
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2620])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_93,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_19704,c_11468,c_9102,c_7891,c_2622,c_93,c_82,c_34,c_33,c_32,c_31,c_30,c_29])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:32:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.65/1.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.65/1.48  
% 7.65/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.65/1.48  
% 7.65/1.48  ------  iProver source info
% 7.65/1.48  
% 7.65/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.65/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.65/1.48  git: non_committed_changes: false
% 7.65/1.48  git: last_make_outside_of_git: false
% 7.65/1.48  
% 7.65/1.48  ------ 
% 7.65/1.48  
% 7.65/1.48  ------ Input Options
% 7.65/1.48  
% 7.65/1.48  --out_options                           all
% 7.65/1.48  --tptp_safe_out                         true
% 7.65/1.48  --problem_path                          ""
% 7.65/1.48  --include_path                          ""
% 7.65/1.48  --clausifier                            res/vclausify_rel
% 7.65/1.48  --clausifier_options                    ""
% 7.65/1.48  --stdin                                 false
% 7.65/1.48  --stats_out                             all
% 7.65/1.48  
% 7.65/1.48  ------ General Options
% 7.65/1.48  
% 7.65/1.48  --fof                                   false
% 7.65/1.48  --time_out_real                         305.
% 7.65/1.48  --time_out_virtual                      -1.
% 7.65/1.48  --symbol_type_check                     false
% 7.65/1.48  --clausify_out                          false
% 7.65/1.48  --sig_cnt_out                           false
% 7.65/1.48  --trig_cnt_out                          false
% 7.65/1.48  --trig_cnt_out_tolerance                1.
% 7.65/1.48  --trig_cnt_out_sk_spl                   false
% 7.65/1.48  --abstr_cl_out                          false
% 7.65/1.48  
% 7.65/1.48  ------ Global Options
% 7.65/1.48  
% 7.65/1.48  --schedule                              default
% 7.65/1.48  --add_important_lit                     false
% 7.65/1.48  --prop_solver_per_cl                    1000
% 7.65/1.48  --min_unsat_core                        false
% 7.65/1.48  --soft_assumptions                      false
% 7.65/1.48  --soft_lemma_size                       3
% 7.65/1.48  --prop_impl_unit_size                   0
% 7.65/1.48  --prop_impl_unit                        []
% 7.65/1.48  --share_sel_clauses                     true
% 7.65/1.48  --reset_solvers                         false
% 7.65/1.48  --bc_imp_inh                            [conj_cone]
% 7.65/1.48  --conj_cone_tolerance                   3.
% 7.65/1.48  --extra_neg_conj                        none
% 7.65/1.48  --large_theory_mode                     true
% 7.65/1.48  --prolific_symb_bound                   200
% 7.65/1.48  --lt_threshold                          2000
% 7.65/1.48  --clause_weak_htbl                      true
% 7.65/1.48  --gc_record_bc_elim                     false
% 7.65/1.48  
% 7.65/1.48  ------ Preprocessing Options
% 7.65/1.48  
% 7.65/1.48  --preprocessing_flag                    true
% 7.65/1.48  --time_out_prep_mult                    0.1
% 7.65/1.48  --splitting_mode                        input
% 7.65/1.48  --splitting_grd                         true
% 7.65/1.48  --splitting_cvd                         false
% 7.65/1.48  --splitting_cvd_svl                     false
% 7.65/1.48  --splitting_nvd                         32
% 7.65/1.48  --sub_typing                            true
% 7.65/1.48  --prep_gs_sim                           true
% 7.65/1.48  --prep_unflatten                        true
% 7.65/1.48  --prep_res_sim                          true
% 7.65/1.48  --prep_upred                            true
% 7.65/1.48  --prep_sem_filter                       exhaustive
% 7.65/1.48  --prep_sem_filter_out                   false
% 7.65/1.48  --pred_elim                             true
% 7.65/1.48  --res_sim_input                         true
% 7.65/1.48  --eq_ax_congr_red                       true
% 7.65/1.48  --pure_diseq_elim                       true
% 7.65/1.48  --brand_transform                       false
% 7.65/1.48  --non_eq_to_eq                          false
% 7.65/1.48  --prep_def_merge                        true
% 7.65/1.48  --prep_def_merge_prop_impl              false
% 7.65/1.48  --prep_def_merge_mbd                    true
% 7.65/1.48  --prep_def_merge_tr_red                 false
% 7.65/1.48  --prep_def_merge_tr_cl                  false
% 7.65/1.48  --smt_preprocessing                     true
% 7.65/1.48  --smt_ac_axioms                         fast
% 7.65/1.48  --preprocessed_out                      false
% 7.65/1.48  --preprocessed_stats                    false
% 7.65/1.48  
% 7.65/1.48  ------ Abstraction refinement Options
% 7.65/1.48  
% 7.65/1.48  --abstr_ref                             []
% 7.65/1.48  --abstr_ref_prep                        false
% 7.65/1.48  --abstr_ref_until_sat                   false
% 7.65/1.48  --abstr_ref_sig_restrict                funpre
% 7.65/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.65/1.48  --abstr_ref_under                       []
% 7.65/1.48  
% 7.65/1.48  ------ SAT Options
% 7.65/1.48  
% 7.65/1.48  --sat_mode                              false
% 7.65/1.48  --sat_fm_restart_options                ""
% 7.65/1.48  --sat_gr_def                            false
% 7.65/1.48  --sat_epr_types                         true
% 7.65/1.48  --sat_non_cyclic_types                  false
% 7.65/1.48  --sat_finite_models                     false
% 7.65/1.48  --sat_fm_lemmas                         false
% 7.65/1.48  --sat_fm_prep                           false
% 7.65/1.48  --sat_fm_uc_incr                        true
% 7.65/1.48  --sat_out_model                         small
% 7.65/1.48  --sat_out_clauses                       false
% 7.65/1.48  
% 7.65/1.48  ------ QBF Options
% 7.65/1.48  
% 7.65/1.48  --qbf_mode                              false
% 7.65/1.48  --qbf_elim_univ                         false
% 7.65/1.48  --qbf_dom_inst                          none
% 7.65/1.48  --qbf_dom_pre_inst                      false
% 7.65/1.48  --qbf_sk_in                             false
% 7.65/1.48  --qbf_pred_elim                         true
% 7.65/1.48  --qbf_split                             512
% 7.65/1.48  
% 7.65/1.48  ------ BMC1 Options
% 7.65/1.48  
% 7.65/1.48  --bmc1_incremental                      false
% 7.65/1.48  --bmc1_axioms                           reachable_all
% 7.65/1.48  --bmc1_min_bound                        0
% 7.65/1.48  --bmc1_max_bound                        -1
% 7.65/1.48  --bmc1_max_bound_default                -1
% 7.65/1.48  --bmc1_symbol_reachability              true
% 7.65/1.48  --bmc1_property_lemmas                  false
% 7.65/1.48  --bmc1_k_induction                      false
% 7.65/1.48  --bmc1_non_equiv_states                 false
% 7.65/1.48  --bmc1_deadlock                         false
% 7.65/1.48  --bmc1_ucm                              false
% 7.65/1.48  --bmc1_add_unsat_core                   none
% 7.65/1.48  --bmc1_unsat_core_children              false
% 7.65/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.65/1.48  --bmc1_out_stat                         full
% 7.65/1.48  --bmc1_ground_init                      false
% 7.65/1.48  --bmc1_pre_inst_next_state              false
% 7.65/1.48  --bmc1_pre_inst_state                   false
% 7.65/1.48  --bmc1_pre_inst_reach_state             false
% 7.65/1.48  --bmc1_out_unsat_core                   false
% 7.65/1.48  --bmc1_aig_witness_out                  false
% 7.65/1.48  --bmc1_verbose                          false
% 7.65/1.48  --bmc1_dump_clauses_tptp                false
% 7.65/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.65/1.48  --bmc1_dump_file                        -
% 7.65/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.65/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.65/1.48  --bmc1_ucm_extend_mode                  1
% 7.65/1.48  --bmc1_ucm_init_mode                    2
% 7.65/1.48  --bmc1_ucm_cone_mode                    none
% 7.65/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.65/1.48  --bmc1_ucm_relax_model                  4
% 7.65/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.65/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.65/1.48  --bmc1_ucm_layered_model                none
% 7.65/1.48  --bmc1_ucm_max_lemma_size               10
% 7.65/1.48  
% 7.65/1.48  ------ AIG Options
% 7.65/1.48  
% 7.65/1.48  --aig_mode                              false
% 7.65/1.48  
% 7.65/1.48  ------ Instantiation Options
% 7.65/1.48  
% 7.65/1.48  --instantiation_flag                    true
% 7.65/1.48  --inst_sos_flag                         true
% 7.65/1.48  --inst_sos_phase                        true
% 7.65/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.65/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.65/1.48  --inst_lit_sel_side                     num_symb
% 7.65/1.48  --inst_solver_per_active                1400
% 7.65/1.48  --inst_solver_calls_frac                1.
% 7.65/1.48  --inst_passive_queue_type               priority_queues
% 7.65/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.65/1.48  --inst_passive_queues_freq              [25;2]
% 7.65/1.48  --inst_dismatching                      true
% 7.65/1.48  --inst_eager_unprocessed_to_passive     true
% 7.65/1.48  --inst_prop_sim_given                   true
% 7.65/1.48  --inst_prop_sim_new                     false
% 7.65/1.48  --inst_subs_new                         false
% 7.65/1.48  --inst_eq_res_simp                      false
% 7.65/1.48  --inst_subs_given                       false
% 7.65/1.48  --inst_orphan_elimination               true
% 7.65/1.48  --inst_learning_loop_flag               true
% 7.65/1.48  --inst_learning_start                   3000
% 7.65/1.48  --inst_learning_factor                  2
% 7.65/1.48  --inst_start_prop_sim_after_learn       3
% 7.65/1.48  --inst_sel_renew                        solver
% 7.65/1.48  --inst_lit_activity_flag                true
% 7.65/1.48  --inst_restr_to_given                   false
% 7.65/1.48  --inst_activity_threshold               500
% 7.65/1.48  --inst_out_proof                        true
% 7.65/1.48  
% 7.65/1.48  ------ Resolution Options
% 7.65/1.48  
% 7.65/1.48  --resolution_flag                       true
% 7.65/1.48  --res_lit_sel                           adaptive
% 7.65/1.48  --res_lit_sel_side                      none
% 7.65/1.48  --res_ordering                          kbo
% 7.65/1.48  --res_to_prop_solver                    active
% 7.65/1.48  --res_prop_simpl_new                    false
% 7.65/1.48  --res_prop_simpl_given                  true
% 7.65/1.48  --res_passive_queue_type                priority_queues
% 7.65/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.65/1.48  --res_passive_queues_freq               [15;5]
% 7.65/1.48  --res_forward_subs                      full
% 7.65/1.48  --res_backward_subs                     full
% 7.65/1.48  --res_forward_subs_resolution           true
% 7.65/1.48  --res_backward_subs_resolution          true
% 7.65/1.48  --res_orphan_elimination                true
% 7.65/1.48  --res_time_limit                        2.
% 7.65/1.48  --res_out_proof                         true
% 7.65/1.48  
% 7.65/1.48  ------ Superposition Options
% 7.65/1.48  
% 7.65/1.48  --superposition_flag                    true
% 7.65/1.48  --sup_passive_queue_type                priority_queues
% 7.65/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.65/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.65/1.48  --demod_completeness_check              fast
% 7.65/1.48  --demod_use_ground                      true
% 7.65/1.48  --sup_to_prop_solver                    passive
% 7.65/1.48  --sup_prop_simpl_new                    true
% 7.65/1.48  --sup_prop_simpl_given                  true
% 7.65/1.48  --sup_fun_splitting                     true
% 7.65/1.48  --sup_smt_interval                      50000
% 7.65/1.48  
% 7.65/1.48  ------ Superposition Simplification Setup
% 7.65/1.48  
% 7.65/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.65/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.65/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.65/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.65/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.65/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.65/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.65/1.48  --sup_immed_triv                        [TrivRules]
% 7.65/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.65/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.65/1.48  --sup_immed_bw_main                     []
% 7.65/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.65/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.65/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.65/1.48  --sup_input_bw                          []
% 7.65/1.48  
% 7.65/1.48  ------ Combination Options
% 7.65/1.48  
% 7.65/1.48  --comb_res_mult                         3
% 7.65/1.48  --comb_sup_mult                         2
% 7.65/1.48  --comb_inst_mult                        10
% 7.65/1.48  
% 7.65/1.48  ------ Debug Options
% 7.65/1.48  
% 7.65/1.48  --dbg_backtrace                         false
% 7.65/1.48  --dbg_dump_prop_clauses                 false
% 7.65/1.48  --dbg_dump_prop_clauses_file            -
% 7.65/1.48  --dbg_out_stat                          false
% 7.65/1.48  ------ Parsing...
% 7.65/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.65/1.48  
% 7.65/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 7.65/1.48  
% 7.65/1.48  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.65/1.48  
% 7.65/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.65/1.48  ------ Proving...
% 7.65/1.48  ------ Problem Properties 
% 7.65/1.48  
% 7.65/1.48  
% 7.65/1.48  clauses                                 26
% 7.65/1.48  conjectures                             7
% 7.65/1.48  EPR                                     6
% 7.65/1.48  Horn                                    24
% 7.65/1.48  unary                                   10
% 7.65/1.48  binary                                  5
% 7.65/1.48  lits                                    72
% 7.65/1.48  lits eq                                 8
% 7.65/1.48  fd_pure                                 0
% 7.65/1.48  fd_pseudo                               0
% 7.65/1.48  fd_cond                                 1
% 7.65/1.48  fd_pseudo_cond                          2
% 7.65/1.48  AC symbols                              0
% 7.65/1.48  
% 7.65/1.48  ------ Schedule dynamic 5 is on 
% 7.65/1.48  
% 7.65/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.65/1.48  
% 7.65/1.48  
% 7.65/1.48  ------ 
% 7.65/1.48  Current options:
% 7.65/1.48  ------ 
% 7.65/1.48  
% 7.65/1.48  ------ Input Options
% 7.65/1.48  
% 7.65/1.48  --out_options                           all
% 7.65/1.48  --tptp_safe_out                         true
% 7.65/1.48  --problem_path                          ""
% 7.65/1.48  --include_path                          ""
% 7.65/1.48  --clausifier                            res/vclausify_rel
% 7.65/1.48  --clausifier_options                    ""
% 7.65/1.48  --stdin                                 false
% 7.65/1.48  --stats_out                             all
% 7.65/1.48  
% 7.65/1.48  ------ General Options
% 7.65/1.48  
% 7.65/1.48  --fof                                   false
% 7.65/1.48  --time_out_real                         305.
% 7.65/1.48  --time_out_virtual                      -1.
% 7.65/1.48  --symbol_type_check                     false
% 7.65/1.48  --clausify_out                          false
% 7.65/1.48  --sig_cnt_out                           false
% 7.65/1.48  --trig_cnt_out                          false
% 7.65/1.48  --trig_cnt_out_tolerance                1.
% 7.65/1.48  --trig_cnt_out_sk_spl                   false
% 7.65/1.48  --abstr_cl_out                          false
% 7.65/1.48  
% 7.65/1.48  ------ Global Options
% 7.65/1.48  
% 7.65/1.48  --schedule                              default
% 7.65/1.48  --add_important_lit                     false
% 7.65/1.48  --prop_solver_per_cl                    1000
% 7.65/1.48  --min_unsat_core                        false
% 7.65/1.48  --soft_assumptions                      false
% 7.65/1.48  --soft_lemma_size                       3
% 7.65/1.48  --prop_impl_unit_size                   0
% 7.65/1.48  --prop_impl_unit                        []
% 7.65/1.48  --share_sel_clauses                     true
% 7.65/1.48  --reset_solvers                         false
% 7.65/1.48  --bc_imp_inh                            [conj_cone]
% 7.65/1.48  --conj_cone_tolerance                   3.
% 7.65/1.48  --extra_neg_conj                        none
% 7.65/1.48  --large_theory_mode                     true
% 7.65/1.48  --prolific_symb_bound                   200
% 7.65/1.48  --lt_threshold                          2000
% 7.65/1.48  --clause_weak_htbl                      true
% 7.65/1.48  --gc_record_bc_elim                     false
% 7.65/1.48  
% 7.65/1.48  ------ Preprocessing Options
% 7.65/1.48  
% 7.65/1.48  --preprocessing_flag                    true
% 7.65/1.48  --time_out_prep_mult                    0.1
% 7.65/1.48  --splitting_mode                        input
% 7.65/1.48  --splitting_grd                         true
% 7.65/1.48  --splitting_cvd                         false
% 7.65/1.48  --splitting_cvd_svl                     false
% 7.65/1.48  --splitting_nvd                         32
% 7.65/1.48  --sub_typing                            true
% 7.65/1.48  --prep_gs_sim                           true
% 7.65/1.48  --prep_unflatten                        true
% 7.65/1.48  --prep_res_sim                          true
% 7.65/1.48  --prep_upred                            true
% 7.65/1.48  --prep_sem_filter                       exhaustive
% 7.65/1.48  --prep_sem_filter_out                   false
% 7.65/1.48  --pred_elim                             true
% 7.65/1.48  --res_sim_input                         true
% 7.65/1.48  --eq_ax_congr_red                       true
% 7.65/1.48  --pure_diseq_elim                       true
% 7.65/1.48  --brand_transform                       false
% 7.65/1.48  --non_eq_to_eq                          false
% 7.65/1.48  --prep_def_merge                        true
% 7.65/1.48  --prep_def_merge_prop_impl              false
% 7.65/1.48  --prep_def_merge_mbd                    true
% 7.65/1.48  --prep_def_merge_tr_red                 false
% 7.65/1.48  --prep_def_merge_tr_cl                  false
% 7.65/1.48  --smt_preprocessing                     true
% 7.65/1.48  --smt_ac_axioms                         fast
% 7.65/1.48  --preprocessed_out                      false
% 7.65/1.48  --preprocessed_stats                    false
% 7.65/1.48  
% 7.65/1.48  ------ Abstraction refinement Options
% 7.65/1.48  
% 7.65/1.48  --abstr_ref                             []
% 7.65/1.48  --abstr_ref_prep                        false
% 7.65/1.48  --abstr_ref_until_sat                   false
% 7.65/1.48  --abstr_ref_sig_restrict                funpre
% 7.65/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.65/1.48  --abstr_ref_under                       []
% 7.65/1.48  
% 7.65/1.48  ------ SAT Options
% 7.65/1.48  
% 7.65/1.48  --sat_mode                              false
% 7.65/1.48  --sat_fm_restart_options                ""
% 7.65/1.48  --sat_gr_def                            false
% 7.65/1.48  --sat_epr_types                         true
% 7.65/1.48  --sat_non_cyclic_types                  false
% 7.65/1.48  --sat_finite_models                     false
% 7.65/1.48  --sat_fm_lemmas                         false
% 7.65/1.48  --sat_fm_prep                           false
% 7.65/1.48  --sat_fm_uc_incr                        true
% 7.65/1.48  --sat_out_model                         small
% 7.65/1.48  --sat_out_clauses                       false
% 7.65/1.48  
% 7.65/1.48  ------ QBF Options
% 7.65/1.48  
% 7.65/1.48  --qbf_mode                              false
% 7.65/1.48  --qbf_elim_univ                         false
% 7.65/1.48  --qbf_dom_inst                          none
% 7.65/1.48  --qbf_dom_pre_inst                      false
% 7.65/1.48  --qbf_sk_in                             false
% 7.65/1.48  --qbf_pred_elim                         true
% 7.65/1.48  --qbf_split                             512
% 7.65/1.48  
% 7.65/1.48  ------ BMC1 Options
% 7.65/1.48  
% 7.65/1.48  --bmc1_incremental                      false
% 7.65/1.48  --bmc1_axioms                           reachable_all
% 7.65/1.48  --bmc1_min_bound                        0
% 7.65/1.48  --bmc1_max_bound                        -1
% 7.65/1.48  --bmc1_max_bound_default                -1
% 7.65/1.48  --bmc1_symbol_reachability              true
% 7.65/1.48  --bmc1_property_lemmas                  false
% 7.65/1.48  --bmc1_k_induction                      false
% 7.65/1.48  --bmc1_non_equiv_states                 false
% 7.65/1.48  --bmc1_deadlock                         false
% 7.65/1.48  --bmc1_ucm                              false
% 7.65/1.48  --bmc1_add_unsat_core                   none
% 7.65/1.48  --bmc1_unsat_core_children              false
% 7.65/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.65/1.48  --bmc1_out_stat                         full
% 7.65/1.48  --bmc1_ground_init                      false
% 7.65/1.48  --bmc1_pre_inst_next_state              false
% 7.65/1.48  --bmc1_pre_inst_state                   false
% 7.65/1.48  --bmc1_pre_inst_reach_state             false
% 7.65/1.48  --bmc1_out_unsat_core                   false
% 7.65/1.48  --bmc1_aig_witness_out                  false
% 7.65/1.48  --bmc1_verbose                          false
% 7.65/1.48  --bmc1_dump_clauses_tptp                false
% 7.65/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.65/1.48  --bmc1_dump_file                        -
% 7.65/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.65/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.65/1.48  --bmc1_ucm_extend_mode                  1
% 7.65/1.48  --bmc1_ucm_init_mode                    2
% 7.65/1.48  --bmc1_ucm_cone_mode                    none
% 7.65/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.65/1.48  --bmc1_ucm_relax_model                  4
% 7.65/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.65/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.65/1.48  --bmc1_ucm_layered_model                none
% 7.65/1.48  --bmc1_ucm_max_lemma_size               10
% 7.65/1.48  
% 7.65/1.48  ------ AIG Options
% 7.65/1.48  
% 7.65/1.48  --aig_mode                              false
% 7.65/1.48  
% 7.65/1.48  ------ Instantiation Options
% 7.65/1.48  
% 7.65/1.48  --instantiation_flag                    true
% 7.65/1.48  --inst_sos_flag                         true
% 7.65/1.48  --inst_sos_phase                        true
% 7.65/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.65/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.65/1.48  --inst_lit_sel_side                     none
% 7.65/1.48  --inst_solver_per_active                1400
% 7.65/1.48  --inst_solver_calls_frac                1.
% 7.65/1.48  --inst_passive_queue_type               priority_queues
% 7.65/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.65/1.48  --inst_passive_queues_freq              [25;2]
% 7.65/1.48  --inst_dismatching                      true
% 7.65/1.48  --inst_eager_unprocessed_to_passive     true
% 7.65/1.48  --inst_prop_sim_given                   true
% 7.65/1.48  --inst_prop_sim_new                     false
% 7.65/1.48  --inst_subs_new                         false
% 7.65/1.48  --inst_eq_res_simp                      false
% 7.65/1.48  --inst_subs_given                       false
% 7.65/1.48  --inst_orphan_elimination               true
% 7.65/1.48  --inst_learning_loop_flag               true
% 7.65/1.48  --inst_learning_start                   3000
% 7.65/1.48  --inst_learning_factor                  2
% 7.65/1.48  --inst_start_prop_sim_after_learn       3
% 7.65/1.48  --inst_sel_renew                        solver
% 7.65/1.48  --inst_lit_activity_flag                true
% 7.65/1.48  --inst_restr_to_given                   false
% 7.65/1.48  --inst_activity_threshold               500
% 7.65/1.48  --inst_out_proof                        true
% 7.65/1.48  
% 7.65/1.48  ------ Resolution Options
% 7.65/1.48  
% 7.65/1.48  --resolution_flag                       false
% 7.65/1.48  --res_lit_sel                           adaptive
% 7.65/1.48  --res_lit_sel_side                      none
% 7.65/1.48  --res_ordering                          kbo
% 7.65/1.48  --res_to_prop_solver                    active
% 7.65/1.48  --res_prop_simpl_new                    false
% 7.65/1.48  --res_prop_simpl_given                  true
% 7.65/1.48  --res_passive_queue_type                priority_queues
% 7.65/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.65/1.48  --res_passive_queues_freq               [15;5]
% 7.65/1.48  --res_forward_subs                      full
% 7.65/1.48  --res_backward_subs                     full
% 7.65/1.48  --res_forward_subs_resolution           true
% 7.65/1.48  --res_backward_subs_resolution          true
% 7.65/1.48  --res_orphan_elimination                true
% 7.65/1.48  --res_time_limit                        2.
% 7.65/1.48  --res_out_proof                         true
% 7.65/1.48  
% 7.65/1.48  ------ Superposition Options
% 7.65/1.48  
% 7.65/1.48  --superposition_flag                    true
% 7.65/1.48  --sup_passive_queue_type                priority_queues
% 7.65/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.65/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.65/1.48  --demod_completeness_check              fast
% 7.65/1.48  --demod_use_ground                      true
% 7.65/1.48  --sup_to_prop_solver                    passive
% 7.65/1.48  --sup_prop_simpl_new                    true
% 7.65/1.48  --sup_prop_simpl_given                  true
% 7.65/1.48  --sup_fun_splitting                     true
% 7.65/1.48  --sup_smt_interval                      50000
% 7.65/1.48  
% 7.65/1.48  ------ Superposition Simplification Setup
% 7.65/1.48  
% 7.65/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.65/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.65/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.65/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.65/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.65/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.65/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.65/1.48  --sup_immed_triv                        [TrivRules]
% 7.65/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.65/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.65/1.48  --sup_immed_bw_main                     []
% 7.65/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.65/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.65/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.65/1.48  --sup_input_bw                          []
% 7.65/1.48  
% 7.65/1.48  ------ Combination Options
% 7.65/1.48  
% 7.65/1.48  --comb_res_mult                         3
% 7.65/1.48  --comb_sup_mult                         2
% 7.65/1.48  --comb_inst_mult                        10
% 7.65/1.48  
% 7.65/1.48  ------ Debug Options
% 7.65/1.48  
% 7.65/1.48  --dbg_backtrace                         false
% 7.65/1.48  --dbg_dump_prop_clauses                 false
% 7.65/1.48  --dbg_dump_prop_clauses_file            -
% 7.65/1.48  --dbg_out_stat                          false
% 7.65/1.48  
% 7.65/1.48  
% 7.65/1.48  
% 7.65/1.48  
% 7.65/1.48  ------ Proving...
% 7.65/1.48  
% 7.65/1.48  
% 7.65/1.48  % SZS status Theorem for theBenchmark.p
% 7.65/1.48  
% 7.65/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.65/1.48  
% 7.65/1.48  fof(f19,conjecture,(
% 7.65/1.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 7.65/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.48  
% 7.65/1.48  fof(f20,negated_conjecture,(
% 7.65/1.48    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 7.65/1.48    inference(negated_conjecture,[],[f19])).
% 7.65/1.48  
% 7.65/1.48  fof(f43,plain,(
% 7.65/1.48    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 7.65/1.48    inference(ennf_transformation,[],[f20])).
% 7.65/1.48  
% 7.65/1.48  fof(f44,plain,(
% 7.65/1.48    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 7.65/1.48    inference(flattening,[],[f43])).
% 7.65/1.48  
% 7.65/1.48  fof(f50,plain,(
% 7.65/1.48    ( ! [X2,X0,X1] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((~v2_funct_2(sK4,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK4),k6_partfun1(X0)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK4,X1,X0) & v1_funct_1(sK4))) )),
% 7.65/1.48    introduced(choice_axiom,[])).
% 7.65/1.48  
% 7.65/1.48  fof(f49,plain,(
% 7.65/1.48    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK1) | ~v2_funct_1(sK3)) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,X3),k6_partfun1(sK1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(X3,sK2,sK1) & v1_funct_1(X3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 7.65/1.48    introduced(choice_axiom,[])).
% 7.65/1.48  
% 7.65/1.48  fof(f51,plain,(
% 7.65/1.48    ((~v2_funct_2(sK4,sK1) | ~v2_funct_1(sK3)) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 7.65/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f44,f50,f49])).
% 7.65/1.48  
% 7.65/1.48  fof(f76,plain,(
% 7.65/1.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 7.65/1.48    inference(cnf_transformation,[],[f51])).
% 7.65/1.48  
% 7.65/1.48  fof(f79,plain,(
% 7.65/1.48    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 7.65/1.48    inference(cnf_transformation,[],[f51])).
% 7.65/1.48  
% 7.65/1.48  fof(f15,axiom,(
% 7.65/1.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 7.65/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.48  
% 7.65/1.48  fof(f37,plain,(
% 7.65/1.48    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 7.65/1.48    inference(ennf_transformation,[],[f15])).
% 7.65/1.48  
% 7.65/1.48  fof(f38,plain,(
% 7.65/1.48    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 7.65/1.48    inference(flattening,[],[f37])).
% 7.65/1.48  
% 7.65/1.48  fof(f69,plain,(
% 7.65/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 7.65/1.48    inference(cnf_transformation,[],[f38])).
% 7.65/1.48  
% 7.65/1.48  fof(f77,plain,(
% 7.65/1.48    v1_funct_1(sK4)),
% 7.65/1.48    inference(cnf_transformation,[],[f51])).
% 7.65/1.48  
% 7.65/1.48  fof(f74,plain,(
% 7.65/1.48    v1_funct_1(sK3)),
% 7.65/1.48    inference(cnf_transformation,[],[f51])).
% 7.65/1.48  
% 7.65/1.48  fof(f80,plain,(
% 7.65/1.48    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1))),
% 7.65/1.48    inference(cnf_transformation,[],[f51])).
% 7.65/1.48  
% 7.65/1.48  fof(f11,axiom,(
% 7.65/1.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 7.65/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.48  
% 7.65/1.48  fof(f31,plain,(
% 7.65/1.48    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 7.65/1.48    inference(ennf_transformation,[],[f11])).
% 7.65/1.48  
% 7.65/1.48  fof(f32,plain,(
% 7.65/1.48    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.65/1.48    inference(flattening,[],[f31])).
% 7.65/1.48  
% 7.65/1.48  fof(f63,plain,(
% 7.65/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.65/1.48    inference(cnf_transformation,[],[f32])).
% 7.65/1.48  
% 7.65/1.48  fof(f9,axiom,(
% 7.65/1.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))))),
% 7.65/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.48  
% 7.65/1.48  fof(f28,plain,(
% 7.65/1.48    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 7.65/1.48    inference(ennf_transformation,[],[f9])).
% 7.65/1.48  
% 7.65/1.48  fof(f29,plain,(
% 7.65/1.48    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.65/1.48    inference(flattening,[],[f28])).
% 7.65/1.48  
% 7.65/1.48  fof(f61,plain,(
% 7.65/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.65/1.48    inference(cnf_transformation,[],[f29])).
% 7.65/1.48  
% 7.65/1.48  fof(f12,axiom,(
% 7.65/1.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 7.65/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.48  
% 7.65/1.48  fof(f33,plain,(
% 7.65/1.48    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 7.65/1.48    inference(ennf_transformation,[],[f12])).
% 7.65/1.48  
% 7.65/1.48  fof(f34,plain,(
% 7.65/1.48    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.65/1.48    inference(flattening,[],[f33])).
% 7.65/1.48  
% 7.65/1.48  fof(f47,plain,(
% 7.65/1.48    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.65/1.48    inference(nnf_transformation,[],[f34])).
% 7.65/1.48  
% 7.65/1.48  fof(f64,plain,(
% 7.65/1.48    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.65/1.48    inference(cnf_transformation,[],[f47])).
% 7.65/1.48  
% 7.65/1.48  fof(f13,axiom,(
% 7.65/1.48    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 7.65/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.48  
% 7.65/1.48  fof(f66,plain,(
% 7.65/1.48    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 7.65/1.48    inference(cnf_transformation,[],[f13])).
% 7.65/1.48  
% 7.65/1.48  fof(f16,axiom,(
% 7.65/1.48    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 7.65/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.48  
% 7.65/1.48  fof(f70,plain,(
% 7.65/1.48    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 7.65/1.48    inference(cnf_transformation,[],[f16])).
% 7.65/1.48  
% 7.65/1.48  fof(f83,plain,(
% 7.65/1.48    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 7.65/1.48    inference(definition_unfolding,[],[f66,f70])).
% 7.65/1.48  
% 7.65/1.48  fof(f18,axiom,(
% 7.65/1.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 7.65/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.48  
% 7.65/1.48  fof(f41,plain,(
% 7.65/1.48    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 7.65/1.48    inference(ennf_transformation,[],[f18])).
% 7.65/1.48  
% 7.65/1.48  fof(f42,plain,(
% 7.65/1.48    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 7.65/1.48    inference(flattening,[],[f41])).
% 7.65/1.48  
% 7.65/1.48  fof(f72,plain,(
% 7.65/1.48    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X3) | k1_xboole_0 = X2 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 7.65/1.48    inference(cnf_transformation,[],[f42])).
% 7.65/1.48  
% 7.65/1.48  fof(f8,axiom,(
% 7.65/1.48    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 7.65/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.48  
% 7.65/1.48  fof(f27,plain,(
% 7.65/1.48    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 7.65/1.48    inference(ennf_transformation,[],[f8])).
% 7.65/1.48  
% 7.65/1.48  fof(f60,plain,(
% 7.65/1.48    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 7.65/1.48    inference(cnf_transformation,[],[f27])).
% 7.65/1.48  
% 7.65/1.48  fof(f5,axiom,(
% 7.65/1.48    ! [X0] : v2_funct_1(k6_relat_1(X0))),
% 7.65/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.48  
% 7.65/1.48  fof(f57,plain,(
% 7.65/1.48    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 7.65/1.48    inference(cnf_transformation,[],[f5])).
% 7.65/1.48  
% 7.65/1.48  fof(f82,plain,(
% 7.65/1.48    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 7.65/1.48    inference(definition_unfolding,[],[f57,f70])).
% 7.65/1.48  
% 7.65/1.48  fof(f65,plain,(
% 7.65/1.48    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.65/1.48    inference(cnf_transformation,[],[f47])).
% 7.65/1.48  
% 7.65/1.48  fof(f84,plain,(
% 7.65/1.48    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.65/1.48    inference(equality_resolution,[],[f65])).
% 7.65/1.48  
% 7.65/1.48  fof(f2,axiom,(
% 7.65/1.48    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 7.65/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.48  
% 7.65/1.48  fof(f22,plain,(
% 7.65/1.48    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 7.65/1.48    inference(ennf_transformation,[],[f2])).
% 7.65/1.48  
% 7.65/1.48  fof(f53,plain,(
% 7.65/1.48    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 7.65/1.48    inference(cnf_transformation,[],[f22])).
% 7.65/1.48  
% 7.65/1.48  fof(f17,axiom,(
% 7.65/1.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 7.65/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.48  
% 7.65/1.48  fof(f39,plain,(
% 7.65/1.48    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 7.65/1.48    inference(ennf_transformation,[],[f17])).
% 7.65/1.48  
% 7.65/1.48  fof(f40,plain,(
% 7.65/1.48    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.65/1.48    inference(flattening,[],[f39])).
% 7.65/1.48  
% 7.65/1.48  fof(f71,plain,(
% 7.65/1.48    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.65/1.48    inference(cnf_transformation,[],[f40])).
% 7.65/1.48  
% 7.65/1.48  fof(f10,axiom,(
% 7.65/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 7.65/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.48  
% 7.65/1.48  fof(f30,plain,(
% 7.65/1.48    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.65/1.48    inference(ennf_transformation,[],[f10])).
% 7.65/1.48  
% 7.65/1.48  fof(f62,plain,(
% 7.65/1.48    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.65/1.48    inference(cnf_transformation,[],[f30])).
% 7.65/1.48  
% 7.65/1.48  fof(f75,plain,(
% 7.65/1.48    v1_funct_2(sK3,sK1,sK2)),
% 7.65/1.48    inference(cnf_transformation,[],[f51])).
% 7.65/1.48  
% 7.65/1.48  fof(f78,plain,(
% 7.65/1.48    v1_funct_2(sK4,sK2,sK1)),
% 7.65/1.48    inference(cnf_transformation,[],[f51])).
% 7.65/1.48  
% 7.65/1.48  fof(f7,axiom,(
% 7.65/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.65/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.48  
% 7.65/1.48  fof(f21,plain,(
% 7.65/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 7.65/1.48    inference(pure_predicate_removal,[],[f7])).
% 7.65/1.48  
% 7.65/1.48  fof(f26,plain,(
% 7.65/1.48    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.65/1.48    inference(ennf_transformation,[],[f21])).
% 7.65/1.48  
% 7.65/1.48  fof(f59,plain,(
% 7.65/1.48    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.65/1.48    inference(cnf_transformation,[],[f26])).
% 7.65/1.48  
% 7.65/1.48  fof(f14,axiom,(
% 7.65/1.48    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 7.65/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.48  
% 7.65/1.48  fof(f35,plain,(
% 7.65/1.48    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 7.65/1.48    inference(ennf_transformation,[],[f14])).
% 7.65/1.48  
% 7.65/1.48  fof(f36,plain,(
% 7.65/1.48    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.65/1.48    inference(flattening,[],[f35])).
% 7.65/1.48  
% 7.65/1.48  fof(f48,plain,(
% 7.65/1.48    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.65/1.48    inference(nnf_transformation,[],[f36])).
% 7.65/1.48  
% 7.65/1.48  fof(f68,plain,(
% 7.65/1.48    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.65/1.48    inference(cnf_transformation,[],[f48])).
% 7.65/1.48  
% 7.65/1.48  fof(f85,plain,(
% 7.65/1.48    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 7.65/1.48    inference(equality_resolution,[],[f68])).
% 7.65/1.48  
% 7.65/1.48  fof(f6,axiom,(
% 7.65/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.65/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.48  
% 7.65/1.48  fof(f25,plain,(
% 7.65/1.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.65/1.48    inference(ennf_transformation,[],[f6])).
% 7.65/1.48  
% 7.65/1.48  fof(f58,plain,(
% 7.65/1.48    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.65/1.48    inference(cnf_transformation,[],[f25])).
% 7.65/1.48  
% 7.65/1.48  fof(f81,plain,(
% 7.65/1.48    ~v2_funct_2(sK4,sK1) | ~v2_funct_1(sK3)),
% 7.65/1.48    inference(cnf_transformation,[],[f51])).
% 7.65/1.48  
% 7.65/1.48  fof(f1,axiom,(
% 7.65/1.48    v1_xboole_0(k1_xboole_0)),
% 7.65/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.48  
% 7.65/1.48  fof(f52,plain,(
% 7.65/1.48    v1_xboole_0(k1_xboole_0)),
% 7.65/1.48    inference(cnf_transformation,[],[f1])).
% 7.65/1.48  
% 7.65/1.48  cnf(c_26,negated_conjecture,
% 7.65/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 7.65/1.48      inference(cnf_transformation,[],[f76]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_1253,plain,
% 7.65/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 7.65/1.48      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_23,negated_conjecture,
% 7.65/1.48      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 7.65/1.48      inference(cnf_transformation,[],[f79]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_1256,plain,
% 7.65/1.48      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 7.65/1.48      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_17,plain,
% 7.65/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.65/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.65/1.48      | ~ v1_funct_1(X0)
% 7.65/1.48      | ~ v1_funct_1(X3)
% 7.65/1.48      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 7.65/1.48      inference(cnf_transformation,[],[f69]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_1261,plain,
% 7.65/1.48      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 7.65/1.48      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 7.65/1.48      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.65/1.48      | v1_funct_1(X4) != iProver_top
% 7.65/1.48      | v1_funct_1(X5) != iProver_top ),
% 7.65/1.48      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_2805,plain,
% 7.65/1.48      ( k1_partfun1(X0,X1,sK2,sK1,X2,sK4) = k5_relat_1(X2,sK4)
% 7.65/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.65/1.48      | v1_funct_1(X2) != iProver_top
% 7.65/1.48      | v1_funct_1(sK4) != iProver_top ),
% 7.65/1.48      inference(superposition,[status(thm)],[c_1256,c_1261]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_25,negated_conjecture,
% 7.65/1.48      ( v1_funct_1(sK4) ),
% 7.65/1.48      inference(cnf_transformation,[],[f77]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_32,plain,
% 7.65/1.48      ( v1_funct_1(sK4) = iProver_top ),
% 7.65/1.48      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_3097,plain,
% 7.65/1.48      ( v1_funct_1(X2) != iProver_top
% 7.65/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.65/1.48      | k1_partfun1(X0,X1,sK2,sK1,X2,sK4) = k5_relat_1(X2,sK4) ),
% 7.65/1.48      inference(global_propositional_subsumption,
% 7.65/1.48                [status(thm)],
% 7.65/1.48                [c_2805,c_32]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_3098,plain,
% 7.65/1.48      ( k1_partfun1(X0,X1,sK2,sK1,X2,sK4) = k5_relat_1(X2,sK4)
% 7.65/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.65/1.48      | v1_funct_1(X2) != iProver_top ),
% 7.65/1.48      inference(renaming,[status(thm)],[c_3097]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_3107,plain,
% 7.65/1.48      ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k5_relat_1(sK3,sK4)
% 7.65/1.48      | v1_funct_1(sK3) != iProver_top ),
% 7.65/1.48      inference(superposition,[status(thm)],[c_1253,c_3098]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_28,negated_conjecture,
% 7.65/1.48      ( v1_funct_1(sK3) ),
% 7.65/1.48      inference(cnf_transformation,[],[f74]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_29,plain,
% 7.65/1.48      ( v1_funct_1(sK3) = iProver_top ),
% 7.65/1.48      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_3409,plain,
% 7.65/1.48      ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 7.65/1.48      inference(global_propositional_subsumption,
% 7.65/1.48                [status(thm)],
% 7.65/1.48                [c_3107,c_29]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_22,negated_conjecture,
% 7.65/1.48      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) ),
% 7.65/1.48      inference(cnf_transformation,[],[f80]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_1257,plain,
% 7.65/1.48      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) = iProver_top ),
% 7.65/1.48      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_3411,plain,
% 7.65/1.48      ( r2_relset_1(sK1,sK1,k5_relat_1(sK3,sK4),k6_partfun1(sK1)) = iProver_top ),
% 7.65/1.48      inference(demodulation,[status(thm)],[c_3409,c_1257]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_11,plain,
% 7.65/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.65/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.65/1.48      | k4_relset_1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 7.65/1.48      inference(cnf_transformation,[],[f63]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_1265,plain,
% 7.65/1.48      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 7.65/1.48      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 7.65/1.48      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.65/1.48      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_2332,plain,
% 7.65/1.48      ( k4_relset_1(X0,X1,sK2,sK1,X2,sK4) = k5_relat_1(X2,sK4)
% 7.65/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.65/1.48      inference(superposition,[status(thm)],[c_1256,c_1265]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_2595,plain,
% 7.65/1.48      ( k4_relset_1(sK1,sK2,sK2,sK1,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 7.65/1.48      inference(superposition,[status(thm)],[c_1253,c_2332]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_9,plain,
% 7.65/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.65/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.65/1.48      | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) ),
% 7.65/1.48      inference(cnf_transformation,[],[f61]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_1267,plain,
% 7.65/1.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.65/1.48      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 7.65/1.48      | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top ),
% 7.65/1.48      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_2904,plain,
% 7.65/1.48      ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
% 7.65/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 7.65/1.48      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 7.65/1.48      inference(superposition,[status(thm)],[c_2595,c_1267]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_31,plain,
% 7.65/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 7.65/1.48      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_34,plain,
% 7.65/1.48      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 7.65/1.48      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_5427,plain,
% 7.65/1.48      ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 7.65/1.48      inference(global_propositional_subsumption,
% 7.65/1.48                [status(thm)],
% 7.65/1.48                [c_2904,c_31,c_34]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_13,plain,
% 7.65/1.48      ( ~ r2_relset_1(X0,X1,X2,X3)
% 7.65/1.48      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.65/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.65/1.48      | X3 = X2 ),
% 7.65/1.48      inference(cnf_transformation,[],[f64]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_1263,plain,
% 7.65/1.48      ( X0 = X1
% 7.65/1.48      | r2_relset_1(X2,X3,X1,X0) != iProver_top
% 7.65/1.48      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 7.65/1.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top ),
% 7.65/1.48      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_5441,plain,
% 7.65/1.48      ( k5_relat_1(sK3,sK4) = X0
% 7.65/1.48      | r2_relset_1(sK1,sK1,k5_relat_1(sK3,sK4),X0) != iProver_top
% 7.65/1.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
% 7.65/1.48      inference(superposition,[status(thm)],[c_5427,c_1263]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_19170,plain,
% 7.65/1.48      ( k5_relat_1(sK3,sK4) = k6_partfun1(sK1)
% 7.65/1.48      | m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
% 7.65/1.48      inference(superposition,[status(thm)],[c_3411,c_5441]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_14,plain,
% 7.65/1.48      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 7.65/1.48      inference(cnf_transformation,[],[f83]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_55,plain,
% 7.65/1.48      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 7.65/1.48      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_57,plain,
% 7.65/1.48      ( m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 7.65/1.48      inference(instantiation,[status(thm)],[c_55]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_19609,plain,
% 7.65/1.48      ( k5_relat_1(sK3,sK4) = k6_partfun1(sK1) ),
% 7.65/1.48      inference(global_propositional_subsumption,
% 7.65/1.48                [status(thm)],
% 7.65/1.48                [c_19170,c_57]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_19626,plain,
% 7.65/1.48      ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k6_partfun1(sK1) ),
% 7.65/1.48      inference(demodulation,[status(thm)],[c_19609,c_3409]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_20,plain,
% 7.65/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 7.65/1.48      | ~ v1_funct_2(X3,X2,X4)
% 7.65/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.65/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
% 7.65/1.48      | ~ v1_funct_1(X3)
% 7.65/1.48      | ~ v1_funct_1(X0)
% 7.65/1.48      | v2_funct_1(X0)
% 7.65/1.48      | ~ v2_funct_1(k1_partfun1(X1,X2,X2,X4,X0,X3))
% 7.65/1.48      | k1_xboole_0 = X4 ),
% 7.65/1.48      inference(cnf_transformation,[],[f72]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_1258,plain,
% 7.65/1.48      ( k1_xboole_0 = X0
% 7.65/1.48      | v1_funct_2(X1,X2,X3) != iProver_top
% 7.65/1.48      | v1_funct_2(X4,X3,X0) != iProver_top
% 7.65/1.48      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 7.65/1.48      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) != iProver_top
% 7.65/1.48      | v1_funct_1(X4) != iProver_top
% 7.65/1.48      | v1_funct_1(X1) != iProver_top
% 7.65/1.48      | v2_funct_1(X1) = iProver_top
% 7.65/1.48      | v2_funct_1(k1_partfun1(X2,X3,X3,X0,X1,X4)) != iProver_top ),
% 7.65/1.48      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_19704,plain,
% 7.65/1.48      ( sK1 = k1_xboole_0
% 7.65/1.48      | v1_funct_2(sK3,sK1,sK2) != iProver_top
% 7.65/1.48      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.65/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 7.65/1.48      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.65/1.48      | v1_funct_1(sK3) != iProver_top
% 7.65/1.48      | v1_funct_1(sK4) != iProver_top
% 7.65/1.48      | v2_funct_1(k6_partfun1(sK1)) != iProver_top
% 7.65/1.48      | v2_funct_1(sK3) = iProver_top ),
% 7.65/1.48      inference(superposition,[status(thm)],[c_19626,c_1258]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_1262,plain,
% 7.65/1.48      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 7.65/1.48      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_2331,plain,
% 7.65/1.48      ( k4_relset_1(X0,X1,X2,X2,X3,k6_partfun1(X2)) = k5_relat_1(X3,k6_partfun1(X2))
% 7.65/1.48      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.65/1.48      inference(superposition,[status(thm)],[c_1262,c_1265]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_7901,plain,
% 7.65/1.48      ( k4_relset_1(sK1,sK2,X0,X0,sK3,k6_partfun1(X0)) = k5_relat_1(sK3,k6_partfun1(X0)) ),
% 7.65/1.48      inference(superposition,[status(thm)],[c_1253,c_2331]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_8216,plain,
% 7.65/1.48      ( m1_subset_1(k5_relat_1(sK3,k6_partfun1(X0)),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
% 7.65/1.48      | m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 7.65/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
% 7.65/1.48      inference(superposition,[status(thm)],[c_7901,c_1267]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_11168,plain,
% 7.65/1.48      ( m1_subset_1(k5_relat_1(sK3,k6_partfun1(X0)),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top ),
% 7.65/1.48      inference(global_propositional_subsumption,
% 7.65/1.48                [status(thm)],
% 7.65/1.48                [c_8216,c_31,c_55]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_8,plain,
% 7.65/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.65/1.48      | ~ v1_xboole_0(X1)
% 7.65/1.48      | v1_xboole_0(X0) ),
% 7.65/1.48      inference(cnf_transformation,[],[f60]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_1268,plain,
% 7.65/1.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.65/1.48      | v1_xboole_0(X1) != iProver_top
% 7.65/1.48      | v1_xboole_0(X0) = iProver_top ),
% 7.65/1.48      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_11175,plain,
% 7.65/1.48      ( v1_xboole_0(k5_relat_1(sK3,k6_partfun1(X0))) = iProver_top
% 7.65/1.48      | v1_xboole_0(sK1) != iProver_top ),
% 7.65/1.48      inference(superposition,[status(thm)],[c_11168,c_1268]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_5,plain,
% 7.65/1.48      ( v2_funct_1(k6_partfun1(X0)) ),
% 7.65/1.48      inference(cnf_transformation,[],[f82]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_80,plain,
% 7.65/1.48      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 7.65/1.48      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_82,plain,
% 7.65/1.48      ( v2_funct_1(k6_partfun1(sK1)) = iProver_top ),
% 7.65/1.48      inference(instantiation,[status(thm)],[c_80]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_798,plain,
% 7.65/1.48      ( ~ v2_funct_1(X0) | v2_funct_1(X1) | X1 != X0 ),
% 7.65/1.48      theory(equality) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_1320,plain,
% 7.65/1.48      ( ~ v2_funct_1(X0) | v2_funct_1(sK3) | sK3 != X0 ),
% 7.65/1.48      inference(instantiation,[status(thm)],[c_798]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_1327,plain,
% 7.65/1.48      ( ~ v2_funct_1(k6_partfun1(X0))
% 7.65/1.48      | v2_funct_1(sK3)
% 7.65/1.48      | sK3 != k6_partfun1(X0) ),
% 7.65/1.48      inference(instantiation,[status(thm)],[c_1320]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_1328,plain,
% 7.65/1.48      ( sK3 != k6_partfun1(X0)
% 7.65/1.48      | v2_funct_1(k6_partfun1(X0)) != iProver_top
% 7.65/1.48      | v2_funct_1(sK3) = iProver_top ),
% 7.65/1.48      inference(predicate_to_equality,[status(thm)],[c_1327]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_1330,plain,
% 7.65/1.48      ( sK3 != k6_partfun1(sK1)
% 7.65/1.48      | v2_funct_1(k6_partfun1(sK1)) != iProver_top
% 7.65/1.48      | v2_funct_1(sK3) = iProver_top ),
% 7.65/1.48      inference(instantiation,[status(thm)],[c_1328]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_793,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_1401,plain,
% 7.65/1.48      ( k6_partfun1(X0) != X1 | sK3 != X1 | sK3 = k6_partfun1(X0) ),
% 7.65/1.48      inference(instantiation,[status(thm)],[c_793]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_1663,plain,
% 7.65/1.48      ( k6_partfun1(X0) != sK3 | sK3 = k6_partfun1(X0) | sK3 != sK3 ),
% 7.65/1.48      inference(instantiation,[status(thm)],[c_1401]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_1664,plain,
% 7.65/1.48      ( k6_partfun1(sK1) != sK3 | sK3 = k6_partfun1(sK1) | sK3 != sK3 ),
% 7.65/1.48      inference(instantiation,[status(thm)],[c_1663]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_1714,plain,
% 7.65/1.48      ( ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.65/1.48      | ~ v1_xboole_0(X1)
% 7.65/1.48      | v1_xboole_0(k6_partfun1(X0)) ),
% 7.65/1.48      inference(instantiation,[status(thm)],[c_8]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_1730,plain,
% 7.65/1.48      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.65/1.48      | v1_xboole_0(X1) != iProver_top
% 7.65/1.48      | v1_xboole_0(k6_partfun1(X0)) = iProver_top ),
% 7.65/1.48      inference(predicate_to_equality,[status(thm)],[c_1714]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_1732,plain,
% 7.65/1.48      ( m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 7.65/1.48      | v1_xboole_0(k6_partfun1(sK1)) = iProver_top
% 7.65/1.48      | v1_xboole_0(sK1) != iProver_top ),
% 7.65/1.48      inference(instantiation,[status(thm)],[c_1730]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_1463,plain,
% 7.65/1.48      ( ~ r2_relset_1(X0,X1,sK3,X2)
% 7.65/1.48      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.65/1.48      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.65/1.48      | X2 = sK3 ),
% 7.65/1.48      inference(instantiation,[status(thm)],[c_13]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_1640,plain,
% 7.65/1.48      ( ~ r2_relset_1(sK1,sK2,sK3,X0)
% 7.65/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 7.65/1.48      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 7.65/1.48      | X0 = sK3 ),
% 7.65/1.48      inference(instantiation,[status(thm)],[c_1463]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_1749,plain,
% 7.65/1.48      ( ~ r2_relset_1(sK1,sK2,sK3,sK3)
% 7.65/1.48      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 7.65/1.48      | sK3 = sK3 ),
% 7.65/1.48      inference(instantiation,[status(thm)],[c_1640]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_12,plain,
% 7.65/1.48      ( r2_relset_1(X0,X1,X2,X2)
% 7.65/1.48      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 7.65/1.48      inference(cnf_transformation,[],[f84]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_1832,plain,
% 7.65/1.48      ( r2_relset_1(sK1,sK2,sK3,sK3)
% 7.65/1.48      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 7.65/1.48      inference(instantiation,[status(thm)],[c_12]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_1,plain,
% 7.65/1.48      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X1 = X0 ),
% 7.65/1.48      inference(cnf_transformation,[],[f53]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_1458,plain,
% 7.65/1.48      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(sK3) | X0 = sK3 ),
% 7.65/1.48      inference(instantiation,[status(thm)],[c_1]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_2063,plain,
% 7.65/1.48      ( ~ v1_xboole_0(k6_partfun1(X0))
% 7.65/1.48      | ~ v1_xboole_0(sK3)
% 7.65/1.48      | k6_partfun1(X0) = sK3 ),
% 7.65/1.48      inference(instantiation,[status(thm)],[c_1458]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_2069,plain,
% 7.65/1.48      ( k6_partfun1(X0) = sK3
% 7.65/1.48      | v1_xboole_0(k6_partfun1(X0)) != iProver_top
% 7.65/1.48      | v1_xboole_0(sK3) != iProver_top ),
% 7.65/1.48      inference(predicate_to_equality,[status(thm)],[c_2063]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_2071,plain,
% 7.65/1.48      ( k6_partfun1(sK1) = sK3
% 7.65/1.48      | v1_xboole_0(k6_partfun1(sK1)) != iProver_top
% 7.65/1.48      | v1_xboole_0(sK3) != iProver_top ),
% 7.65/1.48      inference(instantiation,[status(thm)],[c_2069]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_2255,plain,
% 7.65/1.48      ( v1_xboole_0(sK3) = iProver_top
% 7.65/1.48      | v1_xboole_0(sK1) != iProver_top ),
% 7.65/1.48      inference(superposition,[status(thm)],[c_1253,c_1268]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_18,plain,
% 7.65/1.48      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 7.65/1.48      | ~ v1_funct_2(X2,X0,X1)
% 7.65/1.48      | ~ v1_funct_2(X3,X1,X0)
% 7.65/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 7.65/1.48      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.65/1.48      | ~ v1_funct_1(X2)
% 7.65/1.48      | ~ v1_funct_1(X3)
% 7.65/1.48      | k2_relset_1(X1,X0,X3) = X0 ),
% 7.65/1.48      inference(cnf_transformation,[],[f71]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_1260,plain,
% 7.65/1.48      ( k2_relset_1(X0,X1,X2) = X1
% 7.65/1.48      | r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) != iProver_top
% 7.65/1.48      | v1_funct_2(X3,X1,X0) != iProver_top
% 7.65/1.48      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.65/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.65/1.48      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
% 7.65/1.48      | v1_funct_1(X2) != iProver_top
% 7.65/1.48      | v1_funct_1(X3) != iProver_top ),
% 7.65/1.48      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_2823,plain,
% 7.65/1.48      ( k2_relset_1(sK2,sK1,sK4) = sK1
% 7.65/1.48      | v1_funct_2(sK3,sK1,sK2) != iProver_top
% 7.65/1.48      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.65/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 7.65/1.48      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.65/1.48      | v1_funct_1(sK3) != iProver_top
% 7.65/1.48      | v1_funct_1(sK4) != iProver_top ),
% 7.65/1.48      inference(superposition,[status(thm)],[c_1257,c_1260]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_10,plain,
% 7.65/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.65/1.48      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 7.65/1.48      inference(cnf_transformation,[],[f62]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_1266,plain,
% 7.65/1.48      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 7.65/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.65/1.48      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_2088,plain,
% 7.65/1.48      ( k2_relset_1(sK2,sK1,sK4) = k2_relat_1(sK4) ),
% 7.65/1.48      inference(superposition,[status(thm)],[c_1256,c_1266]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_2824,plain,
% 7.65/1.48      ( k2_relat_1(sK4) = sK1
% 7.65/1.48      | v1_funct_2(sK3,sK1,sK2) != iProver_top
% 7.65/1.48      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.65/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 7.65/1.48      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.65/1.48      | v1_funct_1(sK3) != iProver_top
% 7.65/1.48      | v1_funct_1(sK4) != iProver_top ),
% 7.65/1.48      inference(demodulation,[status(thm)],[c_2823,c_2088]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_27,negated_conjecture,
% 7.65/1.48      ( v1_funct_2(sK3,sK1,sK2) ),
% 7.65/1.48      inference(cnf_transformation,[],[f75]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_30,plain,
% 7.65/1.48      ( v1_funct_2(sK3,sK1,sK2) = iProver_top ),
% 7.65/1.48      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_24,negated_conjecture,
% 7.65/1.48      ( v1_funct_2(sK4,sK2,sK1) ),
% 7.65/1.48      inference(cnf_transformation,[],[f78]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_33,plain,
% 7.65/1.48      ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
% 7.65/1.48      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_7886,plain,
% 7.65/1.48      ( k2_relat_1(sK4) = sK1 ),
% 7.65/1.48      inference(global_propositional_subsumption,
% 7.65/1.48                [status(thm)],
% 7.65/1.48                [c_2824,c_29,c_30,c_31,c_32,c_33,c_34]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_7,plain,
% 7.65/1.48      ( v5_relat_1(X0,X1)
% 7.65/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 7.65/1.48      inference(cnf_transformation,[],[f59]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_15,plain,
% 7.65/1.48      ( v2_funct_2(X0,k2_relat_1(X0))
% 7.65/1.48      | ~ v5_relat_1(X0,k2_relat_1(X0))
% 7.65/1.48      | ~ v1_relat_1(X0) ),
% 7.65/1.48      inference(cnf_transformation,[],[f85]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_376,plain,
% 7.65/1.48      ( v2_funct_2(X0,k2_relat_1(X0))
% 7.65/1.48      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 7.65/1.48      | ~ v1_relat_1(X0)
% 7.65/1.48      | X0 != X1
% 7.65/1.48      | k2_relat_1(X0) != X3 ),
% 7.65/1.48      inference(resolution_lifted,[status(thm)],[c_7,c_15]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_377,plain,
% 7.65/1.48      ( v2_funct_2(X0,k2_relat_1(X0))
% 7.65/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
% 7.65/1.48      | ~ v1_relat_1(X0) ),
% 7.65/1.48      inference(unflattening,[status(thm)],[c_376]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_6,plain,
% 7.65/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.65/1.48      | v1_relat_1(X0) ),
% 7.65/1.48      inference(cnf_transformation,[],[f58]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_387,plain,
% 7.65/1.48      ( v2_funct_2(X0,k2_relat_1(X0))
% 7.65/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0)))) ),
% 7.65/1.48      inference(forward_subsumption_resolution,[status(thm)],[c_377,c_6]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_21,negated_conjecture,
% 7.65/1.48      ( ~ v2_funct_2(sK4,sK1) | ~ v2_funct_1(sK3) ),
% 7.65/1.48      inference(cnf_transformation,[],[f81]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_402,plain,
% 7.65/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
% 7.65/1.48      | ~ v2_funct_1(sK3)
% 7.65/1.48      | k2_relat_1(X0) != sK1
% 7.65/1.48      | sK4 != X0 ),
% 7.65/1.48      inference(resolution_lifted,[status(thm)],[c_387,c_21]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_403,plain,
% 7.65/1.48      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK4))))
% 7.65/1.48      | ~ v2_funct_1(sK3)
% 7.65/1.48      | k2_relat_1(sK4) != sK1 ),
% 7.65/1.48      inference(unflattening,[status(thm)],[c_402]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_790,plain,
% 7.65/1.48      ( ~ v2_funct_1(sK3) | sP0_iProver_split | k2_relat_1(sK4) != sK1 ),
% 7.65/1.48      inference(splitting,
% 7.65/1.48                [splitting(split),new_symbols(definition,[])],
% 7.65/1.48                [c_403]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_1249,plain,
% 7.65/1.48      ( k2_relat_1(sK4) != sK1
% 7.65/1.48      | v2_funct_1(sK3) != iProver_top
% 7.65/1.48      | sP0_iProver_split = iProver_top ),
% 7.65/1.48      inference(predicate_to_equality,[status(thm)],[c_790]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_7890,plain,
% 7.65/1.48      ( sK1 != sK1
% 7.65/1.48      | v2_funct_1(sK3) != iProver_top
% 7.65/1.48      | sP0_iProver_split = iProver_top ),
% 7.65/1.48      inference(demodulation,[status(thm)],[c_7886,c_1249]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_7891,plain,
% 7.65/1.48      ( v2_funct_1(sK3) != iProver_top
% 7.65/1.48      | sP0_iProver_split = iProver_top ),
% 7.65/1.48      inference(equality_resolution_simp,[status(thm)],[c_7890]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_789,plain,
% 7.65/1.48      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK4))))
% 7.65/1.48      | ~ sP0_iProver_split ),
% 7.65/1.48      inference(splitting,
% 7.65/1.48                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 7.65/1.48                [c_403]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_1250,plain,
% 7.65/1.48      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK4)))) != iProver_top
% 7.65/1.48      | sP0_iProver_split != iProver_top ),
% 7.65/1.48      inference(predicate_to_equality,[status(thm)],[c_789]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_7889,plain,
% 7.65/1.48      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 7.65/1.48      | sP0_iProver_split != iProver_top ),
% 7.65/1.48      inference(demodulation,[status(thm)],[c_7886,c_1250]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_9102,plain,
% 7.65/1.48      ( sP0_iProver_split != iProver_top ),
% 7.65/1.48      inference(superposition,[status(thm)],[c_1256,c_7889]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_11468,plain,
% 7.65/1.48      ( v1_xboole_0(sK1) != iProver_top ),
% 7.65/1.48      inference(global_propositional_subsumption,
% 7.65/1.48                [status(thm)],
% 7.65/1.48                [c_11175,c_26,c_57,c_82,c_1330,c_1664,c_1732,c_1749,
% 7.65/1.48                 c_1832,c_2071,c_2255,c_7891,c_9102]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_794,plain,
% 7.65/1.48      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 7.65/1.48      theory(equality) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_2619,plain,
% 7.65/1.48      ( v1_xboole_0(X0)
% 7.65/1.48      | ~ v1_xboole_0(k1_xboole_0)
% 7.65/1.48      | X0 != k1_xboole_0 ),
% 7.65/1.48      inference(instantiation,[status(thm)],[c_794]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_2620,plain,
% 7.65/1.48      ( X0 != k1_xboole_0
% 7.65/1.48      | v1_xboole_0(X0) = iProver_top
% 7.65/1.48      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 7.65/1.48      inference(predicate_to_equality,[status(thm)],[c_2619]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_2622,plain,
% 7.65/1.48      ( sK1 != k1_xboole_0
% 7.65/1.48      | v1_xboole_0(sK1) = iProver_top
% 7.65/1.48      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 7.65/1.48      inference(instantiation,[status(thm)],[c_2620]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_0,plain,
% 7.65/1.48      ( v1_xboole_0(k1_xboole_0) ),
% 7.65/1.48      inference(cnf_transformation,[],[f52]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(c_93,plain,
% 7.65/1.48      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 7.65/1.48      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.65/1.48  
% 7.65/1.48  cnf(contradiction,plain,
% 7.65/1.48      ( $false ),
% 7.65/1.48      inference(minisat,
% 7.65/1.48                [status(thm)],
% 7.65/1.48                [c_19704,c_11468,c_9102,c_7891,c_2622,c_93,c_82,c_34,
% 7.65/1.48                 c_33,c_32,c_31,c_30,c_29]) ).
% 7.65/1.48  
% 7.65/1.48  
% 7.65/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.65/1.48  
% 7.65/1.48  ------                               Statistics
% 7.65/1.48  
% 7.65/1.48  ------ General
% 7.65/1.48  
% 7.65/1.48  abstr_ref_over_cycles:                  0
% 7.65/1.48  abstr_ref_under_cycles:                 0
% 7.65/1.48  gc_basic_clause_elim:                   0
% 7.65/1.48  forced_gc_time:                         0
% 7.65/1.49  parsing_time:                           0.009
% 7.65/1.49  unif_index_cands_time:                  0.
% 7.65/1.49  unif_index_add_time:                    0.
% 7.65/1.49  orderings_time:                         0.
% 7.65/1.49  out_proof_time:                         0.014
% 7.65/1.49  total_time:                             0.696
% 7.65/1.49  num_of_symbols:                         55
% 7.65/1.49  num_of_terms:                           31622
% 7.65/1.49  
% 7.65/1.49  ------ Preprocessing
% 7.65/1.49  
% 7.65/1.49  num_of_splits:                          1
% 7.65/1.49  num_of_split_atoms:                     1
% 7.65/1.49  num_of_reused_defs:                     0
% 7.65/1.49  num_eq_ax_congr_red:                    39
% 7.65/1.49  num_of_sem_filtered_clauses:            1
% 7.65/1.49  num_of_subtypes:                        0
% 7.65/1.49  monotx_restored_types:                  0
% 7.65/1.49  sat_num_of_epr_types:                   0
% 7.65/1.49  sat_num_of_non_cyclic_types:            0
% 7.65/1.49  sat_guarded_non_collapsed_types:        0
% 7.65/1.49  num_pure_diseq_elim:                    0
% 7.65/1.49  simp_replaced_by:                       0
% 7.65/1.49  res_preprocessed:                       133
% 7.65/1.49  prep_upred:                             0
% 7.65/1.49  prep_unflattend:                        29
% 7.65/1.49  smt_new_axioms:                         0
% 7.65/1.49  pred_elim_cands:                        6
% 7.65/1.49  pred_elim:                              3
% 7.65/1.49  pred_elim_cl:                           4
% 7.65/1.49  pred_elim_cycles:                       6
% 7.65/1.49  merged_defs:                            0
% 7.65/1.49  merged_defs_ncl:                        0
% 7.65/1.49  bin_hyper_res:                          0
% 7.65/1.49  prep_cycles:                            4
% 7.65/1.49  pred_elim_time:                         0.008
% 7.65/1.49  splitting_time:                         0.
% 7.65/1.49  sem_filter_time:                        0.
% 7.65/1.49  monotx_time:                            0.001
% 7.65/1.49  subtype_inf_time:                       0.
% 7.65/1.49  
% 7.65/1.49  ------ Problem properties
% 7.65/1.49  
% 7.65/1.49  clauses:                                26
% 7.65/1.49  conjectures:                            7
% 7.65/1.49  epr:                                    6
% 7.65/1.49  horn:                                   24
% 7.65/1.49  ground:                                 9
% 7.65/1.49  unary:                                  10
% 7.65/1.49  binary:                                 5
% 7.65/1.49  lits:                                   72
% 7.65/1.49  lits_eq:                                8
% 7.65/1.49  fd_pure:                                0
% 7.65/1.49  fd_pseudo:                              0
% 7.65/1.49  fd_cond:                                1
% 7.65/1.49  fd_pseudo_cond:                         2
% 7.65/1.49  ac_symbols:                             0
% 7.65/1.49  
% 7.65/1.49  ------ Propositional Solver
% 7.65/1.49  
% 7.65/1.49  prop_solver_calls:                      34
% 7.65/1.49  prop_fast_solver_calls:                 1379
% 7.65/1.49  smt_solver_calls:                       0
% 7.65/1.49  smt_fast_solver_calls:                  0
% 7.65/1.49  prop_num_of_clauses:                    9679
% 7.65/1.49  prop_preprocess_simplified:             14830
% 7.65/1.49  prop_fo_subsumed:                       32
% 7.65/1.49  prop_solver_time:                       0.
% 7.65/1.49  smt_solver_time:                        0.
% 7.65/1.49  smt_fast_solver_time:                   0.
% 7.65/1.49  prop_fast_solver_time:                  0.
% 7.65/1.49  prop_unsat_core_time:                   0.001
% 7.65/1.49  
% 7.65/1.49  ------ QBF
% 7.65/1.49  
% 7.65/1.49  qbf_q_res:                              0
% 7.65/1.49  qbf_num_tautologies:                    0
% 7.65/1.49  qbf_prep_cycles:                        0
% 7.65/1.49  
% 7.65/1.49  ------ BMC1
% 7.65/1.49  
% 7.65/1.49  bmc1_current_bound:                     -1
% 7.65/1.49  bmc1_last_solved_bound:                 -1
% 7.65/1.49  bmc1_unsat_core_size:                   -1
% 7.65/1.49  bmc1_unsat_core_parents_size:           -1
% 7.65/1.49  bmc1_merge_next_fun:                    0
% 7.65/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.65/1.49  
% 7.65/1.49  ------ Instantiation
% 7.65/1.49  
% 7.65/1.49  inst_num_of_clauses:                    2025
% 7.65/1.49  inst_num_in_passive:                    626
% 7.65/1.49  inst_num_in_active:                     1038
% 7.65/1.49  inst_num_in_unprocessed:                361
% 7.65/1.49  inst_num_of_loops:                      1230
% 7.65/1.49  inst_num_of_learning_restarts:          0
% 7.65/1.49  inst_num_moves_active_passive:          186
% 7.65/1.49  inst_lit_activity:                      0
% 7.65/1.49  inst_lit_activity_moves:                1
% 7.65/1.49  inst_num_tautologies:                   0
% 7.65/1.49  inst_num_prop_implied:                  0
% 7.65/1.49  inst_num_existing_simplified:           0
% 7.65/1.49  inst_num_eq_res_simplified:             0
% 7.65/1.49  inst_num_child_elim:                    0
% 7.65/1.49  inst_num_of_dismatching_blockings:      2087
% 7.65/1.49  inst_num_of_non_proper_insts:           3298
% 7.65/1.49  inst_num_of_duplicates:                 0
% 7.65/1.49  inst_inst_num_from_inst_to_res:         0
% 7.65/1.49  inst_dismatching_checking_time:         0.
% 7.65/1.49  
% 7.65/1.49  ------ Resolution
% 7.65/1.49  
% 7.65/1.49  res_num_of_clauses:                     0
% 7.65/1.49  res_num_in_passive:                     0
% 7.65/1.49  res_num_in_active:                      0
% 7.65/1.49  res_num_of_loops:                       137
% 7.65/1.49  res_forward_subset_subsumed:            103
% 7.65/1.49  res_backward_subset_subsumed:           0
% 7.65/1.49  res_forward_subsumed:                   0
% 7.65/1.49  res_backward_subsumed:                  0
% 7.65/1.49  res_forward_subsumption_resolution:     2
% 7.65/1.49  res_backward_subsumption_resolution:    0
% 7.65/1.49  res_clause_to_clause_subsumption:       2483
% 7.65/1.49  res_orphan_elimination:                 0
% 7.65/1.49  res_tautology_del:                      124
% 7.65/1.49  res_num_eq_res_simplified:              0
% 7.65/1.49  res_num_sel_changes:                    0
% 7.65/1.49  res_moves_from_active_to_pass:          0
% 7.65/1.49  
% 7.65/1.49  ------ Superposition
% 7.65/1.49  
% 7.65/1.49  sup_time_total:                         0.
% 7.65/1.49  sup_time_generating:                    0.
% 7.65/1.49  sup_time_sim_full:                      0.
% 7.65/1.49  sup_time_sim_immed:                     0.
% 7.65/1.49  
% 7.65/1.49  sup_num_of_clauses:                     1043
% 7.65/1.49  sup_num_in_active:                      217
% 7.65/1.49  sup_num_in_passive:                     826
% 7.65/1.49  sup_num_of_loops:                       244
% 7.65/1.49  sup_fw_superposition:                   845
% 7.65/1.49  sup_bw_superposition:                   414
% 7.65/1.49  sup_immediate_simplified:               473
% 7.65/1.49  sup_given_eliminated:                   1
% 7.65/1.49  comparisons_done:                       0
% 7.65/1.49  comparisons_avoided:                    1
% 7.65/1.49  
% 7.65/1.49  ------ Simplifications
% 7.65/1.49  
% 7.65/1.49  
% 7.65/1.49  sim_fw_subset_subsumed:                 69
% 7.65/1.49  sim_bw_subset_subsumed:                 5
% 7.65/1.49  sim_fw_subsumed:                        38
% 7.65/1.49  sim_bw_subsumed:                        4
% 7.65/1.49  sim_fw_subsumption_res:                 0
% 7.65/1.49  sim_bw_subsumption_res:                 0
% 7.65/1.49  sim_tautology_del:                      2
% 7.65/1.49  sim_eq_tautology_del:                   38
% 7.65/1.49  sim_eq_res_simp:                        1
% 7.65/1.49  sim_fw_demodulated:                     95
% 7.65/1.49  sim_bw_demodulated:                     35
% 7.65/1.49  sim_light_normalised:                   287
% 7.65/1.49  sim_joinable_taut:                      0
% 7.65/1.49  sim_joinable_simp:                      0
% 7.65/1.49  sim_ac_normalised:                      0
% 7.65/1.49  sim_smt_subsumption:                    0
% 7.65/1.49  
%------------------------------------------------------------------------------
