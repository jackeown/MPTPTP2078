%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:01:56 EST 2020

% Result     : Theorem 11.50s
% Output     : CNFRefutation 11.50s
% Verified   : 
% Statistics : Number of formulae       :  221 ( 922 expanded)
%              Number of clauses        :  146 ( 315 expanded)
%              Number of leaves         :   28 ( 233 expanded)
%              Depth                    :   18
%              Number of atoms          :  728 (5799 expanded)
%              Number of equality atoms :  266 ( 468 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f13,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f63,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f18,conjecture,(
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

fof(f19,negated_conjecture,(
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
    inference(negated_conjecture,[],[f18])).

fof(f41,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
     => ( ( ~ v2_funct_2(sK3,X0)
          | ~ v2_funct_1(X2) )
        & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0))
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(sK3,X1,X0)
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
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
          ( ( ~ v2_funct_2(X3,sK0)
            | ~ v2_funct_1(sK2) )
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ( ~ v2_funct_2(sK3,sK0)
      | ~ v2_funct_1(sK2) )
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f42,f46,f45])).

fof(f75,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f47])).

fof(f69,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f71,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f47])).

fof(f72,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f74,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f47])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f29])).

fof(f58,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f26])).

fof(f56,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
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

fof(f64,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f70,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f73,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f4,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f15,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f78,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f52,f65])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f77,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f50,f65])).

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

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f17,axiom,(
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

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f67,plain,(
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
    inference(cnf_transformation,[],[f40])).

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

fof(f66,plain,(
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

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f81,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f62])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f76,plain,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_12,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_723,plain,
    ( ~ r2_relset_1(X0_50,X1_50,X2_50,X3_50)
    | ~ m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
    | ~ m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
    | X3_50 = X2_50 ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_15,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_722,plain,
    ( m1_subset_1(k6_partfun1(X0_50),k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50))) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_7799,plain,
    ( ~ r2_relset_1(X0_50,X0_50,X1_50,k6_partfun1(X0_50))
    | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50)))
    | k6_partfun1(X0_50) = X1_50 ),
    inference(resolution,[status(thm)],[c_723,c_722])).

cnf(c_21,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_717,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_27483,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(resolution,[status(thm)],[c_7799,c_717])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | k4_relset_1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_725,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
    | ~ m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X4_50,X5_50)))
    | k4_relset_1(X4_50,X5_50,X1_50,X2_50,X3_50,X0_50) = k5_relat_1(X3_50,X0_50) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1535,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k4_relset_1(sK0,sK1,X1_50,X2_50,sK2,X0_50) = k5_relat_1(sK2,X0_50) ),
    inference(instantiation,[status(thm)],[c_725])).

cnf(c_1751,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k4_relset_1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1535])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_727,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
    | ~ m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X4_50,X5_50)))
    | m1_subset_1(k4_relset_1(X4_50,X5_50,X1_50,X2_50,X3_50,X0_50),k1_zfmisc_1(k2_zfmisc_1(X4_50,X2_50))) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1550,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
    | m1_subset_1(k4_relset_1(sK0,sK1,X1_50,X2_50,sK2,X0_50),k1_zfmisc_1(k2_zfmisc_1(sK0,X2_50)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_727])).

cnf(c_1794,plain,
    ( m1_subset_1(k4_relset_1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(instantiation,[status(thm)],[c_1550])).

cnf(c_737,plain,
    ( X0_51 = X0_51 ),
    theory(equality)).

cnf(c_1988,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50)) = k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50)) ),
    inference(instantiation,[status(thm)],[c_737])).

cnf(c_3269,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_1988])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_721,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
    | ~ m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X4_50,X5_50)))
    | ~ v1_funct_1(X3_50)
    | ~ v1_funct_1(X0_50)
    | k1_partfun1(X4_50,X5_50,X1_50,X2_50,X3_50,X0_50) = k5_relat_1(X3_50,X0_50) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1560,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3_50,X4_50)))
    | ~ v1_funct_1(X0_50)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(X1_50,X2_50,X3_50,X4_50,X0_50,sK3) = k5_relat_1(X0_50,sK3) ),
    inference(instantiation,[status(thm)],[c_721])).

cnf(c_1815,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2_50,X3_50)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(X0_50,X1_50,X2_50,X3_50,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1560])).

cnf(c_2350,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(X0_50,X1_50,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1815])).

cnf(c_3664,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_2350])).

cnf(c_739,plain,
    ( X0_50 != X1_50
    | X2_50 != X1_50
    | X2_50 = X0_50 ),
    theory(equality)).

cnf(c_3630,plain,
    ( X0_50 != X1_50
    | k1_partfun1(X2_50,X3_50,X3_50,X4_50,X5_50,X6_50) != X1_50
    | k1_partfun1(X2_50,X3_50,X3_50,X4_50,X5_50,X6_50) = X0_50 ),
    inference(instantiation,[status(thm)],[c_739])).

cnf(c_5808,plain,
    ( X0_50 != k5_relat_1(sK2,sK3)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = X0_50
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_3630])).

cnf(c_7483,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k4_relset_1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != k5_relat_1(sK2,sK3)
    | k4_relset_1(sK0,sK1,sK1,sK0,sK2,sK3) != k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_5808])).

cnf(c_745,plain,
    ( ~ m1_subset_1(X0_50,X0_51)
    | m1_subset_1(X1_50,X1_51)
    | X1_51 != X0_51
    | X1_50 != X0_50 ),
    theory(equality)).

cnf(c_2186,plain,
    ( m1_subset_1(X0_50,X0_51)
    | ~ m1_subset_1(k4_relset_1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | X0_51 != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | X0_50 != k4_relset_1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_745])).

cnf(c_3270,plain,
    ( m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k4_relset_1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | X0_50 != k4_relset_1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_2186])).

cnf(c_7484,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k4_relset_1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != k4_relset_1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_3270])).

cnf(c_8337,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_722])).

cnf(c_5525,plain,
    ( ~ r2_relset_1(X0_50,X1_50,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),X2_50)
    | ~ m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
    | X2_50 = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_723])).

cnf(c_13531,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_5525])).

cnf(c_29013,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_27483,c_27,c_25,c_24,c_22,c_21,c_1751,c_1794,c_3269,c_3664,c_7483,c_7484,c_8337,c_13531])).

cnf(c_747,plain,
    ( ~ r2_relset_1(X0_50,X1_50,X2_50,X3_50)
    | r2_relset_1(X4_50,X5_50,X6_50,X7_50)
    | X4_50 != X0_50
    | X5_50 != X1_50
    | X6_50 != X2_50
    | X7_50 != X3_50 ),
    theory(equality)).

cnf(c_2708,plain,
    ( r2_relset_1(X0_50,X1_50,X2_50,X3_50)
    | X2_50 != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | X3_50 != k6_partfun1(sK0)
    | X1_50 != sK0
    | X0_50 != sK0 ),
    inference(resolution,[status(thm)],[c_747,c_717])).

cnf(c_29268,plain,
    ( r2_relset_1(X0_50,X1_50,k6_partfun1(sK0),X2_50)
    | X2_50 != k6_partfun1(sK0)
    | X1_50 != sK0
    | X0_50 != sK0 ),
    inference(resolution,[status(thm)],[c_29013,c_2708])).

cnf(c_28,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_29,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_30,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_31,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_32,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_33,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_82,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_84,plain,
    ( v2_funct_1(k6_partfun1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_82])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_736,plain,
    ( X0_50 = X0_50 ),
    theory(equality)).

cnf(c_763,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_736])).

cnf(c_2,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_730,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_729,plain,
    ( v2_funct_1(k6_partfun1(X0_50)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_768,plain,
    ( v2_funct_1(k6_partfun1(X0_50)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_729])).

cnf(c_742,plain,
    ( ~ v2_funct_1(X0_50)
    | v2_funct_1(X1_50)
    | X1_50 != X0_50 ),
    theory(equality)).

cnf(c_1446,plain,
    ( v2_funct_1(X0_50)
    | ~ v2_funct_1(k6_partfun1(X1_50))
    | X0_50 != k6_partfun1(X1_50) ),
    inference(instantiation,[status(thm)],[c_742])).

cnf(c_1447,plain,
    ( X0_50 != k6_partfun1(X1_50)
    | v2_funct_1(X0_50) = iProver_top
    | v2_funct_1(k6_partfun1(X1_50)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1446])).

cnf(c_1449,plain,
    ( k1_xboole_0 != k6_partfun1(k1_xboole_0)
    | v2_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top
    | v2_funct_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1447])).

cnf(c_1784,plain,
    ( X0_50 != X1_50
    | X0_50 = k6_partfun1(X2_50)
    | k6_partfun1(X2_50) != X1_50 ),
    inference(instantiation,[status(thm)],[c_739])).

cnf(c_1785,plain,
    ( k6_partfun1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k6_partfun1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1784])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_731,plain,
    ( ~ v1_xboole_0(X0_50)
    | ~ v1_xboole_0(X1_50)
    | X1_50 = X0_50 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1954,plain,
    ( ~ v1_xboole_0(X0_50)
    | ~ v1_xboole_0(sK2)
    | sK2 = X0_50 ),
    inference(instantiation,[status(thm)],[c_731])).

cnf(c_1956,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK2 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1954])).

cnf(c_713,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_1229,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_713])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_728,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
    | ~ v1_xboole_0(X1_50)
    | v1_xboole_0(X0_50) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1214,plain,
    ( m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50))) != iProver_top
    | v1_xboole_0(X1_50) != iProver_top
    | v1_xboole_0(X0_50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_728])).

cnf(c_2406,plain,
    ( v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1229,c_1214])).

cnf(c_2422,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_xboole_0(sK0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2406])).

cnf(c_740,plain,
    ( ~ v1_xboole_0(X0_50)
    | v1_xboole_0(X1_50)
    | X1_50 != X0_50 ),
    theory(equality)).

cnf(c_2602,plain,
    ( ~ v1_xboole_0(X0_50)
    | v1_xboole_0(sK0)
    | sK0 != X0_50 ),
    inference(instantiation,[status(thm)],[c_740])).

cnf(c_2604,plain,
    ( v1_xboole_0(sK0)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2602])).

cnf(c_3252,plain,
    ( ~ v2_funct_1(X0_50)
    | v2_funct_1(sK2)
    | sK2 != X0_50 ),
    inference(instantiation,[status(thm)],[c_742])).

cnf(c_3253,plain,
    ( sK2 != X0_50
    | v2_funct_1(X0_50) != iProver_top
    | v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3252])).

cnf(c_3255,plain,
    ( sK2 != k1_xboole_0
    | v2_funct_1(sK2) = iProver_top
    | v2_funct_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3253])).

cnf(c_716,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1226,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_716])).

cnf(c_1221,plain,
    ( k1_partfun1(X0_50,X1_50,X2_50,X3_50,X4_50,X5_50) = k5_relat_1(X4_50,X5_50)
    | m1_subset_1(X5_50,k1_zfmisc_1(k2_zfmisc_1(X2_50,X3_50))) != iProver_top
    | m1_subset_1(X4_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
    | v1_funct_1(X5_50) != iProver_top
    | v1_funct_1(X4_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_721])).

cnf(c_3120,plain,
    ( k1_partfun1(X0_50,X1_50,sK1,sK0,X2_50,sK3) = k5_relat_1(X2_50,sK3)
    | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
    | v1_funct_1(X2_50) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1226,c_1221])).

cnf(c_4108,plain,
    ( v1_funct_1(X2_50) != iProver_top
    | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
    | k1_partfun1(X0_50,X1_50,sK1,sK0,X2_50,sK3) = k5_relat_1(X2_50,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3120,c_31])).

cnf(c_4109,plain,
    ( k1_partfun1(X0_50,X1_50,sK1,sK0,X2_50,sK3) = k5_relat_1(X2_50,sK3)
    | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
    | v1_funct_1(X2_50) != iProver_top ),
    inference(renaming,[status(thm)],[c_4108])).

cnf(c_4118,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1229,c_4109])).

cnf(c_4345,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4118,c_27,c_25,c_24,c_22,c_3664])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ v2_funct_1(k1_partfun1(X1,X2,X2,X4,X0,X3))
    | k1_xboole_0 = X4 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_718,plain,
    ( ~ v1_funct_2(X0_50,X1_50,X2_50)
    | ~ v1_funct_2(X3_50,X2_50,X4_50)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
    | ~ m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X2_50,X4_50)))
    | ~ v1_funct_1(X3_50)
    | ~ v1_funct_1(X0_50)
    | v2_funct_1(X0_50)
    | ~ v2_funct_1(k1_partfun1(X1_50,X2_50,X2_50,X4_50,X0_50,X3_50))
    | k1_xboole_0 = X4_50 ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1224,plain,
    ( k1_xboole_0 = X0_50
    | v1_funct_2(X1_50,X2_50,X3_50) != iProver_top
    | v1_funct_2(X4_50,X3_50,X0_50) != iProver_top
    | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_50,X3_50))) != iProver_top
    | m1_subset_1(X4_50,k1_zfmisc_1(k2_zfmisc_1(X3_50,X0_50))) != iProver_top
    | v1_funct_1(X1_50) != iProver_top
    | v1_funct_1(X4_50) != iProver_top
    | v2_funct_1(X1_50) = iProver_top
    | v2_funct_1(k1_partfun1(X2_50,X3_50,X3_50,X0_50,X1_50,X4_50)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_718])).

cnf(c_4350,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
    | v2_funct_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4345,c_1224])).

cnf(c_7279,plain,
    ( v2_funct_1(k5_relat_1(sK2,sK3))
    | ~ v2_funct_1(k6_partfun1(X0_50))
    | k5_relat_1(sK2,sK3) != k6_partfun1(X0_50) ),
    inference(instantiation,[status(thm)],[c_1446])).

cnf(c_7280,plain,
    ( k5_relat_1(sK2,sK3) != k6_partfun1(X0_50)
    | v2_funct_1(k5_relat_1(sK2,sK3)) = iProver_top
    | v2_funct_1(k6_partfun1(X0_50)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7279])).

cnf(c_7752,plain,
    ( k5_relat_1(sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_736])).

cnf(c_5541,plain,
    ( X0_50 != X1_50
    | X0_50 = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X1_50 ),
    inference(instantiation,[status(thm)],[c_739])).

cnf(c_12684,plain,
    ( X0_50 = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | X0_50 != k5_relat_1(sK2,sK3)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_5541])).

cnf(c_18142,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != k5_relat_1(sK2,sK3)
    | k5_relat_1(sK2,sK3) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k5_relat_1(sK2,sK3) != k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_12684])).

cnf(c_2564,plain,
    ( X0_50 != X1_50
    | X1_50 = X0_50 ),
    inference(resolution,[status(thm)],[c_739,c_736])).

cnf(c_29203,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    inference(resolution,[status(thm)],[c_29013,c_2564])).

cnf(c_741,plain,
    ( X0_50 != X1_50
    | k6_partfun1(X0_50) = k6_partfun1(X1_50) ),
    theory(equality)).

cnf(c_2565,plain,
    ( X0_50 != X1_50
    | X2_50 != k6_partfun1(X1_50)
    | k6_partfun1(X0_50) = X2_50 ),
    inference(resolution,[status(thm)],[c_739,c_741])).

cnf(c_29354,plain,
    ( X0_50 != sK0
    | k6_partfun1(X0_50) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(resolution,[status(thm)],[c_29203,c_2565])).

cnf(c_1225,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_717])).

cnf(c_17,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_720,plain,
    ( ~ r2_relset_1(X0_50,X0_50,k1_partfun1(X0_50,X1_50,X1_50,X0_50,X2_50,X3_50),k6_partfun1(X0_50))
    | ~ v1_funct_2(X2_50,X0_50,X1_50)
    | ~ v1_funct_2(X3_50,X1_50,X0_50)
    | ~ m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X0_50)))
    | ~ m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
    | ~ v1_funct_1(X3_50)
    | ~ v1_funct_1(X2_50)
    | k2_relset_1(X1_50,X0_50,X3_50) = X0_50 ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1222,plain,
    ( k2_relset_1(X0_50,X1_50,X2_50) = X1_50
    | r2_relset_1(X1_50,X1_50,k1_partfun1(X1_50,X0_50,X0_50,X1_50,X3_50,X2_50),k6_partfun1(X1_50)) != iProver_top
    | v1_funct_2(X2_50,X0_50,X1_50) != iProver_top
    | v1_funct_2(X3_50,X1_50,X0_50) != iProver_top
    | m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X0_50))) != iProver_top
    | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
    | v1_funct_1(X3_50) != iProver_top
    | v1_funct_1(X2_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_720])).

cnf(c_3490,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1225,c_1222])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_726,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
    | k2_relset_1(X1_50,X2_50,X0_50) = k2_relat_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1216,plain,
    ( k2_relset_1(X0_50,X1_50,X2_50) = k2_relat_1(X2_50)
    | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_726])).

cnf(c_2198,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1226,c_1216])).

cnf(c_3515,plain,
    ( k2_relat_1(sK3) = sK0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3490,c_2198])).

cnf(c_31446,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3515,c_28,c_29,c_30,c_31,c_32,c_33])).

cnf(c_6,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_13,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_318,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X0)
    | X0 != X1
    | k2_relat_1(X0) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_13])).

cnf(c_319,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_318])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_329,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0)))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_319,c_5])).

cnf(c_20,negated_conjecture,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_344,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
    | ~ v2_funct_1(sK2)
    | k2_relat_1(X0) != sK0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_329,c_20])).

cnf(c_345,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3))))
    | ~ v2_funct_1(sK2)
    | k2_relat_1(sK3) != sK0 ),
    inference(unflattening,[status(thm)],[c_344])).

cnf(c_710,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_50,k2_relat_1(sK3))))
    | ~ v2_funct_1(sK2)
    | k2_relat_1(sK3) != sK0 ),
    inference(subtyping,[status(esa)],[c_345])).

cnf(c_734,plain,
    ( ~ v2_funct_1(sK2)
    | sP0_iProver_split
    | k2_relat_1(sK3) != sK0 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_710])).

cnf(c_1232,plain,
    ( k2_relat_1(sK3) != sK0
    | v2_funct_1(sK2) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_734])).

cnf(c_31451,plain,
    ( sK0 != sK0
    | v2_funct_1(sK2) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_31446,c_1232])).

cnf(c_31452,plain,
    ( v2_funct_1(sK2) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_31451])).

cnf(c_733,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_50,k2_relat_1(sK3))))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_710])).

cnf(c_1233,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_50,k2_relat_1(sK3)))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_733])).

cnf(c_31450,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_50,sK0))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(demodulation,[status(thm)],[c_31446,c_1233])).

cnf(c_32386,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_1226,c_31450])).

cnf(c_10318,plain,
    ( k5_relat_1(sK2,sK3) != X0_50
    | k5_relat_1(sK2,sK3) = k6_partfun1(X1_50)
    | k6_partfun1(X1_50) != X0_50 ),
    inference(instantiation,[status(thm)],[c_1784])).

cnf(c_33370,plain,
    ( k5_relat_1(sK2,sK3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k5_relat_1(sK2,sK3) = k6_partfun1(X0_50)
    | k6_partfun1(X0_50) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_10318])).

cnf(c_34221,plain,
    ( X0_50 != sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_29268,c_27,c_28,c_29,c_25,c_30,c_24,c_31,c_32,c_22,c_33,c_84,c_0,c_763,c_730,c_768,c_1449,c_1785,c_1956,c_2422,c_2604,c_3255,c_3664,c_4350,c_7280,c_7752,c_18142,c_29354,c_31452,c_32386,c_33370])).

cnf(c_10589,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK3)
    | k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(resolution,[status(thm)],[c_720,c_717])).

cnf(c_1594,plain,
    ( ~ r2_relset_1(X0_50,X0_50,k1_partfun1(X0_50,X1_50,X1_50,X0_50,sK2,X2_50),k6_partfun1(X0_50))
    | ~ v1_funct_2(X2_50,X1_50,X0_50)
    | ~ v1_funct_2(sK2,X0_50,X1_50)
    | ~ m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X0_50)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
    | ~ v1_funct_1(X2_50)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X1_50,X0_50,X2_50) = X0_50 ),
    inference(instantiation,[status(thm)],[c_720])).

cnf(c_1858,plain,
    ( ~ r2_relset_1(X0_50,X0_50,k1_partfun1(X0_50,X1_50,X1_50,X0_50,sK2,sK3),k6_partfun1(X0_50))
    | ~ v1_funct_2(sK2,X0_50,X1_50)
    | ~ v1_funct_2(sK3,X1_50,X0_50)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1_50,X0_50)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK3)
    | k2_relset_1(X1_50,X0_50,sK3) = X0_50 ),
    inference(instantiation,[status(thm)],[c_1594])).

cnf(c_2365,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK3)
    | k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(instantiation,[status(thm)],[c_1858])).

cnf(c_10822,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10589,c_27,c_26,c_25,c_24,c_23,c_22,c_21,c_2365])).

cnf(c_34889,plain,
    ( $false ),
    inference(backward_subsumption_resolution,[status(thm)],[c_34221,c_10822])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:39:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.50/2.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.50/2.01  
% 11.50/2.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.50/2.01  
% 11.50/2.01  ------  iProver source info
% 11.50/2.01  
% 11.50/2.01  git: date: 2020-06-30 10:37:57 +0100
% 11.50/2.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.50/2.01  git: non_committed_changes: false
% 11.50/2.01  git: last_make_outside_of_git: false
% 11.50/2.01  
% 11.50/2.01  ------ 
% 11.50/2.01  ------ Parsing...
% 11.50/2.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.50/2.01  
% 11.50/2.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 11.50/2.01  
% 11.50/2.01  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.50/2.01  
% 11.50/2.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.50/2.01  ------ Proving...
% 11.50/2.01  ------ Problem Properties 
% 11.50/2.01  
% 11.50/2.01  
% 11.50/2.01  clauses                                 24
% 11.50/2.01  conjectures                             7
% 11.50/2.01  EPR                                     6
% 11.50/2.01  Horn                                    23
% 11.50/2.01  unary                                   11
% 11.50/2.01  binary                                  3
% 11.50/2.01  lits                                    66
% 11.50/2.01  lits eq                                 9
% 11.50/2.01  fd_pure                                 0
% 11.50/2.01  fd_pseudo                               0
% 11.50/2.01  fd_cond                                 1
% 11.50/2.01  fd_pseudo_cond                          2
% 11.50/2.01  AC symbols                              0
% 11.50/2.01  
% 11.50/2.01  ------ Input Options Time Limit: Unbounded
% 11.50/2.01  
% 11.50/2.01  
% 11.50/2.01  ------ 
% 11.50/2.01  Current options:
% 11.50/2.01  ------ 
% 11.50/2.01  
% 11.50/2.01  
% 11.50/2.01  
% 11.50/2.01  
% 11.50/2.01  ------ Proving...
% 11.50/2.01  
% 11.50/2.01  
% 11.50/2.01  % SZS status Theorem for theBenchmark.p
% 11.50/2.01  
% 11.50/2.01   Resolution empty clause
% 11.50/2.01  
% 11.50/2.01  % SZS output start CNFRefutation for theBenchmark.p
% 11.50/2.01  
% 11.50/2.01  fof(f11,axiom,(
% 11.50/2.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 11.50/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.50/2.01  
% 11.50/2.01  fof(f31,plain,(
% 11.50/2.01    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 11.50/2.01    inference(ennf_transformation,[],[f11])).
% 11.50/2.01  
% 11.50/2.01  fof(f32,plain,(
% 11.50/2.01    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.50/2.01    inference(flattening,[],[f31])).
% 11.50/2.01  
% 11.50/2.01  fof(f43,plain,(
% 11.50/2.01    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.50/2.01    inference(nnf_transformation,[],[f32])).
% 11.50/2.01  
% 11.50/2.01  fof(f59,plain,(
% 11.50/2.01    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.50/2.01    inference(cnf_transformation,[],[f43])).
% 11.50/2.01  
% 11.50/2.01  fof(f13,axiom,(
% 11.50/2.01    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 11.50/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.50/2.01  
% 11.50/2.01  fof(f20,plain,(
% 11.50/2.01    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 11.50/2.01    inference(pure_predicate_removal,[],[f13])).
% 11.50/2.01  
% 11.50/2.01  fof(f63,plain,(
% 11.50/2.01    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 11.50/2.01    inference(cnf_transformation,[],[f20])).
% 11.50/2.01  
% 11.50/2.01  fof(f18,conjecture,(
% 11.50/2.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 11.50/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.50/2.01  
% 11.50/2.01  fof(f19,negated_conjecture,(
% 11.50/2.01    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 11.50/2.01    inference(negated_conjecture,[],[f18])).
% 11.50/2.01  
% 11.50/2.01  fof(f41,plain,(
% 11.50/2.01    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 11.50/2.01    inference(ennf_transformation,[],[f19])).
% 11.50/2.01  
% 11.50/2.01  fof(f42,plain,(
% 11.50/2.01    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 11.50/2.01    inference(flattening,[],[f41])).
% 11.50/2.01  
% 11.50/2.01  fof(f46,plain,(
% 11.50/2.01    ( ! [X2,X0,X1] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((~v2_funct_2(sK3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 11.50/2.01    introduced(choice_axiom,[])).
% 11.50/2.01  
% 11.50/2.01  fof(f45,plain,(
% 11.50/2.01    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 11.50/2.01    introduced(choice_axiom,[])).
% 11.50/2.01  
% 11.50/2.01  fof(f47,plain,(
% 11.50/2.01    ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 11.50/2.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f42,f46,f45])).
% 11.50/2.01  
% 11.50/2.01  fof(f75,plain,(
% 11.50/2.01    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 11.50/2.01    inference(cnf_transformation,[],[f47])).
% 11.50/2.01  
% 11.50/2.01  fof(f69,plain,(
% 11.50/2.01    v1_funct_1(sK2)),
% 11.50/2.01    inference(cnf_transformation,[],[f47])).
% 11.50/2.01  
% 11.50/2.01  fof(f71,plain,(
% 11.50/2.01    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 11.50/2.01    inference(cnf_transformation,[],[f47])).
% 11.50/2.01  
% 11.50/2.01  fof(f72,plain,(
% 11.50/2.01    v1_funct_1(sK3)),
% 11.50/2.01    inference(cnf_transformation,[],[f47])).
% 11.50/2.01  
% 11.50/2.01  fof(f74,plain,(
% 11.50/2.01    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 11.50/2.01    inference(cnf_transformation,[],[f47])).
% 11.50/2.01  
% 11.50/2.01  fof(f10,axiom,(
% 11.50/2.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 11.50/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.50/2.01  
% 11.50/2.01  fof(f29,plain,(
% 11.50/2.01    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 11.50/2.01    inference(ennf_transformation,[],[f10])).
% 11.50/2.01  
% 11.50/2.01  fof(f30,plain,(
% 11.50/2.01    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.50/2.01    inference(flattening,[],[f29])).
% 11.50/2.01  
% 11.50/2.01  fof(f58,plain,(
% 11.50/2.01    ( ! [X4,X2,X0,X5,X3,X1] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.50/2.01    inference(cnf_transformation,[],[f30])).
% 11.50/2.01  
% 11.50/2.01  fof(f8,axiom,(
% 11.50/2.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))))),
% 11.50/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.50/2.01  
% 11.50/2.01  fof(f26,plain,(
% 11.50/2.01    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 11.50/2.01    inference(ennf_transformation,[],[f8])).
% 11.50/2.01  
% 11.50/2.01  fof(f27,plain,(
% 11.50/2.01    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.50/2.01    inference(flattening,[],[f26])).
% 11.50/2.01  
% 11.50/2.01  fof(f56,plain,(
% 11.50/2.01    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.50/2.01    inference(cnf_transformation,[],[f27])).
% 11.50/2.01  
% 11.50/2.01  fof(f14,axiom,(
% 11.50/2.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 11.50/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.50/2.01  
% 11.50/2.01  fof(f35,plain,(
% 11.50/2.01    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 11.50/2.01    inference(ennf_transformation,[],[f14])).
% 11.50/2.01  
% 11.50/2.01  fof(f36,plain,(
% 11.50/2.01    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 11.50/2.01    inference(flattening,[],[f35])).
% 11.50/2.01  
% 11.50/2.01  fof(f64,plain,(
% 11.50/2.01    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 11.50/2.01    inference(cnf_transformation,[],[f36])).
% 11.50/2.01  
% 11.50/2.01  fof(f70,plain,(
% 11.50/2.01    v1_funct_2(sK2,sK0,sK1)),
% 11.50/2.01    inference(cnf_transformation,[],[f47])).
% 11.50/2.01  
% 11.50/2.01  fof(f73,plain,(
% 11.50/2.01    v1_funct_2(sK3,sK1,sK0)),
% 11.50/2.01    inference(cnf_transformation,[],[f47])).
% 11.50/2.01  
% 11.50/2.01  fof(f4,axiom,(
% 11.50/2.01    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 11.50/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.50/2.01  
% 11.50/2.01  fof(f52,plain,(
% 11.50/2.01    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 11.50/2.01    inference(cnf_transformation,[],[f4])).
% 11.50/2.01  
% 11.50/2.01  fof(f15,axiom,(
% 11.50/2.01    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 11.50/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.50/2.01  
% 11.50/2.01  fof(f65,plain,(
% 11.50/2.01    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 11.50/2.01    inference(cnf_transformation,[],[f15])).
% 11.50/2.01  
% 11.50/2.01  fof(f78,plain,(
% 11.50/2.01    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 11.50/2.01    inference(definition_unfolding,[],[f52,f65])).
% 11.50/2.01  
% 11.50/2.01  fof(f1,axiom,(
% 11.50/2.01    v1_xboole_0(k1_xboole_0)),
% 11.50/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.50/2.01  
% 11.50/2.01  fof(f48,plain,(
% 11.50/2.01    v1_xboole_0(k1_xboole_0)),
% 11.50/2.01    inference(cnf_transformation,[],[f1])).
% 11.50/2.01  
% 11.50/2.01  fof(f3,axiom,(
% 11.50/2.01    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 11.50/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.50/2.01  
% 11.50/2.01  fof(f50,plain,(
% 11.50/2.01    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 11.50/2.01    inference(cnf_transformation,[],[f3])).
% 11.50/2.01  
% 11.50/2.01  fof(f77,plain,(
% 11.50/2.01    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 11.50/2.01    inference(definition_unfolding,[],[f50,f65])).
% 11.50/2.01  
% 11.50/2.01  fof(f2,axiom,(
% 11.50/2.01    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 11.50/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.50/2.01  
% 11.50/2.01  fof(f22,plain,(
% 11.50/2.01    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 11.50/2.01    inference(ennf_transformation,[],[f2])).
% 11.50/2.01  
% 11.50/2.01  fof(f49,plain,(
% 11.50/2.01    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 11.50/2.01    inference(cnf_transformation,[],[f22])).
% 11.50/2.01  
% 11.50/2.01  fof(f7,axiom,(
% 11.50/2.01    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 11.50/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.50/2.01  
% 11.50/2.01  fof(f25,plain,(
% 11.50/2.01    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 11.50/2.01    inference(ennf_transformation,[],[f7])).
% 11.50/2.01  
% 11.50/2.01  fof(f55,plain,(
% 11.50/2.01    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 11.50/2.01    inference(cnf_transformation,[],[f25])).
% 11.50/2.01  
% 11.50/2.01  fof(f17,axiom,(
% 11.50/2.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 11.50/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.50/2.01  
% 11.50/2.01  fof(f39,plain,(
% 11.50/2.01    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 11.50/2.01    inference(ennf_transformation,[],[f17])).
% 11.50/2.01  
% 11.50/2.01  fof(f40,plain,(
% 11.50/2.01    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 11.50/2.01    inference(flattening,[],[f39])).
% 11.50/2.01  
% 11.50/2.01  fof(f67,plain,(
% 11.50/2.01    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X3) | k1_xboole_0 = X2 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 11.50/2.01    inference(cnf_transformation,[],[f40])).
% 11.50/2.01  
% 11.50/2.01  fof(f16,axiom,(
% 11.50/2.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 11.50/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.50/2.01  
% 11.50/2.01  fof(f37,plain,(
% 11.50/2.01    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 11.50/2.01    inference(ennf_transformation,[],[f16])).
% 11.50/2.01  
% 11.50/2.01  fof(f38,plain,(
% 11.50/2.01    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 11.50/2.01    inference(flattening,[],[f37])).
% 11.50/2.01  
% 11.50/2.01  fof(f66,plain,(
% 11.50/2.01    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 11.50/2.01    inference(cnf_transformation,[],[f38])).
% 11.50/2.01  
% 11.50/2.01  fof(f9,axiom,(
% 11.50/2.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 11.50/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.50/2.01  
% 11.50/2.01  fof(f28,plain,(
% 11.50/2.01    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.50/2.01    inference(ennf_transformation,[],[f9])).
% 11.50/2.01  
% 11.50/2.01  fof(f57,plain,(
% 11.50/2.01    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.50/2.01    inference(cnf_transformation,[],[f28])).
% 11.50/2.01  
% 11.50/2.01  fof(f6,axiom,(
% 11.50/2.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 11.50/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.50/2.01  
% 11.50/2.01  fof(f21,plain,(
% 11.50/2.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 11.50/2.01    inference(pure_predicate_removal,[],[f6])).
% 11.50/2.01  
% 11.50/2.01  fof(f24,plain,(
% 11.50/2.01    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.50/2.01    inference(ennf_transformation,[],[f21])).
% 11.50/2.01  
% 11.50/2.01  fof(f54,plain,(
% 11.50/2.01    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.50/2.01    inference(cnf_transformation,[],[f24])).
% 11.50/2.01  
% 11.50/2.01  fof(f12,axiom,(
% 11.50/2.01    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 11.50/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.50/2.01  
% 11.50/2.01  fof(f33,plain,(
% 11.50/2.01    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 11.50/2.01    inference(ennf_transformation,[],[f12])).
% 11.50/2.01  
% 11.50/2.01  fof(f34,plain,(
% 11.50/2.01    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 11.50/2.01    inference(flattening,[],[f33])).
% 11.50/2.01  
% 11.50/2.01  fof(f44,plain,(
% 11.50/2.01    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 11.50/2.01    inference(nnf_transformation,[],[f34])).
% 11.50/2.01  
% 11.50/2.01  fof(f62,plain,(
% 11.50/2.01    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.50/2.01    inference(cnf_transformation,[],[f44])).
% 11.50/2.01  
% 11.50/2.01  fof(f81,plain,(
% 11.50/2.01    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 11.50/2.01    inference(equality_resolution,[],[f62])).
% 11.50/2.01  
% 11.50/2.01  fof(f5,axiom,(
% 11.50/2.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 11.50/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.50/2.01  
% 11.50/2.01  fof(f23,plain,(
% 11.50/2.01    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.50/2.01    inference(ennf_transformation,[],[f5])).
% 11.50/2.01  
% 11.50/2.01  fof(f53,plain,(
% 11.50/2.01    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.50/2.01    inference(cnf_transformation,[],[f23])).
% 11.50/2.01  
% 11.50/2.01  fof(f76,plain,(
% 11.50/2.01    ~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)),
% 11.50/2.01    inference(cnf_transformation,[],[f47])).
% 11.50/2.01  
% 11.50/2.01  cnf(c_12,plain,
% 11.50/2.01      ( ~ r2_relset_1(X0,X1,X2,X3)
% 11.50/2.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.50/2.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.50/2.01      | X3 = X2 ),
% 11.50/2.01      inference(cnf_transformation,[],[f59]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_723,plain,
% 11.50/2.01      ( ~ r2_relset_1(X0_50,X1_50,X2_50,X3_50)
% 11.50/2.01      | ~ m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
% 11.50/2.01      | ~ m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
% 11.50/2.01      | X3_50 = X2_50 ),
% 11.50/2.01      inference(subtyping,[status(esa)],[c_12]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_15,plain,
% 11.50/2.01      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 11.50/2.01      inference(cnf_transformation,[],[f63]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_722,plain,
% 11.50/2.01      ( m1_subset_1(k6_partfun1(X0_50),k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50))) ),
% 11.50/2.01      inference(subtyping,[status(esa)],[c_15]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_7799,plain,
% 11.50/2.01      ( ~ r2_relset_1(X0_50,X0_50,X1_50,k6_partfun1(X0_50))
% 11.50/2.01      | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50)))
% 11.50/2.01      | k6_partfun1(X0_50) = X1_50 ),
% 11.50/2.01      inference(resolution,[status(thm)],[c_723,c_722]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_21,negated_conjecture,
% 11.50/2.01      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 11.50/2.01      inference(cnf_transformation,[],[f75]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_717,negated_conjecture,
% 11.50/2.01      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 11.50/2.01      inference(subtyping,[status(esa)],[c_21]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_27483,plain,
% 11.50/2.01      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.50/2.01      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 11.50/2.01      inference(resolution,[status(thm)],[c_7799,c_717]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_27,negated_conjecture,
% 11.50/2.01      ( v1_funct_1(sK2) ),
% 11.50/2.01      inference(cnf_transformation,[],[f69]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_25,negated_conjecture,
% 11.50/2.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 11.50/2.01      inference(cnf_transformation,[],[f71]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_24,negated_conjecture,
% 11.50/2.01      ( v1_funct_1(sK3) ),
% 11.50/2.01      inference(cnf_transformation,[],[f72]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_22,negated_conjecture,
% 11.50/2.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 11.50/2.01      inference(cnf_transformation,[],[f74]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_10,plain,
% 11.50/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.50/2.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 11.50/2.01      | k4_relset_1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 11.50/2.01      inference(cnf_transformation,[],[f58]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_725,plain,
% 11.50/2.01      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
% 11.50/2.01      | ~ m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X4_50,X5_50)))
% 11.50/2.01      | k4_relset_1(X4_50,X5_50,X1_50,X2_50,X3_50,X0_50) = k5_relat_1(X3_50,X0_50) ),
% 11.50/2.01      inference(subtyping,[status(esa)],[c_10]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_1535,plain,
% 11.50/2.01      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
% 11.50/2.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 11.50/2.01      | k4_relset_1(sK0,sK1,X1_50,X2_50,sK2,X0_50) = k5_relat_1(sK2,X0_50) ),
% 11.50/2.01      inference(instantiation,[status(thm)],[c_725]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_1751,plain,
% 11.50/2.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 11.50/2.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 11.50/2.01      | k4_relset_1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 11.50/2.01      inference(instantiation,[status(thm)],[c_1535]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_8,plain,
% 11.50/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.50/2.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 11.50/2.01      | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) ),
% 11.50/2.01      inference(cnf_transformation,[],[f56]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_727,plain,
% 11.50/2.01      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
% 11.50/2.01      | ~ m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X4_50,X5_50)))
% 11.50/2.01      | m1_subset_1(k4_relset_1(X4_50,X5_50,X1_50,X2_50,X3_50,X0_50),k1_zfmisc_1(k2_zfmisc_1(X4_50,X2_50))) ),
% 11.50/2.01      inference(subtyping,[status(esa)],[c_8]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_1550,plain,
% 11.50/2.01      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
% 11.50/2.01      | m1_subset_1(k4_relset_1(sK0,sK1,X1_50,X2_50,sK2,X0_50),k1_zfmisc_1(k2_zfmisc_1(sK0,X2_50)))
% 11.50/2.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 11.50/2.01      inference(instantiation,[status(thm)],[c_727]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_1794,plain,
% 11.50/2.01      ( m1_subset_1(k4_relset_1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.50/2.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 11.50/2.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 11.50/2.01      inference(instantiation,[status(thm)],[c_1550]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_737,plain,( X0_51 = X0_51 ),theory(equality) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_1988,plain,
% 11.50/2.01      ( k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50)) = k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50)) ),
% 11.50/2.01      inference(instantiation,[status(thm)],[c_737]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_3269,plain,
% 11.50/2.01      ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
% 11.50/2.01      inference(instantiation,[status(thm)],[c_1988]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_16,plain,
% 11.50/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.50/2.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 11.50/2.01      | ~ v1_funct_1(X0)
% 11.50/2.01      | ~ v1_funct_1(X3)
% 11.50/2.01      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 11.50/2.01      inference(cnf_transformation,[],[f64]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_721,plain,
% 11.50/2.01      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
% 11.50/2.01      | ~ m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X4_50,X5_50)))
% 11.50/2.01      | ~ v1_funct_1(X3_50)
% 11.50/2.01      | ~ v1_funct_1(X0_50)
% 11.50/2.01      | k1_partfun1(X4_50,X5_50,X1_50,X2_50,X3_50,X0_50) = k5_relat_1(X3_50,X0_50) ),
% 11.50/2.01      inference(subtyping,[status(esa)],[c_16]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_1560,plain,
% 11.50/2.01      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
% 11.50/2.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3_50,X4_50)))
% 11.50/2.01      | ~ v1_funct_1(X0_50)
% 11.50/2.01      | ~ v1_funct_1(sK3)
% 11.50/2.01      | k1_partfun1(X1_50,X2_50,X3_50,X4_50,X0_50,sK3) = k5_relat_1(X0_50,sK3) ),
% 11.50/2.01      inference(instantiation,[status(thm)],[c_721]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_1815,plain,
% 11.50/2.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
% 11.50/2.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2_50,X3_50)))
% 11.50/2.01      | ~ v1_funct_1(sK2)
% 11.50/2.01      | ~ v1_funct_1(sK3)
% 11.50/2.01      | k1_partfun1(X0_50,X1_50,X2_50,X3_50,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 11.50/2.01      inference(instantiation,[status(thm)],[c_1560]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_2350,plain,
% 11.50/2.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
% 11.50/2.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 11.50/2.01      | ~ v1_funct_1(sK2)
% 11.50/2.01      | ~ v1_funct_1(sK3)
% 11.50/2.01      | k1_partfun1(X0_50,X1_50,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 11.50/2.01      inference(instantiation,[status(thm)],[c_1815]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_3664,plain,
% 11.50/2.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 11.50/2.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 11.50/2.01      | ~ v1_funct_1(sK2)
% 11.50/2.01      | ~ v1_funct_1(sK3)
% 11.50/2.01      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 11.50/2.01      inference(instantiation,[status(thm)],[c_2350]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_739,plain,
% 11.50/2.01      ( X0_50 != X1_50 | X2_50 != X1_50 | X2_50 = X0_50 ),
% 11.50/2.01      theory(equality) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_3630,plain,
% 11.50/2.01      ( X0_50 != X1_50
% 11.50/2.01      | k1_partfun1(X2_50,X3_50,X3_50,X4_50,X5_50,X6_50) != X1_50
% 11.50/2.01      | k1_partfun1(X2_50,X3_50,X3_50,X4_50,X5_50,X6_50) = X0_50 ),
% 11.50/2.01      inference(instantiation,[status(thm)],[c_739]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_5808,plain,
% 11.50/2.01      ( X0_50 != k5_relat_1(sK2,sK3)
% 11.50/2.01      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = X0_50
% 11.50/2.01      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != k5_relat_1(sK2,sK3) ),
% 11.50/2.01      inference(instantiation,[status(thm)],[c_3630]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_7483,plain,
% 11.50/2.01      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k4_relset_1(sK0,sK1,sK1,sK0,sK2,sK3)
% 11.50/2.01      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != k5_relat_1(sK2,sK3)
% 11.50/2.01      | k4_relset_1(sK0,sK1,sK1,sK0,sK2,sK3) != k5_relat_1(sK2,sK3) ),
% 11.50/2.01      inference(instantiation,[status(thm)],[c_5808]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_745,plain,
% 11.50/2.01      ( ~ m1_subset_1(X0_50,X0_51)
% 11.50/2.01      | m1_subset_1(X1_50,X1_51)
% 11.50/2.01      | X1_51 != X0_51
% 11.50/2.01      | X1_50 != X0_50 ),
% 11.50/2.01      theory(equality) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_2186,plain,
% 11.50/2.01      ( m1_subset_1(X0_50,X0_51)
% 11.50/2.01      | ~ m1_subset_1(k4_relset_1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.50/2.01      | X0_51 != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
% 11.50/2.01      | X0_50 != k4_relset_1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 11.50/2.01      inference(instantiation,[status(thm)],[c_745]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_3270,plain,
% 11.50/2.01      ( m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.50/2.01      | ~ m1_subset_1(k4_relset_1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.50/2.01      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
% 11.50/2.01      | X0_50 != k4_relset_1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 11.50/2.01      inference(instantiation,[status(thm)],[c_2186]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_7484,plain,
% 11.50/2.01      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.50/2.01      | ~ m1_subset_1(k4_relset_1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.50/2.01      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
% 11.50/2.01      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != k4_relset_1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 11.50/2.01      inference(instantiation,[status(thm)],[c_3270]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_8337,plain,
% 11.50/2.01      ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 11.50/2.01      inference(instantiation,[status(thm)],[c_722]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_5525,plain,
% 11.50/2.01      ( ~ r2_relset_1(X0_50,X1_50,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),X2_50)
% 11.50/2.01      | ~ m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
% 11.50/2.01      | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
% 11.50/2.01      | X2_50 = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 11.50/2.01      inference(instantiation,[status(thm)],[c_723]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_13531,plain,
% 11.50/2.01      ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
% 11.50/2.01      | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.50/2.01      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.50/2.01      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 11.50/2.01      inference(instantiation,[status(thm)],[c_5525]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_29013,plain,
% 11.50/2.01      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 11.50/2.01      inference(global_propositional_subsumption,
% 11.50/2.01                [status(thm)],
% 11.50/2.01                [c_27483,c_27,c_25,c_24,c_22,c_21,c_1751,c_1794,c_3269,
% 11.50/2.01                 c_3664,c_7483,c_7484,c_8337,c_13531]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_747,plain,
% 11.50/2.01      ( ~ r2_relset_1(X0_50,X1_50,X2_50,X3_50)
% 11.50/2.01      | r2_relset_1(X4_50,X5_50,X6_50,X7_50)
% 11.50/2.01      | X4_50 != X0_50
% 11.50/2.01      | X5_50 != X1_50
% 11.50/2.01      | X6_50 != X2_50
% 11.50/2.01      | X7_50 != X3_50 ),
% 11.50/2.01      theory(equality) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_2708,plain,
% 11.50/2.01      ( r2_relset_1(X0_50,X1_50,X2_50,X3_50)
% 11.50/2.01      | X2_50 != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 11.50/2.01      | X3_50 != k6_partfun1(sK0)
% 11.50/2.01      | X1_50 != sK0
% 11.50/2.01      | X0_50 != sK0 ),
% 11.50/2.01      inference(resolution,[status(thm)],[c_747,c_717]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_29268,plain,
% 11.50/2.01      ( r2_relset_1(X0_50,X1_50,k6_partfun1(sK0),X2_50)
% 11.50/2.01      | X2_50 != k6_partfun1(sK0)
% 11.50/2.01      | X1_50 != sK0
% 11.50/2.01      | X0_50 != sK0 ),
% 11.50/2.01      inference(resolution,[status(thm)],[c_29013,c_2708]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_28,plain,
% 11.50/2.01      ( v1_funct_1(sK2) = iProver_top ),
% 11.50/2.01      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_26,negated_conjecture,
% 11.50/2.01      ( v1_funct_2(sK2,sK0,sK1) ),
% 11.50/2.01      inference(cnf_transformation,[],[f70]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_29,plain,
% 11.50/2.01      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 11.50/2.01      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_30,plain,
% 11.50/2.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 11.50/2.01      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_31,plain,
% 11.50/2.01      ( v1_funct_1(sK3) = iProver_top ),
% 11.50/2.01      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_23,negated_conjecture,
% 11.50/2.01      ( v1_funct_2(sK3,sK1,sK0) ),
% 11.50/2.01      inference(cnf_transformation,[],[f73]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_32,plain,
% 11.50/2.01      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 11.50/2.01      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_33,plain,
% 11.50/2.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 11.50/2.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_3,plain,
% 11.50/2.01      ( v2_funct_1(k6_partfun1(X0)) ),
% 11.50/2.01      inference(cnf_transformation,[],[f78]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_82,plain,
% 11.50/2.01      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 11.50/2.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_84,plain,
% 11.50/2.01      ( v2_funct_1(k6_partfun1(k1_xboole_0)) = iProver_top ),
% 11.50/2.01      inference(instantiation,[status(thm)],[c_82]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_0,plain,
% 11.50/2.01      ( v1_xboole_0(k1_xboole_0) ),
% 11.50/2.01      inference(cnf_transformation,[],[f48]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_736,plain,( X0_50 = X0_50 ),theory(equality) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_763,plain,
% 11.50/2.01      ( k1_xboole_0 = k1_xboole_0 ),
% 11.50/2.01      inference(instantiation,[status(thm)],[c_736]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_2,plain,
% 11.50/2.01      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 11.50/2.01      inference(cnf_transformation,[],[f77]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_730,plain,
% 11.50/2.01      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 11.50/2.01      inference(subtyping,[status(esa)],[c_2]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_729,plain,
% 11.50/2.01      ( v2_funct_1(k6_partfun1(X0_50)) ),
% 11.50/2.01      inference(subtyping,[status(esa)],[c_3]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_768,plain,
% 11.50/2.01      ( v2_funct_1(k6_partfun1(X0_50)) = iProver_top ),
% 11.50/2.01      inference(predicate_to_equality,[status(thm)],[c_729]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_742,plain,
% 11.50/2.01      ( ~ v2_funct_1(X0_50) | v2_funct_1(X1_50) | X1_50 != X0_50 ),
% 11.50/2.01      theory(equality) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_1446,plain,
% 11.50/2.01      ( v2_funct_1(X0_50)
% 11.50/2.01      | ~ v2_funct_1(k6_partfun1(X1_50))
% 11.50/2.01      | X0_50 != k6_partfun1(X1_50) ),
% 11.50/2.01      inference(instantiation,[status(thm)],[c_742]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_1447,plain,
% 11.50/2.01      ( X0_50 != k6_partfun1(X1_50)
% 11.50/2.01      | v2_funct_1(X0_50) = iProver_top
% 11.50/2.01      | v2_funct_1(k6_partfun1(X1_50)) != iProver_top ),
% 11.50/2.01      inference(predicate_to_equality,[status(thm)],[c_1446]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_1449,plain,
% 11.50/2.01      ( k1_xboole_0 != k6_partfun1(k1_xboole_0)
% 11.50/2.01      | v2_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top
% 11.50/2.01      | v2_funct_1(k1_xboole_0) = iProver_top ),
% 11.50/2.01      inference(instantiation,[status(thm)],[c_1447]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_1784,plain,
% 11.50/2.01      ( X0_50 != X1_50
% 11.50/2.01      | X0_50 = k6_partfun1(X2_50)
% 11.50/2.01      | k6_partfun1(X2_50) != X1_50 ),
% 11.50/2.01      inference(instantiation,[status(thm)],[c_739]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_1785,plain,
% 11.50/2.01      ( k6_partfun1(k1_xboole_0) != k1_xboole_0
% 11.50/2.01      | k1_xboole_0 = k6_partfun1(k1_xboole_0)
% 11.50/2.01      | k1_xboole_0 != k1_xboole_0 ),
% 11.50/2.01      inference(instantiation,[status(thm)],[c_1784]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_1,plain,
% 11.50/2.01      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X1 = X0 ),
% 11.50/2.01      inference(cnf_transformation,[],[f49]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_731,plain,
% 11.50/2.01      ( ~ v1_xboole_0(X0_50) | ~ v1_xboole_0(X1_50) | X1_50 = X0_50 ),
% 11.50/2.01      inference(subtyping,[status(esa)],[c_1]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_1954,plain,
% 11.50/2.01      ( ~ v1_xboole_0(X0_50) | ~ v1_xboole_0(sK2) | sK2 = X0_50 ),
% 11.50/2.01      inference(instantiation,[status(thm)],[c_731]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_1956,plain,
% 11.50/2.01      ( ~ v1_xboole_0(sK2) | ~ v1_xboole_0(k1_xboole_0) | sK2 = k1_xboole_0 ),
% 11.50/2.01      inference(instantiation,[status(thm)],[c_1954]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_713,negated_conjecture,
% 11.50/2.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 11.50/2.01      inference(subtyping,[status(esa)],[c_25]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_1229,plain,
% 11.50/2.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 11.50/2.01      inference(predicate_to_equality,[status(thm)],[c_713]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_7,plain,
% 11.50/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.50/2.01      | ~ v1_xboole_0(X1)
% 11.50/2.01      | v1_xboole_0(X0) ),
% 11.50/2.01      inference(cnf_transformation,[],[f55]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_728,plain,
% 11.50/2.01      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
% 11.50/2.01      | ~ v1_xboole_0(X1_50)
% 11.50/2.01      | v1_xboole_0(X0_50) ),
% 11.50/2.01      inference(subtyping,[status(esa)],[c_7]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_1214,plain,
% 11.50/2.01      ( m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50))) != iProver_top
% 11.50/2.01      | v1_xboole_0(X1_50) != iProver_top
% 11.50/2.01      | v1_xboole_0(X0_50) = iProver_top ),
% 11.50/2.01      inference(predicate_to_equality,[status(thm)],[c_728]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_2406,plain,
% 11.50/2.01      ( v1_xboole_0(sK2) = iProver_top | v1_xboole_0(sK0) != iProver_top ),
% 11.50/2.01      inference(superposition,[status(thm)],[c_1229,c_1214]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_2422,plain,
% 11.50/2.01      ( v1_xboole_0(sK2) | ~ v1_xboole_0(sK0) ),
% 11.50/2.01      inference(predicate_to_equality_rev,[status(thm)],[c_2406]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_740,plain,
% 11.50/2.01      ( ~ v1_xboole_0(X0_50) | v1_xboole_0(X1_50) | X1_50 != X0_50 ),
% 11.50/2.01      theory(equality) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_2602,plain,
% 11.50/2.01      ( ~ v1_xboole_0(X0_50) | v1_xboole_0(sK0) | sK0 != X0_50 ),
% 11.50/2.01      inference(instantiation,[status(thm)],[c_740]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_2604,plain,
% 11.50/2.01      ( v1_xboole_0(sK0) | ~ v1_xboole_0(k1_xboole_0) | sK0 != k1_xboole_0 ),
% 11.50/2.01      inference(instantiation,[status(thm)],[c_2602]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_3252,plain,
% 11.50/2.01      ( ~ v2_funct_1(X0_50) | v2_funct_1(sK2) | sK2 != X0_50 ),
% 11.50/2.01      inference(instantiation,[status(thm)],[c_742]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_3253,plain,
% 11.50/2.01      ( sK2 != X0_50
% 11.50/2.01      | v2_funct_1(X0_50) != iProver_top
% 11.50/2.01      | v2_funct_1(sK2) = iProver_top ),
% 11.50/2.01      inference(predicate_to_equality,[status(thm)],[c_3252]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_3255,plain,
% 11.50/2.01      ( sK2 != k1_xboole_0
% 11.50/2.01      | v2_funct_1(sK2) = iProver_top
% 11.50/2.01      | v2_funct_1(k1_xboole_0) != iProver_top ),
% 11.50/2.01      inference(instantiation,[status(thm)],[c_3253]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_716,negated_conjecture,
% 11.50/2.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 11.50/2.01      inference(subtyping,[status(esa)],[c_22]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_1226,plain,
% 11.50/2.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 11.50/2.01      inference(predicate_to_equality,[status(thm)],[c_716]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_1221,plain,
% 11.50/2.01      ( k1_partfun1(X0_50,X1_50,X2_50,X3_50,X4_50,X5_50) = k5_relat_1(X4_50,X5_50)
% 11.50/2.01      | m1_subset_1(X5_50,k1_zfmisc_1(k2_zfmisc_1(X2_50,X3_50))) != iProver_top
% 11.50/2.01      | m1_subset_1(X4_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
% 11.50/2.01      | v1_funct_1(X5_50) != iProver_top
% 11.50/2.01      | v1_funct_1(X4_50) != iProver_top ),
% 11.50/2.01      inference(predicate_to_equality,[status(thm)],[c_721]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_3120,plain,
% 11.50/2.01      ( k1_partfun1(X0_50,X1_50,sK1,sK0,X2_50,sK3) = k5_relat_1(X2_50,sK3)
% 11.50/2.01      | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
% 11.50/2.01      | v1_funct_1(X2_50) != iProver_top
% 11.50/2.01      | v1_funct_1(sK3) != iProver_top ),
% 11.50/2.01      inference(superposition,[status(thm)],[c_1226,c_1221]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_4108,plain,
% 11.50/2.01      ( v1_funct_1(X2_50) != iProver_top
% 11.50/2.01      | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
% 11.50/2.01      | k1_partfun1(X0_50,X1_50,sK1,sK0,X2_50,sK3) = k5_relat_1(X2_50,sK3) ),
% 11.50/2.01      inference(global_propositional_subsumption,[status(thm)],[c_3120,c_31]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_4109,plain,
% 11.50/2.01      ( k1_partfun1(X0_50,X1_50,sK1,sK0,X2_50,sK3) = k5_relat_1(X2_50,sK3)
% 11.50/2.01      | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
% 11.50/2.01      | v1_funct_1(X2_50) != iProver_top ),
% 11.50/2.01      inference(renaming,[status(thm)],[c_4108]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_4118,plain,
% 11.50/2.01      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 11.50/2.01      | v1_funct_1(sK2) != iProver_top ),
% 11.50/2.01      inference(superposition,[status(thm)],[c_1229,c_4109]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_4345,plain,
% 11.50/2.01      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 11.50/2.01      inference(global_propositional_subsumption,
% 11.50/2.01                [status(thm)],
% 11.50/2.01                [c_4118,c_27,c_25,c_24,c_22,c_3664]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_19,plain,
% 11.50/2.01      ( ~ v1_funct_2(X0,X1,X2)
% 11.50/2.01      | ~ v1_funct_2(X3,X2,X4)
% 11.50/2.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.50/2.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
% 11.50/2.01      | ~ v1_funct_1(X3)
% 11.50/2.01      | ~ v1_funct_1(X0)
% 11.50/2.01      | v2_funct_1(X0)
% 11.50/2.01      | ~ v2_funct_1(k1_partfun1(X1,X2,X2,X4,X0,X3))
% 11.50/2.01      | k1_xboole_0 = X4 ),
% 11.50/2.01      inference(cnf_transformation,[],[f67]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_718,plain,
% 11.50/2.01      ( ~ v1_funct_2(X0_50,X1_50,X2_50)
% 11.50/2.01      | ~ v1_funct_2(X3_50,X2_50,X4_50)
% 11.50/2.01      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
% 11.50/2.01      | ~ m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X2_50,X4_50)))
% 11.50/2.01      | ~ v1_funct_1(X3_50)
% 11.50/2.01      | ~ v1_funct_1(X0_50)
% 11.50/2.01      | v2_funct_1(X0_50)
% 11.50/2.01      | ~ v2_funct_1(k1_partfun1(X1_50,X2_50,X2_50,X4_50,X0_50,X3_50))
% 11.50/2.01      | k1_xboole_0 = X4_50 ),
% 11.50/2.01      inference(subtyping,[status(esa)],[c_19]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_1224,plain,
% 11.50/2.01      ( k1_xboole_0 = X0_50
% 11.50/2.01      | v1_funct_2(X1_50,X2_50,X3_50) != iProver_top
% 11.50/2.01      | v1_funct_2(X4_50,X3_50,X0_50) != iProver_top
% 11.50/2.01      | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_50,X3_50))) != iProver_top
% 11.50/2.01      | m1_subset_1(X4_50,k1_zfmisc_1(k2_zfmisc_1(X3_50,X0_50))) != iProver_top
% 11.50/2.01      | v1_funct_1(X1_50) != iProver_top
% 11.50/2.01      | v1_funct_1(X4_50) != iProver_top
% 11.50/2.01      | v2_funct_1(X1_50) = iProver_top
% 11.50/2.01      | v2_funct_1(k1_partfun1(X2_50,X3_50,X3_50,X0_50,X1_50,X4_50)) != iProver_top ),
% 11.50/2.01      inference(predicate_to_equality,[status(thm)],[c_718]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_4350,plain,
% 11.50/2.01      ( sK0 = k1_xboole_0
% 11.50/2.01      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 11.50/2.01      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 11.50/2.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 11.50/2.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 11.50/2.01      | v1_funct_1(sK2) != iProver_top
% 11.50/2.01      | v1_funct_1(sK3) != iProver_top
% 11.50/2.01      | v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
% 11.50/2.01      | v2_funct_1(sK2) = iProver_top ),
% 11.50/2.01      inference(superposition,[status(thm)],[c_4345,c_1224]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_7279,plain,
% 11.50/2.01      ( v2_funct_1(k5_relat_1(sK2,sK3))
% 11.50/2.01      | ~ v2_funct_1(k6_partfun1(X0_50))
% 11.50/2.01      | k5_relat_1(sK2,sK3) != k6_partfun1(X0_50) ),
% 11.50/2.01      inference(instantiation,[status(thm)],[c_1446]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_7280,plain,
% 11.50/2.01      ( k5_relat_1(sK2,sK3) != k6_partfun1(X0_50)
% 11.50/2.01      | v2_funct_1(k5_relat_1(sK2,sK3)) = iProver_top
% 11.50/2.01      | v2_funct_1(k6_partfun1(X0_50)) != iProver_top ),
% 11.50/2.01      inference(predicate_to_equality,[status(thm)],[c_7279]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_7752,plain,
% 11.50/2.01      ( k5_relat_1(sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 11.50/2.01      inference(instantiation,[status(thm)],[c_736]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_5541,plain,
% 11.50/2.01      ( X0_50 != X1_50
% 11.50/2.01      | X0_50 = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 11.50/2.01      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X1_50 ),
% 11.50/2.01      inference(instantiation,[status(thm)],[c_739]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_12684,plain,
% 11.50/2.01      ( X0_50 = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 11.50/2.01      | X0_50 != k5_relat_1(sK2,sK3)
% 11.50/2.01      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != k5_relat_1(sK2,sK3) ),
% 11.50/2.01      inference(instantiation,[status(thm)],[c_5541]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_18142,plain,
% 11.50/2.01      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != k5_relat_1(sK2,sK3)
% 11.50/2.01      | k5_relat_1(sK2,sK3) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 11.50/2.01      | k5_relat_1(sK2,sK3) != k5_relat_1(sK2,sK3) ),
% 11.50/2.01      inference(instantiation,[status(thm)],[c_12684]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_2564,plain,
% 11.50/2.01      ( X0_50 != X1_50 | X1_50 = X0_50 ),
% 11.50/2.01      inference(resolution,[status(thm)],[c_739,c_736]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_29203,plain,
% 11.50/2.01      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
% 11.50/2.01      inference(resolution,[status(thm)],[c_29013,c_2564]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_741,plain,
% 11.50/2.01      ( X0_50 != X1_50 | k6_partfun1(X0_50) = k6_partfun1(X1_50) ),
% 11.50/2.01      theory(equality) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_2565,plain,
% 11.50/2.01      ( X0_50 != X1_50
% 11.50/2.01      | X2_50 != k6_partfun1(X1_50)
% 11.50/2.01      | k6_partfun1(X0_50) = X2_50 ),
% 11.50/2.01      inference(resolution,[status(thm)],[c_739,c_741]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_29354,plain,
% 11.50/2.01      ( X0_50 != sK0
% 11.50/2.01      | k6_partfun1(X0_50) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 11.50/2.01      inference(resolution,[status(thm)],[c_29203,c_2565]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_1225,plain,
% 11.50/2.01      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) = iProver_top ),
% 11.50/2.01      inference(predicate_to_equality,[status(thm)],[c_717]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_17,plain,
% 11.50/2.01      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 11.50/2.01      | ~ v1_funct_2(X2,X0,X1)
% 11.50/2.01      | ~ v1_funct_2(X3,X1,X0)
% 11.50/2.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 11.50/2.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.50/2.01      | ~ v1_funct_1(X2)
% 11.50/2.01      | ~ v1_funct_1(X3)
% 11.50/2.01      | k2_relset_1(X1,X0,X3) = X0 ),
% 11.50/2.01      inference(cnf_transformation,[],[f66]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_720,plain,
% 11.50/2.01      ( ~ r2_relset_1(X0_50,X0_50,k1_partfun1(X0_50,X1_50,X1_50,X0_50,X2_50,X3_50),k6_partfun1(X0_50))
% 11.50/2.01      | ~ v1_funct_2(X2_50,X0_50,X1_50)
% 11.50/2.01      | ~ v1_funct_2(X3_50,X1_50,X0_50)
% 11.50/2.01      | ~ m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X0_50)))
% 11.50/2.01      | ~ m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
% 11.50/2.01      | ~ v1_funct_1(X3_50)
% 11.50/2.01      | ~ v1_funct_1(X2_50)
% 11.50/2.01      | k2_relset_1(X1_50,X0_50,X3_50) = X0_50 ),
% 11.50/2.01      inference(subtyping,[status(esa)],[c_17]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_1222,plain,
% 11.50/2.01      ( k2_relset_1(X0_50,X1_50,X2_50) = X1_50
% 11.50/2.01      | r2_relset_1(X1_50,X1_50,k1_partfun1(X1_50,X0_50,X0_50,X1_50,X3_50,X2_50),k6_partfun1(X1_50)) != iProver_top
% 11.50/2.01      | v1_funct_2(X2_50,X0_50,X1_50) != iProver_top
% 11.50/2.01      | v1_funct_2(X3_50,X1_50,X0_50) != iProver_top
% 11.50/2.01      | m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X0_50))) != iProver_top
% 11.50/2.01      | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
% 11.50/2.01      | v1_funct_1(X3_50) != iProver_top
% 11.50/2.01      | v1_funct_1(X2_50) != iProver_top ),
% 11.50/2.01      inference(predicate_to_equality,[status(thm)],[c_720]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_3490,plain,
% 11.50/2.01      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 11.50/2.01      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 11.50/2.01      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 11.50/2.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 11.50/2.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 11.50/2.01      | v1_funct_1(sK2) != iProver_top
% 11.50/2.01      | v1_funct_1(sK3) != iProver_top ),
% 11.50/2.01      inference(superposition,[status(thm)],[c_1225,c_1222]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_9,plain,
% 11.50/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.50/2.01      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 11.50/2.01      inference(cnf_transformation,[],[f57]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_726,plain,
% 11.50/2.01      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
% 11.50/2.01      | k2_relset_1(X1_50,X2_50,X0_50) = k2_relat_1(X0_50) ),
% 11.50/2.01      inference(subtyping,[status(esa)],[c_9]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_1216,plain,
% 11.50/2.01      ( k2_relset_1(X0_50,X1_50,X2_50) = k2_relat_1(X2_50)
% 11.50/2.01      | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top ),
% 11.50/2.01      inference(predicate_to_equality,[status(thm)],[c_726]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_2198,plain,
% 11.50/2.01      ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 11.50/2.01      inference(superposition,[status(thm)],[c_1226,c_1216]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_3515,plain,
% 11.50/2.01      ( k2_relat_1(sK3) = sK0
% 11.50/2.01      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 11.50/2.01      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 11.50/2.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 11.50/2.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 11.50/2.01      | v1_funct_1(sK2) != iProver_top
% 11.50/2.01      | v1_funct_1(sK3) != iProver_top ),
% 11.50/2.01      inference(demodulation,[status(thm)],[c_3490,c_2198]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_31446,plain,
% 11.50/2.01      ( k2_relat_1(sK3) = sK0 ),
% 11.50/2.01      inference(global_propositional_subsumption,
% 11.50/2.01                [status(thm)],
% 11.50/2.01                [c_3515,c_28,c_29,c_30,c_31,c_32,c_33]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_6,plain,
% 11.50/2.01      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 11.50/2.01      inference(cnf_transformation,[],[f54]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_13,plain,
% 11.50/2.01      ( v2_funct_2(X0,k2_relat_1(X0))
% 11.50/2.01      | ~ v5_relat_1(X0,k2_relat_1(X0))
% 11.50/2.01      | ~ v1_relat_1(X0) ),
% 11.50/2.01      inference(cnf_transformation,[],[f81]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_318,plain,
% 11.50/2.01      ( v2_funct_2(X0,k2_relat_1(X0))
% 11.50/2.01      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 11.50/2.01      | ~ v1_relat_1(X0)
% 11.50/2.01      | X0 != X1
% 11.50/2.01      | k2_relat_1(X0) != X3 ),
% 11.50/2.01      inference(resolution_lifted,[status(thm)],[c_6,c_13]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_319,plain,
% 11.50/2.01      ( v2_funct_2(X0,k2_relat_1(X0))
% 11.50/2.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
% 11.50/2.01      | ~ v1_relat_1(X0) ),
% 11.50/2.01      inference(unflattening,[status(thm)],[c_318]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_5,plain,
% 11.50/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 11.50/2.01      inference(cnf_transformation,[],[f53]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_329,plain,
% 11.50/2.01      ( v2_funct_2(X0,k2_relat_1(X0))
% 11.50/2.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0)))) ),
% 11.50/2.01      inference(forward_subsumption_resolution,[status(thm)],[c_319,c_5]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_20,negated_conjecture,
% 11.50/2.01      ( ~ v2_funct_2(sK3,sK0) | ~ v2_funct_1(sK2) ),
% 11.50/2.01      inference(cnf_transformation,[],[f76]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_344,plain,
% 11.50/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
% 11.50/2.01      | ~ v2_funct_1(sK2)
% 11.50/2.01      | k2_relat_1(X0) != sK0
% 11.50/2.01      | sK3 != X0 ),
% 11.50/2.01      inference(resolution_lifted,[status(thm)],[c_329,c_20]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_345,plain,
% 11.50/2.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3))))
% 11.50/2.01      | ~ v2_funct_1(sK2)
% 11.50/2.01      | k2_relat_1(sK3) != sK0 ),
% 11.50/2.01      inference(unflattening,[status(thm)],[c_344]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_710,plain,
% 11.50/2.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_50,k2_relat_1(sK3))))
% 11.50/2.01      | ~ v2_funct_1(sK2)
% 11.50/2.01      | k2_relat_1(sK3) != sK0 ),
% 11.50/2.01      inference(subtyping,[status(esa)],[c_345]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_734,plain,
% 11.50/2.01      ( ~ v2_funct_1(sK2) | sP0_iProver_split | k2_relat_1(sK3) != sK0 ),
% 11.50/2.01      inference(splitting,
% 11.50/2.01                [splitting(split),new_symbols(definition,[])],
% 11.50/2.01                [c_710]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_1232,plain,
% 11.50/2.01      ( k2_relat_1(sK3) != sK0
% 11.50/2.01      | v2_funct_1(sK2) != iProver_top
% 11.50/2.01      | sP0_iProver_split = iProver_top ),
% 11.50/2.01      inference(predicate_to_equality,[status(thm)],[c_734]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_31451,plain,
% 11.50/2.01      ( sK0 != sK0
% 11.50/2.01      | v2_funct_1(sK2) != iProver_top
% 11.50/2.01      | sP0_iProver_split = iProver_top ),
% 11.50/2.01      inference(demodulation,[status(thm)],[c_31446,c_1232]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_31452,plain,
% 11.50/2.01      ( v2_funct_1(sK2) != iProver_top | sP0_iProver_split = iProver_top ),
% 11.50/2.01      inference(equality_resolution_simp,[status(thm)],[c_31451]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_733,plain,
% 11.50/2.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_50,k2_relat_1(sK3))))
% 11.50/2.01      | ~ sP0_iProver_split ),
% 11.50/2.01      inference(splitting,
% 11.50/2.01                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 11.50/2.01                [c_710]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_1233,plain,
% 11.50/2.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_50,k2_relat_1(sK3)))) != iProver_top
% 11.50/2.01      | sP0_iProver_split != iProver_top ),
% 11.50/2.01      inference(predicate_to_equality,[status(thm)],[c_733]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_31450,plain,
% 11.50/2.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_50,sK0))) != iProver_top
% 11.50/2.01      | sP0_iProver_split != iProver_top ),
% 11.50/2.01      inference(demodulation,[status(thm)],[c_31446,c_1233]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_32386,plain,
% 11.50/2.01      ( sP0_iProver_split != iProver_top ),
% 11.50/2.01      inference(superposition,[status(thm)],[c_1226,c_31450]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_10318,plain,
% 11.50/2.01      ( k5_relat_1(sK2,sK3) != X0_50
% 11.50/2.01      | k5_relat_1(sK2,sK3) = k6_partfun1(X1_50)
% 11.50/2.01      | k6_partfun1(X1_50) != X0_50 ),
% 11.50/2.01      inference(instantiation,[status(thm)],[c_1784]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_33370,plain,
% 11.50/2.01      ( k5_relat_1(sK2,sK3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 11.50/2.01      | k5_relat_1(sK2,sK3) = k6_partfun1(X0_50)
% 11.50/2.01      | k6_partfun1(X0_50) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 11.50/2.01      inference(instantiation,[status(thm)],[c_10318]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_34221,plain,
% 11.50/2.01      ( X0_50 != sK0 ),
% 11.50/2.01      inference(global_propositional_subsumption,
% 11.50/2.01                [status(thm)],
% 11.50/2.01                [c_29268,c_27,c_28,c_29,c_25,c_30,c_24,c_31,c_32,c_22,c_33,
% 11.50/2.01                 c_84,c_0,c_763,c_730,c_768,c_1449,c_1785,c_1956,c_2422,
% 11.50/2.01                 c_2604,c_3255,c_3664,c_4350,c_7280,c_7752,c_18142,c_29354,
% 11.50/2.01                 c_31452,c_32386,c_33370]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_10589,plain,
% 11.50/2.01      ( ~ v1_funct_2(sK2,sK0,sK1)
% 11.50/2.01      | ~ v1_funct_2(sK3,sK1,sK0)
% 11.50/2.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 11.50/2.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 11.50/2.01      | ~ v1_funct_1(sK2)
% 11.50/2.01      | ~ v1_funct_1(sK3)
% 11.50/2.01      | k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 11.50/2.01      inference(resolution,[status(thm)],[c_720,c_717]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_1594,plain,
% 11.50/2.01      ( ~ r2_relset_1(X0_50,X0_50,k1_partfun1(X0_50,X1_50,X1_50,X0_50,sK2,X2_50),k6_partfun1(X0_50))
% 11.50/2.01      | ~ v1_funct_2(X2_50,X1_50,X0_50)
% 11.50/2.01      | ~ v1_funct_2(sK2,X0_50,X1_50)
% 11.50/2.01      | ~ m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X0_50)))
% 11.50/2.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
% 11.50/2.01      | ~ v1_funct_1(X2_50)
% 11.50/2.01      | ~ v1_funct_1(sK2)
% 11.50/2.01      | k2_relset_1(X1_50,X0_50,X2_50) = X0_50 ),
% 11.50/2.01      inference(instantiation,[status(thm)],[c_720]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_1858,plain,
% 11.50/2.01      ( ~ r2_relset_1(X0_50,X0_50,k1_partfun1(X0_50,X1_50,X1_50,X0_50,sK2,sK3),k6_partfun1(X0_50))
% 11.50/2.01      | ~ v1_funct_2(sK2,X0_50,X1_50)
% 11.50/2.01      | ~ v1_funct_2(sK3,X1_50,X0_50)
% 11.50/2.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
% 11.50/2.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1_50,X0_50)))
% 11.50/2.01      | ~ v1_funct_1(sK2)
% 11.50/2.01      | ~ v1_funct_1(sK3)
% 11.50/2.01      | k2_relset_1(X1_50,X0_50,sK3) = X0_50 ),
% 11.50/2.01      inference(instantiation,[status(thm)],[c_1594]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_2365,plain,
% 11.50/2.01      ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
% 11.50/2.01      | ~ v1_funct_2(sK2,sK0,sK1)
% 11.50/2.01      | ~ v1_funct_2(sK3,sK1,sK0)
% 11.50/2.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 11.50/2.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 11.50/2.01      | ~ v1_funct_1(sK2)
% 11.50/2.01      | ~ v1_funct_1(sK3)
% 11.50/2.01      | k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 11.50/2.01      inference(instantiation,[status(thm)],[c_1858]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_10822,plain,
% 11.50/2.01      ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 11.50/2.01      inference(global_propositional_subsumption,
% 11.50/2.01                [status(thm)],
% 11.50/2.01                [c_10589,c_27,c_26,c_25,c_24,c_23,c_22,c_21,c_2365]) ).
% 11.50/2.01  
% 11.50/2.01  cnf(c_34889,plain,
% 11.50/2.01      ( $false ),
% 11.50/2.01      inference(backward_subsumption_resolution,
% 11.50/2.01                [status(thm)],
% 11.50/2.01                [c_34221,c_10822]) ).
% 11.50/2.01  
% 11.50/2.01  
% 11.50/2.01  % SZS output end CNFRefutation for theBenchmark.p
% 11.50/2.01  
% 11.50/2.01  ------                               Statistics
% 11.50/2.01  
% 11.50/2.01  ------ Selected
% 11.50/2.01  
% 11.50/2.01  total_time:                             1.097
% 11.50/2.01  
%------------------------------------------------------------------------------
