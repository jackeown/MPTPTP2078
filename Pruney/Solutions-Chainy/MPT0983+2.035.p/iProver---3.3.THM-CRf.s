%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:01:52 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 507 expanded)
%              Number of clauses        :   91 ( 162 expanded)
%              Number of leaves         :   19 ( 124 expanded)
%              Depth                    :   18
%              Number of atoms          :  575 (3391 expanded)
%              Number of equality atoms :  162 ( 261 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f29])).

fof(f56,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f25])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f15,conjecture,(
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

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f40,plain,(
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

fof(f39,plain,
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

fof(f41,plain,
    ( ( ~ v2_funct_2(sK3,sK0)
      | ~ v2_funct_1(sK2) )
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f36,f40,f39])).

fof(f68,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f41])).

fof(f11,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f57,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f62,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f64,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f41])).

fof(f65,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f67,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f41])).

fof(f14,axiom,(
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

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f60,plain,(
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
    inference(cnf_transformation,[],[f34])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f13,axiom,(
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

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f63,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f66,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f72,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f54])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f69,plain,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0)
        & v1_xboole_0(X0) )
     => ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f20,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f45,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f12,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f70,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f46,f58])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_653,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | ~ m1_subset_1(X3_48,k1_zfmisc_1(k2_zfmisc_1(X4_48,X5_48)))
    | m1_subset_1(k1_partfun1(X4_48,X5_48,X1_48,X2_48,X3_48,X0_48),k1_zfmisc_1(k2_zfmisc_1(X4_48,X2_48)))
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(X3_48) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1090,plain,
    ( m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48))) != iProver_top
    | m1_subset_1(X3_48,k1_zfmisc_1(k2_zfmisc_1(X4_48,X5_48))) != iProver_top
    | m1_subset_1(k1_partfun1(X4_48,X5_48,X1_48,X2_48,X3_48,X0_48),k1_zfmisc_1(k2_zfmisc_1(X4_48,X2_48))) = iProver_top
    | v1_funct_1(X3_48) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_653])).

cnf(c_10,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_20,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_405,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_20])).

cnf(c_406,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_405])).

cnf(c_15,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_45,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_408,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_406,c_45])).

cnf(c_640,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_408])).

cnf(c_1104,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_640])).

cnf(c_2203,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1090,c_1104])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_27,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_29,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_30,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_32,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2553,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2203,c_27,c_29,c_30,c_32])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v2_funct_1(X3)
    | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_649,plain,
    ( ~ v1_funct_2(X0_48,X1_48,X2_48)
    | ~ v1_funct_2(X3_48,X4_48,X1_48)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | ~ m1_subset_1(X3_48,k1_zfmisc_1(k2_zfmisc_1(X4_48,X1_48)))
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(X3_48)
    | v2_funct_1(X3_48)
    | ~ v2_funct_1(k1_partfun1(X4_48,X1_48,X1_48,X2_48,X3_48,X0_48))
    | k1_xboole_0 = X2_48 ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1094,plain,
    ( k1_xboole_0 = X0_48
    | v1_funct_2(X1_48,X2_48,X0_48) != iProver_top
    | v1_funct_2(X3_48,X4_48,X2_48) != iProver_top
    | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_48,X0_48))) != iProver_top
    | m1_subset_1(X3_48,k1_zfmisc_1(k2_zfmisc_1(X4_48,X2_48))) != iProver_top
    | v1_funct_1(X3_48) != iProver_top
    | v1_funct_1(X1_48) != iProver_top
    | v2_funct_1(X3_48) = iProver_top
    | v2_funct_1(k1_partfun1(X4_48,X2_48,X2_48,X0_48,X3_48,X1_48)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_649])).

cnf(c_2632,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2553,c_1094])).

cnf(c_648,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1095,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_648])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_654,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | k2_relset_1(X1_48,X2_48,X0_48) = k2_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1089,plain,
    ( k2_relset_1(X0_48,X1_48,X2_48) = k2_relat_1(X2_48)
    | m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_654])).

cnf(c_2150,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1095,c_1089])).

cnf(c_16,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_419,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k1_partfun1(X1,X2,X2,X1,X0,X3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X2,X1,X3) = X1
    | k6_partfun1(X1) != k6_partfun1(sK0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_20])).

cnf(c_420,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X0)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0
    | k6_partfun1(sK0) != k6_partfun1(sK0) ),
    inference(unflattening,[status(thm)],[c_419])).

cnf(c_495,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_420])).

cnf(c_639,plain,
    ( ~ v1_funct_2(X0_48,X1_48,sK0)
    | ~ v1_funct_2(X2_48,sK0,X1_48)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,sK0)))
    | ~ m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(sK0,X1_48)))
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(X2_48)
    | k1_partfun1(sK0,X1_48,X1_48,sK0,X2_48,X0_48) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1_48,sK0,X0_48) = sK0 ),
    inference(subtyping,[status(esa)],[c_495])).

cnf(c_1105,plain,
    ( k1_partfun1(sK0,X0_48,X0_48,sK0,X1_48,X2_48) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X0_48,sK0,X2_48) = sK0
    | v1_funct_2(X2_48,X0_48,sK0) != iProver_top
    | v1_funct_2(X1_48,sK0,X0_48) != iProver_top
    | m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,sK0))) != iProver_top
    | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_48))) != iProver_top
    | v1_funct_1(X2_48) != iProver_top
    | v1_funct_1(X1_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_639])).

cnf(c_2035,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1105])).

cnf(c_25,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_22,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1295,plain,
    ( ~ v1_funct_2(X0_48,sK0,X1_48)
    | ~ v1_funct_2(sK3,X1_48,sK0)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(sK0,X1_48)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1_48,sK0)))
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(sK0,X1_48,X1_48,sK0,X0_48,sK3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1_48,sK0,sK3) = sK0 ),
    inference(instantiation,[status(thm)],[c_639])).

cnf(c_1536,plain,
    ( ~ v1_funct_2(sK2,sK0,X0_48)
    | ~ v1_funct_2(sK3,X0_48,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_48)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_48,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(sK0,X0_48,X0_48,sK0,sK2,sK3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X0_48,sK0,sK3) = sK0 ),
    inference(instantiation,[status(thm)],[c_1295])).

cnf(c_1740,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(instantiation,[status(thm)],[c_1536])).

cnf(c_663,plain,
    ( X0_48 = X0_48 ),
    theory(equality)).

cnf(c_1983,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_663])).

cnf(c_2038,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2035,c_26,c_25,c_24,c_23,c_22,c_21,c_1740,c_1983])).

cnf(c_2158,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_2150,c_2038])).

cnf(c_6,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_11,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_302,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X0)
    | X0 != X1
    | k2_relat_1(X0) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_11])).

cnf(c_303,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_302])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_313,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0)))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_303,c_5])).

cnf(c_19,negated_conjecture,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_349,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
    | ~ v2_funct_1(sK2)
    | k2_relat_1(X0) != sK0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_313,c_19])).

cnf(c_350,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3))))
    | ~ v2_funct_1(sK2)
    | k2_relat_1(sK3) != sK0 ),
    inference(unflattening,[status(thm)],[c_349])).

cnf(c_642,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_48,k2_relat_1(sK3))))
    | ~ v2_funct_1(sK2)
    | k2_relat_1(sK3) != sK0 ),
    inference(subtyping,[status(esa)],[c_350])).

cnf(c_660,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_48,k2_relat_1(sK3))))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_642])).

cnf(c_1102,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_48,k2_relat_1(sK3)))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_660])).

cnf(c_2421,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_48,sK0))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(demodulation,[status(thm)],[c_2158,c_1102])).

cnf(c_2521,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_1095,c_2421])).

cnf(c_661,plain,
    ( ~ v2_funct_1(sK2)
    | sP0_iProver_split
    | k2_relat_1(sK3) != sK0 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_642])).

cnf(c_1101,plain,
    ( k2_relat_1(sK3) != sK0
    | v2_funct_1(sK2) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_661])).

cnf(c_2422,plain,
    ( sK0 != sK0
    | v2_funct_1(sK2) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_2158,c_1101])).

cnf(c_2423,plain,
    ( v2_funct_1(sK2) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2422])).

cnf(c_645,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1098,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_645])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_655,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | ~ v1_xboole_0(X1_48)
    | v1_xboole_0(X0_48) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1088,plain,
    ( m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48))) != iProver_top
    | v1_xboole_0(X1_48) != iProver_top
    | v1_xboole_0(X0_48) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_655])).

cnf(c_2088,plain,
    ( v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1098,c_1088])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_658,plain,
    ( ~ v1_relat_1(X0_48)
    | ~ v1_funct_1(X0_48)
    | v2_funct_1(X0_48)
    | ~ v1_xboole_0(X0_48) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1442,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | v2_funct_1(sK2)
    | ~ v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_658])).

cnf(c_1443,plain,
    ( v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) = iProver_top
    | v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1442])).

cnf(c_667,plain,
    ( ~ v1_xboole_0(X0_48)
    | v1_xboole_0(X1_48)
    | X1_48 != X0_48 ),
    theory(equality)).

cnf(c_1434,plain,
    ( v1_xboole_0(X0_48)
    | ~ v1_xboole_0(k1_xboole_0)
    | X0_48 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_667])).

cnf(c_1435,plain,
    ( X0_48 != k1_xboole_0
    | v1_xboole_0(X0_48) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1434])).

cnf(c_1437,plain,
    ( sK0 != k1_xboole_0
    | v1_xboole_0(sK0) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1435])).

cnf(c_656,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | v1_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1312,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_656])).

cnf(c_1313,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1312])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_83,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_75,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_77,plain,
    ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_75])).

cnf(c_31,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_28,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2632,c_2521,c_2423,c_2088,c_1443,c_1437,c_1313,c_83,c_77,c_32,c_31,c_30,c_29,c_28,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.14/0.33  % Computer   : n011.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 10:15:57 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 2.69/0.92  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/0.92  
% 2.69/0.92  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.69/0.92  
% 2.69/0.92  ------  iProver source info
% 2.69/0.92  
% 2.69/0.92  git: date: 2020-06-30 10:37:57 +0100
% 2.69/0.92  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.69/0.92  git: non_committed_changes: false
% 2.69/0.92  git: last_make_outside_of_git: false
% 2.69/0.92  
% 2.69/0.92  ------ 
% 2.69/0.92  
% 2.69/0.92  ------ Input Options
% 2.69/0.92  
% 2.69/0.92  --out_options                           all
% 2.69/0.92  --tptp_safe_out                         true
% 2.69/0.92  --problem_path                          ""
% 2.69/0.92  --include_path                          ""
% 2.69/0.92  --clausifier                            res/vclausify_rel
% 2.69/0.92  --clausifier_options                    --mode clausify
% 2.69/0.92  --stdin                                 false
% 2.69/0.92  --stats_out                             all
% 2.69/0.92  
% 2.69/0.92  ------ General Options
% 2.69/0.92  
% 2.69/0.92  --fof                                   false
% 2.69/0.92  --time_out_real                         305.
% 2.69/0.92  --time_out_virtual                      -1.
% 2.69/0.92  --symbol_type_check                     false
% 2.69/0.92  --clausify_out                          false
% 2.69/0.92  --sig_cnt_out                           false
% 2.69/0.92  --trig_cnt_out                          false
% 2.69/0.92  --trig_cnt_out_tolerance                1.
% 2.69/0.92  --trig_cnt_out_sk_spl                   false
% 2.69/0.92  --abstr_cl_out                          false
% 2.69/0.92  
% 2.69/0.92  ------ Global Options
% 2.69/0.92  
% 2.69/0.92  --schedule                              default
% 2.69/0.92  --add_important_lit                     false
% 2.69/0.92  --prop_solver_per_cl                    1000
% 2.69/0.92  --min_unsat_core                        false
% 2.69/0.92  --soft_assumptions                      false
% 2.69/0.92  --soft_lemma_size                       3
% 2.69/0.92  --prop_impl_unit_size                   0
% 2.69/0.92  --prop_impl_unit                        []
% 2.69/0.92  --share_sel_clauses                     true
% 2.69/0.92  --reset_solvers                         false
% 2.69/0.92  --bc_imp_inh                            [conj_cone]
% 2.69/0.92  --conj_cone_tolerance                   3.
% 2.69/0.92  --extra_neg_conj                        none
% 2.69/0.92  --large_theory_mode                     true
% 2.69/0.92  --prolific_symb_bound                   200
% 2.69/0.92  --lt_threshold                          2000
% 2.69/0.92  --clause_weak_htbl                      true
% 2.69/0.92  --gc_record_bc_elim                     false
% 2.69/0.92  
% 2.69/0.92  ------ Preprocessing Options
% 2.69/0.92  
% 2.69/0.92  --preprocessing_flag                    true
% 2.69/0.92  --time_out_prep_mult                    0.1
% 2.69/0.92  --splitting_mode                        input
% 2.69/0.92  --splitting_grd                         true
% 2.69/0.92  --splitting_cvd                         false
% 2.69/0.92  --splitting_cvd_svl                     false
% 2.69/0.92  --splitting_nvd                         32
% 2.69/0.92  --sub_typing                            true
% 2.69/0.92  --prep_gs_sim                           true
% 2.69/0.92  --prep_unflatten                        true
% 2.69/0.92  --prep_res_sim                          true
% 2.69/0.92  --prep_upred                            true
% 2.69/0.92  --prep_sem_filter                       exhaustive
% 2.69/0.92  --prep_sem_filter_out                   false
% 2.69/0.92  --pred_elim                             true
% 2.69/0.92  --res_sim_input                         true
% 2.69/0.92  --eq_ax_congr_red                       true
% 2.69/0.92  --pure_diseq_elim                       true
% 2.69/0.92  --brand_transform                       false
% 2.69/0.92  --non_eq_to_eq                          false
% 2.69/0.92  --prep_def_merge                        true
% 2.69/0.92  --prep_def_merge_prop_impl              false
% 2.69/0.92  --prep_def_merge_mbd                    true
% 2.69/0.92  --prep_def_merge_tr_red                 false
% 2.69/0.92  --prep_def_merge_tr_cl                  false
% 2.69/0.92  --smt_preprocessing                     true
% 2.69/0.92  --smt_ac_axioms                         fast
% 2.69/0.92  --preprocessed_out                      false
% 2.69/0.92  --preprocessed_stats                    false
% 2.69/0.92  
% 2.69/0.92  ------ Abstraction refinement Options
% 2.69/0.92  
% 2.69/0.92  --abstr_ref                             []
% 2.69/0.92  --abstr_ref_prep                        false
% 2.69/0.92  --abstr_ref_until_sat                   false
% 2.69/0.92  --abstr_ref_sig_restrict                funpre
% 2.69/0.92  --abstr_ref_af_restrict_to_split_sk     false
% 2.69/0.92  --abstr_ref_under                       []
% 2.69/0.92  
% 2.69/0.92  ------ SAT Options
% 2.69/0.92  
% 2.69/0.92  --sat_mode                              false
% 2.69/0.92  --sat_fm_restart_options                ""
% 2.69/0.92  --sat_gr_def                            false
% 2.69/0.92  --sat_epr_types                         true
% 2.69/0.92  --sat_non_cyclic_types                  false
% 2.69/0.92  --sat_finite_models                     false
% 2.69/0.92  --sat_fm_lemmas                         false
% 2.69/0.92  --sat_fm_prep                           false
% 2.69/0.92  --sat_fm_uc_incr                        true
% 2.69/0.92  --sat_out_model                         small
% 2.69/0.92  --sat_out_clauses                       false
% 2.69/0.92  
% 2.69/0.92  ------ QBF Options
% 2.69/0.92  
% 2.69/0.92  --qbf_mode                              false
% 2.69/0.92  --qbf_elim_univ                         false
% 2.69/0.92  --qbf_dom_inst                          none
% 2.69/0.92  --qbf_dom_pre_inst                      false
% 2.69/0.92  --qbf_sk_in                             false
% 2.69/0.92  --qbf_pred_elim                         true
% 2.69/0.92  --qbf_split                             512
% 2.69/0.92  
% 2.69/0.92  ------ BMC1 Options
% 2.69/0.92  
% 2.69/0.92  --bmc1_incremental                      false
% 2.69/0.92  --bmc1_axioms                           reachable_all
% 2.69/0.92  --bmc1_min_bound                        0
% 2.69/0.92  --bmc1_max_bound                        -1
% 2.69/0.92  --bmc1_max_bound_default                -1
% 2.69/0.92  --bmc1_symbol_reachability              true
% 2.69/0.92  --bmc1_property_lemmas                  false
% 2.69/0.92  --bmc1_k_induction                      false
% 2.69/0.92  --bmc1_non_equiv_states                 false
% 2.69/0.92  --bmc1_deadlock                         false
% 2.69/0.92  --bmc1_ucm                              false
% 2.69/0.92  --bmc1_add_unsat_core                   none
% 2.69/0.92  --bmc1_unsat_core_children              false
% 2.69/0.92  --bmc1_unsat_core_extrapolate_axioms    false
% 2.69/0.92  --bmc1_out_stat                         full
% 2.69/0.92  --bmc1_ground_init                      false
% 2.69/0.92  --bmc1_pre_inst_next_state              false
% 2.69/0.92  --bmc1_pre_inst_state                   false
% 2.69/0.92  --bmc1_pre_inst_reach_state             false
% 2.69/0.92  --bmc1_out_unsat_core                   false
% 2.69/0.92  --bmc1_aig_witness_out                  false
% 2.69/0.92  --bmc1_verbose                          false
% 2.69/0.92  --bmc1_dump_clauses_tptp                false
% 2.69/0.92  --bmc1_dump_unsat_core_tptp             false
% 2.69/0.92  --bmc1_dump_file                        -
% 2.69/0.92  --bmc1_ucm_expand_uc_limit              128
% 2.69/0.92  --bmc1_ucm_n_expand_iterations          6
% 2.69/0.92  --bmc1_ucm_extend_mode                  1
% 2.69/0.92  --bmc1_ucm_init_mode                    2
% 2.69/0.92  --bmc1_ucm_cone_mode                    none
% 2.69/0.92  --bmc1_ucm_reduced_relation_type        0
% 2.69/0.92  --bmc1_ucm_relax_model                  4
% 2.69/0.92  --bmc1_ucm_full_tr_after_sat            true
% 2.69/0.92  --bmc1_ucm_expand_neg_assumptions       false
% 2.69/0.92  --bmc1_ucm_layered_model                none
% 2.69/0.92  --bmc1_ucm_max_lemma_size               10
% 2.69/0.92  
% 2.69/0.92  ------ AIG Options
% 2.69/0.92  
% 2.69/0.92  --aig_mode                              false
% 2.69/0.92  
% 2.69/0.92  ------ Instantiation Options
% 2.69/0.92  
% 2.69/0.92  --instantiation_flag                    true
% 2.69/0.92  --inst_sos_flag                         false
% 2.69/0.92  --inst_sos_phase                        true
% 2.69/0.92  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.69/0.92  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.69/0.92  --inst_lit_sel_side                     num_symb
% 2.69/0.92  --inst_solver_per_active                1400
% 2.69/0.92  --inst_solver_calls_frac                1.
% 2.69/0.92  --inst_passive_queue_type               priority_queues
% 2.69/0.92  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.69/0.92  --inst_passive_queues_freq              [25;2]
% 2.69/0.92  --inst_dismatching                      true
% 2.69/0.92  --inst_eager_unprocessed_to_passive     true
% 2.69/0.92  --inst_prop_sim_given                   true
% 2.69/0.92  --inst_prop_sim_new                     false
% 2.69/0.92  --inst_subs_new                         false
% 2.69/0.92  --inst_eq_res_simp                      false
% 2.69/0.92  --inst_subs_given                       false
% 2.69/0.92  --inst_orphan_elimination               true
% 2.69/0.92  --inst_learning_loop_flag               true
% 2.69/0.92  --inst_learning_start                   3000
% 2.69/0.92  --inst_learning_factor                  2
% 2.69/0.92  --inst_start_prop_sim_after_learn       3
% 2.69/0.92  --inst_sel_renew                        solver
% 2.69/0.92  --inst_lit_activity_flag                true
% 2.69/0.92  --inst_restr_to_given                   false
% 2.69/0.92  --inst_activity_threshold               500
% 2.69/0.92  --inst_out_proof                        true
% 2.69/0.92  
% 2.69/0.92  ------ Resolution Options
% 2.69/0.92  
% 2.69/0.92  --resolution_flag                       true
% 2.69/0.92  --res_lit_sel                           adaptive
% 2.69/0.92  --res_lit_sel_side                      none
% 2.69/0.92  --res_ordering                          kbo
% 2.69/0.92  --res_to_prop_solver                    active
% 2.69/0.92  --res_prop_simpl_new                    false
% 2.69/0.92  --res_prop_simpl_given                  true
% 2.69/0.92  --res_passive_queue_type                priority_queues
% 2.69/0.92  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.69/0.92  --res_passive_queues_freq               [15;5]
% 2.69/0.92  --res_forward_subs                      full
% 2.69/0.92  --res_backward_subs                     full
% 2.69/0.92  --res_forward_subs_resolution           true
% 2.69/0.92  --res_backward_subs_resolution          true
% 2.69/0.92  --res_orphan_elimination                true
% 2.69/0.92  --res_time_limit                        2.
% 2.69/0.92  --res_out_proof                         true
% 2.69/0.92  
% 2.69/0.92  ------ Superposition Options
% 2.69/0.92  
% 2.69/0.92  --superposition_flag                    true
% 2.69/0.92  --sup_passive_queue_type                priority_queues
% 2.69/0.92  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.69/0.92  --sup_passive_queues_freq               [8;1;4]
% 2.69/0.92  --demod_completeness_check              fast
% 2.69/0.92  --demod_use_ground                      true
% 2.69/0.92  --sup_to_prop_solver                    passive
% 2.69/0.92  --sup_prop_simpl_new                    true
% 2.69/0.92  --sup_prop_simpl_given                  true
% 2.69/0.92  --sup_fun_splitting                     false
% 2.69/0.92  --sup_smt_interval                      50000
% 2.69/0.92  
% 2.69/0.92  ------ Superposition Simplification Setup
% 2.69/0.92  
% 2.69/0.92  --sup_indices_passive                   []
% 2.69/0.92  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.69/0.92  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.69/0.92  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.69/0.92  --sup_full_triv                         [TrivRules;PropSubs]
% 2.69/0.92  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.69/0.92  --sup_full_bw                           [BwDemod]
% 2.69/0.92  --sup_immed_triv                        [TrivRules]
% 2.69/0.92  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.69/0.92  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.69/0.92  --sup_immed_bw_main                     []
% 2.69/0.92  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.69/0.92  --sup_input_triv                        [Unflattening;TrivRules]
% 2.69/0.92  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.69/0.92  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.69/0.92  
% 2.69/0.92  ------ Combination Options
% 2.69/0.92  
% 2.69/0.92  --comb_res_mult                         3
% 2.69/0.92  --comb_sup_mult                         2
% 2.69/0.92  --comb_inst_mult                        10
% 2.69/0.92  
% 2.69/0.92  ------ Debug Options
% 2.69/0.92  
% 2.69/0.92  --dbg_backtrace                         false
% 2.69/0.92  --dbg_dump_prop_clauses                 false
% 2.69/0.92  --dbg_dump_prop_clauses_file            -
% 2.69/0.92  --dbg_out_stat                          false
% 2.69/0.92  ------ Parsing...
% 2.69/0.92  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.69/0.92  
% 2.69/0.92  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.69/0.92  
% 2.69/0.92  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.69/0.92  
% 2.69/0.92  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.69/0.92  ------ Proving...
% 2.69/0.92  ------ Problem Properties 
% 2.69/0.92  
% 2.69/0.92  
% 2.69/0.92  clauses                                 22
% 2.69/0.92  conjectures                             6
% 2.69/0.92  EPR                                     6
% 2.69/0.92  Horn                                    21
% 2.69/0.92  unary                                   9
% 2.69/0.92  binary                                  4
% 2.69/0.92  lits                                    70
% 2.69/0.92  lits eq                                 8
% 2.69/0.92  fd_pure                                 0
% 2.69/0.92  fd_pseudo                               0
% 2.69/0.92  fd_cond                                 1
% 2.69/0.92  fd_pseudo_cond                          0
% 2.69/0.92  AC symbols                              0
% 2.69/0.92  
% 2.69/0.92  ------ Schedule dynamic 5 is on 
% 2.69/0.92  
% 2.69/0.92  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.69/0.92  
% 2.69/0.92  
% 2.69/0.92  ------ 
% 2.69/0.92  Current options:
% 2.69/0.92  ------ 
% 2.69/0.92  
% 2.69/0.92  ------ Input Options
% 2.69/0.92  
% 2.69/0.92  --out_options                           all
% 2.69/0.92  --tptp_safe_out                         true
% 2.69/0.92  --problem_path                          ""
% 2.69/0.92  --include_path                          ""
% 2.69/0.92  --clausifier                            res/vclausify_rel
% 2.69/0.92  --clausifier_options                    --mode clausify
% 2.69/0.92  --stdin                                 false
% 2.69/0.92  --stats_out                             all
% 2.69/0.92  
% 2.69/0.92  ------ General Options
% 2.69/0.92  
% 2.69/0.92  --fof                                   false
% 2.69/0.92  --time_out_real                         305.
% 2.69/0.92  --time_out_virtual                      -1.
% 2.69/0.92  --symbol_type_check                     false
% 2.69/0.92  --clausify_out                          false
% 2.69/0.92  --sig_cnt_out                           false
% 2.69/0.92  --trig_cnt_out                          false
% 2.69/0.92  --trig_cnt_out_tolerance                1.
% 2.69/0.92  --trig_cnt_out_sk_spl                   false
% 2.69/0.92  --abstr_cl_out                          false
% 2.69/0.92  
% 2.69/0.92  ------ Global Options
% 2.69/0.92  
% 2.69/0.92  --schedule                              default
% 2.69/0.92  --add_important_lit                     false
% 2.69/0.92  --prop_solver_per_cl                    1000
% 2.69/0.92  --min_unsat_core                        false
% 2.69/0.92  --soft_assumptions                      false
% 2.69/0.92  --soft_lemma_size                       3
% 2.69/0.92  --prop_impl_unit_size                   0
% 2.69/0.92  --prop_impl_unit                        []
% 2.69/0.92  --share_sel_clauses                     true
% 2.69/0.92  --reset_solvers                         false
% 2.69/0.92  --bc_imp_inh                            [conj_cone]
% 2.69/0.92  --conj_cone_tolerance                   3.
% 2.69/0.92  --extra_neg_conj                        none
% 2.69/0.92  --large_theory_mode                     true
% 2.69/0.92  --prolific_symb_bound                   200
% 2.69/0.92  --lt_threshold                          2000
% 2.69/0.92  --clause_weak_htbl                      true
% 2.69/0.92  --gc_record_bc_elim                     false
% 2.69/0.92  
% 2.69/0.92  ------ Preprocessing Options
% 2.69/0.92  
% 2.69/0.92  --preprocessing_flag                    true
% 2.69/0.92  --time_out_prep_mult                    0.1
% 2.69/0.92  --splitting_mode                        input
% 2.69/0.92  --splitting_grd                         true
% 2.69/0.92  --splitting_cvd                         false
% 2.69/0.92  --splitting_cvd_svl                     false
% 2.69/0.92  --splitting_nvd                         32
% 2.69/0.92  --sub_typing                            true
% 2.69/0.92  --prep_gs_sim                           true
% 2.69/0.92  --prep_unflatten                        true
% 2.69/0.92  --prep_res_sim                          true
% 2.69/0.92  --prep_upred                            true
% 2.69/0.92  --prep_sem_filter                       exhaustive
% 2.69/0.92  --prep_sem_filter_out                   false
% 2.69/0.92  --pred_elim                             true
% 2.69/0.92  --res_sim_input                         true
% 2.69/0.92  --eq_ax_congr_red                       true
% 2.69/0.92  --pure_diseq_elim                       true
% 2.69/0.92  --brand_transform                       false
% 2.69/0.92  --non_eq_to_eq                          false
% 2.69/0.92  --prep_def_merge                        true
% 2.69/0.92  --prep_def_merge_prop_impl              false
% 2.69/0.92  --prep_def_merge_mbd                    true
% 2.69/0.92  --prep_def_merge_tr_red                 false
% 2.69/0.92  --prep_def_merge_tr_cl                  false
% 2.69/0.92  --smt_preprocessing                     true
% 2.69/0.92  --smt_ac_axioms                         fast
% 2.69/0.92  --preprocessed_out                      false
% 2.69/0.92  --preprocessed_stats                    false
% 2.69/0.92  
% 2.69/0.92  ------ Abstraction refinement Options
% 2.69/0.92  
% 2.69/0.92  --abstr_ref                             []
% 2.69/0.92  --abstr_ref_prep                        false
% 2.69/0.92  --abstr_ref_until_sat                   false
% 2.69/0.92  --abstr_ref_sig_restrict                funpre
% 2.69/0.92  --abstr_ref_af_restrict_to_split_sk     false
% 2.69/0.92  --abstr_ref_under                       []
% 2.69/0.92  
% 2.69/0.92  ------ SAT Options
% 2.69/0.92  
% 2.69/0.92  --sat_mode                              false
% 2.69/0.92  --sat_fm_restart_options                ""
% 2.69/0.92  --sat_gr_def                            false
% 2.69/0.92  --sat_epr_types                         true
% 2.69/0.92  --sat_non_cyclic_types                  false
% 2.69/0.92  --sat_finite_models                     false
% 2.69/0.92  --sat_fm_lemmas                         false
% 2.69/0.92  --sat_fm_prep                           false
% 2.69/0.92  --sat_fm_uc_incr                        true
% 2.69/0.92  --sat_out_model                         small
% 2.69/0.92  --sat_out_clauses                       false
% 2.69/0.92  
% 2.69/0.92  ------ QBF Options
% 2.69/0.92  
% 2.69/0.92  --qbf_mode                              false
% 2.69/0.92  --qbf_elim_univ                         false
% 2.69/0.92  --qbf_dom_inst                          none
% 2.69/0.92  --qbf_dom_pre_inst                      false
% 2.69/0.92  --qbf_sk_in                             false
% 2.69/0.92  --qbf_pred_elim                         true
% 2.69/0.92  --qbf_split                             512
% 2.69/0.92  
% 2.69/0.92  ------ BMC1 Options
% 2.69/0.92  
% 2.69/0.92  --bmc1_incremental                      false
% 2.69/0.92  --bmc1_axioms                           reachable_all
% 2.69/0.92  --bmc1_min_bound                        0
% 2.69/0.92  --bmc1_max_bound                        -1
% 2.69/0.92  --bmc1_max_bound_default                -1
% 2.69/0.92  --bmc1_symbol_reachability              true
% 2.69/0.92  --bmc1_property_lemmas                  false
% 2.69/0.92  --bmc1_k_induction                      false
% 2.69/0.92  --bmc1_non_equiv_states                 false
% 2.69/0.92  --bmc1_deadlock                         false
% 2.69/0.92  --bmc1_ucm                              false
% 2.69/0.92  --bmc1_add_unsat_core                   none
% 2.69/0.92  --bmc1_unsat_core_children              false
% 2.69/0.92  --bmc1_unsat_core_extrapolate_axioms    false
% 2.69/0.92  --bmc1_out_stat                         full
% 2.69/0.92  --bmc1_ground_init                      false
% 2.69/0.92  --bmc1_pre_inst_next_state              false
% 2.69/0.92  --bmc1_pre_inst_state                   false
% 2.69/0.92  --bmc1_pre_inst_reach_state             false
% 2.69/0.92  --bmc1_out_unsat_core                   false
% 2.69/0.92  --bmc1_aig_witness_out                  false
% 2.69/0.92  --bmc1_verbose                          false
% 2.69/0.92  --bmc1_dump_clauses_tptp                false
% 2.69/0.92  --bmc1_dump_unsat_core_tptp             false
% 2.69/0.92  --bmc1_dump_file                        -
% 2.69/0.92  --bmc1_ucm_expand_uc_limit              128
% 2.69/0.92  --bmc1_ucm_n_expand_iterations          6
% 2.69/0.92  --bmc1_ucm_extend_mode                  1
% 2.69/0.92  --bmc1_ucm_init_mode                    2
% 2.69/0.92  --bmc1_ucm_cone_mode                    none
% 2.69/0.92  --bmc1_ucm_reduced_relation_type        0
% 2.69/0.92  --bmc1_ucm_relax_model                  4
% 2.69/0.92  --bmc1_ucm_full_tr_after_sat            true
% 2.69/0.92  --bmc1_ucm_expand_neg_assumptions       false
% 2.69/0.92  --bmc1_ucm_layered_model                none
% 2.69/0.92  --bmc1_ucm_max_lemma_size               10
% 2.69/0.92  
% 2.69/0.92  ------ AIG Options
% 2.69/0.92  
% 2.69/0.92  --aig_mode                              false
% 2.69/0.92  
% 2.69/0.92  ------ Instantiation Options
% 2.69/0.92  
% 2.69/0.92  --instantiation_flag                    true
% 2.69/0.92  --inst_sos_flag                         false
% 2.69/0.92  --inst_sos_phase                        true
% 2.69/0.92  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.69/0.92  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.69/0.92  --inst_lit_sel_side                     none
% 2.69/0.92  --inst_solver_per_active                1400
% 2.69/0.92  --inst_solver_calls_frac                1.
% 2.69/0.92  --inst_passive_queue_type               priority_queues
% 2.69/0.92  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.69/0.92  --inst_passive_queues_freq              [25;2]
% 2.69/0.92  --inst_dismatching                      true
% 2.69/0.92  --inst_eager_unprocessed_to_passive     true
% 2.69/0.92  --inst_prop_sim_given                   true
% 2.69/0.92  --inst_prop_sim_new                     false
% 2.69/0.92  --inst_subs_new                         false
% 2.69/0.92  --inst_eq_res_simp                      false
% 2.69/0.92  --inst_subs_given                       false
% 2.69/0.92  --inst_orphan_elimination               true
% 2.69/0.92  --inst_learning_loop_flag               true
% 2.69/0.92  --inst_learning_start                   3000
% 2.69/0.92  --inst_learning_factor                  2
% 2.69/0.92  --inst_start_prop_sim_after_learn       3
% 2.69/0.92  --inst_sel_renew                        solver
% 2.69/0.92  --inst_lit_activity_flag                true
% 2.69/0.92  --inst_restr_to_given                   false
% 2.69/0.92  --inst_activity_threshold               500
% 2.69/0.92  --inst_out_proof                        true
% 2.69/0.92  
% 2.69/0.92  ------ Resolution Options
% 2.69/0.92  
% 2.69/0.92  --resolution_flag                       false
% 2.69/0.92  --res_lit_sel                           adaptive
% 2.69/0.92  --res_lit_sel_side                      none
% 2.69/0.92  --res_ordering                          kbo
% 2.69/0.92  --res_to_prop_solver                    active
% 2.69/0.92  --res_prop_simpl_new                    false
% 2.69/0.92  --res_prop_simpl_given                  true
% 2.69/0.92  --res_passive_queue_type                priority_queues
% 2.69/0.92  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.69/0.92  --res_passive_queues_freq               [15;5]
% 2.69/0.92  --res_forward_subs                      full
% 2.69/0.92  --res_backward_subs                     full
% 2.69/0.92  --res_forward_subs_resolution           true
% 2.69/0.92  --res_backward_subs_resolution          true
% 2.69/0.92  --res_orphan_elimination                true
% 2.69/0.92  --res_time_limit                        2.
% 2.69/0.92  --res_out_proof                         true
% 2.69/0.92  
% 2.69/0.92  ------ Superposition Options
% 2.69/0.92  
% 2.69/0.92  --superposition_flag                    true
% 2.69/0.92  --sup_passive_queue_type                priority_queues
% 2.69/0.92  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.69/0.92  --sup_passive_queues_freq               [8;1;4]
% 2.69/0.92  --demod_completeness_check              fast
% 2.69/0.92  --demod_use_ground                      true
% 2.69/0.92  --sup_to_prop_solver                    passive
% 2.69/0.92  --sup_prop_simpl_new                    true
% 2.69/0.92  --sup_prop_simpl_given                  true
% 2.69/0.92  --sup_fun_splitting                     false
% 2.69/0.92  --sup_smt_interval                      50000
% 2.69/0.92  
% 2.69/0.92  ------ Superposition Simplification Setup
% 2.69/0.92  
% 2.69/0.92  --sup_indices_passive                   []
% 2.69/0.92  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.69/0.92  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.69/0.92  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.69/0.92  --sup_full_triv                         [TrivRules;PropSubs]
% 2.69/0.92  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.69/0.92  --sup_full_bw                           [BwDemod]
% 2.69/0.92  --sup_immed_triv                        [TrivRules]
% 2.69/0.92  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.69/0.92  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.69/0.92  --sup_immed_bw_main                     []
% 2.69/0.92  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.69/0.92  --sup_input_triv                        [Unflattening;TrivRules]
% 2.69/0.92  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.69/0.92  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.69/0.92  
% 2.69/0.92  ------ Combination Options
% 2.69/0.92  
% 2.69/0.92  --comb_res_mult                         3
% 2.69/0.92  --comb_sup_mult                         2
% 2.69/0.92  --comb_inst_mult                        10
% 2.69/0.92  
% 2.69/0.92  ------ Debug Options
% 2.69/0.92  
% 2.69/0.92  --dbg_backtrace                         false
% 2.69/0.92  --dbg_dump_prop_clauses                 false
% 2.69/0.92  --dbg_dump_prop_clauses_file            -
% 2.69/0.92  --dbg_out_stat                          false
% 2.69/0.92  
% 2.69/0.92  
% 2.69/0.92  
% 2.69/0.92  
% 2.69/0.92  ------ Proving...
% 2.69/0.92  
% 2.69/0.92  
% 2.69/0.92  % SZS status Theorem for theBenchmark.p
% 2.69/0.92  
% 2.69/0.92  % SZS output start CNFRefutation for theBenchmark.p
% 2.69/0.92  
% 2.69/0.92  fof(f10,axiom,(
% 2.69/0.92    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 2.69/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/0.92  
% 2.69/0.92  fof(f29,plain,(
% 2.69/0.92    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.69/0.92    inference(ennf_transformation,[],[f10])).
% 2.69/0.92  
% 2.69/0.92  fof(f30,plain,(
% 2.69/0.92    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.69/0.92    inference(flattening,[],[f29])).
% 2.69/0.92  
% 2.69/0.92  fof(f56,plain,(
% 2.69/0.92    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.69/0.92    inference(cnf_transformation,[],[f30])).
% 2.69/0.92  
% 2.69/0.92  fof(f8,axiom,(
% 2.69/0.92    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.69/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/0.92  
% 2.69/0.92  fof(f25,plain,(
% 2.69/0.92    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.69/0.92    inference(ennf_transformation,[],[f8])).
% 2.69/0.92  
% 2.69/0.92  fof(f26,plain,(
% 2.69/0.92    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.69/0.92    inference(flattening,[],[f25])).
% 2.69/0.92  
% 2.69/0.92  fof(f37,plain,(
% 2.69/0.92    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.69/0.92    inference(nnf_transformation,[],[f26])).
% 2.69/0.92  
% 2.69/0.92  fof(f51,plain,(
% 2.69/0.92    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.69/0.92    inference(cnf_transformation,[],[f37])).
% 2.69/0.92  
% 2.69/0.92  fof(f15,conjecture,(
% 2.69/0.92    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 2.69/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/0.92  
% 2.69/0.92  fof(f16,negated_conjecture,(
% 2.69/0.92    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 2.69/0.92    inference(negated_conjecture,[],[f15])).
% 2.69/0.92  
% 2.69/0.92  fof(f35,plain,(
% 2.69/0.92    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.69/0.92    inference(ennf_transformation,[],[f16])).
% 2.69/0.92  
% 2.69/0.92  fof(f36,plain,(
% 2.69/0.92    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.69/0.92    inference(flattening,[],[f35])).
% 2.69/0.92  
% 2.69/0.92  fof(f40,plain,(
% 2.69/0.92    ( ! [X2,X0,X1] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((~v2_funct_2(sK3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 2.69/0.92    introduced(choice_axiom,[])).
% 2.69/0.92  
% 2.69/0.92  fof(f39,plain,(
% 2.69/0.92    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 2.69/0.92    introduced(choice_axiom,[])).
% 2.69/0.92  
% 2.69/0.92  fof(f41,plain,(
% 2.69/0.92    ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 2.69/0.92    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f36,f40,f39])).
% 2.69/0.92  
% 2.69/0.92  fof(f68,plain,(
% 2.69/0.92    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.69/0.92    inference(cnf_transformation,[],[f41])).
% 2.69/0.92  
% 2.69/0.92  fof(f11,axiom,(
% 2.69/0.92    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 2.69/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/0.92  
% 2.69/0.92  fof(f17,plain,(
% 2.69/0.92    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 2.69/0.92    inference(pure_predicate_removal,[],[f11])).
% 2.69/0.92  
% 2.69/0.92  fof(f57,plain,(
% 2.69/0.92    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.69/0.92    inference(cnf_transformation,[],[f17])).
% 2.69/0.92  
% 2.69/0.92  fof(f62,plain,(
% 2.69/0.92    v1_funct_1(sK2)),
% 2.69/0.92    inference(cnf_transformation,[],[f41])).
% 2.69/0.92  
% 2.69/0.92  fof(f64,plain,(
% 2.69/0.92    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.69/0.92    inference(cnf_transformation,[],[f41])).
% 2.69/0.92  
% 2.69/0.92  fof(f65,plain,(
% 2.69/0.92    v1_funct_1(sK3)),
% 2.69/0.92    inference(cnf_transformation,[],[f41])).
% 2.69/0.92  
% 2.69/0.92  fof(f67,plain,(
% 2.69/0.92    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.69/0.92    inference(cnf_transformation,[],[f41])).
% 2.69/0.92  
% 2.69/0.92  fof(f14,axiom,(
% 2.69/0.92    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 2.69/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/0.92  
% 2.69/0.92  fof(f33,plain,(
% 2.69/0.92    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.69/0.92    inference(ennf_transformation,[],[f14])).
% 2.69/0.92  
% 2.69/0.92  fof(f34,plain,(
% 2.69/0.92    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.69/0.92    inference(flattening,[],[f33])).
% 2.69/0.92  
% 2.69/0.92  fof(f60,plain,(
% 2.69/0.92    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X3) | k1_xboole_0 = X2 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.69/0.92    inference(cnf_transformation,[],[f34])).
% 2.69/0.92  
% 2.69/0.92  fof(f7,axiom,(
% 2.69/0.92    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 2.69/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/0.92  
% 2.69/0.92  fof(f24,plain,(
% 2.69/0.92    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.69/0.92    inference(ennf_transformation,[],[f7])).
% 2.69/0.92  
% 2.69/0.92  fof(f50,plain,(
% 2.69/0.92    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.69/0.92    inference(cnf_transformation,[],[f24])).
% 2.69/0.92  
% 2.69/0.92  fof(f13,axiom,(
% 2.69/0.92    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 2.69/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/0.92  
% 2.69/0.92  fof(f31,plain,(
% 2.69/0.92    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.69/0.92    inference(ennf_transformation,[],[f13])).
% 2.69/0.92  
% 2.69/0.92  fof(f32,plain,(
% 2.69/0.92    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.69/0.92    inference(flattening,[],[f31])).
% 2.69/0.92  
% 2.69/0.92  fof(f59,plain,(
% 2.69/0.92    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.69/0.92    inference(cnf_transformation,[],[f32])).
% 2.69/0.92  
% 2.69/0.92  fof(f63,plain,(
% 2.69/0.92    v1_funct_2(sK2,sK0,sK1)),
% 2.69/0.92    inference(cnf_transformation,[],[f41])).
% 2.69/0.92  
% 2.69/0.92  fof(f66,plain,(
% 2.69/0.92    v1_funct_2(sK3,sK1,sK0)),
% 2.69/0.92    inference(cnf_transformation,[],[f41])).
% 2.69/0.92  
% 2.69/0.92  fof(f5,axiom,(
% 2.69/0.92    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.69/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/0.92  
% 2.69/0.92  fof(f18,plain,(
% 2.69/0.92    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 2.69/0.92    inference(pure_predicate_removal,[],[f5])).
% 2.69/0.92  
% 2.69/0.92  fof(f22,plain,(
% 2.69/0.92    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.69/0.92    inference(ennf_transformation,[],[f18])).
% 2.69/0.92  
% 2.69/0.92  fof(f48,plain,(
% 2.69/0.92    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.69/0.92    inference(cnf_transformation,[],[f22])).
% 2.69/0.92  
% 2.69/0.92  fof(f9,axiom,(
% 2.69/0.92    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 2.69/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/0.92  
% 2.69/0.92  fof(f27,plain,(
% 2.69/0.92    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.69/0.92    inference(ennf_transformation,[],[f9])).
% 2.69/0.92  
% 2.69/0.92  fof(f28,plain,(
% 2.69/0.92    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.69/0.92    inference(flattening,[],[f27])).
% 2.69/0.92  
% 2.69/0.92  fof(f38,plain,(
% 2.69/0.92    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.69/0.92    inference(nnf_transformation,[],[f28])).
% 2.69/0.92  
% 2.69/0.92  fof(f54,plain,(
% 2.69/0.92    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.69/0.92    inference(cnf_transformation,[],[f38])).
% 2.69/0.92  
% 2.69/0.92  fof(f72,plain,(
% 2.69/0.92    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.69/0.92    inference(equality_resolution,[],[f54])).
% 2.69/0.92  
% 2.69/0.92  fof(f4,axiom,(
% 2.69/0.92    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.69/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/0.92  
% 2.69/0.92  fof(f21,plain,(
% 2.69/0.92    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.69/0.92    inference(ennf_transformation,[],[f4])).
% 2.69/0.92  
% 2.69/0.92  fof(f47,plain,(
% 2.69/0.92    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.69/0.92    inference(cnf_transformation,[],[f21])).
% 2.69/0.92  
% 2.69/0.92  fof(f69,plain,(
% 2.69/0.92    ~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)),
% 2.69/0.92    inference(cnf_transformation,[],[f41])).
% 2.69/0.92  
% 2.69/0.92  fof(f6,axiom,(
% 2.69/0.92    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 2.69/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/0.92  
% 2.69/0.92  fof(f23,plain,(
% 2.69/0.92    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 2.69/0.92    inference(ennf_transformation,[],[f6])).
% 2.69/0.92  
% 2.69/0.92  fof(f49,plain,(
% 2.69/0.92    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 2.69/0.92    inference(cnf_transformation,[],[f23])).
% 2.69/0.92  
% 2.69/0.92  fof(f2,axiom,(
% 2.69/0.92    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0) & v1_xboole_0(X0)) => (v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)))),
% 2.69/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/0.92  
% 2.69/0.92  fof(f19,plain,(
% 2.69/0.92    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_xboole_0(X0)))),
% 2.69/0.92    inference(ennf_transformation,[],[f2])).
% 2.69/0.92  
% 2.69/0.92  fof(f20,plain,(
% 2.69/0.92    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 2.69/0.92    inference(flattening,[],[f19])).
% 2.69/0.92  
% 2.69/0.92  fof(f45,plain,(
% 2.69/0.92    ( ! [X0] : (v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 2.69/0.92    inference(cnf_transformation,[],[f20])).
% 2.69/0.92  
% 2.69/0.92  fof(f1,axiom,(
% 2.69/0.92    v1_xboole_0(k1_xboole_0)),
% 2.69/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/0.92  
% 2.69/0.92  fof(f42,plain,(
% 2.69/0.92    v1_xboole_0(k1_xboole_0)),
% 2.69/0.92    inference(cnf_transformation,[],[f1])).
% 2.69/0.92  
% 2.69/0.92  fof(f3,axiom,(
% 2.69/0.92    ! [X0] : v2_funct_1(k6_relat_1(X0))),
% 2.69/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/0.92  
% 2.69/0.92  fof(f46,plain,(
% 2.69/0.92    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 2.69/0.92    inference(cnf_transformation,[],[f3])).
% 2.69/0.92  
% 2.69/0.92  fof(f12,axiom,(
% 2.69/0.92    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.69/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/0.92  
% 2.69/0.92  fof(f58,plain,(
% 2.69/0.92    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.69/0.92    inference(cnf_transformation,[],[f12])).
% 2.69/0.92  
% 2.69/0.92  fof(f70,plain,(
% 2.69/0.92    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 2.69/0.92    inference(definition_unfolding,[],[f46,f58])).
% 2.69/0.92  
% 2.69/0.92  cnf(c_13,plain,
% 2.69/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.69/0.92      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 2.69/0.92      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 2.69/0.92      | ~ v1_funct_1(X0)
% 2.69/0.92      | ~ v1_funct_1(X3) ),
% 2.69/0.92      inference(cnf_transformation,[],[f56]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_653,plain,
% 2.69/0.92      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
% 2.69/0.92      | ~ m1_subset_1(X3_48,k1_zfmisc_1(k2_zfmisc_1(X4_48,X5_48)))
% 2.69/0.92      | m1_subset_1(k1_partfun1(X4_48,X5_48,X1_48,X2_48,X3_48,X0_48),k1_zfmisc_1(k2_zfmisc_1(X4_48,X2_48)))
% 2.69/0.92      | ~ v1_funct_1(X0_48)
% 2.69/0.92      | ~ v1_funct_1(X3_48) ),
% 2.69/0.92      inference(subtyping,[status(esa)],[c_13]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_1090,plain,
% 2.69/0.92      ( m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48))) != iProver_top
% 2.69/0.92      | m1_subset_1(X3_48,k1_zfmisc_1(k2_zfmisc_1(X4_48,X5_48))) != iProver_top
% 2.69/0.92      | m1_subset_1(k1_partfun1(X4_48,X5_48,X1_48,X2_48,X3_48,X0_48),k1_zfmisc_1(k2_zfmisc_1(X4_48,X2_48))) = iProver_top
% 2.69/0.92      | v1_funct_1(X3_48) != iProver_top
% 2.69/0.92      | v1_funct_1(X0_48) != iProver_top ),
% 2.69/0.92      inference(predicate_to_equality,[status(thm)],[c_653]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_10,plain,
% 2.69/0.92      ( ~ r2_relset_1(X0,X1,X2,X3)
% 2.69/0.92      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.69/0.92      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.69/0.92      | X3 = X2 ),
% 2.69/0.92      inference(cnf_transformation,[],[f51]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_20,negated_conjecture,
% 2.69/0.92      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 2.69/0.92      inference(cnf_transformation,[],[f68]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_405,plain,
% 2.69/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.69/0.92      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.69/0.92      | X3 = X0
% 2.69/0.92      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 2.69/0.92      | k6_partfun1(sK0) != X3
% 2.69/0.92      | sK0 != X2
% 2.69/0.92      | sK0 != X1 ),
% 2.69/0.92      inference(resolution_lifted,[status(thm)],[c_10,c_20]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_406,plain,
% 2.69/0.92      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.69/0.92      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.69/0.92      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 2.69/0.92      inference(unflattening,[status(thm)],[c_405]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_15,plain,
% 2.69/0.92      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 2.69/0.92      inference(cnf_transformation,[],[f57]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_45,plain,
% 2.69/0.92      ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 2.69/0.92      inference(instantiation,[status(thm)],[c_15]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_408,plain,
% 2.69/0.92      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.69/0.92      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 2.69/0.92      inference(global_propositional_subsumption,
% 2.69/0.92                [status(thm)],
% 2.69/0.92                [c_406,c_45]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_640,plain,
% 2.69/0.92      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.69/0.92      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 2.69/0.92      inference(subtyping,[status(esa)],[c_408]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_1104,plain,
% 2.69/0.92      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 2.69/0.92      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 2.69/0.92      inference(predicate_to_equality,[status(thm)],[c_640]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_2203,plain,
% 2.69/0.92      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
% 2.69/0.92      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.69/0.92      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.69/0.92      | v1_funct_1(sK2) != iProver_top
% 2.69/0.92      | v1_funct_1(sK3) != iProver_top ),
% 2.69/0.92      inference(superposition,[status(thm)],[c_1090,c_1104]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_26,negated_conjecture,
% 2.69/0.92      ( v1_funct_1(sK2) ),
% 2.69/0.92      inference(cnf_transformation,[],[f62]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_27,plain,
% 2.69/0.92      ( v1_funct_1(sK2) = iProver_top ),
% 2.69/0.92      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_24,negated_conjecture,
% 2.69/0.92      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.69/0.92      inference(cnf_transformation,[],[f64]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_29,plain,
% 2.69/0.92      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.69/0.92      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_23,negated_conjecture,
% 2.69/0.92      ( v1_funct_1(sK3) ),
% 2.69/0.92      inference(cnf_transformation,[],[f65]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_30,plain,
% 2.69/0.92      ( v1_funct_1(sK3) = iProver_top ),
% 2.69/0.92      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_21,negated_conjecture,
% 2.69/0.92      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 2.69/0.92      inference(cnf_transformation,[],[f67]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_32,plain,
% 2.69/0.92      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 2.69/0.92      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_2553,plain,
% 2.69/0.92      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
% 2.69/0.92      inference(global_propositional_subsumption,
% 2.69/0.92                [status(thm)],
% 2.69/0.92                [c_2203,c_27,c_29,c_30,c_32]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_18,plain,
% 2.69/0.92      ( ~ v1_funct_2(X0,X1,X2)
% 2.69/0.92      | ~ v1_funct_2(X3,X4,X1)
% 2.69/0.92      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 2.69/0.92      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.69/0.92      | ~ v1_funct_1(X0)
% 2.69/0.92      | ~ v1_funct_1(X3)
% 2.69/0.92      | v2_funct_1(X3)
% 2.69/0.92      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 2.69/0.92      | k1_xboole_0 = X2 ),
% 2.69/0.92      inference(cnf_transformation,[],[f60]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_649,plain,
% 2.69/0.92      ( ~ v1_funct_2(X0_48,X1_48,X2_48)
% 2.69/0.92      | ~ v1_funct_2(X3_48,X4_48,X1_48)
% 2.69/0.92      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
% 2.69/0.92      | ~ m1_subset_1(X3_48,k1_zfmisc_1(k2_zfmisc_1(X4_48,X1_48)))
% 2.69/0.92      | ~ v1_funct_1(X0_48)
% 2.69/0.92      | ~ v1_funct_1(X3_48)
% 2.69/0.92      | v2_funct_1(X3_48)
% 2.69/0.92      | ~ v2_funct_1(k1_partfun1(X4_48,X1_48,X1_48,X2_48,X3_48,X0_48))
% 2.69/0.92      | k1_xboole_0 = X2_48 ),
% 2.69/0.92      inference(subtyping,[status(esa)],[c_18]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_1094,plain,
% 2.69/0.92      ( k1_xboole_0 = X0_48
% 2.69/0.92      | v1_funct_2(X1_48,X2_48,X0_48) != iProver_top
% 2.69/0.92      | v1_funct_2(X3_48,X4_48,X2_48) != iProver_top
% 2.69/0.92      | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_48,X0_48))) != iProver_top
% 2.69/0.92      | m1_subset_1(X3_48,k1_zfmisc_1(k2_zfmisc_1(X4_48,X2_48))) != iProver_top
% 2.69/0.92      | v1_funct_1(X3_48) != iProver_top
% 2.69/0.92      | v1_funct_1(X1_48) != iProver_top
% 2.69/0.92      | v2_funct_1(X3_48) = iProver_top
% 2.69/0.92      | v2_funct_1(k1_partfun1(X4_48,X2_48,X2_48,X0_48,X3_48,X1_48)) != iProver_top ),
% 2.69/0.92      inference(predicate_to_equality,[status(thm)],[c_649]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_2632,plain,
% 2.69/0.92      ( sK0 = k1_xboole_0
% 2.69/0.92      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 2.69/0.92      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 2.69/0.92      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.69/0.92      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.69/0.92      | v1_funct_1(sK2) != iProver_top
% 2.69/0.92      | v1_funct_1(sK3) != iProver_top
% 2.69/0.92      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 2.69/0.92      | v2_funct_1(sK2) = iProver_top ),
% 2.69/0.92      inference(superposition,[status(thm)],[c_2553,c_1094]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_648,negated_conjecture,
% 2.69/0.92      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 2.69/0.92      inference(subtyping,[status(esa)],[c_21]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_1095,plain,
% 2.69/0.92      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 2.69/0.92      inference(predicate_to_equality,[status(thm)],[c_648]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_8,plain,
% 2.69/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.69/0.92      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.69/0.92      inference(cnf_transformation,[],[f50]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_654,plain,
% 2.69/0.92      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
% 2.69/0.92      | k2_relset_1(X1_48,X2_48,X0_48) = k2_relat_1(X0_48) ),
% 2.69/0.92      inference(subtyping,[status(esa)],[c_8]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_1089,plain,
% 2.69/0.92      ( k2_relset_1(X0_48,X1_48,X2_48) = k2_relat_1(X2_48)
% 2.69/0.92      | m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top ),
% 2.69/0.92      inference(predicate_to_equality,[status(thm)],[c_654]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_2150,plain,
% 2.69/0.92      ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 2.69/0.92      inference(superposition,[status(thm)],[c_1095,c_1089]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_16,plain,
% 2.69/0.92      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 2.69/0.92      | ~ v1_funct_2(X2,X0,X1)
% 2.69/0.92      | ~ v1_funct_2(X3,X1,X0)
% 2.69/0.92      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.69/0.92      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.69/0.92      | ~ v1_funct_1(X2)
% 2.69/0.92      | ~ v1_funct_1(X3)
% 2.69/0.92      | k2_relset_1(X1,X0,X3) = X0 ),
% 2.69/0.92      inference(cnf_transformation,[],[f59]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_419,plain,
% 2.69/0.92      ( ~ v1_funct_2(X0,X1,X2)
% 2.69/0.92      | ~ v1_funct_2(X3,X2,X1)
% 2.69/0.92      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.69/0.92      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.69/0.92      | ~ v1_funct_1(X3)
% 2.69/0.92      | ~ v1_funct_1(X0)
% 2.69/0.92      | k1_partfun1(X1,X2,X2,X1,X0,X3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 2.69/0.92      | k2_relset_1(X2,X1,X3) = X1
% 2.69/0.92      | k6_partfun1(X1) != k6_partfun1(sK0)
% 2.69/0.92      | sK0 != X1 ),
% 2.69/0.92      inference(resolution_lifted,[status(thm)],[c_16,c_20]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_420,plain,
% 2.69/0.92      ( ~ v1_funct_2(X0,X1,sK0)
% 2.69/0.92      | ~ v1_funct_2(X2,sK0,X1)
% 2.69/0.92      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 2.69/0.92      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 2.69/0.92      | ~ v1_funct_1(X2)
% 2.69/0.92      | ~ v1_funct_1(X0)
% 2.69/0.92      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 2.69/0.92      | k2_relset_1(X1,sK0,X0) = sK0
% 2.69/0.92      | k6_partfun1(sK0) != k6_partfun1(sK0) ),
% 2.69/0.92      inference(unflattening,[status(thm)],[c_419]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_495,plain,
% 2.69/0.92      ( ~ v1_funct_2(X0,X1,sK0)
% 2.69/0.92      | ~ v1_funct_2(X2,sK0,X1)
% 2.69/0.92      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 2.69/0.92      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 2.69/0.92      | ~ v1_funct_1(X0)
% 2.69/0.92      | ~ v1_funct_1(X2)
% 2.69/0.92      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 2.69/0.92      | k2_relset_1(X1,sK0,X0) = sK0 ),
% 2.69/0.92      inference(equality_resolution_simp,[status(thm)],[c_420]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_639,plain,
% 2.69/0.92      ( ~ v1_funct_2(X0_48,X1_48,sK0)
% 2.69/0.92      | ~ v1_funct_2(X2_48,sK0,X1_48)
% 2.69/0.92      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,sK0)))
% 2.69/0.92      | ~ m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(sK0,X1_48)))
% 2.69/0.92      | ~ v1_funct_1(X0_48)
% 2.69/0.92      | ~ v1_funct_1(X2_48)
% 2.69/0.92      | k1_partfun1(sK0,X1_48,X1_48,sK0,X2_48,X0_48) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 2.69/0.92      | k2_relset_1(X1_48,sK0,X0_48) = sK0 ),
% 2.69/0.92      inference(subtyping,[status(esa)],[c_495]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_1105,plain,
% 2.69/0.92      ( k1_partfun1(sK0,X0_48,X0_48,sK0,X1_48,X2_48) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 2.69/0.92      | k2_relset_1(X0_48,sK0,X2_48) = sK0
% 2.69/0.92      | v1_funct_2(X2_48,X0_48,sK0) != iProver_top
% 2.69/0.92      | v1_funct_2(X1_48,sK0,X0_48) != iProver_top
% 2.69/0.92      | m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,sK0))) != iProver_top
% 2.69/0.92      | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_48))) != iProver_top
% 2.69/0.92      | v1_funct_1(X2_48) != iProver_top
% 2.69/0.92      | v1_funct_1(X1_48) != iProver_top ),
% 2.69/0.92      inference(predicate_to_equality,[status(thm)],[c_639]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_2035,plain,
% 2.69/0.92      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 2.69/0.92      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 2.69/0.92      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 2.69/0.92      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.69/0.92      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.69/0.92      | v1_funct_1(sK2) != iProver_top
% 2.69/0.92      | v1_funct_1(sK3) != iProver_top ),
% 2.69/0.92      inference(equality_resolution,[status(thm)],[c_1105]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_25,negated_conjecture,
% 2.69/0.92      ( v1_funct_2(sK2,sK0,sK1) ),
% 2.69/0.92      inference(cnf_transformation,[],[f63]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_22,negated_conjecture,
% 2.69/0.92      ( v1_funct_2(sK3,sK1,sK0) ),
% 2.69/0.92      inference(cnf_transformation,[],[f66]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_1295,plain,
% 2.69/0.92      ( ~ v1_funct_2(X0_48,sK0,X1_48)
% 2.69/0.92      | ~ v1_funct_2(sK3,X1_48,sK0)
% 2.69/0.92      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(sK0,X1_48)))
% 2.69/0.92      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1_48,sK0)))
% 2.69/0.92      | ~ v1_funct_1(X0_48)
% 2.69/0.92      | ~ v1_funct_1(sK3)
% 2.69/0.92      | k1_partfun1(sK0,X1_48,X1_48,sK0,X0_48,sK3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 2.69/0.92      | k2_relset_1(X1_48,sK0,sK3) = sK0 ),
% 2.69/0.92      inference(instantiation,[status(thm)],[c_639]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_1536,plain,
% 2.69/0.92      ( ~ v1_funct_2(sK2,sK0,X0_48)
% 2.69/0.92      | ~ v1_funct_2(sK3,X0_48,sK0)
% 2.69/0.92      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_48)))
% 2.69/0.92      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_48,sK0)))
% 2.69/0.92      | ~ v1_funct_1(sK2)
% 2.69/0.92      | ~ v1_funct_1(sK3)
% 2.69/0.92      | k1_partfun1(sK0,X0_48,X0_48,sK0,sK2,sK3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 2.69/0.92      | k2_relset_1(X0_48,sK0,sK3) = sK0 ),
% 2.69/0.92      inference(instantiation,[status(thm)],[c_1295]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_1740,plain,
% 2.69/0.92      ( ~ v1_funct_2(sK2,sK0,sK1)
% 2.69/0.92      | ~ v1_funct_2(sK3,sK1,sK0)
% 2.69/0.92      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.69/0.92      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.69/0.92      | ~ v1_funct_1(sK2)
% 2.69/0.92      | ~ v1_funct_1(sK3)
% 2.69/0.92      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 2.69/0.92      | k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 2.69/0.92      inference(instantiation,[status(thm)],[c_1536]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_663,plain,( X0_48 = X0_48 ),theory(equality) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_1983,plain,
% 2.69/0.92      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 2.69/0.92      inference(instantiation,[status(thm)],[c_663]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_2038,plain,
% 2.69/0.92      ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 2.69/0.92      inference(global_propositional_subsumption,
% 2.69/0.92                [status(thm)],
% 2.69/0.92                [c_2035,c_26,c_25,c_24,c_23,c_22,c_21,c_1740,c_1983]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_2158,plain,
% 2.69/0.92      ( k2_relat_1(sK3) = sK0 ),
% 2.69/0.92      inference(light_normalisation,[status(thm)],[c_2150,c_2038]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_6,plain,
% 2.69/0.92      ( v5_relat_1(X0,X1)
% 2.69/0.92      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.69/0.92      inference(cnf_transformation,[],[f48]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_11,plain,
% 2.69/0.92      ( v2_funct_2(X0,k2_relat_1(X0))
% 2.69/0.92      | ~ v5_relat_1(X0,k2_relat_1(X0))
% 2.69/0.92      | ~ v1_relat_1(X0) ),
% 2.69/0.92      inference(cnf_transformation,[],[f72]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_302,plain,
% 2.69/0.92      ( v2_funct_2(X0,k2_relat_1(X0))
% 2.69/0.92      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 2.69/0.92      | ~ v1_relat_1(X0)
% 2.69/0.92      | X0 != X1
% 2.69/0.92      | k2_relat_1(X0) != X3 ),
% 2.69/0.92      inference(resolution_lifted,[status(thm)],[c_6,c_11]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_303,plain,
% 2.69/0.92      ( v2_funct_2(X0,k2_relat_1(X0))
% 2.69/0.92      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
% 2.69/0.92      | ~ v1_relat_1(X0) ),
% 2.69/0.92      inference(unflattening,[status(thm)],[c_302]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_5,plain,
% 2.69/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.69/0.92      | v1_relat_1(X0) ),
% 2.69/0.92      inference(cnf_transformation,[],[f47]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_313,plain,
% 2.69/0.92      ( v2_funct_2(X0,k2_relat_1(X0))
% 2.69/0.92      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0)))) ),
% 2.69/0.92      inference(forward_subsumption_resolution,[status(thm)],[c_303,c_5]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_19,negated_conjecture,
% 2.69/0.92      ( ~ v2_funct_2(sK3,sK0) | ~ v2_funct_1(sK2) ),
% 2.69/0.92      inference(cnf_transformation,[],[f69]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_349,plain,
% 2.69/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
% 2.69/0.92      | ~ v2_funct_1(sK2)
% 2.69/0.92      | k2_relat_1(X0) != sK0
% 2.69/0.92      | sK3 != X0 ),
% 2.69/0.92      inference(resolution_lifted,[status(thm)],[c_313,c_19]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_350,plain,
% 2.69/0.92      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3))))
% 2.69/0.92      | ~ v2_funct_1(sK2)
% 2.69/0.92      | k2_relat_1(sK3) != sK0 ),
% 2.69/0.92      inference(unflattening,[status(thm)],[c_349]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_642,plain,
% 2.69/0.92      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_48,k2_relat_1(sK3))))
% 2.69/0.92      | ~ v2_funct_1(sK2)
% 2.69/0.92      | k2_relat_1(sK3) != sK0 ),
% 2.69/0.92      inference(subtyping,[status(esa)],[c_350]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_660,plain,
% 2.69/0.92      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_48,k2_relat_1(sK3))))
% 2.69/0.92      | ~ sP0_iProver_split ),
% 2.69/0.92      inference(splitting,
% 2.69/0.92                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.69/0.92                [c_642]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_1102,plain,
% 2.69/0.92      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_48,k2_relat_1(sK3)))) != iProver_top
% 2.69/0.92      | sP0_iProver_split != iProver_top ),
% 2.69/0.92      inference(predicate_to_equality,[status(thm)],[c_660]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_2421,plain,
% 2.69/0.92      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_48,sK0))) != iProver_top
% 2.69/0.92      | sP0_iProver_split != iProver_top ),
% 2.69/0.92      inference(demodulation,[status(thm)],[c_2158,c_1102]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_2521,plain,
% 2.69/0.92      ( sP0_iProver_split != iProver_top ),
% 2.69/0.92      inference(superposition,[status(thm)],[c_1095,c_2421]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_661,plain,
% 2.69/0.92      ( ~ v2_funct_1(sK2) | sP0_iProver_split | k2_relat_1(sK3) != sK0 ),
% 2.69/0.92      inference(splitting,
% 2.69/0.92                [splitting(split),new_symbols(definition,[])],
% 2.69/0.92                [c_642]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_1101,plain,
% 2.69/0.92      ( k2_relat_1(sK3) != sK0
% 2.69/0.92      | v2_funct_1(sK2) != iProver_top
% 2.69/0.92      | sP0_iProver_split = iProver_top ),
% 2.69/0.92      inference(predicate_to_equality,[status(thm)],[c_661]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_2422,plain,
% 2.69/0.92      ( sK0 != sK0
% 2.69/0.92      | v2_funct_1(sK2) != iProver_top
% 2.69/0.92      | sP0_iProver_split = iProver_top ),
% 2.69/0.92      inference(demodulation,[status(thm)],[c_2158,c_1101]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_2423,plain,
% 2.69/0.92      ( v2_funct_1(sK2) != iProver_top
% 2.69/0.92      | sP0_iProver_split = iProver_top ),
% 2.69/0.92      inference(equality_resolution_simp,[status(thm)],[c_2422]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_645,negated_conjecture,
% 2.69/0.92      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.69/0.92      inference(subtyping,[status(esa)],[c_24]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_1098,plain,
% 2.69/0.92      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.69/0.92      inference(predicate_to_equality,[status(thm)],[c_645]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_7,plain,
% 2.69/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.69/0.92      | ~ v1_xboole_0(X1)
% 2.69/0.92      | v1_xboole_0(X0) ),
% 2.69/0.92      inference(cnf_transformation,[],[f49]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_655,plain,
% 2.69/0.92      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
% 2.69/0.92      | ~ v1_xboole_0(X1_48)
% 2.69/0.92      | v1_xboole_0(X0_48) ),
% 2.69/0.92      inference(subtyping,[status(esa)],[c_7]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_1088,plain,
% 2.69/0.92      ( m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48))) != iProver_top
% 2.69/0.92      | v1_xboole_0(X1_48) != iProver_top
% 2.69/0.92      | v1_xboole_0(X0_48) = iProver_top ),
% 2.69/0.92      inference(predicate_to_equality,[status(thm)],[c_655]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_2088,plain,
% 2.69/0.92      ( v1_xboole_0(sK2) = iProver_top
% 2.69/0.92      | v1_xboole_0(sK0) != iProver_top ),
% 2.69/0.92      inference(superposition,[status(thm)],[c_1098,c_1088]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_1,plain,
% 2.69/0.92      ( ~ v1_relat_1(X0)
% 2.69/0.92      | ~ v1_funct_1(X0)
% 2.69/0.92      | v2_funct_1(X0)
% 2.69/0.92      | ~ v1_xboole_0(X0) ),
% 2.69/0.92      inference(cnf_transformation,[],[f45]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_658,plain,
% 2.69/0.92      ( ~ v1_relat_1(X0_48)
% 2.69/0.92      | ~ v1_funct_1(X0_48)
% 2.69/0.92      | v2_funct_1(X0_48)
% 2.69/0.92      | ~ v1_xboole_0(X0_48) ),
% 2.69/0.92      inference(subtyping,[status(esa)],[c_1]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_1442,plain,
% 2.69/0.92      ( ~ v1_relat_1(sK2)
% 2.69/0.92      | ~ v1_funct_1(sK2)
% 2.69/0.92      | v2_funct_1(sK2)
% 2.69/0.92      | ~ v1_xboole_0(sK2) ),
% 2.69/0.92      inference(instantiation,[status(thm)],[c_658]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_1443,plain,
% 2.69/0.92      ( v1_relat_1(sK2) != iProver_top
% 2.69/0.92      | v1_funct_1(sK2) != iProver_top
% 2.69/0.92      | v2_funct_1(sK2) = iProver_top
% 2.69/0.92      | v1_xboole_0(sK2) != iProver_top ),
% 2.69/0.92      inference(predicate_to_equality,[status(thm)],[c_1442]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_667,plain,
% 2.69/0.92      ( ~ v1_xboole_0(X0_48) | v1_xboole_0(X1_48) | X1_48 != X0_48 ),
% 2.69/0.92      theory(equality) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_1434,plain,
% 2.69/0.92      ( v1_xboole_0(X0_48)
% 2.69/0.92      | ~ v1_xboole_0(k1_xboole_0)
% 2.69/0.92      | X0_48 != k1_xboole_0 ),
% 2.69/0.92      inference(instantiation,[status(thm)],[c_667]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_1435,plain,
% 2.69/0.92      ( X0_48 != k1_xboole_0
% 2.69/0.92      | v1_xboole_0(X0_48) = iProver_top
% 2.69/0.92      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.69/0.92      inference(predicate_to_equality,[status(thm)],[c_1434]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_1437,plain,
% 2.69/0.92      ( sK0 != k1_xboole_0
% 2.69/0.92      | v1_xboole_0(sK0) = iProver_top
% 2.69/0.92      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.69/0.92      inference(instantiation,[status(thm)],[c_1435]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_656,plain,
% 2.69/0.92      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
% 2.69/0.92      | v1_relat_1(X0_48) ),
% 2.69/0.92      inference(subtyping,[status(esa)],[c_5]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_1312,plain,
% 2.69/0.92      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.69/0.92      | v1_relat_1(sK2) ),
% 2.69/0.92      inference(instantiation,[status(thm)],[c_656]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_1313,plain,
% 2.69/0.92      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.69/0.92      | v1_relat_1(sK2) = iProver_top ),
% 2.69/0.92      inference(predicate_to_equality,[status(thm)],[c_1312]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_0,plain,
% 2.69/0.92      ( v1_xboole_0(k1_xboole_0) ),
% 2.69/0.92      inference(cnf_transformation,[],[f42]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_83,plain,
% 2.69/0.92      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.69/0.92      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_4,plain,
% 2.69/0.92      ( v2_funct_1(k6_partfun1(X0)) ),
% 2.69/0.92      inference(cnf_transformation,[],[f70]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_75,plain,
% 2.69/0.92      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 2.69/0.92      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_77,plain,
% 2.69/0.92      ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
% 2.69/0.92      inference(instantiation,[status(thm)],[c_75]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_31,plain,
% 2.69/0.92      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 2.69/0.92      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(c_28,plain,
% 2.69/0.92      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 2.69/0.92      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.69/0.92  
% 2.69/0.92  cnf(contradiction,plain,
% 2.69/0.92      ( $false ),
% 2.69/0.92      inference(minisat,
% 2.69/0.92                [status(thm)],
% 2.69/0.92                [c_2632,c_2521,c_2423,c_2088,c_1443,c_1437,c_1313,c_83,
% 2.69/0.92                 c_77,c_32,c_31,c_30,c_29,c_28,c_27]) ).
% 2.69/0.92  
% 2.69/0.92  
% 2.69/0.92  % SZS output end CNFRefutation for theBenchmark.p
% 2.69/0.92  
% 2.69/0.92  ------                               Statistics
% 2.69/0.92  
% 2.69/0.92  ------ General
% 2.69/0.92  
% 2.69/0.92  abstr_ref_over_cycles:                  0
% 2.69/0.92  abstr_ref_under_cycles:                 0
% 2.69/0.92  gc_basic_clause_elim:                   0
% 2.69/0.92  forced_gc_time:                         0
% 2.69/0.92  parsing_time:                           0.01
% 2.69/0.92  unif_index_cands_time:                  0.
% 2.69/0.92  unif_index_add_time:                    0.
% 2.69/0.92  orderings_time:                         0.
% 2.69/0.92  out_proof_time:                         0.01
% 2.69/0.92  total_time:                             0.138
% 2.69/0.92  num_of_symbols:                         52
% 2.69/0.92  num_of_terms:                           4517
% 2.69/0.92  
% 2.69/0.92  ------ Preprocessing
% 2.69/0.92  
% 2.69/0.92  num_of_splits:                          1
% 2.69/0.92  num_of_split_atoms:                     1
% 2.69/0.92  num_of_reused_defs:                     0
% 2.69/0.92  num_eq_ax_congr_red:                    12
% 2.69/0.92  num_of_sem_filtered_clauses:            1
% 2.69/0.92  num_of_subtypes:                        3
% 2.69/0.92  monotx_restored_types:                  0
% 2.69/0.92  sat_num_of_epr_types:                   0
% 2.69/0.92  sat_num_of_non_cyclic_types:            0
% 2.69/0.92  sat_guarded_non_collapsed_types:        1
% 2.69/0.92  num_pure_diseq_elim:                    0
% 2.69/0.92  simp_replaced_by:                       0
% 2.69/0.92  res_preprocessed:                       121
% 2.69/0.92  prep_upred:                             0
% 2.69/0.92  prep_unflattend:                        17
% 2.69/0.92  smt_new_axioms:                         0
% 2.69/0.92  pred_elim_cands:                        6
% 2.69/0.92  pred_elim:                              3
% 2.69/0.92  pred_elim_cl:                           4
% 2.69/0.92  pred_elim_cycles:                       6
% 2.69/0.92  merged_defs:                            0
% 2.69/0.92  merged_defs_ncl:                        0
% 2.69/0.92  bin_hyper_res:                          0
% 2.69/0.92  prep_cycles:                            4
% 2.69/0.92  pred_elim_time:                         0.005
% 2.69/0.92  splitting_time:                         0.
% 2.69/0.92  sem_filter_time:                        0.
% 2.69/0.92  monotx_time:                            0.
% 2.69/0.92  subtype_inf_time:                       0.001
% 2.69/0.92  
% 2.69/0.92  ------ Problem properties
% 2.69/0.92  
% 2.69/0.92  clauses:                                22
% 2.69/0.92  conjectures:                            6
% 2.69/0.92  epr:                                    6
% 2.69/0.92  horn:                                   21
% 2.69/0.92  ground:                                 9
% 2.69/0.92  unary:                                  9
% 2.69/0.92  binary:                                 4
% 2.69/0.92  lits:                                   70
% 2.69/0.92  lits_eq:                                8
% 2.69/0.92  fd_pure:                                0
% 2.69/0.92  fd_pseudo:                              0
% 2.69/0.92  fd_cond:                                1
% 2.69/0.92  fd_pseudo_cond:                         0
% 2.69/0.92  ac_symbols:                             0
% 2.69/0.92  
% 2.69/0.92  ------ Propositional Solver
% 2.69/0.92  
% 2.69/0.92  prop_solver_calls:                      26
% 2.69/0.92  prop_fast_solver_calls:                 874
% 2.69/0.92  smt_solver_calls:                       0
% 2.69/0.92  smt_fast_solver_calls:                  0
% 2.69/0.92  prop_num_of_clauses:                    979
% 2.69/0.92  prop_preprocess_simplified:             3870
% 2.69/0.92  prop_fo_subsumed:                       14
% 2.69/0.92  prop_solver_time:                       0.
% 2.69/0.92  smt_solver_time:                        0.
% 2.69/0.92  smt_fast_solver_time:                   0.
% 2.69/0.92  prop_fast_solver_time:                  0.
% 2.69/0.92  prop_unsat_core_time:                   0.
% 2.69/0.92  
% 2.69/0.92  ------ QBF
% 2.69/0.92  
% 2.69/0.92  qbf_q_res:                              0
% 2.69/0.92  qbf_num_tautologies:                    0
% 2.69/0.92  qbf_prep_cycles:                        0
% 2.69/0.92  
% 2.69/0.92  ------ BMC1
% 2.69/0.92  
% 2.69/0.92  bmc1_current_bound:                     -1
% 2.69/0.92  bmc1_last_solved_bound:                 -1
% 2.69/0.92  bmc1_unsat_core_size:                   -1
% 2.69/0.92  bmc1_unsat_core_parents_size:           -1
% 2.69/0.92  bmc1_merge_next_fun:                    0
% 2.69/0.92  bmc1_unsat_core_clauses_time:           0.
% 2.69/0.92  
% 2.69/0.92  ------ Instantiation
% 2.69/0.92  
% 2.69/0.92  inst_num_of_clauses:                    257
% 2.69/0.92  inst_num_in_passive:                    71
% 2.69/0.92  inst_num_in_active:                     175
% 2.69/0.92  inst_num_in_unprocessed:                11
% 2.69/0.92  inst_num_of_loops:                      180
% 2.69/0.92  inst_num_of_learning_restarts:          0
% 2.69/0.92  inst_num_moves_active_passive:          2
% 2.69/0.92  inst_lit_activity:                      0
% 2.69/0.92  inst_lit_activity_moves:                0
% 2.69/0.92  inst_num_tautologies:                   0
% 2.69/0.92  inst_num_prop_implied:                  0
% 2.69/0.92  inst_num_existing_simplified:           0
% 2.69/0.92  inst_num_eq_res_simplified:             0
% 2.69/0.92  inst_num_child_elim:                    0
% 2.69/0.92  inst_num_of_dismatching_blockings:      5
% 2.69/0.92  inst_num_of_non_proper_insts:           177
% 2.69/0.92  inst_num_of_duplicates:                 0
% 2.69/0.92  inst_inst_num_from_inst_to_res:         0
% 2.69/0.92  inst_dismatching_checking_time:         0.
% 2.69/0.92  
% 2.69/0.92  ------ Resolution
% 2.69/0.92  
% 2.69/0.92  res_num_of_clauses:                     0
% 2.69/0.92  res_num_in_passive:                     0
% 2.69/0.92  res_num_in_active:                      0
% 2.69/0.92  res_num_of_loops:                       125
% 2.69/0.92  res_forward_subset_subsumed:            18
% 2.69/0.92  res_backward_subset_subsumed:           0
% 2.69/0.92  res_forward_subsumed:                   0
% 2.69/0.92  res_backward_subsumed:                  0
% 2.69/0.92  res_forward_subsumption_resolution:     3
% 2.69/0.92  res_backward_subsumption_resolution:    0
% 2.69/0.92  res_clause_to_clause_subsumption:       51
% 2.69/0.92  res_orphan_elimination:                 0
% 2.69/0.92  res_tautology_del:                      15
% 2.69/0.92  res_num_eq_res_simplified:              1
% 2.69/0.92  res_num_sel_changes:                    0
% 2.69/0.92  res_moves_from_active_to_pass:          0
% 2.69/0.92  
% 2.69/0.92  ------ Superposition
% 2.69/0.92  
% 2.69/0.92  sup_time_total:                         0.
% 2.69/0.92  sup_time_generating:                    0.
% 2.69/0.92  sup_time_sim_full:                      0.
% 2.69/0.92  sup_time_sim_immed:                     0.
% 2.69/0.92  
% 2.69/0.92  sup_num_of_clauses:                     41
% 2.69/0.92  sup_num_in_active:                      31
% 2.69/0.92  sup_num_in_passive:                     10
% 2.69/0.92  sup_num_of_loops:                       34
% 2.69/0.92  sup_fw_superposition:                   13
% 2.69/0.92  sup_bw_superposition:                   7
% 2.69/0.92  sup_immediate_simplified:               2
% 2.69/0.92  sup_given_eliminated:                   0
% 2.69/0.92  comparisons_done:                       0
% 2.69/0.92  comparisons_avoided:                    0
% 2.69/0.92  
% 2.69/0.92  ------ Simplifications
% 2.69/0.92  
% 2.69/0.92  
% 2.69/0.92  sim_fw_subset_subsumed:                 0
% 2.69/0.92  sim_bw_subset_subsumed:                 0
% 2.69/0.92  sim_fw_subsumed:                        1
% 2.69/0.92  sim_bw_subsumed:                        0
% 2.69/0.92  sim_fw_subsumption_res:                 0
% 2.69/0.92  sim_bw_subsumption_res:                 0
% 2.69/0.92  sim_tautology_del:                      0
% 2.69/0.92  sim_eq_tautology_del:                   1
% 2.69/0.92  sim_eq_res_simp:                        1
% 2.69/0.92  sim_fw_demodulated:                     0
% 2.69/0.92  sim_bw_demodulated:                     4
% 2.69/0.92  sim_light_normalised:                   1
% 2.69/0.92  sim_joinable_taut:                      0
% 2.69/0.92  sim_joinable_simp:                      0
% 2.69/0.92  sim_ac_normalised:                      0
% 2.69/0.92  sim_smt_subsumption:                    0
% 2.69/0.92  
%------------------------------------------------------------------------------
