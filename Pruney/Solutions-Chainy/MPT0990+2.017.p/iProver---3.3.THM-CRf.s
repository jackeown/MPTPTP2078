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
% DateTime   : Thu Dec  3 12:02:59 EST 2020

% Result     : Theorem 1.00s
% Output     : CNFRefutation 1.00s
% Verified   : 
% Statistics : Number of formulae       :  184 ( 623 expanded)
%              Number of clauses        :  110 ( 200 expanded)
%              Number of leaves         :   18 ( 134 expanded)
%              Depth                    :   19
%              Number of atoms          :  568 (4066 expanded)
%              Number of equality atoms :  223 (1533 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
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

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f18,plain,(
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
    inference(pure_predicate_removal,[],[f17])).

fof(f42,plain,(
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
    inference(ennf_transformation,[],[f18])).

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
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f42])).

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

fof(f48,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f43,f47,f46])).

fof(f73,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f48])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f71,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f48])).

fof(f70,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f54,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
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
    inference(ennf_transformation,[],[f2])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f74,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f48])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f32,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f59,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f15,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f82,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f59,f69])).

fof(f76,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f40])).

fof(f68,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f72,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f36])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f75,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f48])).

fof(f13,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f67,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f38])).

fof(f66,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f30,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f57,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_partfun1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f53,f69])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_partfun1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f52,f69])).

fof(f79,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_643,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_1092,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_643])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_653,plain,
    ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
    | v1_relat_1(X0_49) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1086,plain,
    ( m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
    | v1_relat_1(X0_49) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_653])).

cnf(c_1421,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1092,c_1086])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_641,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_1094,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_641])).

cnf(c_1422,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1094,c_1086])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_640,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_1095,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_640])).

cnf(c_6,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_654,plain,
    ( ~ v1_funct_1(X0_49)
    | ~ v1_relat_1(X0_49)
    | v1_relat_1(k2_funct_1(X0_49)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1085,plain,
    ( v1_funct_1(X0_49) != iProver_top
    | v1_relat_1(X0_49) != iProver_top
    | v1_relat_1(k2_funct_1(X0_49)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_654])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k5_relat_1(k5_relat_1(X2,X0),X1) = k5_relat_1(X2,k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_658,plain,
    ( ~ v1_relat_1(X0_49)
    | ~ v1_relat_1(X1_49)
    | ~ v1_relat_1(X2_49)
    | k5_relat_1(k5_relat_1(X2_49,X0_49),X1_49) = k5_relat_1(X2_49,k5_relat_1(X0_49,X1_49)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1081,plain,
    ( k5_relat_1(k5_relat_1(X0_49,X1_49),X2_49) = k5_relat_1(X0_49,k5_relat_1(X1_49,X2_49))
    | v1_relat_1(X1_49) != iProver_top
    | v1_relat_1(X2_49) != iProver_top
    | v1_relat_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_658])).

cnf(c_2143,plain,
    ( k5_relat_1(k2_funct_1(X0_49),k5_relat_1(X1_49,X2_49)) = k5_relat_1(k5_relat_1(k2_funct_1(X0_49),X1_49),X2_49)
    | v1_funct_1(X0_49) != iProver_top
    | v1_relat_1(X0_49) != iProver_top
    | v1_relat_1(X1_49) != iProver_top
    | v1_relat_1(X2_49) != iProver_top ),
    inference(superposition,[status(thm)],[c_1085,c_1081])).

cnf(c_4564,plain,
    ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0_49),X1_49) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0_49,X1_49))
    | v1_relat_1(X0_49) != iProver_top
    | v1_relat_1(X1_49) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1095,c_2143])).

cnf(c_31,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_1267,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_653])).

cnf(c_1268,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1267])).

cnf(c_4705,plain,
    ( v1_relat_1(X1_49) != iProver_top
    | v1_relat_1(X0_49) != iProver_top
    | k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0_49),X1_49) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0_49,X1_49)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4564,c_31,c_1268])).

cnf(c_4706,plain,
    ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0_49),X1_49) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0_49,X1_49))
    | v1_relat_1(X0_49) != iProver_top
    | v1_relat_1(X1_49) != iProver_top ),
    inference(renaming,[status(thm)],[c_4705])).

cnf(c_4712,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0_49)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),X0_49)
    | v1_relat_1(X0_49) != iProver_top ),
    inference(superposition,[status(thm)],[c_1422,c_4706])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_652,plain,
    ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
    | k2_relset_1(X0_50,X1_50,X0_49) = k2_relat_1(X0_49) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1087,plain,
    ( k2_relset_1(X0_50,X1_50,X0_49) = k2_relat_1(X0_49)
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_652])).

cnf(c_2043,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1094,c_1087])).

cnf(c_25,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_644,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_2048,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2043,c_644])).

cnf(c_9,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_23,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_395,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_23])).

cnf(c_396,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(unflattening,[status(thm)],[c_395])).

cnf(c_398,plain,
    ( ~ v1_relat_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_396,c_29])).

cnf(c_636,plain,
    ( ~ v1_relat_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(subtyping,[status(esa)],[c_398])).

cnf(c_1099,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_636])).

cnf(c_1706,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1099,c_28,c_636,c_1267])).

cnf(c_2055,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(demodulation,[status(thm)],[c_2048,c_1706])).

cnf(c_4734,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0_49)) = k5_relat_1(k6_partfun1(sK1),X0_49)
    | v1_relat_1(X0_49) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4712,c_2055])).

cnf(c_4800,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
    inference(superposition,[status(thm)],[c_1421,c_4734])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_648,plain,
    ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
    | ~ m1_subset_1(X1_49,k1_zfmisc_1(k2_zfmisc_1(X2_50,X3_50)))
    | ~ v1_funct_1(X0_49)
    | ~ v1_funct_1(X1_49)
    | k1_partfun1(X2_50,X3_50,X0_50,X1_50,X1_49,X0_49) = k5_relat_1(X1_49,X0_49) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1091,plain,
    ( k1_partfun1(X0_50,X1_50,X2_50,X3_50,X0_49,X1_49) = k5_relat_1(X0_49,X1_49)
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
    | m1_subset_1(X1_49,k1_zfmisc_1(k2_zfmisc_1(X2_50,X3_50))) != iProver_top
    | v1_funct_1(X1_49) != iProver_top
    | v1_funct_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_648])).

cnf(c_3089,plain,
    ( k1_partfun1(X0_50,X1_50,sK1,sK0,X0_49,sK3) = k5_relat_1(X0_49,sK3)
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1092,c_1091])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_32,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3689,plain,
    ( v1_funct_1(X0_49) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
    | k1_partfun1(X0_50,X1_50,sK1,sK0,X0_49,sK3) = k5_relat_1(X0_49,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3089,c_32])).

cnf(c_3690,plain,
    ( k1_partfun1(X0_50,X1_50,sK1,sK0,X0_49,sK3) = k5_relat_1(X0_49,sK3)
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
    | v1_funct_1(X0_49) != iProver_top ),
    inference(renaming,[status(thm)],[c_3689])).

cnf(c_3699,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1094,c_3690])).

cnf(c_15,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_24,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_364,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_24])).

cnf(c_365,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_364])).

cnf(c_18,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_40,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_367,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_365,c_40])).

cnf(c_638,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_367])).

cnf(c_1097,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_638])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_651,plain,
    ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
    | ~ m1_subset_1(X1_49,k1_zfmisc_1(k2_zfmisc_1(X2_50,X3_50)))
    | m1_subset_1(k1_partfun1(X2_50,X3_50,X0_50,X1_50,X1_49,X0_49),k1_zfmisc_1(k2_zfmisc_1(X2_50,X1_50)))
    | ~ v1_funct_1(X0_49)
    | ~ v1_funct_1(X1_49) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1354,plain,
    ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
    | m1_subset_1(k1_partfun1(X0_50,X1_50,sK1,sK0,X0_49,sK3),k1_zfmisc_1(k2_zfmisc_1(X0_50,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(X0_49)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_651])).

cnf(c_1519,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1354])).

cnf(c_1710,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1097,c_29,c_28,c_27,c_26,c_638,c_1519])).

cnf(c_3720,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3699,c_1710])).

cnf(c_30,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_4309,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3720,c_30])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v4_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_300,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_12,c_1])).

cnf(c_304,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_300,c_11])).

cnf(c_305,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_304])).

cnf(c_639,plain,
    ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
    | r1_tarski(k1_relat_1(X0_49),X0_50) ),
    inference(subtyping,[status(esa)],[c_305])).

cnf(c_1096,plain,
    ( m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
    | r1_tarski(k1_relat_1(X0_49),X0_50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_639])).

cnf(c_4317,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1094,c_1096])).

cnf(c_7,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_423,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_23])).

cnf(c_424,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_423])).

cnf(c_426,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_424,c_29])).

cnf(c_634,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_426])).

cnf(c_1101,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_634])).

cnf(c_1651,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1101,c_28,c_634,c_1267])).

cnf(c_4,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_partfun1(X1)) = X0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_656,plain,
    ( ~ r1_tarski(k2_relat_1(X0_49),X0_50)
    | ~ v1_relat_1(X0_49)
    | k5_relat_1(X0_49,k6_partfun1(X0_50)) = X0_49 ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1083,plain,
    ( k5_relat_1(X0_49,k6_partfun1(X0_50)) = X0_49
    | r1_tarski(k2_relat_1(X0_49),X0_50) != iProver_top
    | v1_relat_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_656])).

cnf(c_1733,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0_50)) = k2_funct_1(sK2)
    | r1_tarski(k1_relat_1(sK2),X0_50) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1651,c_1083])).

cnf(c_709,plain,
    ( v1_funct_1(X0_49) != iProver_top
    | v1_relat_1(X0_49) != iProver_top
    | v1_relat_1(k2_funct_1(X0_49)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_654])).

cnf(c_711,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_709])).

cnf(c_2413,plain,
    ( r1_tarski(k1_relat_1(sK2),X0_50) != iProver_top
    | k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0_50)) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1733,c_30,c_31,c_711,c_1268])).

cnf(c_2414,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0_50)) = k2_funct_1(sK2)
    | r1_tarski(k1_relat_1(sK2),X0_50) != iProver_top ),
    inference(renaming,[status(thm)],[c_2413])).

cnf(c_4366,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k2_funct_1(sK2) ),
    inference(superposition,[status(thm)],[c_4317,c_2414])).

cnf(c_4316,plain,
    ( r1_tarski(k1_relat_1(sK3),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1092,c_1096])).

cnf(c_3,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k6_partfun1(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_657,plain,
    ( ~ r1_tarski(k1_relat_1(X0_49),X0_50)
    | ~ v1_relat_1(X0_49)
    | k5_relat_1(k6_partfun1(X0_50),X0_49) = X0_49 ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1082,plain,
    ( k5_relat_1(k6_partfun1(X0_50),X0_49) = X0_49
    | r1_tarski(k1_relat_1(X0_49),X0_50) != iProver_top
    | v1_relat_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_657])).

cnf(c_4361,plain,
    ( k5_relat_1(k6_partfun1(sK1),sK3) = sK3
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4316,c_1082])).

cnf(c_1264,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_653])).

cnf(c_1275,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | r1_tarski(k1_relat_1(sK3),sK1) ),
    inference(instantiation,[status(thm)],[c_639])).

cnf(c_1370,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),X0_50)
    | ~ v1_relat_1(sK3)
    | k5_relat_1(k6_partfun1(X0_50),sK3) = sK3 ),
    inference(instantiation,[status(thm)],[c_657])).

cnf(c_1549,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),sK1)
    | ~ v1_relat_1(sK3)
    | k5_relat_1(k6_partfun1(sK1),sK3) = sK3 ),
    inference(instantiation,[status(thm)],[c_1370])).

cnf(c_4387,plain,
    ( k5_relat_1(k6_partfun1(sK1),sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4361,c_26,c_1264,c_1275,c_1549])).

cnf(c_4805,plain,
    ( k2_funct_1(sK2) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_4800,c_4309,c_4366,c_4387])).

cnf(c_20,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_647,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4805,c_647])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:52:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 1.00/1.05  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.00/1.05  
% 1.00/1.05  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.00/1.05  
% 1.00/1.05  ------  iProver source info
% 1.00/1.05  
% 1.00/1.05  git: date: 2020-06-30 10:37:57 +0100
% 1.00/1.05  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.00/1.05  git: non_committed_changes: false
% 1.00/1.05  git: last_make_outside_of_git: false
% 1.00/1.05  
% 1.00/1.05  ------ 
% 1.00/1.05  
% 1.00/1.05  ------ Input Options
% 1.00/1.05  
% 1.00/1.05  --out_options                           all
% 1.00/1.05  --tptp_safe_out                         true
% 1.00/1.05  --problem_path                          ""
% 1.00/1.05  --include_path                          ""
% 1.00/1.05  --clausifier                            res/vclausify_rel
% 1.00/1.05  --clausifier_options                    --mode clausify
% 1.00/1.05  --stdin                                 false
% 1.00/1.05  --stats_out                             all
% 1.00/1.05  
% 1.00/1.05  ------ General Options
% 1.00/1.05  
% 1.00/1.05  --fof                                   false
% 1.00/1.05  --time_out_real                         305.
% 1.00/1.05  --time_out_virtual                      -1.
% 1.00/1.05  --symbol_type_check                     false
% 1.00/1.05  --clausify_out                          false
% 1.00/1.05  --sig_cnt_out                           false
% 1.00/1.05  --trig_cnt_out                          false
% 1.00/1.05  --trig_cnt_out_tolerance                1.
% 1.00/1.05  --trig_cnt_out_sk_spl                   false
% 1.00/1.05  --abstr_cl_out                          false
% 1.00/1.05  
% 1.00/1.05  ------ Global Options
% 1.00/1.05  
% 1.00/1.05  --schedule                              default
% 1.00/1.05  --add_important_lit                     false
% 1.00/1.05  --prop_solver_per_cl                    1000
% 1.00/1.05  --min_unsat_core                        false
% 1.00/1.05  --soft_assumptions                      false
% 1.00/1.05  --soft_lemma_size                       3
% 1.00/1.05  --prop_impl_unit_size                   0
% 1.00/1.05  --prop_impl_unit                        []
% 1.00/1.05  --share_sel_clauses                     true
% 1.00/1.05  --reset_solvers                         false
% 1.00/1.05  --bc_imp_inh                            [conj_cone]
% 1.00/1.05  --conj_cone_tolerance                   3.
% 1.00/1.05  --extra_neg_conj                        none
% 1.00/1.05  --large_theory_mode                     true
% 1.00/1.05  --prolific_symb_bound                   200
% 1.00/1.05  --lt_threshold                          2000
% 1.00/1.05  --clause_weak_htbl                      true
% 1.00/1.05  --gc_record_bc_elim                     false
% 1.00/1.05  
% 1.00/1.05  ------ Preprocessing Options
% 1.00/1.05  
% 1.00/1.05  --preprocessing_flag                    true
% 1.00/1.05  --time_out_prep_mult                    0.1
% 1.00/1.05  --splitting_mode                        input
% 1.00/1.05  --splitting_grd                         true
% 1.00/1.05  --splitting_cvd                         false
% 1.00/1.05  --splitting_cvd_svl                     false
% 1.00/1.05  --splitting_nvd                         32
% 1.00/1.05  --sub_typing                            true
% 1.00/1.05  --prep_gs_sim                           true
% 1.00/1.05  --prep_unflatten                        true
% 1.00/1.05  --prep_res_sim                          true
% 1.00/1.05  --prep_upred                            true
% 1.00/1.05  --prep_sem_filter                       exhaustive
% 1.00/1.05  --prep_sem_filter_out                   false
% 1.00/1.05  --pred_elim                             true
% 1.00/1.05  --res_sim_input                         true
% 1.00/1.05  --eq_ax_congr_red                       true
% 1.00/1.05  --pure_diseq_elim                       true
% 1.00/1.05  --brand_transform                       false
% 1.00/1.05  --non_eq_to_eq                          false
% 1.00/1.05  --prep_def_merge                        true
% 1.00/1.05  --prep_def_merge_prop_impl              false
% 1.00/1.05  --prep_def_merge_mbd                    true
% 1.00/1.05  --prep_def_merge_tr_red                 false
% 1.00/1.05  --prep_def_merge_tr_cl                  false
% 1.00/1.05  --smt_preprocessing                     true
% 1.00/1.05  --smt_ac_axioms                         fast
% 1.00/1.05  --preprocessed_out                      false
% 1.00/1.05  --preprocessed_stats                    false
% 1.00/1.05  
% 1.00/1.05  ------ Abstraction refinement Options
% 1.00/1.05  
% 1.00/1.05  --abstr_ref                             []
% 1.00/1.05  --abstr_ref_prep                        false
% 1.00/1.05  --abstr_ref_until_sat                   false
% 1.00/1.05  --abstr_ref_sig_restrict                funpre
% 1.00/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 1.00/1.05  --abstr_ref_under                       []
% 1.00/1.05  
% 1.00/1.05  ------ SAT Options
% 1.00/1.05  
% 1.00/1.05  --sat_mode                              false
% 1.00/1.05  --sat_fm_restart_options                ""
% 1.00/1.05  --sat_gr_def                            false
% 1.00/1.05  --sat_epr_types                         true
% 1.00/1.05  --sat_non_cyclic_types                  false
% 1.00/1.05  --sat_finite_models                     false
% 1.00/1.05  --sat_fm_lemmas                         false
% 1.00/1.05  --sat_fm_prep                           false
% 1.00/1.05  --sat_fm_uc_incr                        true
% 1.00/1.05  --sat_out_model                         small
% 1.00/1.05  --sat_out_clauses                       false
% 1.00/1.05  
% 1.00/1.05  ------ QBF Options
% 1.00/1.05  
% 1.00/1.05  --qbf_mode                              false
% 1.00/1.05  --qbf_elim_univ                         false
% 1.00/1.05  --qbf_dom_inst                          none
% 1.00/1.05  --qbf_dom_pre_inst                      false
% 1.00/1.05  --qbf_sk_in                             false
% 1.00/1.05  --qbf_pred_elim                         true
% 1.00/1.05  --qbf_split                             512
% 1.00/1.05  
% 1.00/1.05  ------ BMC1 Options
% 1.00/1.05  
% 1.00/1.05  --bmc1_incremental                      false
% 1.00/1.05  --bmc1_axioms                           reachable_all
% 1.00/1.05  --bmc1_min_bound                        0
% 1.00/1.05  --bmc1_max_bound                        -1
% 1.00/1.05  --bmc1_max_bound_default                -1
% 1.00/1.05  --bmc1_symbol_reachability              true
% 1.00/1.05  --bmc1_property_lemmas                  false
% 1.00/1.05  --bmc1_k_induction                      false
% 1.00/1.05  --bmc1_non_equiv_states                 false
% 1.00/1.05  --bmc1_deadlock                         false
% 1.00/1.05  --bmc1_ucm                              false
% 1.00/1.05  --bmc1_add_unsat_core                   none
% 1.00/1.05  --bmc1_unsat_core_children              false
% 1.00/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 1.00/1.05  --bmc1_out_stat                         full
% 1.00/1.05  --bmc1_ground_init                      false
% 1.00/1.05  --bmc1_pre_inst_next_state              false
% 1.00/1.05  --bmc1_pre_inst_state                   false
% 1.00/1.05  --bmc1_pre_inst_reach_state             false
% 1.00/1.05  --bmc1_out_unsat_core                   false
% 1.00/1.05  --bmc1_aig_witness_out                  false
% 1.00/1.05  --bmc1_verbose                          false
% 1.00/1.05  --bmc1_dump_clauses_tptp                false
% 1.00/1.05  --bmc1_dump_unsat_core_tptp             false
% 1.00/1.05  --bmc1_dump_file                        -
% 1.00/1.05  --bmc1_ucm_expand_uc_limit              128
% 1.00/1.05  --bmc1_ucm_n_expand_iterations          6
% 1.00/1.05  --bmc1_ucm_extend_mode                  1
% 1.00/1.05  --bmc1_ucm_init_mode                    2
% 1.00/1.05  --bmc1_ucm_cone_mode                    none
% 1.00/1.05  --bmc1_ucm_reduced_relation_type        0
% 1.00/1.05  --bmc1_ucm_relax_model                  4
% 1.00/1.05  --bmc1_ucm_full_tr_after_sat            true
% 1.00/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 1.00/1.05  --bmc1_ucm_layered_model                none
% 1.00/1.05  --bmc1_ucm_max_lemma_size               10
% 1.00/1.05  
% 1.00/1.05  ------ AIG Options
% 1.00/1.05  
% 1.00/1.05  --aig_mode                              false
% 1.00/1.05  
% 1.00/1.05  ------ Instantiation Options
% 1.00/1.05  
% 1.00/1.05  --instantiation_flag                    true
% 1.00/1.05  --inst_sos_flag                         false
% 1.00/1.05  --inst_sos_phase                        true
% 1.00/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.00/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.00/1.05  --inst_lit_sel_side                     num_symb
% 1.00/1.05  --inst_solver_per_active                1400
% 1.00/1.05  --inst_solver_calls_frac                1.
% 1.00/1.05  --inst_passive_queue_type               priority_queues
% 1.00/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.00/1.05  --inst_passive_queues_freq              [25;2]
% 1.00/1.05  --inst_dismatching                      true
% 1.00/1.05  --inst_eager_unprocessed_to_passive     true
% 1.00/1.05  --inst_prop_sim_given                   true
% 1.00/1.05  --inst_prop_sim_new                     false
% 1.00/1.05  --inst_subs_new                         false
% 1.00/1.05  --inst_eq_res_simp                      false
% 1.00/1.05  --inst_subs_given                       false
% 1.00/1.05  --inst_orphan_elimination               true
% 1.00/1.05  --inst_learning_loop_flag               true
% 1.00/1.05  --inst_learning_start                   3000
% 1.00/1.05  --inst_learning_factor                  2
% 1.00/1.05  --inst_start_prop_sim_after_learn       3
% 1.00/1.05  --inst_sel_renew                        solver
% 1.00/1.05  --inst_lit_activity_flag                true
% 1.00/1.05  --inst_restr_to_given                   false
% 1.00/1.05  --inst_activity_threshold               500
% 1.00/1.05  --inst_out_proof                        true
% 1.00/1.05  
% 1.00/1.05  ------ Resolution Options
% 1.00/1.05  
% 1.00/1.05  --resolution_flag                       true
% 1.00/1.05  --res_lit_sel                           adaptive
% 1.00/1.05  --res_lit_sel_side                      none
% 1.00/1.05  --res_ordering                          kbo
% 1.00/1.05  --res_to_prop_solver                    active
% 1.00/1.05  --res_prop_simpl_new                    false
% 1.00/1.05  --res_prop_simpl_given                  true
% 1.00/1.05  --res_passive_queue_type                priority_queues
% 1.00/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.00/1.05  --res_passive_queues_freq               [15;5]
% 1.00/1.05  --res_forward_subs                      full
% 1.00/1.05  --res_backward_subs                     full
% 1.00/1.05  --res_forward_subs_resolution           true
% 1.00/1.05  --res_backward_subs_resolution          true
% 1.00/1.05  --res_orphan_elimination                true
% 1.00/1.05  --res_time_limit                        2.
% 1.00/1.05  --res_out_proof                         true
% 1.00/1.05  
% 1.00/1.05  ------ Superposition Options
% 1.00/1.05  
% 1.00/1.05  --superposition_flag                    true
% 1.00/1.05  --sup_passive_queue_type                priority_queues
% 1.00/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.00/1.05  --sup_passive_queues_freq               [8;1;4]
% 1.00/1.05  --demod_completeness_check              fast
% 1.00/1.05  --demod_use_ground                      true
% 1.00/1.05  --sup_to_prop_solver                    passive
% 1.00/1.05  --sup_prop_simpl_new                    true
% 1.00/1.05  --sup_prop_simpl_given                  true
% 1.00/1.05  --sup_fun_splitting                     false
% 1.00/1.05  --sup_smt_interval                      50000
% 1.00/1.05  
% 1.00/1.05  ------ Superposition Simplification Setup
% 1.00/1.05  
% 1.00/1.05  --sup_indices_passive                   []
% 1.00/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.00/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.00/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.00/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 1.00/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.00/1.05  --sup_full_bw                           [BwDemod]
% 1.00/1.05  --sup_immed_triv                        [TrivRules]
% 1.00/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.00/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.00/1.05  --sup_immed_bw_main                     []
% 1.00/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.00/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 1.00/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.00/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.00/1.05  
% 1.00/1.05  ------ Combination Options
% 1.00/1.05  
% 1.00/1.05  --comb_res_mult                         3
% 1.00/1.05  --comb_sup_mult                         2
% 1.00/1.05  --comb_inst_mult                        10
% 1.00/1.05  
% 1.00/1.05  ------ Debug Options
% 1.00/1.05  
% 1.00/1.05  --dbg_backtrace                         false
% 1.00/1.05  --dbg_dump_prop_clauses                 false
% 1.00/1.05  --dbg_dump_prop_clauses_file            -
% 1.00/1.05  --dbg_out_stat                          false
% 1.00/1.05  ------ Parsing...
% 1.00/1.05  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.00/1.05  
% 1.00/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 1.00/1.05  
% 1.00/1.05  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.00/1.05  
% 1.00/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.00/1.05  ------ Proving...
% 1.00/1.05  ------ Problem Properties 
% 1.00/1.05  
% 1.00/1.05  
% 1.00/1.05  clauses                                 25
% 1.00/1.05  conjectures                             8
% 1.00/1.05  EPR                                     4
% 1.00/1.05  Horn                                    25
% 1.00/1.05  unary                                   9
% 1.00/1.05  binary                                  8
% 1.00/1.05  lits                                    56
% 1.00/1.05  lits eq                                 14
% 1.00/1.05  fd_pure                                 0
% 1.00/1.05  fd_pseudo                               0
% 1.00/1.05  fd_cond                                 0
% 1.00/1.05  fd_pseudo_cond                          0
% 1.00/1.05  AC symbols                              0
% 1.00/1.05  
% 1.00/1.05  ------ Schedule dynamic 5 is on 
% 1.00/1.05  
% 1.00/1.05  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.00/1.05  
% 1.00/1.05  
% 1.00/1.05  ------ 
% 1.00/1.05  Current options:
% 1.00/1.05  ------ 
% 1.00/1.05  
% 1.00/1.05  ------ Input Options
% 1.00/1.05  
% 1.00/1.05  --out_options                           all
% 1.00/1.05  --tptp_safe_out                         true
% 1.00/1.05  --problem_path                          ""
% 1.00/1.05  --include_path                          ""
% 1.00/1.05  --clausifier                            res/vclausify_rel
% 1.00/1.05  --clausifier_options                    --mode clausify
% 1.00/1.05  --stdin                                 false
% 1.00/1.05  --stats_out                             all
% 1.00/1.05  
% 1.00/1.05  ------ General Options
% 1.00/1.05  
% 1.00/1.05  --fof                                   false
% 1.00/1.05  --time_out_real                         305.
% 1.00/1.05  --time_out_virtual                      -1.
% 1.00/1.05  --symbol_type_check                     false
% 1.00/1.05  --clausify_out                          false
% 1.00/1.05  --sig_cnt_out                           false
% 1.00/1.05  --trig_cnt_out                          false
% 1.00/1.05  --trig_cnt_out_tolerance                1.
% 1.00/1.05  --trig_cnt_out_sk_spl                   false
% 1.00/1.05  --abstr_cl_out                          false
% 1.00/1.05  
% 1.00/1.05  ------ Global Options
% 1.00/1.05  
% 1.00/1.05  --schedule                              default
% 1.00/1.05  --add_important_lit                     false
% 1.00/1.05  --prop_solver_per_cl                    1000
% 1.00/1.05  --min_unsat_core                        false
% 1.00/1.05  --soft_assumptions                      false
% 1.00/1.05  --soft_lemma_size                       3
% 1.00/1.05  --prop_impl_unit_size                   0
% 1.00/1.05  --prop_impl_unit                        []
% 1.00/1.05  --share_sel_clauses                     true
% 1.00/1.05  --reset_solvers                         false
% 1.00/1.05  --bc_imp_inh                            [conj_cone]
% 1.00/1.05  --conj_cone_tolerance                   3.
% 1.00/1.05  --extra_neg_conj                        none
% 1.00/1.05  --large_theory_mode                     true
% 1.00/1.05  --prolific_symb_bound                   200
% 1.00/1.05  --lt_threshold                          2000
% 1.00/1.05  --clause_weak_htbl                      true
% 1.00/1.05  --gc_record_bc_elim                     false
% 1.00/1.05  
% 1.00/1.05  ------ Preprocessing Options
% 1.00/1.05  
% 1.00/1.05  --preprocessing_flag                    true
% 1.00/1.05  --time_out_prep_mult                    0.1
% 1.00/1.05  --splitting_mode                        input
% 1.00/1.05  --splitting_grd                         true
% 1.00/1.05  --splitting_cvd                         false
% 1.00/1.05  --splitting_cvd_svl                     false
% 1.00/1.05  --splitting_nvd                         32
% 1.00/1.05  --sub_typing                            true
% 1.00/1.05  --prep_gs_sim                           true
% 1.00/1.05  --prep_unflatten                        true
% 1.00/1.05  --prep_res_sim                          true
% 1.00/1.05  --prep_upred                            true
% 1.00/1.05  --prep_sem_filter                       exhaustive
% 1.00/1.05  --prep_sem_filter_out                   false
% 1.00/1.05  --pred_elim                             true
% 1.00/1.05  --res_sim_input                         true
% 1.00/1.05  --eq_ax_congr_red                       true
% 1.00/1.05  --pure_diseq_elim                       true
% 1.00/1.05  --brand_transform                       false
% 1.00/1.05  --non_eq_to_eq                          false
% 1.00/1.05  --prep_def_merge                        true
% 1.00/1.05  --prep_def_merge_prop_impl              false
% 1.00/1.05  --prep_def_merge_mbd                    true
% 1.00/1.05  --prep_def_merge_tr_red                 false
% 1.00/1.05  --prep_def_merge_tr_cl                  false
% 1.00/1.05  --smt_preprocessing                     true
% 1.00/1.05  --smt_ac_axioms                         fast
% 1.00/1.05  --preprocessed_out                      false
% 1.00/1.05  --preprocessed_stats                    false
% 1.00/1.05  
% 1.00/1.05  ------ Abstraction refinement Options
% 1.00/1.05  
% 1.00/1.05  --abstr_ref                             []
% 1.00/1.05  --abstr_ref_prep                        false
% 1.00/1.05  --abstr_ref_until_sat                   false
% 1.00/1.05  --abstr_ref_sig_restrict                funpre
% 1.00/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 1.00/1.05  --abstr_ref_under                       []
% 1.00/1.05  
% 1.00/1.05  ------ SAT Options
% 1.00/1.05  
% 1.00/1.05  --sat_mode                              false
% 1.00/1.05  --sat_fm_restart_options                ""
% 1.00/1.05  --sat_gr_def                            false
% 1.00/1.05  --sat_epr_types                         true
% 1.00/1.05  --sat_non_cyclic_types                  false
% 1.00/1.05  --sat_finite_models                     false
% 1.00/1.05  --sat_fm_lemmas                         false
% 1.00/1.05  --sat_fm_prep                           false
% 1.00/1.05  --sat_fm_uc_incr                        true
% 1.00/1.05  --sat_out_model                         small
% 1.00/1.05  --sat_out_clauses                       false
% 1.00/1.05  
% 1.00/1.05  ------ QBF Options
% 1.00/1.05  
% 1.00/1.05  --qbf_mode                              false
% 1.00/1.05  --qbf_elim_univ                         false
% 1.00/1.05  --qbf_dom_inst                          none
% 1.00/1.05  --qbf_dom_pre_inst                      false
% 1.00/1.05  --qbf_sk_in                             false
% 1.00/1.05  --qbf_pred_elim                         true
% 1.00/1.05  --qbf_split                             512
% 1.00/1.05  
% 1.00/1.05  ------ BMC1 Options
% 1.00/1.05  
% 1.00/1.05  --bmc1_incremental                      false
% 1.00/1.05  --bmc1_axioms                           reachable_all
% 1.00/1.05  --bmc1_min_bound                        0
% 1.00/1.05  --bmc1_max_bound                        -1
% 1.00/1.05  --bmc1_max_bound_default                -1
% 1.00/1.05  --bmc1_symbol_reachability              true
% 1.00/1.05  --bmc1_property_lemmas                  false
% 1.00/1.05  --bmc1_k_induction                      false
% 1.00/1.05  --bmc1_non_equiv_states                 false
% 1.00/1.05  --bmc1_deadlock                         false
% 1.00/1.05  --bmc1_ucm                              false
% 1.00/1.05  --bmc1_add_unsat_core                   none
% 1.00/1.05  --bmc1_unsat_core_children              false
% 1.00/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 1.00/1.05  --bmc1_out_stat                         full
% 1.00/1.05  --bmc1_ground_init                      false
% 1.00/1.05  --bmc1_pre_inst_next_state              false
% 1.00/1.05  --bmc1_pre_inst_state                   false
% 1.00/1.05  --bmc1_pre_inst_reach_state             false
% 1.00/1.05  --bmc1_out_unsat_core                   false
% 1.00/1.05  --bmc1_aig_witness_out                  false
% 1.00/1.05  --bmc1_verbose                          false
% 1.00/1.05  --bmc1_dump_clauses_tptp                false
% 1.00/1.05  --bmc1_dump_unsat_core_tptp             false
% 1.00/1.05  --bmc1_dump_file                        -
% 1.00/1.05  --bmc1_ucm_expand_uc_limit              128
% 1.00/1.05  --bmc1_ucm_n_expand_iterations          6
% 1.00/1.05  --bmc1_ucm_extend_mode                  1
% 1.00/1.05  --bmc1_ucm_init_mode                    2
% 1.00/1.05  --bmc1_ucm_cone_mode                    none
% 1.00/1.05  --bmc1_ucm_reduced_relation_type        0
% 1.00/1.05  --bmc1_ucm_relax_model                  4
% 1.00/1.05  --bmc1_ucm_full_tr_after_sat            true
% 1.00/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 1.00/1.05  --bmc1_ucm_layered_model                none
% 1.00/1.05  --bmc1_ucm_max_lemma_size               10
% 1.00/1.05  
% 1.00/1.05  ------ AIG Options
% 1.00/1.05  
% 1.00/1.05  --aig_mode                              false
% 1.00/1.05  
% 1.00/1.05  ------ Instantiation Options
% 1.00/1.05  
% 1.00/1.05  --instantiation_flag                    true
% 1.00/1.05  --inst_sos_flag                         false
% 1.00/1.05  --inst_sos_phase                        true
% 1.00/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.00/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.00/1.05  --inst_lit_sel_side                     none
% 1.00/1.05  --inst_solver_per_active                1400
% 1.00/1.05  --inst_solver_calls_frac                1.
% 1.00/1.05  --inst_passive_queue_type               priority_queues
% 1.00/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.00/1.05  --inst_passive_queues_freq              [25;2]
% 1.00/1.05  --inst_dismatching                      true
% 1.00/1.05  --inst_eager_unprocessed_to_passive     true
% 1.00/1.05  --inst_prop_sim_given                   true
% 1.00/1.05  --inst_prop_sim_new                     false
% 1.00/1.05  --inst_subs_new                         false
% 1.00/1.05  --inst_eq_res_simp                      false
% 1.00/1.05  --inst_subs_given                       false
% 1.00/1.05  --inst_orphan_elimination               true
% 1.00/1.05  --inst_learning_loop_flag               true
% 1.00/1.05  --inst_learning_start                   3000
% 1.00/1.05  --inst_learning_factor                  2
% 1.00/1.05  --inst_start_prop_sim_after_learn       3
% 1.00/1.05  --inst_sel_renew                        solver
% 1.00/1.05  --inst_lit_activity_flag                true
% 1.00/1.05  --inst_restr_to_given                   false
% 1.00/1.05  --inst_activity_threshold               500
% 1.00/1.05  --inst_out_proof                        true
% 1.00/1.05  
% 1.00/1.05  ------ Resolution Options
% 1.00/1.05  
% 1.00/1.05  --resolution_flag                       false
% 1.00/1.05  --res_lit_sel                           adaptive
% 1.00/1.05  --res_lit_sel_side                      none
% 1.00/1.05  --res_ordering                          kbo
% 1.00/1.05  --res_to_prop_solver                    active
% 1.00/1.05  --res_prop_simpl_new                    false
% 1.00/1.05  --res_prop_simpl_given                  true
% 1.00/1.05  --res_passive_queue_type                priority_queues
% 1.00/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.00/1.05  --res_passive_queues_freq               [15;5]
% 1.00/1.05  --res_forward_subs                      full
% 1.00/1.05  --res_backward_subs                     full
% 1.00/1.05  --res_forward_subs_resolution           true
% 1.00/1.05  --res_backward_subs_resolution          true
% 1.00/1.05  --res_orphan_elimination                true
% 1.00/1.05  --res_time_limit                        2.
% 1.00/1.05  --res_out_proof                         true
% 1.00/1.05  
% 1.00/1.05  ------ Superposition Options
% 1.00/1.05  
% 1.00/1.05  --superposition_flag                    true
% 1.00/1.05  --sup_passive_queue_type                priority_queues
% 1.00/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.00/1.05  --sup_passive_queues_freq               [8;1;4]
% 1.00/1.05  --demod_completeness_check              fast
% 1.00/1.05  --demod_use_ground                      true
% 1.00/1.05  --sup_to_prop_solver                    passive
% 1.00/1.05  --sup_prop_simpl_new                    true
% 1.00/1.05  --sup_prop_simpl_given                  true
% 1.00/1.05  --sup_fun_splitting                     false
% 1.00/1.05  --sup_smt_interval                      50000
% 1.00/1.05  
% 1.00/1.05  ------ Superposition Simplification Setup
% 1.00/1.05  
% 1.00/1.05  --sup_indices_passive                   []
% 1.00/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.00/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.00/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.00/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 1.00/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.00/1.05  --sup_full_bw                           [BwDemod]
% 1.00/1.05  --sup_immed_triv                        [TrivRules]
% 1.00/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.00/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.00/1.05  --sup_immed_bw_main                     []
% 1.00/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.00/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 1.00/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.00/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.00/1.05  
% 1.00/1.05  ------ Combination Options
% 1.00/1.05  
% 1.00/1.05  --comb_res_mult                         3
% 1.00/1.05  --comb_sup_mult                         2
% 1.00/1.05  --comb_inst_mult                        10
% 1.00/1.05  
% 1.00/1.05  ------ Debug Options
% 1.00/1.05  
% 1.00/1.05  --dbg_backtrace                         false
% 1.00/1.05  --dbg_dump_prop_clauses                 false
% 1.00/1.05  --dbg_dump_prop_clauses_file            -
% 1.00/1.05  --dbg_out_stat                          false
% 1.00/1.05  
% 1.00/1.05  
% 1.00/1.05  
% 1.00/1.05  
% 1.00/1.05  ------ Proving...
% 1.00/1.05  
% 1.00/1.05  
% 1.00/1.05  % SZS status Theorem for theBenchmark.p
% 1.00/1.05  
% 1.00/1.05  % SZS output start CNFRefutation for theBenchmark.p
% 1.00/1.05  
% 1.00/1.05  fof(f16,conjecture,(
% 1.00/1.05    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.00/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.00/1.05  
% 1.00/1.05  fof(f17,negated_conjecture,(
% 1.00/1.05    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.00/1.05    inference(negated_conjecture,[],[f16])).
% 1.00/1.05  
% 1.00/1.05  fof(f18,plain,(
% 1.00/1.05    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.00/1.05    inference(pure_predicate_removal,[],[f17])).
% 1.00/1.05  
% 1.00/1.05  fof(f42,plain,(
% 1.00/1.05    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 1.00/1.05    inference(ennf_transformation,[],[f18])).
% 1.00/1.05  
% 1.00/1.05  fof(f43,plain,(
% 1.00/1.05    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 1.00/1.05    inference(flattening,[],[f42])).
% 1.00/1.05  
% 1.00/1.05  fof(f47,plain,(
% 1.00/1.05    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(sK3))) )),
% 1.00/1.05    introduced(choice_axiom,[])).
% 1.00/1.05  
% 1.00/1.05  fof(f46,plain,(
% 1.00/1.05    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2))),
% 1.00/1.05    introduced(choice_axiom,[])).
% 1.00/1.05  
% 1.00/1.05  fof(f48,plain,(
% 1.00/1.05    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2)),
% 1.00/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f43,f47,f46])).
% 1.00/1.05  
% 1.00/1.05  fof(f73,plain,(
% 1.00/1.05    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.00/1.05    inference(cnf_transformation,[],[f48])).
% 1.00/1.05  
% 1.00/1.05  fof(f8,axiom,(
% 1.00/1.05    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.00/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.00/1.05  
% 1.00/1.05  fof(f33,plain,(
% 1.00/1.05    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.00/1.05    inference(ennf_transformation,[],[f8])).
% 1.00/1.05  
% 1.00/1.05  fof(f60,plain,(
% 1.00/1.05    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.00/1.05    inference(cnf_transformation,[],[f33])).
% 1.00/1.05  
% 1.00/1.05  fof(f71,plain,(
% 1.00/1.05    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.00/1.05    inference(cnf_transformation,[],[f48])).
% 1.00/1.05  
% 1.00/1.05  fof(f70,plain,(
% 1.00/1.05    v1_funct_1(sK2)),
% 1.00/1.05    inference(cnf_transformation,[],[f48])).
% 1.00/1.05  
% 1.00/1.05  fof(f5,axiom,(
% 1.00/1.05    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.00/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.00/1.05  
% 1.00/1.05  fof(f27,plain,(
% 1.00/1.05    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.00/1.05    inference(ennf_transformation,[],[f5])).
% 1.00/1.05  
% 1.00/1.05  fof(f28,plain,(
% 1.00/1.05    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.00/1.05    inference(flattening,[],[f27])).
% 1.00/1.05  
% 1.00/1.05  fof(f54,plain,(
% 1.00/1.05    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.00/1.05    inference(cnf_transformation,[],[f28])).
% 1.00/1.05  
% 1.00/1.05  fof(f2,axiom,(
% 1.00/1.05    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2))))),
% 1.00/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.00/1.05  
% 1.00/1.05  fof(f22,plain,(
% 1.00/1.05    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.00/1.05    inference(ennf_transformation,[],[f2])).
% 1.00/1.05  
% 1.00/1.05  fof(f51,plain,(
% 1.00/1.05    ( ! [X2,X0,X1] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.00/1.05    inference(cnf_transformation,[],[f22])).
% 1.00/1.05  
% 1.00/1.05  fof(f10,axiom,(
% 1.00/1.05    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 1.00/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.00/1.05  
% 1.00/1.05  fof(f35,plain,(
% 1.00/1.05    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.00/1.05    inference(ennf_transformation,[],[f10])).
% 1.00/1.05  
% 1.00/1.05  fof(f62,plain,(
% 1.00/1.05    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.00/1.05    inference(cnf_transformation,[],[f35])).
% 1.00/1.05  
% 1.00/1.05  fof(f74,plain,(
% 1.00/1.05    k2_relset_1(sK0,sK1,sK2) = sK1),
% 1.00/1.05    inference(cnf_transformation,[],[f48])).
% 1.00/1.05  
% 1.00/1.05  fof(f7,axiom,(
% 1.00/1.05    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 1.00/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.00/1.05  
% 1.00/1.05  fof(f31,plain,(
% 1.00/1.05    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.00/1.05    inference(ennf_transformation,[],[f7])).
% 1.00/1.05  
% 1.00/1.05  fof(f32,plain,(
% 1.00/1.05    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.00/1.05    inference(flattening,[],[f31])).
% 1.00/1.05  
% 1.00/1.05  fof(f59,plain,(
% 1.00/1.05    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.00/1.05    inference(cnf_transformation,[],[f32])).
% 1.00/1.05  
% 1.00/1.05  fof(f15,axiom,(
% 1.00/1.05    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.00/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.00/1.05  
% 1.00/1.05  fof(f69,plain,(
% 1.00/1.05    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.00/1.05    inference(cnf_transformation,[],[f15])).
% 1.00/1.05  
% 1.00/1.05  fof(f82,plain,(
% 1.00/1.05    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.00/1.05    inference(definition_unfolding,[],[f59,f69])).
% 1.00/1.05  
% 1.00/1.05  fof(f76,plain,(
% 1.00/1.05    v2_funct_1(sK2)),
% 1.00/1.05    inference(cnf_transformation,[],[f48])).
% 1.00/1.05  
% 1.00/1.05  fof(f14,axiom,(
% 1.00/1.05    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 1.00/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.00/1.05  
% 1.00/1.05  fof(f40,plain,(
% 1.00/1.05    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.00/1.05    inference(ennf_transformation,[],[f14])).
% 1.00/1.05  
% 1.00/1.05  fof(f41,plain,(
% 1.00/1.05    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.00/1.05    inference(flattening,[],[f40])).
% 1.00/1.05  
% 1.00/1.05  fof(f68,plain,(
% 1.00/1.05    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.00/1.05    inference(cnf_transformation,[],[f41])).
% 1.00/1.05  
% 1.00/1.05  fof(f72,plain,(
% 1.00/1.05    v1_funct_1(sK3)),
% 1.00/1.05    inference(cnf_transformation,[],[f48])).
% 1.00/1.05  
% 1.00/1.05  fof(f11,axiom,(
% 1.00/1.05    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.00/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.00/1.05  
% 1.00/1.05  fof(f36,plain,(
% 1.00/1.05    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.00/1.05    inference(ennf_transformation,[],[f11])).
% 1.00/1.05  
% 1.00/1.05  fof(f37,plain,(
% 1.00/1.05    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.00/1.05    inference(flattening,[],[f36])).
% 1.00/1.05  
% 1.00/1.05  fof(f45,plain,(
% 1.00/1.05    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.00/1.05    inference(nnf_transformation,[],[f37])).
% 1.00/1.05  
% 1.00/1.05  fof(f63,plain,(
% 1.00/1.05    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.00/1.05    inference(cnf_transformation,[],[f45])).
% 1.00/1.05  
% 1.00/1.05  fof(f75,plain,(
% 1.00/1.05    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.00/1.05    inference(cnf_transformation,[],[f48])).
% 1.00/1.05  
% 1.00/1.05  fof(f13,axiom,(
% 1.00/1.05    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 1.00/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.00/1.05  
% 1.00/1.05  fof(f19,plain,(
% 1.00/1.05    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.00/1.05    inference(pure_predicate_removal,[],[f13])).
% 1.00/1.05  
% 1.00/1.05  fof(f67,plain,(
% 1.00/1.05    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.00/1.05    inference(cnf_transformation,[],[f19])).
% 1.00/1.05  
% 1.00/1.05  fof(f12,axiom,(
% 1.00/1.05    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.00/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.00/1.05  
% 1.00/1.05  fof(f38,plain,(
% 1.00/1.05    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.00/1.05    inference(ennf_transformation,[],[f12])).
% 1.00/1.05  
% 1.00/1.05  fof(f39,plain,(
% 1.00/1.05    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.00/1.05    inference(flattening,[],[f38])).
% 1.00/1.05  
% 1.00/1.05  fof(f66,plain,(
% 1.00/1.05    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.00/1.05    inference(cnf_transformation,[],[f39])).
% 1.00/1.05  
% 1.00/1.05  fof(f9,axiom,(
% 1.00/1.05    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.00/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.00/1.05  
% 1.00/1.05  fof(f20,plain,(
% 1.00/1.05    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.00/1.05    inference(pure_predicate_removal,[],[f9])).
% 1.00/1.05  
% 1.00/1.05  fof(f34,plain,(
% 1.00/1.05    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.00/1.05    inference(ennf_transformation,[],[f20])).
% 1.00/1.05  
% 1.00/1.05  fof(f61,plain,(
% 1.00/1.05    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.00/1.05    inference(cnf_transformation,[],[f34])).
% 1.00/1.05  
% 1.00/1.05  fof(f1,axiom,(
% 1.00/1.05    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.00/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.00/1.05  
% 1.00/1.05  fof(f21,plain,(
% 1.00/1.05    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.00/1.05    inference(ennf_transformation,[],[f1])).
% 1.00/1.05  
% 1.00/1.05  fof(f44,plain,(
% 1.00/1.05    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.00/1.05    inference(nnf_transformation,[],[f21])).
% 1.00/1.05  
% 1.00/1.05  fof(f49,plain,(
% 1.00/1.05    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.00/1.05    inference(cnf_transformation,[],[f44])).
% 1.00/1.05  
% 1.00/1.05  fof(f6,axiom,(
% 1.00/1.05    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 1.00/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.00/1.05  
% 1.00/1.05  fof(f29,plain,(
% 1.00/1.05    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.00/1.05    inference(ennf_transformation,[],[f6])).
% 1.00/1.05  
% 1.00/1.05  fof(f30,plain,(
% 1.00/1.05    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.00/1.05    inference(flattening,[],[f29])).
% 1.00/1.05  
% 1.00/1.05  fof(f57,plain,(
% 1.00/1.05    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.00/1.05    inference(cnf_transformation,[],[f30])).
% 1.00/1.05  
% 1.00/1.05  fof(f4,axiom,(
% 1.00/1.05    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 1.00/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.00/1.05  
% 1.00/1.05  fof(f25,plain,(
% 1.00/1.05    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.00/1.05    inference(ennf_transformation,[],[f4])).
% 1.00/1.05  
% 1.00/1.05  fof(f26,plain,(
% 1.00/1.05    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.00/1.05    inference(flattening,[],[f25])).
% 1.00/1.05  
% 1.00/1.05  fof(f53,plain,(
% 1.00/1.05    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.00/1.05    inference(cnf_transformation,[],[f26])).
% 1.00/1.05  
% 1.00/1.05  fof(f81,plain,(
% 1.00/1.05    ( ! [X0,X1] : (k5_relat_1(X1,k6_partfun1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.00/1.05    inference(definition_unfolding,[],[f53,f69])).
% 1.00/1.05  
% 1.00/1.05  fof(f3,axiom,(
% 1.00/1.05    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 1.00/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.00/1.05  
% 1.00/1.05  fof(f23,plain,(
% 1.00/1.05    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.00/1.05    inference(ennf_transformation,[],[f3])).
% 1.00/1.05  
% 1.00/1.05  fof(f24,plain,(
% 1.00/1.05    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.00/1.05    inference(flattening,[],[f23])).
% 1.00/1.05  
% 1.00/1.05  fof(f52,plain,(
% 1.00/1.05    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.00/1.05    inference(cnf_transformation,[],[f24])).
% 1.00/1.05  
% 1.00/1.05  fof(f80,plain,(
% 1.00/1.05    ( ! [X0,X1] : (k5_relat_1(k6_partfun1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.00/1.05    inference(definition_unfolding,[],[f52,f69])).
% 1.00/1.05  
% 1.00/1.05  fof(f79,plain,(
% 1.00/1.05    k2_funct_1(sK2) != sK3),
% 1.00/1.05    inference(cnf_transformation,[],[f48])).
% 1.00/1.05  
% 1.00/1.05  cnf(c_26,negated_conjecture,
% 1.00/1.05      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 1.00/1.05      inference(cnf_transformation,[],[f73]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_643,negated_conjecture,
% 1.00/1.05      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 1.00/1.05      inference(subtyping,[status(esa)],[c_26]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_1092,plain,
% 1.00/1.05      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 1.00/1.05      inference(predicate_to_equality,[status(thm)],[c_643]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_11,plain,
% 1.00/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.00/1.05      | v1_relat_1(X0) ),
% 1.00/1.05      inference(cnf_transformation,[],[f60]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_653,plain,
% 1.00/1.05      ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
% 1.00/1.05      | v1_relat_1(X0_49) ),
% 1.00/1.05      inference(subtyping,[status(esa)],[c_11]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_1086,plain,
% 1.00/1.05      ( m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
% 1.00/1.05      | v1_relat_1(X0_49) = iProver_top ),
% 1.00/1.05      inference(predicate_to_equality,[status(thm)],[c_653]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_1421,plain,
% 1.00/1.05      ( v1_relat_1(sK3) = iProver_top ),
% 1.00/1.05      inference(superposition,[status(thm)],[c_1092,c_1086]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_28,negated_conjecture,
% 1.00/1.05      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 1.00/1.05      inference(cnf_transformation,[],[f71]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_641,negated_conjecture,
% 1.00/1.05      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 1.00/1.05      inference(subtyping,[status(esa)],[c_28]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_1094,plain,
% 1.00/1.05      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 1.00/1.05      inference(predicate_to_equality,[status(thm)],[c_641]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_1422,plain,
% 1.00/1.05      ( v1_relat_1(sK2) = iProver_top ),
% 1.00/1.05      inference(superposition,[status(thm)],[c_1094,c_1086]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_29,negated_conjecture,
% 1.00/1.05      ( v1_funct_1(sK2) ),
% 1.00/1.05      inference(cnf_transformation,[],[f70]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_640,negated_conjecture,
% 1.00/1.05      ( v1_funct_1(sK2) ),
% 1.00/1.05      inference(subtyping,[status(esa)],[c_29]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_1095,plain,
% 1.00/1.05      ( v1_funct_1(sK2) = iProver_top ),
% 1.00/1.05      inference(predicate_to_equality,[status(thm)],[c_640]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_6,plain,
% 1.00/1.05      ( ~ v1_funct_1(X0)
% 1.00/1.05      | ~ v1_relat_1(X0)
% 1.00/1.05      | v1_relat_1(k2_funct_1(X0)) ),
% 1.00/1.05      inference(cnf_transformation,[],[f54]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_654,plain,
% 1.00/1.05      ( ~ v1_funct_1(X0_49)
% 1.00/1.05      | ~ v1_relat_1(X0_49)
% 1.00/1.05      | v1_relat_1(k2_funct_1(X0_49)) ),
% 1.00/1.05      inference(subtyping,[status(esa)],[c_6]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_1085,plain,
% 1.00/1.05      ( v1_funct_1(X0_49) != iProver_top
% 1.00/1.05      | v1_relat_1(X0_49) != iProver_top
% 1.00/1.05      | v1_relat_1(k2_funct_1(X0_49)) = iProver_top ),
% 1.00/1.05      inference(predicate_to_equality,[status(thm)],[c_654]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_2,plain,
% 1.00/1.05      ( ~ v1_relat_1(X0)
% 1.00/1.05      | ~ v1_relat_1(X1)
% 1.00/1.05      | ~ v1_relat_1(X2)
% 1.00/1.05      | k5_relat_1(k5_relat_1(X2,X0),X1) = k5_relat_1(X2,k5_relat_1(X0,X1)) ),
% 1.00/1.05      inference(cnf_transformation,[],[f51]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_658,plain,
% 1.00/1.05      ( ~ v1_relat_1(X0_49)
% 1.00/1.05      | ~ v1_relat_1(X1_49)
% 1.00/1.05      | ~ v1_relat_1(X2_49)
% 1.00/1.05      | k5_relat_1(k5_relat_1(X2_49,X0_49),X1_49) = k5_relat_1(X2_49,k5_relat_1(X0_49,X1_49)) ),
% 1.00/1.05      inference(subtyping,[status(esa)],[c_2]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_1081,plain,
% 1.00/1.05      ( k5_relat_1(k5_relat_1(X0_49,X1_49),X2_49) = k5_relat_1(X0_49,k5_relat_1(X1_49,X2_49))
% 1.00/1.05      | v1_relat_1(X1_49) != iProver_top
% 1.00/1.05      | v1_relat_1(X2_49) != iProver_top
% 1.00/1.05      | v1_relat_1(X0_49) != iProver_top ),
% 1.00/1.05      inference(predicate_to_equality,[status(thm)],[c_658]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_2143,plain,
% 1.00/1.05      ( k5_relat_1(k2_funct_1(X0_49),k5_relat_1(X1_49,X2_49)) = k5_relat_1(k5_relat_1(k2_funct_1(X0_49),X1_49),X2_49)
% 1.00/1.05      | v1_funct_1(X0_49) != iProver_top
% 1.00/1.05      | v1_relat_1(X0_49) != iProver_top
% 1.00/1.05      | v1_relat_1(X1_49) != iProver_top
% 1.00/1.05      | v1_relat_1(X2_49) != iProver_top ),
% 1.00/1.05      inference(superposition,[status(thm)],[c_1085,c_1081]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_4564,plain,
% 1.00/1.05      ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0_49),X1_49) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0_49,X1_49))
% 1.00/1.05      | v1_relat_1(X0_49) != iProver_top
% 1.00/1.05      | v1_relat_1(X1_49) != iProver_top
% 1.00/1.05      | v1_relat_1(sK2) != iProver_top ),
% 1.00/1.05      inference(superposition,[status(thm)],[c_1095,c_2143]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_31,plain,
% 1.00/1.05      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 1.00/1.05      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_1267,plain,
% 1.00/1.05      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 1.00/1.05      | v1_relat_1(sK2) ),
% 1.00/1.05      inference(instantiation,[status(thm)],[c_653]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_1268,plain,
% 1.00/1.05      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 1.00/1.05      | v1_relat_1(sK2) = iProver_top ),
% 1.00/1.05      inference(predicate_to_equality,[status(thm)],[c_1267]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_4705,plain,
% 1.00/1.05      ( v1_relat_1(X1_49) != iProver_top
% 1.00/1.05      | v1_relat_1(X0_49) != iProver_top
% 1.00/1.05      | k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0_49),X1_49) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0_49,X1_49)) ),
% 1.00/1.05      inference(global_propositional_subsumption,
% 1.00/1.05                [status(thm)],
% 1.00/1.05                [c_4564,c_31,c_1268]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_4706,plain,
% 1.00/1.05      ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0_49),X1_49) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0_49,X1_49))
% 1.00/1.05      | v1_relat_1(X0_49) != iProver_top
% 1.00/1.05      | v1_relat_1(X1_49) != iProver_top ),
% 1.00/1.05      inference(renaming,[status(thm)],[c_4705]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_4712,plain,
% 1.00/1.05      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0_49)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),X0_49)
% 1.00/1.05      | v1_relat_1(X0_49) != iProver_top ),
% 1.00/1.05      inference(superposition,[status(thm)],[c_1422,c_4706]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_13,plain,
% 1.00/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.00/1.05      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 1.00/1.05      inference(cnf_transformation,[],[f62]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_652,plain,
% 1.00/1.05      ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
% 1.00/1.05      | k2_relset_1(X0_50,X1_50,X0_49) = k2_relat_1(X0_49) ),
% 1.00/1.05      inference(subtyping,[status(esa)],[c_13]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_1087,plain,
% 1.00/1.05      ( k2_relset_1(X0_50,X1_50,X0_49) = k2_relat_1(X0_49)
% 1.00/1.05      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top ),
% 1.00/1.05      inference(predicate_to_equality,[status(thm)],[c_652]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_2043,plain,
% 1.00/1.05      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 1.00/1.05      inference(superposition,[status(thm)],[c_1094,c_1087]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_25,negated_conjecture,
% 1.00/1.05      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 1.00/1.05      inference(cnf_transformation,[],[f74]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_644,negated_conjecture,
% 1.00/1.05      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 1.00/1.05      inference(subtyping,[status(esa)],[c_25]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_2048,plain,
% 1.00/1.05      ( k2_relat_1(sK2) = sK1 ),
% 1.00/1.05      inference(light_normalisation,[status(thm)],[c_2043,c_644]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_9,plain,
% 1.00/1.05      ( ~ v2_funct_1(X0)
% 1.00/1.05      | ~ v1_funct_1(X0)
% 1.00/1.05      | ~ v1_relat_1(X0)
% 1.00/1.05      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
% 1.00/1.05      inference(cnf_transformation,[],[f82]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_23,negated_conjecture,
% 1.00/1.05      ( v2_funct_1(sK2) ),
% 1.00/1.05      inference(cnf_transformation,[],[f76]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_395,plain,
% 1.00/1.05      ( ~ v1_funct_1(X0)
% 1.00/1.05      | ~ v1_relat_1(X0)
% 1.00/1.05      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
% 1.00/1.05      | sK2 != X0 ),
% 1.00/1.05      inference(resolution_lifted,[status(thm)],[c_9,c_23]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_396,plain,
% 1.00/1.05      ( ~ v1_funct_1(sK2)
% 1.00/1.05      | ~ v1_relat_1(sK2)
% 1.00/1.05      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 1.00/1.05      inference(unflattening,[status(thm)],[c_395]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_398,plain,
% 1.00/1.05      ( ~ v1_relat_1(sK2)
% 1.00/1.05      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 1.00/1.05      inference(global_propositional_subsumption,
% 1.00/1.05                [status(thm)],
% 1.00/1.05                [c_396,c_29]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_636,plain,
% 1.00/1.05      ( ~ v1_relat_1(sK2)
% 1.00/1.05      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 1.00/1.05      inference(subtyping,[status(esa)],[c_398]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_1099,plain,
% 1.00/1.05      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
% 1.00/1.05      | v1_relat_1(sK2) != iProver_top ),
% 1.00/1.05      inference(predicate_to_equality,[status(thm)],[c_636]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_1706,plain,
% 1.00/1.05      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 1.00/1.05      inference(global_propositional_subsumption,
% 1.00/1.05                [status(thm)],
% 1.00/1.05                [c_1099,c_28,c_636,c_1267]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_2055,plain,
% 1.00/1.05      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
% 1.00/1.05      inference(demodulation,[status(thm)],[c_2048,c_1706]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_4734,plain,
% 1.00/1.05      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0_49)) = k5_relat_1(k6_partfun1(sK1),X0_49)
% 1.00/1.05      | v1_relat_1(X0_49) != iProver_top ),
% 1.00/1.05      inference(light_normalisation,[status(thm)],[c_4712,c_2055]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_4800,plain,
% 1.00/1.05      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
% 1.00/1.05      inference(superposition,[status(thm)],[c_1421,c_4734]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_19,plain,
% 1.00/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.00/1.05      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 1.00/1.05      | ~ v1_funct_1(X0)
% 1.00/1.05      | ~ v1_funct_1(X3)
% 1.00/1.05      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 1.00/1.05      inference(cnf_transformation,[],[f68]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_648,plain,
% 1.00/1.05      ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
% 1.00/1.05      | ~ m1_subset_1(X1_49,k1_zfmisc_1(k2_zfmisc_1(X2_50,X3_50)))
% 1.00/1.05      | ~ v1_funct_1(X0_49)
% 1.00/1.05      | ~ v1_funct_1(X1_49)
% 1.00/1.05      | k1_partfun1(X2_50,X3_50,X0_50,X1_50,X1_49,X0_49) = k5_relat_1(X1_49,X0_49) ),
% 1.00/1.05      inference(subtyping,[status(esa)],[c_19]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_1091,plain,
% 1.00/1.05      ( k1_partfun1(X0_50,X1_50,X2_50,X3_50,X0_49,X1_49) = k5_relat_1(X0_49,X1_49)
% 1.00/1.05      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
% 1.00/1.05      | m1_subset_1(X1_49,k1_zfmisc_1(k2_zfmisc_1(X2_50,X3_50))) != iProver_top
% 1.00/1.05      | v1_funct_1(X1_49) != iProver_top
% 1.00/1.05      | v1_funct_1(X0_49) != iProver_top ),
% 1.00/1.05      inference(predicate_to_equality,[status(thm)],[c_648]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_3089,plain,
% 1.00/1.05      ( k1_partfun1(X0_50,X1_50,sK1,sK0,X0_49,sK3) = k5_relat_1(X0_49,sK3)
% 1.00/1.05      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
% 1.00/1.05      | v1_funct_1(X0_49) != iProver_top
% 1.00/1.05      | v1_funct_1(sK3) != iProver_top ),
% 1.00/1.05      inference(superposition,[status(thm)],[c_1092,c_1091]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_27,negated_conjecture,
% 1.00/1.05      ( v1_funct_1(sK3) ),
% 1.00/1.05      inference(cnf_transformation,[],[f72]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_32,plain,
% 1.00/1.05      ( v1_funct_1(sK3) = iProver_top ),
% 1.00/1.05      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_3689,plain,
% 1.00/1.05      ( v1_funct_1(X0_49) != iProver_top
% 1.00/1.05      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
% 1.00/1.05      | k1_partfun1(X0_50,X1_50,sK1,sK0,X0_49,sK3) = k5_relat_1(X0_49,sK3) ),
% 1.00/1.05      inference(global_propositional_subsumption,
% 1.00/1.05                [status(thm)],
% 1.00/1.05                [c_3089,c_32]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_3690,plain,
% 1.00/1.05      ( k1_partfun1(X0_50,X1_50,sK1,sK0,X0_49,sK3) = k5_relat_1(X0_49,sK3)
% 1.00/1.05      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
% 1.00/1.05      | v1_funct_1(X0_49) != iProver_top ),
% 1.00/1.05      inference(renaming,[status(thm)],[c_3689]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_3699,plain,
% 1.00/1.05      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 1.00/1.05      | v1_funct_1(sK2) != iProver_top ),
% 1.00/1.05      inference(superposition,[status(thm)],[c_1094,c_3690]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_15,plain,
% 1.00/1.05      ( ~ r2_relset_1(X0,X1,X2,X3)
% 1.00/1.05      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.00/1.05      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.00/1.05      | X3 = X2 ),
% 1.00/1.05      inference(cnf_transformation,[],[f63]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_24,negated_conjecture,
% 1.00/1.05      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 1.00/1.05      inference(cnf_transformation,[],[f75]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_364,plain,
% 1.00/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.00/1.05      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.00/1.05      | X3 = X0
% 1.00/1.05      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 1.00/1.05      | k6_partfun1(sK0) != X3
% 1.00/1.05      | sK0 != X2
% 1.00/1.05      | sK0 != X1 ),
% 1.00/1.05      inference(resolution_lifted,[status(thm)],[c_15,c_24]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_365,plain,
% 1.00/1.05      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 1.00/1.05      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 1.00/1.05      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 1.00/1.05      inference(unflattening,[status(thm)],[c_364]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_18,plain,
% 1.00/1.05      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 1.00/1.05      inference(cnf_transformation,[],[f67]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_40,plain,
% 1.00/1.05      ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 1.00/1.05      inference(instantiation,[status(thm)],[c_18]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_367,plain,
% 1.00/1.05      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 1.00/1.05      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 1.00/1.05      inference(global_propositional_subsumption,
% 1.00/1.05                [status(thm)],
% 1.00/1.05                [c_365,c_40]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_638,plain,
% 1.00/1.05      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 1.00/1.05      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 1.00/1.05      inference(subtyping,[status(esa)],[c_367]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_1097,plain,
% 1.00/1.05      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 1.00/1.05      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 1.00/1.05      inference(predicate_to_equality,[status(thm)],[c_638]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_16,plain,
% 1.00/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.00/1.05      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 1.00/1.05      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 1.00/1.05      | ~ v1_funct_1(X0)
% 1.00/1.05      | ~ v1_funct_1(X3) ),
% 1.00/1.05      inference(cnf_transformation,[],[f66]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_651,plain,
% 1.00/1.05      ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
% 1.00/1.05      | ~ m1_subset_1(X1_49,k1_zfmisc_1(k2_zfmisc_1(X2_50,X3_50)))
% 1.00/1.05      | m1_subset_1(k1_partfun1(X2_50,X3_50,X0_50,X1_50,X1_49,X0_49),k1_zfmisc_1(k2_zfmisc_1(X2_50,X1_50)))
% 1.00/1.05      | ~ v1_funct_1(X0_49)
% 1.00/1.05      | ~ v1_funct_1(X1_49) ),
% 1.00/1.05      inference(subtyping,[status(esa)],[c_16]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_1354,plain,
% 1.00/1.05      ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
% 1.00/1.05      | m1_subset_1(k1_partfun1(X0_50,X1_50,sK1,sK0,X0_49,sK3),k1_zfmisc_1(k2_zfmisc_1(X0_50,sK0)))
% 1.00/1.05      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 1.00/1.05      | ~ v1_funct_1(X0_49)
% 1.00/1.05      | ~ v1_funct_1(sK3) ),
% 1.00/1.05      inference(instantiation,[status(thm)],[c_651]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_1519,plain,
% 1.00/1.05      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 1.00/1.05      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 1.00/1.05      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 1.00/1.05      | ~ v1_funct_1(sK3)
% 1.00/1.05      | ~ v1_funct_1(sK2) ),
% 1.00/1.05      inference(instantiation,[status(thm)],[c_1354]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_1710,plain,
% 1.00/1.05      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 1.00/1.05      inference(global_propositional_subsumption,
% 1.00/1.05                [status(thm)],
% 1.00/1.05                [c_1097,c_29,c_28,c_27,c_26,c_638,c_1519]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_3720,plain,
% 1.00/1.05      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 1.00/1.05      | v1_funct_1(sK2) != iProver_top ),
% 1.00/1.05      inference(light_normalisation,[status(thm)],[c_3699,c_1710]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_30,plain,
% 1.00/1.05      ( v1_funct_1(sK2) = iProver_top ),
% 1.00/1.05      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_4309,plain,
% 1.00/1.05      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 1.00/1.05      inference(global_propositional_subsumption,
% 1.00/1.05                [status(thm)],
% 1.00/1.05                [c_3720,c_30]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_12,plain,
% 1.00/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.00/1.05      | v4_relat_1(X0,X1) ),
% 1.00/1.05      inference(cnf_transformation,[],[f61]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_1,plain,
% 1.00/1.05      ( r1_tarski(k1_relat_1(X0),X1)
% 1.00/1.05      | ~ v4_relat_1(X0,X1)
% 1.00/1.05      | ~ v1_relat_1(X0) ),
% 1.00/1.05      inference(cnf_transformation,[],[f49]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_300,plain,
% 1.00/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.00/1.05      | r1_tarski(k1_relat_1(X0),X1)
% 1.00/1.05      | ~ v1_relat_1(X0) ),
% 1.00/1.05      inference(resolution,[status(thm)],[c_12,c_1]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_304,plain,
% 1.00/1.05      ( r1_tarski(k1_relat_1(X0),X1)
% 1.00/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 1.00/1.05      inference(global_propositional_subsumption,
% 1.00/1.05                [status(thm)],
% 1.00/1.05                [c_300,c_11]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_305,plain,
% 1.00/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.00/1.05      | r1_tarski(k1_relat_1(X0),X1) ),
% 1.00/1.05      inference(renaming,[status(thm)],[c_304]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_639,plain,
% 1.00/1.05      ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
% 1.00/1.05      | r1_tarski(k1_relat_1(X0_49),X0_50) ),
% 1.00/1.05      inference(subtyping,[status(esa)],[c_305]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_1096,plain,
% 1.00/1.05      ( m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
% 1.00/1.05      | r1_tarski(k1_relat_1(X0_49),X0_50) = iProver_top ),
% 1.00/1.05      inference(predicate_to_equality,[status(thm)],[c_639]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_4317,plain,
% 1.00/1.05      ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
% 1.00/1.05      inference(superposition,[status(thm)],[c_1094,c_1096]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_7,plain,
% 1.00/1.05      ( ~ v2_funct_1(X0)
% 1.00/1.05      | ~ v1_funct_1(X0)
% 1.00/1.05      | ~ v1_relat_1(X0)
% 1.00/1.05      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 1.00/1.05      inference(cnf_transformation,[],[f57]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_423,plain,
% 1.00/1.05      ( ~ v1_funct_1(X0)
% 1.00/1.05      | ~ v1_relat_1(X0)
% 1.00/1.05      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 1.00/1.05      | sK2 != X0 ),
% 1.00/1.05      inference(resolution_lifted,[status(thm)],[c_7,c_23]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_424,plain,
% 1.00/1.05      ( ~ v1_funct_1(sK2)
% 1.00/1.05      | ~ v1_relat_1(sK2)
% 1.00/1.05      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 1.00/1.05      inference(unflattening,[status(thm)],[c_423]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_426,plain,
% 1.00/1.05      ( ~ v1_relat_1(sK2)
% 1.00/1.05      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 1.00/1.05      inference(global_propositional_subsumption,
% 1.00/1.05                [status(thm)],
% 1.00/1.05                [c_424,c_29]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_634,plain,
% 1.00/1.05      ( ~ v1_relat_1(sK2)
% 1.00/1.05      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 1.00/1.05      inference(subtyping,[status(esa)],[c_426]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_1101,plain,
% 1.00/1.05      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 1.00/1.05      | v1_relat_1(sK2) != iProver_top ),
% 1.00/1.05      inference(predicate_to_equality,[status(thm)],[c_634]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_1651,plain,
% 1.00/1.05      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 1.00/1.05      inference(global_propositional_subsumption,
% 1.00/1.05                [status(thm)],
% 1.00/1.05                [c_1101,c_28,c_634,c_1267]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_4,plain,
% 1.00/1.05      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 1.00/1.05      | ~ v1_relat_1(X0)
% 1.00/1.05      | k5_relat_1(X0,k6_partfun1(X1)) = X0 ),
% 1.00/1.05      inference(cnf_transformation,[],[f81]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_656,plain,
% 1.00/1.05      ( ~ r1_tarski(k2_relat_1(X0_49),X0_50)
% 1.00/1.05      | ~ v1_relat_1(X0_49)
% 1.00/1.05      | k5_relat_1(X0_49,k6_partfun1(X0_50)) = X0_49 ),
% 1.00/1.05      inference(subtyping,[status(esa)],[c_4]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_1083,plain,
% 1.00/1.05      ( k5_relat_1(X0_49,k6_partfun1(X0_50)) = X0_49
% 1.00/1.05      | r1_tarski(k2_relat_1(X0_49),X0_50) != iProver_top
% 1.00/1.05      | v1_relat_1(X0_49) != iProver_top ),
% 1.00/1.05      inference(predicate_to_equality,[status(thm)],[c_656]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_1733,plain,
% 1.00/1.05      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0_50)) = k2_funct_1(sK2)
% 1.00/1.05      | r1_tarski(k1_relat_1(sK2),X0_50) != iProver_top
% 1.00/1.05      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 1.00/1.05      inference(superposition,[status(thm)],[c_1651,c_1083]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_709,plain,
% 1.00/1.05      ( v1_funct_1(X0_49) != iProver_top
% 1.00/1.05      | v1_relat_1(X0_49) != iProver_top
% 1.00/1.05      | v1_relat_1(k2_funct_1(X0_49)) = iProver_top ),
% 1.00/1.05      inference(predicate_to_equality,[status(thm)],[c_654]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_711,plain,
% 1.00/1.05      ( v1_funct_1(sK2) != iProver_top
% 1.00/1.05      | v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 1.00/1.05      | v1_relat_1(sK2) != iProver_top ),
% 1.00/1.05      inference(instantiation,[status(thm)],[c_709]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_2413,plain,
% 1.00/1.05      ( r1_tarski(k1_relat_1(sK2),X0_50) != iProver_top
% 1.00/1.05      | k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0_50)) = k2_funct_1(sK2) ),
% 1.00/1.05      inference(global_propositional_subsumption,
% 1.00/1.05                [status(thm)],
% 1.00/1.05                [c_1733,c_30,c_31,c_711,c_1268]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_2414,plain,
% 1.00/1.05      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0_50)) = k2_funct_1(sK2)
% 1.00/1.05      | r1_tarski(k1_relat_1(sK2),X0_50) != iProver_top ),
% 1.00/1.05      inference(renaming,[status(thm)],[c_2413]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_4366,plain,
% 1.00/1.05      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k2_funct_1(sK2) ),
% 1.00/1.05      inference(superposition,[status(thm)],[c_4317,c_2414]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_4316,plain,
% 1.00/1.05      ( r1_tarski(k1_relat_1(sK3),sK1) = iProver_top ),
% 1.00/1.05      inference(superposition,[status(thm)],[c_1092,c_1096]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_3,plain,
% 1.00/1.05      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 1.00/1.05      | ~ v1_relat_1(X0)
% 1.00/1.05      | k5_relat_1(k6_partfun1(X1),X0) = X0 ),
% 1.00/1.05      inference(cnf_transformation,[],[f80]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_657,plain,
% 1.00/1.05      ( ~ r1_tarski(k1_relat_1(X0_49),X0_50)
% 1.00/1.05      | ~ v1_relat_1(X0_49)
% 1.00/1.05      | k5_relat_1(k6_partfun1(X0_50),X0_49) = X0_49 ),
% 1.00/1.05      inference(subtyping,[status(esa)],[c_3]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_1082,plain,
% 1.00/1.05      ( k5_relat_1(k6_partfun1(X0_50),X0_49) = X0_49
% 1.00/1.05      | r1_tarski(k1_relat_1(X0_49),X0_50) != iProver_top
% 1.00/1.05      | v1_relat_1(X0_49) != iProver_top ),
% 1.00/1.05      inference(predicate_to_equality,[status(thm)],[c_657]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_4361,plain,
% 1.00/1.05      ( k5_relat_1(k6_partfun1(sK1),sK3) = sK3
% 1.00/1.05      | v1_relat_1(sK3) != iProver_top ),
% 1.00/1.05      inference(superposition,[status(thm)],[c_4316,c_1082]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_1264,plain,
% 1.00/1.05      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 1.00/1.05      | v1_relat_1(sK3) ),
% 1.00/1.05      inference(instantiation,[status(thm)],[c_653]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_1275,plain,
% 1.00/1.05      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 1.00/1.05      | r1_tarski(k1_relat_1(sK3),sK1) ),
% 1.00/1.05      inference(instantiation,[status(thm)],[c_639]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_1370,plain,
% 1.00/1.05      ( ~ r1_tarski(k1_relat_1(sK3),X0_50)
% 1.00/1.05      | ~ v1_relat_1(sK3)
% 1.00/1.05      | k5_relat_1(k6_partfun1(X0_50),sK3) = sK3 ),
% 1.00/1.05      inference(instantiation,[status(thm)],[c_657]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_1549,plain,
% 1.00/1.05      ( ~ r1_tarski(k1_relat_1(sK3),sK1)
% 1.00/1.05      | ~ v1_relat_1(sK3)
% 1.00/1.05      | k5_relat_1(k6_partfun1(sK1),sK3) = sK3 ),
% 1.00/1.05      inference(instantiation,[status(thm)],[c_1370]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_4387,plain,
% 1.00/1.05      ( k5_relat_1(k6_partfun1(sK1),sK3) = sK3 ),
% 1.00/1.05      inference(global_propositional_subsumption,
% 1.00/1.05                [status(thm)],
% 1.00/1.05                [c_4361,c_26,c_1264,c_1275,c_1549]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_4805,plain,
% 1.00/1.05      ( k2_funct_1(sK2) = sK3 ),
% 1.00/1.05      inference(light_normalisation,
% 1.00/1.05                [status(thm)],
% 1.00/1.05                [c_4800,c_4309,c_4366,c_4387]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_20,negated_conjecture,
% 1.00/1.05      ( k2_funct_1(sK2) != sK3 ),
% 1.00/1.05      inference(cnf_transformation,[],[f79]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(c_647,negated_conjecture,
% 1.00/1.05      ( k2_funct_1(sK2) != sK3 ),
% 1.00/1.05      inference(subtyping,[status(esa)],[c_20]) ).
% 1.00/1.05  
% 1.00/1.05  cnf(contradiction,plain,
% 1.00/1.05      ( $false ),
% 1.00/1.05      inference(minisat,[status(thm)],[c_4805,c_647]) ).
% 1.00/1.05  
% 1.00/1.05  
% 1.00/1.05  % SZS output end CNFRefutation for theBenchmark.p
% 1.00/1.05  
% 1.00/1.05  ------                               Statistics
% 1.00/1.05  
% 1.00/1.05  ------ General
% 1.00/1.05  
% 1.00/1.05  abstr_ref_over_cycles:                  0
% 1.00/1.05  abstr_ref_under_cycles:                 0
% 1.00/1.05  gc_basic_clause_elim:                   0
% 1.00/1.05  forced_gc_time:                         0
% 1.00/1.05  parsing_time:                           0.013
% 1.00/1.05  unif_index_cands_time:                  0.
% 1.00/1.05  unif_index_add_time:                    0.
% 1.00/1.05  orderings_time:                         0.
% 1.00/1.05  out_proof_time:                         0.014
% 1.00/1.05  total_time:                             0.382
% 1.00/1.05  num_of_symbols:                         56
% 1.00/1.05  num_of_terms:                           5089
% 1.00/1.05  
% 1.00/1.05  ------ Preprocessing
% 1.00/1.05  
% 1.00/1.05  num_of_splits:                          0
% 1.00/1.05  num_of_split_atoms:                     0
% 1.00/1.05  num_of_reused_defs:                     0
% 1.00/1.05  num_eq_ax_congr_red:                    5
% 1.00/1.05  num_of_sem_filtered_clauses:            1
% 1.00/1.05  num_of_subtypes:                        4
% 1.00/1.05  monotx_restored_types:                  1
% 1.00/1.05  sat_num_of_epr_types:                   0
% 1.00/1.05  sat_num_of_non_cyclic_types:            0
% 1.00/1.05  sat_guarded_non_collapsed_types:        0
% 1.00/1.05  num_pure_diseq_elim:                    0
% 1.00/1.05  simp_replaced_by:                       0
% 1.00/1.05  res_preprocessed:                       144
% 1.00/1.05  prep_upred:                             0
% 1.00/1.05  prep_unflattend:                        14
% 1.00/1.05  smt_new_axioms:                         0
% 1.00/1.05  pred_elim_cands:                        4
% 1.00/1.05  pred_elim:                              3
% 1.00/1.05  pred_elim_cl:                           5
% 1.00/1.05  pred_elim_cycles:                       6
% 1.00/1.05  merged_defs:                            0
% 1.00/1.05  merged_defs_ncl:                        0
% 1.00/1.05  bin_hyper_res:                          0
% 1.00/1.05  prep_cycles:                            4
% 1.00/1.05  pred_elim_time:                         0.012
% 1.00/1.05  splitting_time:                         0.
% 1.00/1.05  sem_filter_time:                        0.
% 1.00/1.05  monotx_time:                            0.001
% 1.00/1.05  subtype_inf_time:                       0.002
% 1.00/1.05  
% 1.00/1.05  ------ Problem properties
% 1.00/1.05  
% 1.00/1.05  clauses:                                25
% 1.00/1.05  conjectures:                            8
% 1.00/1.05  epr:                                    4
% 1.00/1.05  horn:                                   25
% 1.00/1.05  ground:                                 13
% 1.00/1.05  unary:                                  9
% 1.00/1.05  binary:                                 8
% 1.00/1.05  lits:                                   56
% 1.00/1.05  lits_eq:                                14
% 1.00/1.05  fd_pure:                                0
% 1.00/1.05  fd_pseudo:                              0
% 1.00/1.05  fd_cond:                                0
% 1.00/1.05  fd_pseudo_cond:                         0
% 1.00/1.05  ac_symbols:                             0
% 1.00/1.05  
% 1.00/1.05  ------ Propositional Solver
% 1.00/1.05  
% 1.00/1.05  prop_solver_calls:                      28
% 1.00/1.05  prop_fast_solver_calls:                 914
% 1.00/1.05  smt_solver_calls:                       0
% 1.00/1.05  smt_fast_solver_calls:                  0
% 1.00/1.05  prop_num_of_clauses:                    2121
% 1.00/1.05  prop_preprocess_simplified:             5720
% 1.00/1.05  prop_fo_subsumed:                       29
% 1.00/1.05  prop_solver_time:                       0.
% 1.00/1.05  smt_solver_time:                        0.
% 1.00/1.05  smt_fast_solver_time:                   0.
% 1.00/1.05  prop_fast_solver_time:                  0.
% 1.00/1.05  prop_unsat_core_time:                   0.
% 1.00/1.05  
% 1.00/1.05  ------ QBF
% 1.00/1.05  
% 1.00/1.05  qbf_q_res:                              0
% 1.00/1.05  qbf_num_tautologies:                    0
% 1.00/1.05  qbf_prep_cycles:                        0
% 1.00/1.05  
% 1.00/1.05  ------ BMC1
% 1.00/1.05  
% 1.00/1.05  bmc1_current_bound:                     -1
% 1.00/1.05  bmc1_last_solved_bound:                 -1
% 1.00/1.05  bmc1_unsat_core_size:                   -1
% 1.00/1.05  bmc1_unsat_core_parents_size:           -1
% 1.00/1.05  bmc1_merge_next_fun:                    0
% 1.00/1.05  bmc1_unsat_core_clauses_time:           0.
% 1.00/1.05  
% 1.00/1.05  ------ Instantiation
% 1.00/1.05  
% 1.00/1.05  inst_num_of_clauses:                    697
% 1.00/1.05  inst_num_in_passive:                    76
% 1.00/1.05  inst_num_in_active:                     307
% 1.00/1.05  inst_num_in_unprocessed:                314
% 1.00/1.05  inst_num_of_loops:                      350
% 1.00/1.05  inst_num_of_learning_restarts:          0
% 1.00/1.05  inst_num_moves_active_passive:          41
% 1.00/1.05  inst_lit_activity:                      0
% 1.00/1.05  inst_lit_activity_moves:                1
% 1.00/1.05  inst_num_tautologies:                   0
% 1.00/1.05  inst_num_prop_implied:                  0
% 1.00/1.05  inst_num_existing_simplified:           0
% 1.00/1.05  inst_num_eq_res_simplified:             0
% 1.00/1.05  inst_num_child_elim:                    0
% 1.00/1.05  inst_num_of_dismatching_blockings:      109
% 1.00/1.05  inst_num_of_non_proper_insts:           304
% 1.00/1.05  inst_num_of_duplicates:                 0
% 1.00/1.05  inst_inst_num_from_inst_to_res:         0
% 1.00/1.05  inst_dismatching_checking_time:         0.
% 1.00/1.05  
% 1.00/1.05  ------ Resolution
% 1.00/1.05  
% 1.00/1.05  res_num_of_clauses:                     0
% 1.00/1.05  res_num_in_passive:                     0
% 1.00/1.05  res_num_in_active:                      0
% 1.00/1.05  res_num_of_loops:                       148
% 1.00/1.05  res_forward_subset_subsumed:            18
% 1.00/1.05  res_backward_subset_subsumed:           0
% 1.00/1.05  res_forward_subsumed:                   0
% 1.00/1.05  res_backward_subsumed:                  0
% 1.00/1.05  res_forward_subsumption_resolution:     0
% 1.00/1.05  res_backward_subsumption_resolution:    0
% 1.00/1.05  res_clause_to_clause_subsumption:       219
% 1.00/1.05  res_orphan_elimination:                 0
% 1.00/1.05  res_tautology_del:                      14
% 1.00/1.05  res_num_eq_res_simplified:              0
% 1.00/1.05  res_num_sel_changes:                    0
% 1.00/1.05  res_moves_from_active_to_pass:          0
% 1.00/1.05  
% 1.00/1.05  ------ Superposition
% 1.00/1.05  
% 1.00/1.05  sup_time_total:                         0.
% 1.00/1.05  sup_time_generating:                    0.
% 1.00/1.05  sup_time_sim_full:                      0.
% 1.00/1.05  sup_time_sim_immed:                     0.
% 1.00/1.05  
% 1.00/1.05  sup_num_of_clauses:                     105
% 1.00/1.05  sup_num_in_active:                      65
% 1.00/1.05  sup_num_in_passive:                     40
% 1.00/1.05  sup_num_of_loops:                       68
% 1.00/1.05  sup_fw_superposition:                   66
% 1.00/1.05  sup_bw_superposition:                   19
% 1.00/1.05  sup_immediate_simplified:               7
% 1.00/1.05  sup_given_eliminated:                   1
% 1.00/1.05  comparisons_done:                       0
% 1.00/1.05  comparisons_avoided:                    0
% 1.00/1.05  
% 1.00/1.05  ------ Simplifications
% 1.00/1.05  
% 1.00/1.05  
% 1.00/1.05  sim_fw_subset_subsumed:                 1
% 1.00/1.05  sim_bw_subset_subsumed:                 0
% 1.00/1.05  sim_fw_subsumed:                        1
% 1.00/1.05  sim_bw_subsumed:                        0
% 1.00/1.05  sim_fw_subsumption_res:                 0
% 1.00/1.05  sim_bw_subsumption_res:                 0
% 1.00/1.05  sim_tautology_del:                      0
% 1.00/1.05  sim_eq_tautology_del:                   0
% 1.00/1.05  sim_eq_res_simp:                        0
% 1.00/1.05  sim_fw_demodulated:                     0
% 1.00/1.05  sim_bw_demodulated:                     6
% 1.00/1.05  sim_light_normalised:                   7
% 1.00/1.05  sim_joinable_taut:                      0
% 1.00/1.05  sim_joinable_simp:                      0
% 1.00/1.05  sim_ac_normalised:                      0
% 1.00/1.05  sim_smt_subsumption:                    0
% 1.00/1.05  
%------------------------------------------------------------------------------
