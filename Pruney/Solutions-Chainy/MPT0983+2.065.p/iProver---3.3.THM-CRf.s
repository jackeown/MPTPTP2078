%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:01:58 EST 2020

% Result     : Theorem 3.74s
% Output     : CNFRefutation 3.74s
% Verified   : 
% Statistics : Number of formulae       :  191 (1986 expanded)
%              Number of clauses        :  112 ( 573 expanded)
%              Number of leaves         :   20 ( 498 expanded)
%              Depth                    :   28
%              Number of atoms          :  667 (13125 expanded)
%              Number of equality atoms :  239 ( 939 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f15,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f85,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f60,f73])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f28])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

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

fof(f40,plain,(
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
    inference(flattening,[],[f40])).

fof(f49,plain,(
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

fof(f48,plain,
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

fof(f50,plain,
    ( ( ~ v2_funct_2(sK3,sK0)
      | ~ v2_funct_1(sK2) )
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f41,f49,f48])).

fof(f83,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f50])).

fof(f13,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f71,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f77,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f79,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f50])).

fof(f80,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f82,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f50])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f32])).

fof(f70,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f33])).

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

fof(f38,plain,(
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
    inference(flattening,[],[f38])).

fof(f75,plain,(
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
    inference(cnf_transformation,[],[f39])).

fof(f78,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f81,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

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

fof(f36,plain,(
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
    inference(flattening,[],[f36])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f89,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f68])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f84,plain,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f34])).

fof(f72,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
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
    inference(ennf_transformation,[],[f3])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f42])).

fof(f53,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f45,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f57,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => v2_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_funct_1(X1)
          | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_funct_1(X1)
          | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f58,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_9,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1209,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_15,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_26,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_482,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_26])).

cnf(c_483,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_482])).

cnf(c_20,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_491,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_483,c_20])).

cnf(c_1190,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_491])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1268,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1697,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1190,c_32,c_30,c_29,c_27,c_491,c_1268])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v2_funct_1(X3)
    | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1201,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | v1_funct_2(X3,X4,X2) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v2_funct_1(X3) = iProver_top
    | v2_funct_1(k1_partfun1(X4,X2,X2,X0,X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2397,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1697,c_1201])).

cnf(c_33,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_34,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_35,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_36,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_37,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_38,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_1200,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1207,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2126,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1200,c_1207])).

cnf(c_22,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_495,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X2,X1,X1,X2,X3,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,X2,X0) = X2
    | k6_partfun1(X2) != k6_partfun1(sK0)
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_26])).

cnf(c_496,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0
    | k6_partfun1(sK0) != k6_partfun1(sK0) ),
    inference(unflattening,[status(thm)],[c_495])).

cnf(c_576,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_496])).

cnf(c_1189,plain,
    ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X0,sK0,X2) = sK0
    | v1_funct_2(X2,X0,sK0) != iProver_top
    | v1_funct_2(X1,sK0,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_576])).

cnf(c_1600,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1189])).

cnf(c_1753,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1600,c_33,c_34,c_35,c_36,c_37,c_38])).

cnf(c_2128,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_2126,c_1753])).

cnf(c_11,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_16,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_400,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X0)
    | X0 != X1
    | k2_relat_1(X0) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_16])).

cnf(c_401,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_400])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_411,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0)))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_401,c_10])).

cnf(c_25,negated_conjecture,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_426,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
    | ~ v2_funct_1(sK2)
    | k2_relat_1(X0) != sK0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_411,c_25])).

cnf(c_427,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3))))
    | ~ v2_funct_1(sK2)
    | k2_relat_1(sK3) != sK0 ),
    inference(unflattening,[status(thm)],[c_426])).

cnf(c_728,plain,
    ( ~ v2_funct_1(sK2)
    | sP0_iProver_split
    | k2_relat_1(sK3) != sK0 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_427])).

cnf(c_1192,plain,
    ( k2_relat_1(sK3) != sK0
    | v2_funct_1(sK2) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_728])).

cnf(c_2319,plain,
    ( sK0 != sK0
    | v2_funct_1(sK2) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_2128,c_1192])).

cnf(c_2320,plain,
    ( v2_funct_1(sK2) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2319])).

cnf(c_727,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3))))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_427])).

cnf(c_1193,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3)))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_727])).

cnf(c_2318,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(demodulation,[status(thm)],[c_2128,c_1193])).

cnf(c_2371,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_1200,c_2318])).

cnf(c_6338,plain,
    ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2397,c_33,c_34,c_35,c_36,c_37,c_38,c_2320,c_2371])).

cnf(c_6339,plain,
    ( sK0 = k1_xboole_0
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_6338])).

cnf(c_6342,plain,
    ( sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1209,c_6339])).

cnf(c_1197,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1203,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2491,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1200,c_1203])).

cnf(c_2574,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2491,c_36])).

cnf(c_2575,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_2574])).

cnf(c_2583,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1197,c_2575])).

cnf(c_2584,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2583,c_1697])).

cnf(c_3427,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2584,c_33])).

cnf(c_6362,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_6342,c_3427])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v4_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_5,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_360,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_12,c_5])).

cnf(c_364,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_360,c_10])).

cnf(c_365,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_364])).

cnf(c_1194,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_365])).

cnf(c_1965,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1197,c_1194])).

cnf(c_6371,plain,
    ( r1_tarski(k1_relat_1(sK2),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6342,c_1965])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1213,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1215,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2132,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1213,c_1215])).

cnf(c_6532,plain,
    ( k1_relat_1(sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6371,c_2132])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) = k1_xboole_0
    | k1_relat_1(X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1211,plain,
    ( k2_relat_1(X0) = k1_xboole_0
    | k1_relat_1(X0) != k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_7081,plain,
    ( k2_relat_1(sK2) = k1_xboole_0
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_6532,c_1211])).

cnf(c_1310,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1564,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1310])).

cnf(c_1565,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1564])).

cnf(c_7224,plain,
    ( k2_relat_1(sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7081,c_35,c_1565])).

cnf(c_8,plain,
    ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | v2_funct_1(X0)
    | ~ v2_funct_1(k5_relat_1(X0,X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1210,plain,
    ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v2_funct_1(X0) = iProver_top
    | v2_funct_1(k5_relat_1(X0,X1)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_7228,plain,
    ( r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k5_relat_1(sK2,X0)) != iProver_top
    | v2_funct_1(sK2) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_7224,c_1210])).

cnf(c_10352,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v2_funct_1(k5_relat_1(sK2,X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7228,c_33,c_35,c_1565,c_2320,c_2371])).

cnf(c_10353,plain,
    ( r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(k5_relat_1(sK2,X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_10352])).

cnf(c_10358,plain,
    ( r1_tarski(k1_xboole_0,k1_relat_1(sK3)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6362,c_10353])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_relat_1(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1212,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_relat_1(X0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2325,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | sK0 != k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2128,c_1212])).

cnf(c_1445,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1645,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1445])).

cnf(c_1646,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1645])).

cnf(c_5318,plain,
    ( sK0 != k1_xboole_0
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2325,c_38,c_1646])).

cnf(c_5319,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_5318])).

cnf(c_6348,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6342,c_5319])).

cnf(c_6379,plain,
    ( k1_relat_1(sK3) = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_6348])).

cnf(c_10359,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10358,c_6379])).

cnf(c_104,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_106,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_104])).

cnf(c_86,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_88,plain,
    ( v2_funct_1(k6_partfun1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_86])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10359,c_1646,c_106,c_88,c_38,c_36])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:14:35 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 3.74/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.74/1.01  
% 3.74/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.74/1.01  
% 3.74/1.01  ------  iProver source info
% 3.74/1.01  
% 3.74/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.74/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.74/1.01  git: non_committed_changes: false
% 3.74/1.01  git: last_make_outside_of_git: false
% 3.74/1.01  
% 3.74/1.01  ------ 
% 3.74/1.01  
% 3.74/1.01  ------ Input Options
% 3.74/1.01  
% 3.74/1.01  --out_options                           all
% 3.74/1.01  --tptp_safe_out                         true
% 3.74/1.01  --problem_path                          ""
% 3.74/1.01  --include_path                          ""
% 3.74/1.01  --clausifier                            res/vclausify_rel
% 3.74/1.01  --clausifier_options                    ""
% 3.74/1.01  --stdin                                 false
% 3.74/1.01  --stats_out                             all
% 3.74/1.01  
% 3.74/1.01  ------ General Options
% 3.74/1.01  
% 3.74/1.01  --fof                                   false
% 3.74/1.01  --time_out_real                         305.
% 3.74/1.01  --time_out_virtual                      -1.
% 3.74/1.01  --symbol_type_check                     false
% 3.74/1.01  --clausify_out                          false
% 3.74/1.01  --sig_cnt_out                           false
% 3.74/1.01  --trig_cnt_out                          false
% 3.74/1.01  --trig_cnt_out_tolerance                1.
% 3.74/1.01  --trig_cnt_out_sk_spl                   false
% 3.74/1.01  --abstr_cl_out                          false
% 3.74/1.01  
% 3.74/1.01  ------ Global Options
% 3.74/1.01  
% 3.74/1.01  --schedule                              default
% 3.74/1.01  --add_important_lit                     false
% 3.74/1.01  --prop_solver_per_cl                    1000
% 3.74/1.01  --min_unsat_core                        false
% 3.74/1.01  --soft_assumptions                      false
% 3.74/1.01  --soft_lemma_size                       3
% 3.74/1.01  --prop_impl_unit_size                   0
% 3.74/1.01  --prop_impl_unit                        []
% 3.74/1.01  --share_sel_clauses                     true
% 3.74/1.01  --reset_solvers                         false
% 3.74/1.01  --bc_imp_inh                            [conj_cone]
% 3.74/1.01  --conj_cone_tolerance                   3.
% 3.74/1.01  --extra_neg_conj                        none
% 3.74/1.01  --large_theory_mode                     true
% 3.74/1.01  --prolific_symb_bound                   200
% 3.74/1.01  --lt_threshold                          2000
% 3.74/1.01  --clause_weak_htbl                      true
% 3.74/1.01  --gc_record_bc_elim                     false
% 3.74/1.01  
% 3.74/1.01  ------ Preprocessing Options
% 3.74/1.01  
% 3.74/1.01  --preprocessing_flag                    true
% 3.74/1.01  --time_out_prep_mult                    0.1
% 3.74/1.01  --splitting_mode                        input
% 3.74/1.01  --splitting_grd                         true
% 3.74/1.01  --splitting_cvd                         false
% 3.74/1.01  --splitting_cvd_svl                     false
% 3.74/1.01  --splitting_nvd                         32
% 3.74/1.01  --sub_typing                            true
% 3.74/1.01  --prep_gs_sim                           true
% 3.74/1.01  --prep_unflatten                        true
% 3.74/1.01  --prep_res_sim                          true
% 3.74/1.01  --prep_upred                            true
% 3.74/1.01  --prep_sem_filter                       exhaustive
% 3.74/1.01  --prep_sem_filter_out                   false
% 3.74/1.01  --pred_elim                             true
% 3.74/1.01  --res_sim_input                         true
% 3.74/1.01  --eq_ax_congr_red                       true
% 3.74/1.01  --pure_diseq_elim                       true
% 3.74/1.01  --brand_transform                       false
% 3.74/1.01  --non_eq_to_eq                          false
% 3.74/1.01  --prep_def_merge                        true
% 3.74/1.01  --prep_def_merge_prop_impl              false
% 3.74/1.01  --prep_def_merge_mbd                    true
% 3.74/1.01  --prep_def_merge_tr_red                 false
% 3.74/1.01  --prep_def_merge_tr_cl                  false
% 3.74/1.01  --smt_preprocessing                     true
% 3.74/1.01  --smt_ac_axioms                         fast
% 3.74/1.01  --preprocessed_out                      false
% 3.74/1.01  --preprocessed_stats                    false
% 3.74/1.01  
% 3.74/1.01  ------ Abstraction refinement Options
% 3.74/1.01  
% 3.74/1.01  --abstr_ref                             []
% 3.74/1.01  --abstr_ref_prep                        false
% 3.74/1.01  --abstr_ref_until_sat                   false
% 3.74/1.01  --abstr_ref_sig_restrict                funpre
% 3.74/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.74/1.01  --abstr_ref_under                       []
% 3.74/1.01  
% 3.74/1.01  ------ SAT Options
% 3.74/1.01  
% 3.74/1.01  --sat_mode                              false
% 3.74/1.01  --sat_fm_restart_options                ""
% 3.74/1.01  --sat_gr_def                            false
% 3.74/1.01  --sat_epr_types                         true
% 3.74/1.01  --sat_non_cyclic_types                  false
% 3.74/1.01  --sat_finite_models                     false
% 3.74/1.01  --sat_fm_lemmas                         false
% 3.74/1.01  --sat_fm_prep                           false
% 3.74/1.01  --sat_fm_uc_incr                        true
% 3.74/1.01  --sat_out_model                         small
% 3.74/1.01  --sat_out_clauses                       false
% 3.74/1.01  
% 3.74/1.01  ------ QBF Options
% 3.74/1.01  
% 3.74/1.01  --qbf_mode                              false
% 3.74/1.01  --qbf_elim_univ                         false
% 3.74/1.01  --qbf_dom_inst                          none
% 3.74/1.01  --qbf_dom_pre_inst                      false
% 3.74/1.01  --qbf_sk_in                             false
% 3.74/1.01  --qbf_pred_elim                         true
% 3.74/1.01  --qbf_split                             512
% 3.74/1.01  
% 3.74/1.01  ------ BMC1 Options
% 3.74/1.01  
% 3.74/1.01  --bmc1_incremental                      false
% 3.74/1.01  --bmc1_axioms                           reachable_all
% 3.74/1.01  --bmc1_min_bound                        0
% 3.74/1.01  --bmc1_max_bound                        -1
% 3.74/1.01  --bmc1_max_bound_default                -1
% 3.74/1.01  --bmc1_symbol_reachability              true
% 3.74/1.01  --bmc1_property_lemmas                  false
% 3.74/1.01  --bmc1_k_induction                      false
% 3.74/1.01  --bmc1_non_equiv_states                 false
% 3.74/1.01  --bmc1_deadlock                         false
% 3.74/1.01  --bmc1_ucm                              false
% 3.74/1.01  --bmc1_add_unsat_core                   none
% 3.74/1.01  --bmc1_unsat_core_children              false
% 3.74/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.74/1.01  --bmc1_out_stat                         full
% 3.74/1.01  --bmc1_ground_init                      false
% 3.74/1.01  --bmc1_pre_inst_next_state              false
% 3.74/1.01  --bmc1_pre_inst_state                   false
% 3.74/1.01  --bmc1_pre_inst_reach_state             false
% 3.74/1.01  --bmc1_out_unsat_core                   false
% 3.74/1.01  --bmc1_aig_witness_out                  false
% 3.74/1.01  --bmc1_verbose                          false
% 3.74/1.01  --bmc1_dump_clauses_tptp                false
% 3.74/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.74/1.01  --bmc1_dump_file                        -
% 3.74/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.74/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.74/1.01  --bmc1_ucm_extend_mode                  1
% 3.74/1.01  --bmc1_ucm_init_mode                    2
% 3.74/1.01  --bmc1_ucm_cone_mode                    none
% 3.74/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.74/1.01  --bmc1_ucm_relax_model                  4
% 3.74/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.74/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.74/1.01  --bmc1_ucm_layered_model                none
% 3.74/1.01  --bmc1_ucm_max_lemma_size               10
% 3.74/1.01  
% 3.74/1.01  ------ AIG Options
% 3.74/1.01  
% 3.74/1.01  --aig_mode                              false
% 3.74/1.01  
% 3.74/1.01  ------ Instantiation Options
% 3.74/1.01  
% 3.74/1.01  --instantiation_flag                    true
% 3.74/1.01  --inst_sos_flag                         true
% 3.74/1.01  --inst_sos_phase                        true
% 3.74/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.74/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.74/1.01  --inst_lit_sel_side                     num_symb
% 3.74/1.01  --inst_solver_per_active                1400
% 3.74/1.01  --inst_solver_calls_frac                1.
% 3.74/1.01  --inst_passive_queue_type               priority_queues
% 3.74/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.74/1.01  --inst_passive_queues_freq              [25;2]
% 3.74/1.01  --inst_dismatching                      true
% 3.74/1.01  --inst_eager_unprocessed_to_passive     true
% 3.74/1.01  --inst_prop_sim_given                   true
% 3.74/1.01  --inst_prop_sim_new                     false
% 3.74/1.01  --inst_subs_new                         false
% 3.74/1.01  --inst_eq_res_simp                      false
% 3.74/1.01  --inst_subs_given                       false
% 3.74/1.01  --inst_orphan_elimination               true
% 3.74/1.01  --inst_learning_loop_flag               true
% 3.74/1.01  --inst_learning_start                   3000
% 3.74/1.01  --inst_learning_factor                  2
% 3.74/1.01  --inst_start_prop_sim_after_learn       3
% 3.74/1.01  --inst_sel_renew                        solver
% 3.74/1.01  --inst_lit_activity_flag                true
% 3.74/1.01  --inst_restr_to_given                   false
% 3.74/1.01  --inst_activity_threshold               500
% 3.74/1.01  --inst_out_proof                        true
% 3.74/1.01  
% 3.74/1.01  ------ Resolution Options
% 3.74/1.01  
% 3.74/1.01  --resolution_flag                       true
% 3.74/1.01  --res_lit_sel                           adaptive
% 3.74/1.01  --res_lit_sel_side                      none
% 3.74/1.01  --res_ordering                          kbo
% 3.74/1.01  --res_to_prop_solver                    active
% 3.74/1.01  --res_prop_simpl_new                    false
% 3.74/1.01  --res_prop_simpl_given                  true
% 3.74/1.01  --res_passive_queue_type                priority_queues
% 3.74/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.74/1.01  --res_passive_queues_freq               [15;5]
% 3.74/1.01  --res_forward_subs                      full
% 3.74/1.01  --res_backward_subs                     full
% 3.74/1.01  --res_forward_subs_resolution           true
% 3.74/1.01  --res_backward_subs_resolution          true
% 3.74/1.01  --res_orphan_elimination                true
% 3.74/1.01  --res_time_limit                        2.
% 3.74/1.01  --res_out_proof                         true
% 3.74/1.01  
% 3.74/1.01  ------ Superposition Options
% 3.74/1.01  
% 3.74/1.01  --superposition_flag                    true
% 3.74/1.01  --sup_passive_queue_type                priority_queues
% 3.74/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.74/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.74/1.01  --demod_completeness_check              fast
% 3.74/1.01  --demod_use_ground                      true
% 3.74/1.01  --sup_to_prop_solver                    passive
% 3.74/1.01  --sup_prop_simpl_new                    true
% 3.74/1.01  --sup_prop_simpl_given                  true
% 3.74/1.01  --sup_fun_splitting                     true
% 3.74/1.01  --sup_smt_interval                      50000
% 3.74/1.01  
% 3.74/1.01  ------ Superposition Simplification Setup
% 3.74/1.01  
% 3.74/1.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.74/1.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.74/1.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.74/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.74/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.74/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.74/1.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.74/1.01  --sup_immed_triv                        [TrivRules]
% 3.74/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.74/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.74/1.01  --sup_immed_bw_main                     []
% 3.74/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.74/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.74/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.74/1.01  --sup_input_bw                          []
% 3.74/1.01  
% 3.74/1.01  ------ Combination Options
% 3.74/1.01  
% 3.74/1.01  --comb_res_mult                         3
% 3.74/1.01  --comb_sup_mult                         2
% 3.74/1.01  --comb_inst_mult                        10
% 3.74/1.01  
% 3.74/1.01  ------ Debug Options
% 3.74/1.01  
% 3.74/1.01  --dbg_backtrace                         false
% 3.74/1.01  --dbg_dump_prop_clauses                 false
% 3.74/1.01  --dbg_dump_prop_clauses_file            -
% 3.74/1.01  --dbg_out_stat                          false
% 3.74/1.01  ------ Parsing...
% 3.74/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.74/1.01  
% 3.74/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.74/1.01  
% 3.74/1.01  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.74/1.01  
% 3.74/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.74/1.01  ------ Proving...
% 3.74/1.01  ------ Problem Properties 
% 3.74/1.01  
% 3.74/1.01  
% 3.74/1.01  clauses                                 27
% 3.74/1.01  conjectures                             6
% 3.74/1.01  EPR                                     7
% 3.74/1.01  Horn                                    26
% 3.74/1.01  unary                                   10
% 3.74/1.01  binary                                  5
% 3.74/1.01  lits                                    87
% 3.74/1.01  lits eq                                 14
% 3.74/1.01  fd_pure                                 0
% 3.74/1.01  fd_pseudo                               0
% 3.74/1.01  fd_cond                                 1
% 3.74/1.01  fd_pseudo_cond                          1
% 3.74/1.01  AC symbols                              0
% 3.74/1.01  
% 3.74/1.01  ------ Schedule dynamic 5 is on 
% 3.74/1.01  
% 3.74/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.74/1.01  
% 3.74/1.01  
% 3.74/1.01  ------ 
% 3.74/1.01  Current options:
% 3.74/1.01  ------ 
% 3.74/1.01  
% 3.74/1.01  ------ Input Options
% 3.74/1.01  
% 3.74/1.01  --out_options                           all
% 3.74/1.01  --tptp_safe_out                         true
% 3.74/1.01  --problem_path                          ""
% 3.74/1.01  --include_path                          ""
% 3.74/1.01  --clausifier                            res/vclausify_rel
% 3.74/1.01  --clausifier_options                    ""
% 3.74/1.01  --stdin                                 false
% 3.74/1.01  --stats_out                             all
% 3.74/1.01  
% 3.74/1.01  ------ General Options
% 3.74/1.01  
% 3.74/1.01  --fof                                   false
% 3.74/1.01  --time_out_real                         305.
% 3.74/1.01  --time_out_virtual                      -1.
% 3.74/1.01  --symbol_type_check                     false
% 3.74/1.01  --clausify_out                          false
% 3.74/1.01  --sig_cnt_out                           false
% 3.74/1.01  --trig_cnt_out                          false
% 3.74/1.01  --trig_cnt_out_tolerance                1.
% 3.74/1.01  --trig_cnt_out_sk_spl                   false
% 3.74/1.01  --abstr_cl_out                          false
% 3.74/1.01  
% 3.74/1.01  ------ Global Options
% 3.74/1.01  
% 3.74/1.01  --schedule                              default
% 3.74/1.01  --add_important_lit                     false
% 3.74/1.01  --prop_solver_per_cl                    1000
% 3.74/1.01  --min_unsat_core                        false
% 3.74/1.01  --soft_assumptions                      false
% 3.74/1.01  --soft_lemma_size                       3
% 3.74/1.01  --prop_impl_unit_size                   0
% 3.74/1.01  --prop_impl_unit                        []
% 3.74/1.01  --share_sel_clauses                     true
% 3.74/1.01  --reset_solvers                         false
% 3.74/1.01  --bc_imp_inh                            [conj_cone]
% 3.74/1.01  --conj_cone_tolerance                   3.
% 3.74/1.01  --extra_neg_conj                        none
% 3.74/1.01  --large_theory_mode                     true
% 3.74/1.01  --prolific_symb_bound                   200
% 3.74/1.01  --lt_threshold                          2000
% 3.74/1.01  --clause_weak_htbl                      true
% 3.74/1.01  --gc_record_bc_elim                     false
% 3.74/1.01  
% 3.74/1.01  ------ Preprocessing Options
% 3.74/1.01  
% 3.74/1.01  --preprocessing_flag                    true
% 3.74/1.01  --time_out_prep_mult                    0.1
% 3.74/1.01  --splitting_mode                        input
% 3.74/1.01  --splitting_grd                         true
% 3.74/1.01  --splitting_cvd                         false
% 3.74/1.01  --splitting_cvd_svl                     false
% 3.74/1.01  --splitting_nvd                         32
% 3.74/1.01  --sub_typing                            true
% 3.74/1.01  --prep_gs_sim                           true
% 3.74/1.01  --prep_unflatten                        true
% 3.74/1.01  --prep_res_sim                          true
% 3.74/1.01  --prep_upred                            true
% 3.74/1.01  --prep_sem_filter                       exhaustive
% 3.74/1.01  --prep_sem_filter_out                   false
% 3.74/1.01  --pred_elim                             true
% 3.74/1.01  --res_sim_input                         true
% 3.74/1.01  --eq_ax_congr_red                       true
% 3.74/1.01  --pure_diseq_elim                       true
% 3.74/1.01  --brand_transform                       false
% 3.74/1.01  --non_eq_to_eq                          false
% 3.74/1.01  --prep_def_merge                        true
% 3.74/1.01  --prep_def_merge_prop_impl              false
% 3.74/1.01  --prep_def_merge_mbd                    true
% 3.74/1.01  --prep_def_merge_tr_red                 false
% 3.74/1.01  --prep_def_merge_tr_cl                  false
% 3.74/1.01  --smt_preprocessing                     true
% 3.74/1.01  --smt_ac_axioms                         fast
% 3.74/1.01  --preprocessed_out                      false
% 3.74/1.01  --preprocessed_stats                    false
% 3.74/1.01  
% 3.74/1.01  ------ Abstraction refinement Options
% 3.74/1.01  
% 3.74/1.01  --abstr_ref                             []
% 3.74/1.01  --abstr_ref_prep                        false
% 3.74/1.01  --abstr_ref_until_sat                   false
% 3.74/1.01  --abstr_ref_sig_restrict                funpre
% 3.74/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.74/1.01  --abstr_ref_under                       []
% 3.74/1.01  
% 3.74/1.01  ------ SAT Options
% 3.74/1.01  
% 3.74/1.01  --sat_mode                              false
% 3.74/1.01  --sat_fm_restart_options                ""
% 3.74/1.01  --sat_gr_def                            false
% 3.74/1.01  --sat_epr_types                         true
% 3.74/1.01  --sat_non_cyclic_types                  false
% 3.74/1.01  --sat_finite_models                     false
% 3.74/1.01  --sat_fm_lemmas                         false
% 3.74/1.01  --sat_fm_prep                           false
% 3.74/1.01  --sat_fm_uc_incr                        true
% 3.74/1.01  --sat_out_model                         small
% 3.74/1.01  --sat_out_clauses                       false
% 3.74/1.01  
% 3.74/1.01  ------ QBF Options
% 3.74/1.01  
% 3.74/1.01  --qbf_mode                              false
% 3.74/1.01  --qbf_elim_univ                         false
% 3.74/1.01  --qbf_dom_inst                          none
% 3.74/1.01  --qbf_dom_pre_inst                      false
% 3.74/1.01  --qbf_sk_in                             false
% 3.74/1.01  --qbf_pred_elim                         true
% 3.74/1.01  --qbf_split                             512
% 3.74/1.01  
% 3.74/1.01  ------ BMC1 Options
% 3.74/1.01  
% 3.74/1.01  --bmc1_incremental                      false
% 3.74/1.01  --bmc1_axioms                           reachable_all
% 3.74/1.01  --bmc1_min_bound                        0
% 3.74/1.01  --bmc1_max_bound                        -1
% 3.74/1.01  --bmc1_max_bound_default                -1
% 3.74/1.01  --bmc1_symbol_reachability              true
% 3.74/1.01  --bmc1_property_lemmas                  false
% 3.74/1.01  --bmc1_k_induction                      false
% 3.74/1.01  --bmc1_non_equiv_states                 false
% 3.74/1.01  --bmc1_deadlock                         false
% 3.74/1.01  --bmc1_ucm                              false
% 3.74/1.01  --bmc1_add_unsat_core                   none
% 3.74/1.01  --bmc1_unsat_core_children              false
% 3.74/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.74/1.01  --bmc1_out_stat                         full
% 3.74/1.01  --bmc1_ground_init                      false
% 3.74/1.01  --bmc1_pre_inst_next_state              false
% 3.74/1.01  --bmc1_pre_inst_state                   false
% 3.74/1.01  --bmc1_pre_inst_reach_state             false
% 3.74/1.01  --bmc1_out_unsat_core                   false
% 3.74/1.01  --bmc1_aig_witness_out                  false
% 3.74/1.01  --bmc1_verbose                          false
% 3.74/1.01  --bmc1_dump_clauses_tptp                false
% 3.74/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.74/1.01  --bmc1_dump_file                        -
% 3.74/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.74/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.74/1.01  --bmc1_ucm_extend_mode                  1
% 3.74/1.01  --bmc1_ucm_init_mode                    2
% 3.74/1.01  --bmc1_ucm_cone_mode                    none
% 3.74/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.74/1.01  --bmc1_ucm_relax_model                  4
% 3.74/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.74/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.74/1.01  --bmc1_ucm_layered_model                none
% 3.74/1.01  --bmc1_ucm_max_lemma_size               10
% 3.74/1.01  
% 3.74/1.01  ------ AIG Options
% 3.74/1.01  
% 3.74/1.01  --aig_mode                              false
% 3.74/1.01  
% 3.74/1.01  ------ Instantiation Options
% 3.74/1.01  
% 3.74/1.01  --instantiation_flag                    true
% 3.74/1.01  --inst_sos_flag                         true
% 3.74/1.01  --inst_sos_phase                        true
% 3.74/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.74/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.74/1.01  --inst_lit_sel_side                     none
% 3.74/1.01  --inst_solver_per_active                1400
% 3.74/1.01  --inst_solver_calls_frac                1.
% 3.74/1.01  --inst_passive_queue_type               priority_queues
% 3.74/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.74/1.01  --inst_passive_queues_freq              [25;2]
% 3.74/1.01  --inst_dismatching                      true
% 3.74/1.01  --inst_eager_unprocessed_to_passive     true
% 3.74/1.01  --inst_prop_sim_given                   true
% 3.74/1.01  --inst_prop_sim_new                     false
% 3.74/1.01  --inst_subs_new                         false
% 3.74/1.01  --inst_eq_res_simp                      false
% 3.74/1.01  --inst_subs_given                       false
% 3.74/1.01  --inst_orphan_elimination               true
% 3.74/1.01  --inst_learning_loop_flag               true
% 3.74/1.01  --inst_learning_start                   3000
% 3.74/1.01  --inst_learning_factor                  2
% 3.74/1.01  --inst_start_prop_sim_after_learn       3
% 3.74/1.01  --inst_sel_renew                        solver
% 3.74/1.01  --inst_lit_activity_flag                true
% 3.74/1.01  --inst_restr_to_given                   false
% 3.74/1.01  --inst_activity_threshold               500
% 3.74/1.01  --inst_out_proof                        true
% 3.74/1.01  
% 3.74/1.01  ------ Resolution Options
% 3.74/1.01  
% 3.74/1.01  --resolution_flag                       false
% 3.74/1.01  --res_lit_sel                           adaptive
% 3.74/1.01  --res_lit_sel_side                      none
% 3.74/1.01  --res_ordering                          kbo
% 3.74/1.01  --res_to_prop_solver                    active
% 3.74/1.01  --res_prop_simpl_new                    false
% 3.74/1.01  --res_prop_simpl_given                  true
% 3.74/1.01  --res_passive_queue_type                priority_queues
% 3.74/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.74/1.01  --res_passive_queues_freq               [15;5]
% 3.74/1.01  --res_forward_subs                      full
% 3.74/1.01  --res_backward_subs                     full
% 3.74/1.01  --res_forward_subs_resolution           true
% 3.74/1.01  --res_backward_subs_resolution          true
% 3.74/1.01  --res_orphan_elimination                true
% 3.74/1.01  --res_time_limit                        2.
% 3.74/1.01  --res_out_proof                         true
% 3.74/1.01  
% 3.74/1.01  ------ Superposition Options
% 3.74/1.01  
% 3.74/1.01  --superposition_flag                    true
% 3.74/1.01  --sup_passive_queue_type                priority_queues
% 3.74/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.74/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.74/1.01  --demod_completeness_check              fast
% 3.74/1.01  --demod_use_ground                      true
% 3.74/1.01  --sup_to_prop_solver                    passive
% 3.74/1.01  --sup_prop_simpl_new                    true
% 3.74/1.01  --sup_prop_simpl_given                  true
% 3.74/1.01  --sup_fun_splitting                     true
% 3.74/1.01  --sup_smt_interval                      50000
% 3.74/1.01  
% 3.74/1.01  ------ Superposition Simplification Setup
% 3.74/1.01  
% 3.74/1.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.74/1.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.74/1.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.74/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.74/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.74/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.74/1.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.74/1.01  --sup_immed_triv                        [TrivRules]
% 3.74/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.74/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.74/1.01  --sup_immed_bw_main                     []
% 3.74/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.74/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.74/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.74/1.01  --sup_input_bw                          []
% 3.74/1.01  
% 3.74/1.01  ------ Combination Options
% 3.74/1.01  
% 3.74/1.01  --comb_res_mult                         3
% 3.74/1.01  --comb_sup_mult                         2
% 3.74/1.01  --comb_inst_mult                        10
% 3.74/1.01  
% 3.74/1.01  ------ Debug Options
% 3.74/1.01  
% 3.74/1.01  --dbg_backtrace                         false
% 3.74/1.01  --dbg_dump_prop_clauses                 false
% 3.74/1.01  --dbg_dump_prop_clauses_file            -
% 3.74/1.01  --dbg_out_stat                          false
% 3.74/1.01  
% 3.74/1.01  
% 3.74/1.01  
% 3.74/1.01  
% 3.74/1.01  ------ Proving...
% 3.74/1.01  
% 3.74/1.01  
% 3.74/1.01  % SZS status Theorem for theBenchmark.p
% 3.74/1.01  
% 3.74/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.74/1.01  
% 3.74/1.01  fof(f6,axiom,(
% 3.74/1.01    ! [X0] : v2_funct_1(k6_relat_1(X0))),
% 3.74/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/1.01  
% 3.74/1.01  fof(f60,plain,(
% 3.74/1.01    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 3.74/1.01    inference(cnf_transformation,[],[f6])).
% 3.74/1.01  
% 3.74/1.01  fof(f15,axiom,(
% 3.74/1.01    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.74/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/1.01  
% 3.74/1.01  fof(f73,plain,(
% 3.74/1.01    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.74/1.01    inference(cnf_transformation,[],[f15])).
% 3.74/1.01  
% 3.74/1.01  fof(f85,plain,(
% 3.74/1.01    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 3.74/1.01    inference(definition_unfolding,[],[f60,f73])).
% 3.74/1.01  
% 3.74/1.01  fof(f10,axiom,(
% 3.74/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.74/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/1.01  
% 3.74/1.01  fof(f28,plain,(
% 3.74/1.01    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.74/1.01    inference(ennf_transformation,[],[f10])).
% 3.74/1.01  
% 3.74/1.01  fof(f29,plain,(
% 3.74/1.01    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.74/1.01    inference(flattening,[],[f28])).
% 3.74/1.01  
% 3.74/1.01  fof(f46,plain,(
% 3.74/1.01    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.74/1.01    inference(nnf_transformation,[],[f29])).
% 3.74/1.01  
% 3.74/1.01  fof(f65,plain,(
% 3.74/1.01    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.74/1.01    inference(cnf_transformation,[],[f46])).
% 3.74/1.01  
% 3.74/1.01  fof(f18,conjecture,(
% 3.74/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 3.74/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/1.01  
% 3.74/1.01  fof(f19,negated_conjecture,(
% 3.74/1.01    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 3.74/1.01    inference(negated_conjecture,[],[f18])).
% 3.74/1.01  
% 3.74/1.01  fof(f40,plain,(
% 3.74/1.01    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.74/1.01    inference(ennf_transformation,[],[f19])).
% 3.74/1.01  
% 3.74/1.01  fof(f41,plain,(
% 3.74/1.01    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.74/1.01    inference(flattening,[],[f40])).
% 3.74/1.01  
% 3.74/1.01  fof(f49,plain,(
% 3.74/1.01    ( ! [X2,X0,X1] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((~v2_funct_2(sK3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 3.74/1.01    introduced(choice_axiom,[])).
% 3.74/1.01  
% 3.74/1.01  fof(f48,plain,(
% 3.74/1.01    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 3.74/1.01    introduced(choice_axiom,[])).
% 3.74/1.01  
% 3.74/1.01  fof(f50,plain,(
% 3.74/1.01    ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 3.74/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f41,f49,f48])).
% 3.74/1.01  
% 3.74/1.01  fof(f83,plain,(
% 3.74/1.01    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 3.74/1.01    inference(cnf_transformation,[],[f50])).
% 3.74/1.01  
% 3.74/1.01  fof(f13,axiom,(
% 3.74/1.01    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 3.74/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/1.01  
% 3.74/1.01  fof(f20,plain,(
% 3.74/1.01    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.74/1.01    inference(pure_predicate_removal,[],[f13])).
% 3.74/1.01  
% 3.74/1.01  fof(f71,plain,(
% 3.74/1.01    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.74/1.01    inference(cnf_transformation,[],[f20])).
% 3.74/1.01  
% 3.74/1.01  fof(f77,plain,(
% 3.74/1.01    v1_funct_1(sK2)),
% 3.74/1.01    inference(cnf_transformation,[],[f50])).
% 3.74/1.01  
% 3.74/1.01  fof(f79,plain,(
% 3.74/1.01    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.74/1.01    inference(cnf_transformation,[],[f50])).
% 3.74/1.01  
% 3.74/1.01  fof(f80,plain,(
% 3.74/1.01    v1_funct_1(sK3)),
% 3.74/1.01    inference(cnf_transformation,[],[f50])).
% 3.74/1.01  
% 3.74/1.01  fof(f82,plain,(
% 3.74/1.01    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 3.74/1.01    inference(cnf_transformation,[],[f50])).
% 3.74/1.01  
% 3.74/1.01  fof(f12,axiom,(
% 3.74/1.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 3.74/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/1.01  
% 3.74/1.01  fof(f32,plain,(
% 3.74/1.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.74/1.01    inference(ennf_transformation,[],[f12])).
% 3.74/1.01  
% 3.74/1.01  fof(f33,plain,(
% 3.74/1.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.74/1.01    inference(flattening,[],[f32])).
% 3.74/1.01  
% 3.74/1.01  fof(f70,plain,(
% 3.74/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.74/1.01    inference(cnf_transformation,[],[f33])).
% 3.74/1.01  
% 3.74/1.01  fof(f17,axiom,(
% 3.74/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 3.74/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/1.01  
% 3.74/1.01  fof(f38,plain,(
% 3.74/1.01    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.74/1.01    inference(ennf_transformation,[],[f17])).
% 3.74/1.01  
% 3.74/1.01  fof(f39,plain,(
% 3.74/1.01    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.74/1.01    inference(flattening,[],[f38])).
% 3.74/1.01  
% 3.74/1.01  fof(f75,plain,(
% 3.74/1.01    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X3) | k1_xboole_0 = X2 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.74/1.01    inference(cnf_transformation,[],[f39])).
% 3.74/1.01  
% 3.74/1.01  fof(f78,plain,(
% 3.74/1.01    v1_funct_2(sK2,sK0,sK1)),
% 3.74/1.01    inference(cnf_transformation,[],[f50])).
% 3.74/1.01  
% 3.74/1.01  fof(f81,plain,(
% 3.74/1.01    v1_funct_2(sK3,sK1,sK0)),
% 3.74/1.01    inference(cnf_transformation,[],[f50])).
% 3.74/1.01  
% 3.74/1.01  fof(f9,axiom,(
% 3.74/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.74/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/1.01  
% 3.74/1.01  fof(f27,plain,(
% 3.74/1.01    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.74/1.01    inference(ennf_transformation,[],[f9])).
% 3.74/1.01  
% 3.74/1.01  fof(f64,plain,(
% 3.74/1.01    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.74/1.01    inference(cnf_transformation,[],[f27])).
% 3.74/1.01  
% 3.74/1.01  fof(f16,axiom,(
% 3.74/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 3.74/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/1.01  
% 3.74/1.01  fof(f36,plain,(
% 3.74/1.01    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.74/1.01    inference(ennf_transformation,[],[f16])).
% 3.74/1.01  
% 3.74/1.01  fof(f37,plain,(
% 3.74/1.01    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.74/1.01    inference(flattening,[],[f36])).
% 3.74/1.01  
% 3.74/1.01  fof(f74,plain,(
% 3.74/1.01    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.74/1.01    inference(cnf_transformation,[],[f37])).
% 3.74/1.01  
% 3.74/1.01  fof(f8,axiom,(
% 3.74/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.74/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/1.01  
% 3.74/1.01  fof(f26,plain,(
% 3.74/1.01    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.74/1.01    inference(ennf_transformation,[],[f8])).
% 3.74/1.01  
% 3.74/1.01  fof(f63,plain,(
% 3.74/1.01    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.74/1.01    inference(cnf_transformation,[],[f26])).
% 3.74/1.01  
% 3.74/1.01  fof(f11,axiom,(
% 3.74/1.01    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 3.74/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/1.01  
% 3.74/1.01  fof(f30,plain,(
% 3.74/1.01    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.74/1.01    inference(ennf_transformation,[],[f11])).
% 3.74/1.01  
% 3.74/1.01  fof(f31,plain,(
% 3.74/1.01    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.74/1.01    inference(flattening,[],[f30])).
% 3.74/1.01  
% 3.74/1.01  fof(f47,plain,(
% 3.74/1.01    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.74/1.01    inference(nnf_transformation,[],[f31])).
% 3.74/1.01  
% 3.74/1.01  fof(f68,plain,(
% 3.74/1.01    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.74/1.01    inference(cnf_transformation,[],[f47])).
% 3.74/1.01  
% 3.74/1.01  fof(f89,plain,(
% 3.74/1.01    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.74/1.01    inference(equality_resolution,[],[f68])).
% 3.74/1.01  
% 3.74/1.01  fof(f7,axiom,(
% 3.74/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.74/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/1.01  
% 3.74/1.01  fof(f25,plain,(
% 3.74/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.74/1.01    inference(ennf_transformation,[],[f7])).
% 3.74/1.01  
% 3.74/1.01  fof(f61,plain,(
% 3.74/1.01    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.74/1.01    inference(cnf_transformation,[],[f25])).
% 3.74/1.01  
% 3.74/1.01  fof(f84,plain,(
% 3.74/1.01    ~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)),
% 3.74/1.01    inference(cnf_transformation,[],[f50])).
% 3.74/1.01  
% 3.74/1.01  fof(f14,axiom,(
% 3.74/1.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.74/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/1.01  
% 3.74/1.01  fof(f34,plain,(
% 3.74/1.01    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.74/1.01    inference(ennf_transformation,[],[f14])).
% 3.74/1.01  
% 3.74/1.01  fof(f35,plain,(
% 3.74/1.01    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.74/1.01    inference(flattening,[],[f34])).
% 3.74/1.01  
% 3.74/1.01  fof(f72,plain,(
% 3.74/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.74/1.01    inference(cnf_transformation,[],[f35])).
% 3.74/1.01  
% 3.74/1.01  fof(f62,plain,(
% 3.74/1.01    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.74/1.01    inference(cnf_transformation,[],[f26])).
% 3.74/1.01  
% 3.74/1.01  fof(f3,axiom,(
% 3.74/1.01    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.74/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/1.01  
% 3.74/1.01  fof(f21,plain,(
% 3.74/1.01    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.74/1.01    inference(ennf_transformation,[],[f3])).
% 3.74/1.01  
% 3.74/1.01  fof(f44,plain,(
% 3.74/1.01    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.74/1.01    inference(nnf_transformation,[],[f21])).
% 3.74/1.01  
% 3.74/1.01  fof(f55,plain,(
% 3.74/1.01    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.74/1.01    inference(cnf_transformation,[],[f44])).
% 3.74/1.01  
% 3.74/1.01  fof(f2,axiom,(
% 3.74/1.01    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.74/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/1.01  
% 3.74/1.01  fof(f54,plain,(
% 3.74/1.01    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.74/1.01    inference(cnf_transformation,[],[f2])).
% 3.74/1.01  
% 3.74/1.01  fof(f1,axiom,(
% 3.74/1.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.74/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/1.01  
% 3.74/1.01  fof(f42,plain,(
% 3.74/1.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.74/1.01    inference(nnf_transformation,[],[f1])).
% 3.74/1.01  
% 3.74/1.01  fof(f43,plain,(
% 3.74/1.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.74/1.01    inference(flattening,[],[f42])).
% 3.74/1.01  
% 3.74/1.01  fof(f53,plain,(
% 3.74/1.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.74/1.01    inference(cnf_transformation,[],[f43])).
% 3.74/1.01  
% 3.74/1.01  fof(f4,axiom,(
% 3.74/1.01    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 3.74/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/1.01  
% 3.74/1.01  fof(f22,plain,(
% 3.74/1.01    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.74/1.01    inference(ennf_transformation,[],[f4])).
% 3.74/1.01  
% 3.74/1.01  fof(f45,plain,(
% 3.74/1.01    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.74/1.01    inference(nnf_transformation,[],[f22])).
% 3.74/1.01  
% 3.74/1.01  fof(f57,plain,(
% 3.74/1.01    ( ! [X0] : (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.74/1.01    inference(cnf_transformation,[],[f45])).
% 3.74/1.01  
% 3.74/1.01  fof(f5,axiom,(
% 3.74/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) & v2_funct_1(k5_relat_1(X1,X0))) => v2_funct_1(X1))))),
% 3.74/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/1.01  
% 3.74/1.01  fof(f23,plain,(
% 3.74/1.01    ! [X0] : (! [X1] : ((v2_funct_1(X1) | (~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.74/1.01    inference(ennf_transformation,[],[f5])).
% 3.74/1.01  
% 3.74/1.01  fof(f24,plain,(
% 3.74/1.01    ! [X0] : (! [X1] : (v2_funct_1(X1) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.74/1.01    inference(flattening,[],[f23])).
% 3.74/1.01  
% 3.74/1.01  fof(f59,plain,(
% 3.74/1.01    ( ! [X0,X1] : (v2_funct_1(X1) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.74/1.01    inference(cnf_transformation,[],[f24])).
% 3.74/1.01  
% 3.74/1.01  fof(f58,plain,(
% 3.74/1.01    ( ! [X0] : (k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.74/1.01    inference(cnf_transformation,[],[f45])).
% 3.74/1.01  
% 3.74/1.01  cnf(c_9,plain,
% 3.74/1.01      ( v2_funct_1(k6_partfun1(X0)) ),
% 3.74/1.01      inference(cnf_transformation,[],[f85]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_1209,plain,
% 3.74/1.01      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 3.74/1.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_15,plain,
% 3.74/1.01      ( ~ r2_relset_1(X0,X1,X2,X3)
% 3.74/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.74/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.74/1.01      | X3 = X2 ),
% 3.74/1.01      inference(cnf_transformation,[],[f65]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_26,negated_conjecture,
% 3.74/1.01      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 3.74/1.01      inference(cnf_transformation,[],[f83]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_482,plain,
% 3.74/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.74/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.74/1.01      | X3 = X0
% 3.74/1.01      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 3.74/1.01      | k6_partfun1(sK0) != X3
% 3.74/1.01      | sK0 != X2
% 3.74/1.01      | sK0 != X1 ),
% 3.74/1.01      inference(resolution_lifted,[status(thm)],[c_15,c_26]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_483,plain,
% 3.74/1.01      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.74/1.01      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.74/1.01      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.74/1.01      inference(unflattening,[status(thm)],[c_482]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_20,plain,
% 3.74/1.01      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.74/1.01      inference(cnf_transformation,[],[f71]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_491,plain,
% 3.74/1.01      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.74/1.01      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.74/1.01      inference(forward_subsumption_resolution,
% 3.74/1.01                [status(thm)],
% 3.74/1.01                [c_483,c_20]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_1190,plain,
% 3.74/1.01      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.74/1.01      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.74/1.01      inference(predicate_to_equality,[status(thm)],[c_491]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_32,negated_conjecture,
% 3.74/1.01      ( v1_funct_1(sK2) ),
% 3.74/1.01      inference(cnf_transformation,[],[f77]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_30,negated_conjecture,
% 3.74/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.74/1.01      inference(cnf_transformation,[],[f79]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_29,negated_conjecture,
% 3.74/1.01      ( v1_funct_1(sK3) ),
% 3.74/1.01      inference(cnf_transformation,[],[f80]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_27,negated_conjecture,
% 3.74/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 3.74/1.01      inference(cnf_transformation,[],[f82]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_18,plain,
% 3.74/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.74/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.74/1.01      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.74/1.01      | ~ v1_funct_1(X0)
% 3.74/1.01      | ~ v1_funct_1(X3) ),
% 3.74/1.01      inference(cnf_transformation,[],[f70]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_1268,plain,
% 3.74/1.01      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.74/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.74/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.74/1.01      | ~ v1_funct_1(sK2)
% 3.74/1.01      | ~ v1_funct_1(sK3) ),
% 3.74/1.01      inference(instantiation,[status(thm)],[c_18]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_1697,plain,
% 3.74/1.01      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.74/1.01      inference(global_propositional_subsumption,
% 3.74/1.01                [status(thm)],
% 3.74/1.01                [c_1190,c_32,c_30,c_29,c_27,c_491,c_1268]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_24,plain,
% 3.74/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 3.74/1.01      | ~ v1_funct_2(X3,X4,X1)
% 3.74/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 3.74/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.74/1.01      | ~ v1_funct_1(X0)
% 3.74/1.01      | ~ v1_funct_1(X3)
% 3.74/1.01      | v2_funct_1(X3)
% 3.74/1.01      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 3.74/1.01      | k1_xboole_0 = X2 ),
% 3.74/1.01      inference(cnf_transformation,[],[f75]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_1201,plain,
% 3.74/1.01      ( k1_xboole_0 = X0
% 3.74/1.01      | v1_funct_2(X1,X2,X0) != iProver_top
% 3.74/1.01      | v1_funct_2(X3,X4,X2) != iProver_top
% 3.74/1.01      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
% 3.74/1.01      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 3.74/1.01      | v1_funct_1(X1) != iProver_top
% 3.74/1.01      | v1_funct_1(X3) != iProver_top
% 3.74/1.01      | v2_funct_1(X3) = iProver_top
% 3.74/1.01      | v2_funct_1(k1_partfun1(X4,X2,X2,X0,X3,X1)) != iProver_top ),
% 3.74/1.01      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_2397,plain,
% 3.74/1.01      ( sK0 = k1_xboole_0
% 3.74/1.01      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 3.74/1.01      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 3.74/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.74/1.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.74/1.01      | v1_funct_1(sK2) != iProver_top
% 3.74/1.01      | v1_funct_1(sK3) != iProver_top
% 3.74/1.01      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 3.74/1.01      | v2_funct_1(sK2) = iProver_top ),
% 3.74/1.01      inference(superposition,[status(thm)],[c_1697,c_1201]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_33,plain,
% 3.74/1.01      ( v1_funct_1(sK2) = iProver_top ),
% 3.74/1.01      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_31,negated_conjecture,
% 3.74/1.01      ( v1_funct_2(sK2,sK0,sK1) ),
% 3.74/1.01      inference(cnf_transformation,[],[f78]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_34,plain,
% 3.74/1.01      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 3.74/1.01      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_35,plain,
% 3.74/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.74/1.01      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_36,plain,
% 3.74/1.01      ( v1_funct_1(sK3) = iProver_top ),
% 3.74/1.01      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_28,negated_conjecture,
% 3.74/1.01      ( v1_funct_2(sK3,sK1,sK0) ),
% 3.74/1.01      inference(cnf_transformation,[],[f81]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_37,plain,
% 3.74/1.01      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 3.74/1.01      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_38,plain,
% 3.74/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.74/1.01      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_1200,plain,
% 3.74/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.74/1.01      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_13,plain,
% 3.74/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.74/1.01      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.74/1.01      inference(cnf_transformation,[],[f64]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_1207,plain,
% 3.74/1.01      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.74/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.74/1.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_2126,plain,
% 3.74/1.01      ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 3.74/1.01      inference(superposition,[status(thm)],[c_1200,c_1207]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_22,plain,
% 3.74/1.01      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.74/1.01      | ~ v1_funct_2(X2,X0,X1)
% 3.74/1.01      | ~ v1_funct_2(X3,X1,X0)
% 3.74/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.74/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.74/1.01      | ~ v1_funct_1(X2)
% 3.74/1.01      | ~ v1_funct_1(X3)
% 3.74/1.01      | k2_relset_1(X1,X0,X3) = X0 ),
% 3.74/1.01      inference(cnf_transformation,[],[f74]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_495,plain,
% 3.74/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 3.74/1.01      | ~ v1_funct_2(X3,X2,X1)
% 3.74/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.74/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.74/1.01      | ~ v1_funct_1(X0)
% 3.74/1.01      | ~ v1_funct_1(X3)
% 3.74/1.01      | k1_partfun1(X2,X1,X1,X2,X3,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.74/1.01      | k2_relset_1(X1,X2,X0) = X2
% 3.74/1.01      | k6_partfun1(X2) != k6_partfun1(sK0)
% 3.74/1.01      | sK0 != X2 ),
% 3.74/1.01      inference(resolution_lifted,[status(thm)],[c_22,c_26]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_496,plain,
% 3.74/1.01      ( ~ v1_funct_2(X0,X1,sK0)
% 3.74/1.01      | ~ v1_funct_2(X2,sK0,X1)
% 3.74/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 3.74/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 3.74/1.01      | ~ v1_funct_1(X0)
% 3.74/1.01      | ~ v1_funct_1(X2)
% 3.74/1.01      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.74/1.01      | k2_relset_1(X1,sK0,X0) = sK0
% 3.74/1.01      | k6_partfun1(sK0) != k6_partfun1(sK0) ),
% 3.74/1.01      inference(unflattening,[status(thm)],[c_495]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_576,plain,
% 3.74/1.01      ( ~ v1_funct_2(X0,X1,sK0)
% 3.74/1.01      | ~ v1_funct_2(X2,sK0,X1)
% 3.74/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 3.74/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 3.74/1.01      | ~ v1_funct_1(X0)
% 3.74/1.01      | ~ v1_funct_1(X2)
% 3.74/1.01      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.74/1.01      | k2_relset_1(X1,sK0,X0) = sK0 ),
% 3.74/1.01      inference(equality_resolution_simp,[status(thm)],[c_496]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_1189,plain,
% 3.74/1.01      ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.74/1.01      | k2_relset_1(X0,sK0,X2) = sK0
% 3.74/1.01      | v1_funct_2(X2,X0,sK0) != iProver_top
% 3.74/1.01      | v1_funct_2(X1,sK0,X0) != iProver_top
% 3.74/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 3.74/1.01      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 3.74/1.01      | v1_funct_1(X2) != iProver_top
% 3.74/1.01      | v1_funct_1(X1) != iProver_top ),
% 3.74/1.01      inference(predicate_to_equality,[status(thm)],[c_576]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_1600,plain,
% 3.74/1.01      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 3.74/1.01      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 3.74/1.01      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 3.74/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.74/1.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.74/1.01      | v1_funct_1(sK2) != iProver_top
% 3.74/1.01      | v1_funct_1(sK3) != iProver_top ),
% 3.74/1.01      inference(equality_resolution,[status(thm)],[c_1189]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_1753,plain,
% 3.74/1.01      ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 3.74/1.01      inference(global_propositional_subsumption,
% 3.74/1.01                [status(thm)],
% 3.74/1.01                [c_1600,c_33,c_34,c_35,c_36,c_37,c_38]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_2128,plain,
% 3.74/1.01      ( k2_relat_1(sK3) = sK0 ),
% 3.74/1.01      inference(light_normalisation,[status(thm)],[c_2126,c_1753]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_11,plain,
% 3.74/1.01      ( v5_relat_1(X0,X1)
% 3.74/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.74/1.01      inference(cnf_transformation,[],[f63]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_16,plain,
% 3.74/1.01      ( v2_funct_2(X0,k2_relat_1(X0))
% 3.74/1.01      | ~ v5_relat_1(X0,k2_relat_1(X0))
% 3.74/1.01      | ~ v1_relat_1(X0) ),
% 3.74/1.01      inference(cnf_transformation,[],[f89]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_400,plain,
% 3.74/1.01      ( v2_funct_2(X0,k2_relat_1(X0))
% 3.74/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.74/1.01      | ~ v1_relat_1(X0)
% 3.74/1.01      | X0 != X1
% 3.74/1.01      | k2_relat_1(X0) != X3 ),
% 3.74/1.01      inference(resolution_lifted,[status(thm)],[c_11,c_16]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_401,plain,
% 3.74/1.01      ( v2_funct_2(X0,k2_relat_1(X0))
% 3.74/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
% 3.74/1.01      | ~ v1_relat_1(X0) ),
% 3.74/1.01      inference(unflattening,[status(thm)],[c_400]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_10,plain,
% 3.74/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.74/1.01      | v1_relat_1(X0) ),
% 3.74/1.01      inference(cnf_transformation,[],[f61]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_411,plain,
% 3.74/1.01      ( v2_funct_2(X0,k2_relat_1(X0))
% 3.74/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0)))) ),
% 3.74/1.01      inference(forward_subsumption_resolution,
% 3.74/1.01                [status(thm)],
% 3.74/1.01                [c_401,c_10]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_25,negated_conjecture,
% 3.74/1.01      ( ~ v2_funct_2(sK3,sK0) | ~ v2_funct_1(sK2) ),
% 3.74/1.01      inference(cnf_transformation,[],[f84]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_426,plain,
% 3.74/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
% 3.74/1.01      | ~ v2_funct_1(sK2)
% 3.74/1.01      | k2_relat_1(X0) != sK0
% 3.74/1.01      | sK3 != X0 ),
% 3.74/1.01      inference(resolution_lifted,[status(thm)],[c_411,c_25]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_427,plain,
% 3.74/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3))))
% 3.74/1.01      | ~ v2_funct_1(sK2)
% 3.74/1.01      | k2_relat_1(sK3) != sK0 ),
% 3.74/1.01      inference(unflattening,[status(thm)],[c_426]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_728,plain,
% 3.74/1.01      ( ~ v2_funct_1(sK2) | sP0_iProver_split | k2_relat_1(sK3) != sK0 ),
% 3.74/1.01      inference(splitting,
% 3.74/1.01                [splitting(split),new_symbols(definition,[])],
% 3.74/1.01                [c_427]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_1192,plain,
% 3.74/1.01      ( k2_relat_1(sK3) != sK0
% 3.74/1.01      | v2_funct_1(sK2) != iProver_top
% 3.74/1.01      | sP0_iProver_split = iProver_top ),
% 3.74/1.01      inference(predicate_to_equality,[status(thm)],[c_728]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_2319,plain,
% 3.74/1.01      ( sK0 != sK0
% 3.74/1.01      | v2_funct_1(sK2) != iProver_top
% 3.74/1.01      | sP0_iProver_split = iProver_top ),
% 3.74/1.01      inference(demodulation,[status(thm)],[c_2128,c_1192]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_2320,plain,
% 3.74/1.01      ( v2_funct_1(sK2) != iProver_top
% 3.74/1.01      | sP0_iProver_split = iProver_top ),
% 3.74/1.01      inference(equality_resolution_simp,[status(thm)],[c_2319]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_727,plain,
% 3.74/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3))))
% 3.74/1.01      | ~ sP0_iProver_split ),
% 3.74/1.01      inference(splitting,
% 3.74/1.01                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 3.74/1.01                [c_427]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_1193,plain,
% 3.74/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3)))) != iProver_top
% 3.74/1.01      | sP0_iProver_split != iProver_top ),
% 3.74/1.01      inference(predicate_to_equality,[status(thm)],[c_727]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_2318,plain,
% 3.74/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 3.74/1.01      | sP0_iProver_split != iProver_top ),
% 3.74/1.01      inference(demodulation,[status(thm)],[c_2128,c_1193]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_2371,plain,
% 3.74/1.01      ( sP0_iProver_split != iProver_top ),
% 3.74/1.01      inference(superposition,[status(thm)],[c_1200,c_2318]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_6338,plain,
% 3.74/1.01      ( v2_funct_1(k6_partfun1(sK0)) != iProver_top | sK0 = k1_xboole_0 ),
% 3.74/1.01      inference(global_propositional_subsumption,
% 3.74/1.01                [status(thm)],
% 3.74/1.01                [c_2397,c_33,c_34,c_35,c_36,c_37,c_38,c_2320,c_2371]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_6339,plain,
% 3.74/1.01      ( sK0 = k1_xboole_0 | v2_funct_1(k6_partfun1(sK0)) != iProver_top ),
% 3.74/1.01      inference(renaming,[status(thm)],[c_6338]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_6342,plain,
% 3.74/1.01      ( sK0 = k1_xboole_0 ),
% 3.74/1.01      inference(superposition,[status(thm)],[c_1209,c_6339]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_1197,plain,
% 3.74/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.74/1.01      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_21,plain,
% 3.74/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.74/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.74/1.01      | ~ v1_funct_1(X0)
% 3.74/1.01      | ~ v1_funct_1(X3)
% 3.74/1.01      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.74/1.01      inference(cnf_transformation,[],[f72]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_1203,plain,
% 3.74/1.01      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 3.74/1.01      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 3.74/1.01      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.74/1.01      | v1_funct_1(X5) != iProver_top
% 3.74/1.01      | v1_funct_1(X4) != iProver_top ),
% 3.74/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_2491,plain,
% 3.74/1.01      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 3.74/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.74/1.01      | v1_funct_1(X2) != iProver_top
% 3.74/1.01      | v1_funct_1(sK3) != iProver_top ),
% 3.74/1.01      inference(superposition,[status(thm)],[c_1200,c_1203]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_2574,plain,
% 3.74/1.01      ( v1_funct_1(X2) != iProver_top
% 3.74/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.74/1.01      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 3.74/1.01      inference(global_propositional_subsumption,
% 3.74/1.01                [status(thm)],
% 3.74/1.01                [c_2491,c_36]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_2575,plain,
% 3.74/1.01      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 3.74/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.74/1.01      | v1_funct_1(X2) != iProver_top ),
% 3.74/1.01      inference(renaming,[status(thm)],[c_2574]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_2583,plain,
% 3.74/1.01      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 3.74/1.01      | v1_funct_1(sK2) != iProver_top ),
% 3.74/1.01      inference(superposition,[status(thm)],[c_1197,c_2575]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_2584,plain,
% 3.74/1.01      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 3.74/1.01      | v1_funct_1(sK2) != iProver_top ),
% 3.74/1.01      inference(light_normalisation,[status(thm)],[c_2583,c_1697]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_3427,plain,
% 3.74/1.01      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 3.74/1.01      inference(global_propositional_subsumption,
% 3.74/1.01                [status(thm)],
% 3.74/1.01                [c_2584,c_33]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_6362,plain,
% 3.74/1.01      ( k5_relat_1(sK2,sK3) = k6_partfun1(k1_xboole_0) ),
% 3.74/1.01      inference(demodulation,[status(thm)],[c_6342,c_3427]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_12,plain,
% 3.74/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.74/1.01      | v4_relat_1(X0,X1) ),
% 3.74/1.01      inference(cnf_transformation,[],[f62]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_5,plain,
% 3.74/1.01      ( ~ v4_relat_1(X0,X1)
% 3.74/1.01      | r1_tarski(k1_relat_1(X0),X1)
% 3.74/1.01      | ~ v1_relat_1(X0) ),
% 3.74/1.01      inference(cnf_transformation,[],[f55]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_360,plain,
% 3.74/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.74/1.01      | r1_tarski(k1_relat_1(X0),X1)
% 3.74/1.01      | ~ v1_relat_1(X0) ),
% 3.74/1.01      inference(resolution,[status(thm)],[c_12,c_5]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_364,plain,
% 3.74/1.01      ( r1_tarski(k1_relat_1(X0),X1)
% 3.74/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.74/1.01      inference(global_propositional_subsumption,
% 3.74/1.01                [status(thm)],
% 3.74/1.01                [c_360,c_10]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_365,plain,
% 3.74/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.74/1.01      | r1_tarski(k1_relat_1(X0),X1) ),
% 3.74/1.01      inference(renaming,[status(thm)],[c_364]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_1194,plain,
% 3.74/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.74/1.01      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 3.74/1.01      inference(predicate_to_equality,[status(thm)],[c_365]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_1965,plain,
% 3.74/1.01      ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
% 3.74/1.01      inference(superposition,[status(thm)],[c_1197,c_1194]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_6371,plain,
% 3.74/1.01      ( r1_tarski(k1_relat_1(sK2),k1_xboole_0) = iProver_top ),
% 3.74/1.01      inference(demodulation,[status(thm)],[c_6342,c_1965]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_3,plain,
% 3.74/1.01      ( r1_tarski(k1_xboole_0,X0) ),
% 3.74/1.01      inference(cnf_transformation,[],[f54]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_1213,plain,
% 3.74/1.01      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.74/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_0,plain,
% 3.74/1.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.74/1.01      inference(cnf_transformation,[],[f53]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_1215,plain,
% 3.74/1.01      ( X0 = X1
% 3.74/1.01      | r1_tarski(X0,X1) != iProver_top
% 3.74/1.01      | r1_tarski(X1,X0) != iProver_top ),
% 3.74/1.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_2132,plain,
% 3.74/1.01      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.74/1.01      inference(superposition,[status(thm)],[c_1213,c_1215]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_6532,plain,
% 3.74/1.01      ( k1_relat_1(sK2) = k1_xboole_0 ),
% 3.74/1.01      inference(superposition,[status(thm)],[c_6371,c_2132]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_7,plain,
% 3.74/1.01      ( ~ v1_relat_1(X0)
% 3.74/1.01      | k2_relat_1(X0) = k1_xboole_0
% 3.74/1.01      | k1_relat_1(X0) != k1_xboole_0 ),
% 3.74/1.01      inference(cnf_transformation,[],[f57]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_1211,plain,
% 3.74/1.01      ( k2_relat_1(X0) = k1_xboole_0
% 3.74/1.01      | k1_relat_1(X0) != k1_xboole_0
% 3.74/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.74/1.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_7081,plain,
% 3.74/1.01      ( k2_relat_1(sK2) = k1_xboole_0 | v1_relat_1(sK2) != iProver_top ),
% 3.74/1.01      inference(superposition,[status(thm)],[c_6532,c_1211]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_1310,plain,
% 3.74/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.74/1.01      | v1_relat_1(sK2) ),
% 3.74/1.01      inference(instantiation,[status(thm)],[c_10]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_1564,plain,
% 3.74/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.74/1.01      | v1_relat_1(sK2) ),
% 3.74/1.01      inference(instantiation,[status(thm)],[c_1310]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_1565,plain,
% 3.74/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.74/1.01      | v1_relat_1(sK2) = iProver_top ),
% 3.74/1.01      inference(predicate_to_equality,[status(thm)],[c_1564]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_7224,plain,
% 3.74/1.01      ( k2_relat_1(sK2) = k1_xboole_0 ),
% 3.74/1.01      inference(global_propositional_subsumption,
% 3.74/1.01                [status(thm)],
% 3.74/1.01                [c_7081,c_35,c_1565]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_8,plain,
% 3.74/1.01      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
% 3.74/1.01      | ~ v1_funct_1(X0)
% 3.74/1.01      | ~ v1_funct_1(X1)
% 3.74/1.01      | v2_funct_1(X0)
% 3.74/1.01      | ~ v2_funct_1(k5_relat_1(X0,X1))
% 3.74/1.01      | ~ v1_relat_1(X0)
% 3.74/1.01      | ~ v1_relat_1(X1) ),
% 3.74/1.01      inference(cnf_transformation,[],[f59]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_1210,plain,
% 3.74/1.01      ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) != iProver_top
% 3.74/1.01      | v1_funct_1(X0) != iProver_top
% 3.74/1.01      | v1_funct_1(X1) != iProver_top
% 3.74/1.01      | v2_funct_1(X0) = iProver_top
% 3.74/1.01      | v2_funct_1(k5_relat_1(X0,X1)) != iProver_top
% 3.74/1.01      | v1_relat_1(X0) != iProver_top
% 3.74/1.01      | v1_relat_1(X1) != iProver_top ),
% 3.74/1.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_7228,plain,
% 3.74/1.01      ( r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 3.74/1.01      | v1_funct_1(X0) != iProver_top
% 3.74/1.01      | v1_funct_1(sK2) != iProver_top
% 3.74/1.01      | v2_funct_1(k5_relat_1(sK2,X0)) != iProver_top
% 3.74/1.01      | v2_funct_1(sK2) = iProver_top
% 3.74/1.01      | v1_relat_1(X0) != iProver_top
% 3.74/1.01      | v1_relat_1(sK2) != iProver_top ),
% 3.74/1.01      inference(superposition,[status(thm)],[c_7224,c_1210]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_10352,plain,
% 3.74/1.01      ( v1_relat_1(X0) != iProver_top
% 3.74/1.01      | v1_funct_1(X0) != iProver_top
% 3.74/1.01      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 3.74/1.01      | v2_funct_1(k5_relat_1(sK2,X0)) != iProver_top ),
% 3.74/1.01      inference(global_propositional_subsumption,
% 3.74/1.01                [status(thm)],
% 3.74/1.01                [c_7228,c_33,c_35,c_1565,c_2320,c_2371]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_10353,plain,
% 3.74/1.01      ( r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 3.74/1.01      | v1_funct_1(X0) != iProver_top
% 3.74/1.01      | v2_funct_1(k5_relat_1(sK2,X0)) != iProver_top
% 3.74/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.74/1.01      inference(renaming,[status(thm)],[c_10352]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_10358,plain,
% 3.74/1.01      ( r1_tarski(k1_xboole_0,k1_relat_1(sK3)) != iProver_top
% 3.74/1.01      | v1_funct_1(sK3) != iProver_top
% 3.74/1.01      | v2_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top
% 3.74/1.01      | v1_relat_1(sK3) != iProver_top ),
% 3.74/1.01      inference(superposition,[status(thm)],[c_6362,c_10353]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_6,plain,
% 3.74/1.01      ( ~ v1_relat_1(X0)
% 3.74/1.01      | k2_relat_1(X0) != k1_xboole_0
% 3.74/1.01      | k1_relat_1(X0) = k1_xboole_0 ),
% 3.74/1.01      inference(cnf_transformation,[],[f58]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_1212,plain,
% 3.74/1.01      ( k2_relat_1(X0) != k1_xboole_0
% 3.74/1.01      | k1_relat_1(X0) = k1_xboole_0
% 3.74/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.74/1.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_2325,plain,
% 3.74/1.01      ( k1_relat_1(sK3) = k1_xboole_0
% 3.74/1.01      | sK0 != k1_xboole_0
% 3.74/1.01      | v1_relat_1(sK3) != iProver_top ),
% 3.74/1.01      inference(superposition,[status(thm)],[c_2128,c_1212]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_1445,plain,
% 3.74/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.74/1.01      | v1_relat_1(sK3) ),
% 3.74/1.01      inference(instantiation,[status(thm)],[c_10]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_1645,plain,
% 3.74/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.74/1.01      | v1_relat_1(sK3) ),
% 3.74/1.01      inference(instantiation,[status(thm)],[c_1445]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_1646,plain,
% 3.74/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.74/1.01      | v1_relat_1(sK3) = iProver_top ),
% 3.74/1.01      inference(predicate_to_equality,[status(thm)],[c_1645]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_5318,plain,
% 3.74/1.01      ( sK0 != k1_xboole_0 | k1_relat_1(sK3) = k1_xboole_0 ),
% 3.74/1.01      inference(global_propositional_subsumption,
% 3.74/1.01                [status(thm)],
% 3.74/1.01                [c_2325,c_38,c_1646]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_5319,plain,
% 3.74/1.01      ( k1_relat_1(sK3) = k1_xboole_0 | sK0 != k1_xboole_0 ),
% 3.74/1.01      inference(renaming,[status(thm)],[c_5318]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_6348,plain,
% 3.74/1.01      ( k1_relat_1(sK3) = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.74/1.01      inference(demodulation,[status(thm)],[c_6342,c_5319]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_6379,plain,
% 3.74/1.01      ( k1_relat_1(sK3) = k1_xboole_0 ),
% 3.74/1.01      inference(equality_resolution_simp,[status(thm)],[c_6348]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_10359,plain,
% 3.74/1.01      ( r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 3.74/1.01      | v1_funct_1(sK3) != iProver_top
% 3.74/1.01      | v2_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top
% 3.74/1.01      | v1_relat_1(sK3) != iProver_top ),
% 3.74/1.01      inference(light_normalisation,[status(thm)],[c_10358,c_6379]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_104,plain,
% 3.74/1.01      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.74/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_106,plain,
% 3.74/1.01      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.74/1.01      inference(instantiation,[status(thm)],[c_104]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_86,plain,
% 3.74/1.01      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 3.74/1.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(c_88,plain,
% 3.74/1.01      ( v2_funct_1(k6_partfun1(k1_xboole_0)) = iProver_top ),
% 3.74/1.01      inference(instantiation,[status(thm)],[c_86]) ).
% 3.74/1.01  
% 3.74/1.01  cnf(contradiction,plain,
% 3.74/1.01      ( $false ),
% 3.74/1.01      inference(minisat,
% 3.74/1.01                [status(thm)],
% 3.74/1.01                [c_10359,c_1646,c_106,c_88,c_38,c_36]) ).
% 3.74/1.01  
% 3.74/1.01  
% 3.74/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.74/1.01  
% 3.74/1.01  ------                               Statistics
% 3.74/1.01  
% 3.74/1.01  ------ General
% 3.74/1.01  
% 3.74/1.01  abstr_ref_over_cycles:                  0
% 3.74/1.01  abstr_ref_under_cycles:                 0
% 3.74/1.01  gc_basic_clause_elim:                   0
% 3.74/1.01  forced_gc_time:                         0
% 3.74/1.01  parsing_time:                           0.01
% 3.74/1.01  unif_index_cands_time:                  0.
% 3.74/1.01  unif_index_add_time:                    0.
% 3.74/1.01  orderings_time:                         0.
% 3.74/1.01  out_proof_time:                         0.014
% 3.74/1.01  total_time:                             0.482
% 3.74/1.01  num_of_symbols:                         55
% 3.74/1.01  num_of_terms:                           17017
% 3.74/1.01  
% 3.74/1.01  ------ Preprocessing
% 3.74/1.01  
% 3.74/1.01  num_of_splits:                          1
% 3.74/1.01  num_of_split_atoms:                     1
% 3.74/1.01  num_of_reused_defs:                     0
% 3.74/1.01  num_eq_ax_congr_red:                    23
% 3.74/1.01  num_of_sem_filtered_clauses:            1
% 3.74/1.01  num_of_subtypes:                        0
% 3.74/1.01  monotx_restored_types:                  0
% 3.74/1.01  sat_num_of_epr_types:                   0
% 3.74/1.01  sat_num_of_non_cyclic_types:            0
% 3.74/1.01  sat_guarded_non_collapsed_types:        0
% 3.74/1.01  num_pure_diseq_elim:                    0
% 3.74/1.01  simp_replaced_by:                       0
% 3.74/1.01  res_preprocessed:                       139
% 3.74/1.01  prep_upred:                             0
% 3.74/1.01  prep_unflattend:                        17
% 3.74/1.01  smt_new_axioms:                         0
% 3.74/1.01  pred_elim_cands:                        6
% 3.74/1.01  pred_elim:                              4
% 3.74/1.01  pred_elim_cl:                           6
% 3.74/1.01  pred_elim_cycles:                       6
% 3.74/1.01  merged_defs:                            0
% 3.74/1.01  merged_defs_ncl:                        0
% 3.74/1.01  bin_hyper_res:                          0
% 3.74/1.01  prep_cycles:                            4
% 3.74/1.01  pred_elim_time:                         0.01
% 3.74/1.01  splitting_time:                         0.
% 3.74/1.01  sem_filter_time:                        0.
% 3.74/1.01  monotx_time:                            0.001
% 3.74/1.01  subtype_inf_time:                       0.
% 3.74/1.01  
% 3.74/1.01  ------ Problem properties
% 3.74/1.01  
% 3.74/1.01  clauses:                                27
% 3.74/1.01  conjectures:                            6
% 3.74/1.01  epr:                                    7
% 3.74/1.01  horn:                                   26
% 3.74/1.01  ground:                                 8
% 3.74/1.01  unary:                                  10
% 3.74/1.01  binary:                                 5
% 3.74/1.01  lits:                                   87
% 3.74/1.01  lits_eq:                                14
% 3.74/1.01  fd_pure:                                0
% 3.74/1.01  fd_pseudo:                              0
% 3.74/1.01  fd_cond:                                1
% 3.74/1.01  fd_pseudo_cond:                         1
% 3.74/1.01  ac_symbols:                             0
% 3.74/1.01  
% 3.74/1.01  ------ Propositional Solver
% 3.74/1.01  
% 3.74/1.01  prop_solver_calls:                      33
% 3.74/1.01  prop_fast_solver_calls:                 1552
% 3.74/1.01  smt_solver_calls:                       0
% 3.74/1.01  smt_fast_solver_calls:                  0
% 3.74/1.01  prop_num_of_clauses:                    5650
% 3.74/1.01  prop_preprocess_simplified:             11258
% 3.74/1.01  prop_fo_subsumed:                       161
% 3.74/1.01  prop_solver_time:                       0.
% 3.74/1.01  smt_solver_time:                        0.
% 3.74/1.01  smt_fast_solver_time:                   0.
% 3.74/1.01  prop_fast_solver_time:                  0.
% 3.74/1.01  prop_unsat_core_time:                   0.
% 3.74/1.01  
% 3.74/1.01  ------ QBF
% 3.74/1.01  
% 3.74/1.01  qbf_q_res:                              0
% 3.74/1.01  qbf_num_tautologies:                    0
% 3.74/1.01  qbf_prep_cycles:                        0
% 3.74/1.01  
% 3.74/1.01  ------ BMC1
% 3.74/1.01  
% 3.74/1.01  bmc1_current_bound:                     -1
% 3.74/1.01  bmc1_last_solved_bound:                 -1
% 3.74/1.01  bmc1_unsat_core_size:                   -1
% 3.74/1.01  bmc1_unsat_core_parents_size:           -1
% 3.74/1.01  bmc1_merge_next_fun:                    0
% 3.74/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.74/1.01  
% 3.74/1.01  ------ Instantiation
% 3.74/1.01  
% 3.74/1.01  inst_num_of_clauses:                    1409
% 3.74/1.01  inst_num_in_passive:                    62
% 3.74/1.01  inst_num_in_active:                     761
% 3.74/1.01  inst_num_in_unprocessed:                586
% 3.74/1.01  inst_num_of_loops:                      890
% 3.74/1.01  inst_num_of_learning_restarts:          0
% 3.74/1.01  inst_num_moves_active_passive:          124
% 3.74/1.01  inst_lit_activity:                      0
% 3.74/1.01  inst_lit_activity_moves:                1
% 3.74/1.01  inst_num_tautologies:                   0
% 3.74/1.01  inst_num_prop_implied:                  0
% 3.74/1.01  inst_num_existing_simplified:           0
% 3.74/1.01  inst_num_eq_res_simplified:             0
% 3.74/1.01  inst_num_child_elim:                    0
% 3.74/1.01  inst_num_of_dismatching_blockings:      382
% 3.74/1.01  inst_num_of_non_proper_insts:           1585
% 3.74/1.01  inst_num_of_duplicates:                 0
% 3.74/1.01  inst_inst_num_from_inst_to_res:         0
% 3.74/1.01  inst_dismatching_checking_time:         0.
% 3.74/1.01  
% 3.74/1.01  ------ Resolution
% 3.74/1.01  
% 3.74/1.01  res_num_of_clauses:                     0
% 3.74/1.01  res_num_in_passive:                     0
% 3.74/1.01  res_num_in_active:                      0
% 3.74/1.01  res_num_of_loops:                       143
% 3.74/1.01  res_forward_subset_subsumed:            56
% 3.74/1.01  res_backward_subset_subsumed:           0
% 3.74/1.01  res_forward_subsumed:                   0
% 3.74/1.01  res_backward_subsumed:                  0
% 3.74/1.01  res_forward_subsumption_resolution:     4
% 3.74/1.01  res_backward_subsumption_resolution:    0
% 3.74/1.01  res_clause_to_clause_subsumption:       780
% 3.74/1.01  res_orphan_elimination:                 0
% 3.74/1.01  res_tautology_del:                      63
% 3.74/1.01  res_num_eq_res_simplified:              1
% 3.74/1.01  res_num_sel_changes:                    0
% 3.74/1.01  res_moves_from_active_to_pass:          0
% 3.74/1.01  
% 3.74/1.01  ------ Superposition
% 3.74/1.01  
% 3.74/1.01  sup_time_total:                         0.
% 3.74/1.01  sup_time_generating:                    0.
% 3.74/1.01  sup_time_sim_full:                      0.
% 3.74/1.01  sup_time_sim_immed:                     0.
% 3.74/1.01  
% 3.74/1.01  sup_num_of_clauses:                     304
% 3.74/1.01  sup_num_in_active:                      130
% 3.74/1.01  sup_num_in_passive:                     174
% 3.74/1.01  sup_num_of_loops:                       177
% 3.74/1.01  sup_fw_superposition:                   186
% 3.74/1.01  sup_bw_superposition:                   195
% 3.74/1.01  sup_immediate_simplified:               112
% 3.74/1.01  sup_given_eliminated:                   1
% 3.74/1.01  comparisons_done:                       0
% 3.74/1.01  comparisons_avoided:                    0
% 3.74/1.01  
% 3.74/1.01  ------ Simplifications
% 3.74/1.01  
% 3.74/1.01  
% 3.74/1.01  sim_fw_subset_subsumed:                 34
% 3.74/1.01  sim_bw_subset_subsumed:                 16
% 3.74/1.01  sim_fw_subsumed:                        15
% 3.74/1.01  sim_bw_subsumed:                        3
% 3.74/1.01  sim_fw_subsumption_res:                 0
% 3.74/1.01  sim_bw_subsumption_res:                 0
% 3.74/1.01  sim_tautology_del:                      0
% 3.74/1.01  sim_eq_tautology_del:                   21
% 3.74/1.01  sim_eq_res_simp:                        2
% 3.74/1.01  sim_fw_demodulated:                     8
% 3.74/1.01  sim_bw_demodulated:                     42
% 3.74/1.01  sim_light_normalised:                   66
% 3.74/1.01  sim_joinable_taut:                      0
% 3.74/1.01  sim_joinable_simp:                      0
% 3.74/1.01  sim_ac_normalised:                      0
% 3.74/1.01  sim_smt_subsumption:                    0
% 3.74/1.01  
%------------------------------------------------------------------------------
