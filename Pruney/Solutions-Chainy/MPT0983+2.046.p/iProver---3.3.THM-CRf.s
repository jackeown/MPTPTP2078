%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:01:54 EST 2020

% Result     : Theorem 3.16s
% Output     : CNFRefutation 3.16s
% Verified   : 
% Statistics : Number of formulae       :  162 (1235 expanded)
%              Number of clauses        :   98 ( 398 expanded)
%              Number of leaves         :   18 ( 296 expanded)
%              Depth                    :   22
%              Number of atoms          :  542 (7931 expanded)
%              Number of equality atoms :  177 ( 635 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f11,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f54,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f42,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f12,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f67,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f43,f55])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f28])).

fof(f53,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f24])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

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

fof(f34,plain,(
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
    inference(flattening,[],[f34])).

fof(f39,plain,(
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

fof(f38,plain,
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

fof(f40,plain,
    ( ( ~ v2_funct_2(sK3,sK0)
      | ~ v2_funct_1(sK2) )
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f35,f39,f38])).

fof(f65,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f40])).

fof(f59,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f61,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f40])).

fof(f62,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f64,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f40])).

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

fof(f32,plain,(
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
    inference(flattening,[],[f32])).

fof(f57,plain,(
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
    inference(cnf_transformation,[],[f33])).

fof(f60,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f63,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f40])).

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

fof(f30,plain,(
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
    inference(flattening,[],[f30])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

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

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f69,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f51])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f66,plain,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_643,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1056,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_643])).

cnf(c_13,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_636,plain,
    ( m1_subset_1(k6_partfun1(X0_48),k1_zfmisc_1(k2_zfmisc_1(X0_48,X0_48))) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1063,plain,
    ( m1_subset_1(k6_partfun1(X0_48),k1_zfmisc_1(k2_zfmisc_1(X0_48,X0_48))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_636])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_640,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | ~ v1_xboole_0(X1_48)
    | v1_xboole_0(X0_48) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1059,plain,
    ( m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48))) != iProver_top
    | v1_xboole_0(X1_48) != iProver_top
    | v1_xboole_0(X0_48) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_640])).

cnf(c_2049,plain,
    ( v1_xboole_0(X0_48) != iProver_top
    | v1_xboole_0(k6_partfun1(X0_48)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1063,c_1059])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_642,plain,
    ( ~ v1_xboole_0(X0_48)
    | k1_xboole_0 = X0_48 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1057,plain,
    ( k1_xboole_0 = X0_48
    | v1_xboole_0(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_642])).

cnf(c_3474,plain,
    ( k6_partfun1(X0_48) = k1_xboole_0
    | v1_xboole_0(X0_48) != iProver_top ),
    inference(superposition,[status(thm)],[c_2049,c_1057])).

cnf(c_3521,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1056,c_3474])).

cnf(c_2,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_641,plain,
    ( v2_funct_1(k6_partfun1(X0_48)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1058,plain,
    ( v2_funct_1(k6_partfun1(X0_48)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_641])).

cnf(c_3536,plain,
    ( v2_funct_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3521,c_1058])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_638,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | ~ m1_subset_1(X3_48,k1_zfmisc_1(k2_zfmisc_1(X4_48,X5_48)))
    | m1_subset_1(k1_partfun1(X4_48,X5_48,X1_48,X2_48,X3_48,X0_48),k1_zfmisc_1(k2_zfmisc_1(X4_48,X2_48)))
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(X3_48) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1061,plain,
    ( m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48))) != iProver_top
    | m1_subset_1(X3_48,k1_zfmisc_1(k2_zfmisc_1(X4_48,X5_48))) != iProver_top
    | m1_subset_1(k1_partfun1(X4_48,X5_48,X1_48,X2_48,X3_48,X0_48),k1_zfmisc_1(k2_zfmisc_1(X4_48,X2_48))) = iProver_top
    | v1_funct_1(X3_48) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_638])).

cnf(c_8,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_18,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_415,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_18])).

cnf(c_416,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_415])).

cnf(c_43,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_418,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_416,c_43])).

cnf(c_625,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_418])).

cnf(c_1075,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_625])).

cnf(c_2109,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1061,c_1075])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_25,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_27,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_28,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_30,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2364,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2109,c_25,c_27,c_28,c_30])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v2_funct_1(X3)
    | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_634,plain,
    ( ~ v1_funct_2(X0_48,X1_48,X2_48)
    | ~ v1_funct_2(X3_48,X4_48,X1_48)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | ~ m1_subset_1(X3_48,k1_zfmisc_1(k2_zfmisc_1(X4_48,X1_48)))
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(X3_48)
    | v2_funct_1(X3_48)
    | ~ v2_funct_1(k1_partfun1(X4_48,X1_48,X1_48,X2_48,X3_48,X0_48))
    | k1_xboole_0 = X2_48 ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1065,plain,
    ( k1_xboole_0 = X0_48
    | v1_funct_2(X1_48,X2_48,X0_48) != iProver_top
    | v1_funct_2(X3_48,X4_48,X2_48) != iProver_top
    | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_48,X0_48))) != iProver_top
    | m1_subset_1(X3_48,k1_zfmisc_1(k2_zfmisc_1(X4_48,X2_48))) != iProver_top
    | v1_funct_1(X3_48) != iProver_top
    | v1_funct_1(X1_48) != iProver_top
    | v2_funct_1(X3_48) = iProver_top
    | v2_funct_1(k1_partfun1(X4_48,X2_48,X2_48,X0_48,X3_48,X1_48)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_634])).

cnf(c_2390,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2364,c_1065])).

cnf(c_23,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_26,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_20,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_29,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_73,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_75,plain,
    ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_73])).

cnf(c_14,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_429,plain,
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
    inference(resolution_lifted,[status(thm)],[c_14,c_18])).

cnf(c_430,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X0)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0
    | k6_partfun1(sK0) != k6_partfun1(sK0) ),
    inference(unflattening,[status(thm)],[c_429])).

cnf(c_504,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_430])).

cnf(c_624,plain,
    ( ~ v1_funct_2(X0_48,X1_48,sK0)
    | ~ v1_funct_2(X2_48,sK0,X1_48)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,sK0)))
    | ~ m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(sK0,X1_48)))
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(X2_48)
    | k1_partfun1(sK0,X1_48,X1_48,sK0,X2_48,X0_48) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1_48,sK0,X0_48) = sK0 ),
    inference(subtyping,[status(esa)],[c_504])).

cnf(c_1076,plain,
    ( k1_partfun1(sK0,X0_48,X0_48,sK0,X1_48,X2_48) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X0_48,sK0,X2_48) = sK0
    | v1_funct_2(X2_48,X0_48,sK0) != iProver_top
    | v1_funct_2(X1_48,sK0,X0_48) != iProver_top
    | m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,sK0))) != iProver_top
    | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_48))) != iProver_top
    | v1_funct_1(X2_48) != iProver_top
    | v1_funct_1(X1_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_624])).

cnf(c_1921,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1076])).

cnf(c_633,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1066,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_633])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_639,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | k2_relset_1(X1_48,X2_48,X0_48) = k2_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1060,plain,
    ( k2_relset_1(X0_48,X1_48,X2_48) = k2_relat_1(X2_48)
    | m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_639])).

cnf(c_1606,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1066,c_1060])).

cnf(c_1922,plain,
    ( k2_relat_1(sK3) = sK0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1921,c_1606])).

cnf(c_1925,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1922,c_25,c_26,c_27,c_28,c_29,c_30])).

cnf(c_4,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_9,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_333,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X0)
    | X0 != X1
    | k2_relat_1(X0) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_9])).

cnf(c_334,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_333])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_344,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0)))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_334,c_3])).

cnf(c_17,negated_conjecture,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_359,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
    | ~ v2_funct_1(sK2)
    | k2_relat_1(X0) != sK0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_344,c_17])).

cnf(c_360,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3))))
    | ~ v2_funct_1(sK2)
    | k2_relat_1(sK3) != sK0 ),
    inference(unflattening,[status(thm)],[c_359])).

cnf(c_627,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_48,k2_relat_1(sK3))))
    | ~ v2_funct_1(sK2)
    | k2_relat_1(sK3) != sK0 ),
    inference(subtyping,[status(esa)],[c_360])).

cnf(c_645,plain,
    ( ~ v2_funct_1(sK2)
    | sP0_iProver_split
    | k2_relat_1(sK3) != sK0 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_627])).

cnf(c_1072,plain,
    ( k2_relat_1(sK3) != sK0
    | v2_funct_1(sK2) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_645])).

cnf(c_1930,plain,
    ( sK0 != sK0
    | v2_funct_1(sK2) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_1925,c_1072])).

cnf(c_1931,plain,
    ( v2_funct_1(sK2) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_1930])).

cnf(c_644,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_48,k2_relat_1(sK3))))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_627])).

cnf(c_1073,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_48,k2_relat_1(sK3)))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_644])).

cnf(c_1929,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_48,sK0))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(demodulation,[status(thm)],[c_1925,c_1073])).

cnf(c_1994,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_1066,c_1929])).

cnf(c_3010,plain,
    ( sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2390,c_25,c_26,c_27,c_28,c_29,c_30,c_75,c_1931,c_1994])).

cnf(c_630,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1069,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_630])).

cnf(c_2048,plain,
    ( v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1069,c_1059])).

cnf(c_3016,plain,
    ( v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3010,c_2048])).

cnf(c_79,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_651,plain,
    ( ~ v1_xboole_0(X0_48)
    | v1_xboole_0(X1_48)
    | X1_48 != X0_48 ),
    theory(equality)).

cnf(c_1387,plain,
    ( v1_xboole_0(X0_48)
    | ~ v1_xboole_0(k1_xboole_0)
    | X0_48 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_651])).

cnf(c_1388,plain,
    ( X0_48 != k1_xboole_0
    | v1_xboole_0(X0_48) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1387])).

cnf(c_1390,plain,
    ( sK0 != k1_xboole_0
    | v1_xboole_0(sK0) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1388])).

cnf(c_3158,plain,
    ( v1_xboole_0(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3016,c_25,c_26,c_27,c_28,c_29,c_30,c_75,c_79,c_1390,c_1931,c_1994,c_2048,c_2390])).

cnf(c_3163,plain,
    ( sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3158,c_1057])).

cnf(c_2427,plain,
    ( v2_funct_1(sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1931,c_1994])).

cnf(c_3169,plain,
    ( v2_funct_1(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3163,c_2427])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3536,c_3169])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:51:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.16/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.01  
% 3.16/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.16/1.01  
% 3.16/1.01  ------  iProver source info
% 3.16/1.01  
% 3.16/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.16/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.16/1.01  git: non_committed_changes: false
% 3.16/1.01  git: last_make_outside_of_git: false
% 3.16/1.01  
% 3.16/1.01  ------ 
% 3.16/1.01  
% 3.16/1.01  ------ Input Options
% 3.16/1.01  
% 3.16/1.01  --out_options                           all
% 3.16/1.01  --tptp_safe_out                         true
% 3.16/1.01  --problem_path                          ""
% 3.16/1.01  --include_path                          ""
% 3.16/1.01  --clausifier                            res/vclausify_rel
% 3.16/1.01  --clausifier_options                    --mode clausify
% 3.16/1.01  --stdin                                 false
% 3.16/1.01  --stats_out                             all
% 3.16/1.01  
% 3.16/1.01  ------ General Options
% 3.16/1.01  
% 3.16/1.01  --fof                                   false
% 3.16/1.01  --time_out_real                         305.
% 3.16/1.01  --time_out_virtual                      -1.
% 3.16/1.01  --symbol_type_check                     false
% 3.16/1.01  --clausify_out                          false
% 3.16/1.01  --sig_cnt_out                           false
% 3.16/1.01  --trig_cnt_out                          false
% 3.16/1.01  --trig_cnt_out_tolerance                1.
% 3.16/1.01  --trig_cnt_out_sk_spl                   false
% 3.16/1.01  --abstr_cl_out                          false
% 3.16/1.01  
% 3.16/1.01  ------ Global Options
% 3.16/1.01  
% 3.16/1.01  --schedule                              default
% 3.16/1.01  --add_important_lit                     false
% 3.16/1.01  --prop_solver_per_cl                    1000
% 3.16/1.01  --min_unsat_core                        false
% 3.16/1.01  --soft_assumptions                      false
% 3.16/1.01  --soft_lemma_size                       3
% 3.16/1.01  --prop_impl_unit_size                   0
% 3.16/1.01  --prop_impl_unit                        []
% 3.16/1.01  --share_sel_clauses                     true
% 3.16/1.01  --reset_solvers                         false
% 3.16/1.01  --bc_imp_inh                            [conj_cone]
% 3.16/1.01  --conj_cone_tolerance                   3.
% 3.16/1.01  --extra_neg_conj                        none
% 3.16/1.01  --large_theory_mode                     true
% 3.16/1.01  --prolific_symb_bound                   200
% 3.16/1.01  --lt_threshold                          2000
% 3.16/1.01  --clause_weak_htbl                      true
% 3.16/1.01  --gc_record_bc_elim                     false
% 3.16/1.01  
% 3.16/1.01  ------ Preprocessing Options
% 3.16/1.01  
% 3.16/1.01  --preprocessing_flag                    true
% 3.16/1.01  --time_out_prep_mult                    0.1
% 3.16/1.01  --splitting_mode                        input
% 3.16/1.01  --splitting_grd                         true
% 3.16/1.01  --splitting_cvd                         false
% 3.16/1.01  --splitting_cvd_svl                     false
% 3.16/1.01  --splitting_nvd                         32
% 3.16/1.01  --sub_typing                            true
% 3.16/1.01  --prep_gs_sim                           true
% 3.16/1.01  --prep_unflatten                        true
% 3.16/1.01  --prep_res_sim                          true
% 3.16/1.01  --prep_upred                            true
% 3.16/1.01  --prep_sem_filter                       exhaustive
% 3.16/1.01  --prep_sem_filter_out                   false
% 3.16/1.01  --pred_elim                             true
% 3.16/1.01  --res_sim_input                         true
% 3.16/1.01  --eq_ax_congr_red                       true
% 3.16/1.01  --pure_diseq_elim                       true
% 3.16/1.01  --brand_transform                       false
% 3.16/1.01  --non_eq_to_eq                          false
% 3.16/1.01  --prep_def_merge                        true
% 3.16/1.01  --prep_def_merge_prop_impl              false
% 3.16/1.01  --prep_def_merge_mbd                    true
% 3.16/1.01  --prep_def_merge_tr_red                 false
% 3.16/1.01  --prep_def_merge_tr_cl                  false
% 3.16/1.01  --smt_preprocessing                     true
% 3.16/1.01  --smt_ac_axioms                         fast
% 3.16/1.01  --preprocessed_out                      false
% 3.16/1.01  --preprocessed_stats                    false
% 3.16/1.01  
% 3.16/1.01  ------ Abstraction refinement Options
% 3.16/1.01  
% 3.16/1.01  --abstr_ref                             []
% 3.16/1.01  --abstr_ref_prep                        false
% 3.16/1.01  --abstr_ref_until_sat                   false
% 3.16/1.01  --abstr_ref_sig_restrict                funpre
% 3.16/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.16/1.01  --abstr_ref_under                       []
% 3.16/1.01  
% 3.16/1.01  ------ SAT Options
% 3.16/1.01  
% 3.16/1.01  --sat_mode                              false
% 3.16/1.01  --sat_fm_restart_options                ""
% 3.16/1.01  --sat_gr_def                            false
% 3.16/1.01  --sat_epr_types                         true
% 3.16/1.01  --sat_non_cyclic_types                  false
% 3.16/1.01  --sat_finite_models                     false
% 3.16/1.01  --sat_fm_lemmas                         false
% 3.16/1.01  --sat_fm_prep                           false
% 3.16/1.01  --sat_fm_uc_incr                        true
% 3.16/1.01  --sat_out_model                         small
% 3.16/1.01  --sat_out_clauses                       false
% 3.16/1.01  
% 3.16/1.01  ------ QBF Options
% 3.16/1.01  
% 3.16/1.01  --qbf_mode                              false
% 3.16/1.01  --qbf_elim_univ                         false
% 3.16/1.01  --qbf_dom_inst                          none
% 3.16/1.01  --qbf_dom_pre_inst                      false
% 3.16/1.01  --qbf_sk_in                             false
% 3.16/1.01  --qbf_pred_elim                         true
% 3.16/1.01  --qbf_split                             512
% 3.16/1.01  
% 3.16/1.01  ------ BMC1 Options
% 3.16/1.01  
% 3.16/1.01  --bmc1_incremental                      false
% 3.16/1.01  --bmc1_axioms                           reachable_all
% 3.16/1.01  --bmc1_min_bound                        0
% 3.16/1.01  --bmc1_max_bound                        -1
% 3.16/1.01  --bmc1_max_bound_default                -1
% 3.16/1.01  --bmc1_symbol_reachability              true
% 3.16/1.01  --bmc1_property_lemmas                  false
% 3.16/1.01  --bmc1_k_induction                      false
% 3.16/1.01  --bmc1_non_equiv_states                 false
% 3.16/1.01  --bmc1_deadlock                         false
% 3.16/1.01  --bmc1_ucm                              false
% 3.16/1.01  --bmc1_add_unsat_core                   none
% 3.16/1.01  --bmc1_unsat_core_children              false
% 3.16/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.16/1.01  --bmc1_out_stat                         full
% 3.16/1.01  --bmc1_ground_init                      false
% 3.16/1.01  --bmc1_pre_inst_next_state              false
% 3.16/1.01  --bmc1_pre_inst_state                   false
% 3.16/1.01  --bmc1_pre_inst_reach_state             false
% 3.16/1.01  --bmc1_out_unsat_core                   false
% 3.16/1.01  --bmc1_aig_witness_out                  false
% 3.16/1.01  --bmc1_verbose                          false
% 3.16/1.01  --bmc1_dump_clauses_tptp                false
% 3.16/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.16/1.01  --bmc1_dump_file                        -
% 3.16/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.16/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.16/1.01  --bmc1_ucm_extend_mode                  1
% 3.16/1.01  --bmc1_ucm_init_mode                    2
% 3.16/1.01  --bmc1_ucm_cone_mode                    none
% 3.16/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.16/1.01  --bmc1_ucm_relax_model                  4
% 3.16/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.16/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.16/1.01  --bmc1_ucm_layered_model                none
% 3.16/1.01  --bmc1_ucm_max_lemma_size               10
% 3.16/1.01  
% 3.16/1.01  ------ AIG Options
% 3.16/1.01  
% 3.16/1.01  --aig_mode                              false
% 3.16/1.01  
% 3.16/1.01  ------ Instantiation Options
% 3.16/1.01  
% 3.16/1.01  --instantiation_flag                    true
% 3.16/1.01  --inst_sos_flag                         false
% 3.16/1.01  --inst_sos_phase                        true
% 3.16/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.16/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.16/1.01  --inst_lit_sel_side                     num_symb
% 3.16/1.01  --inst_solver_per_active                1400
% 3.16/1.01  --inst_solver_calls_frac                1.
% 3.16/1.01  --inst_passive_queue_type               priority_queues
% 3.16/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.16/1.01  --inst_passive_queues_freq              [25;2]
% 3.16/1.01  --inst_dismatching                      true
% 3.16/1.01  --inst_eager_unprocessed_to_passive     true
% 3.16/1.01  --inst_prop_sim_given                   true
% 3.16/1.01  --inst_prop_sim_new                     false
% 3.16/1.01  --inst_subs_new                         false
% 3.16/1.01  --inst_eq_res_simp                      false
% 3.16/1.01  --inst_subs_given                       false
% 3.16/1.01  --inst_orphan_elimination               true
% 3.16/1.01  --inst_learning_loop_flag               true
% 3.16/1.01  --inst_learning_start                   3000
% 3.16/1.01  --inst_learning_factor                  2
% 3.16/1.01  --inst_start_prop_sim_after_learn       3
% 3.16/1.01  --inst_sel_renew                        solver
% 3.16/1.01  --inst_lit_activity_flag                true
% 3.16/1.01  --inst_restr_to_given                   false
% 3.16/1.01  --inst_activity_threshold               500
% 3.16/1.01  --inst_out_proof                        true
% 3.16/1.01  
% 3.16/1.01  ------ Resolution Options
% 3.16/1.01  
% 3.16/1.01  --resolution_flag                       true
% 3.16/1.01  --res_lit_sel                           adaptive
% 3.16/1.01  --res_lit_sel_side                      none
% 3.16/1.01  --res_ordering                          kbo
% 3.16/1.01  --res_to_prop_solver                    active
% 3.16/1.01  --res_prop_simpl_new                    false
% 3.16/1.01  --res_prop_simpl_given                  true
% 3.16/1.01  --res_passive_queue_type                priority_queues
% 3.16/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.16/1.01  --res_passive_queues_freq               [15;5]
% 3.16/1.01  --res_forward_subs                      full
% 3.16/1.01  --res_backward_subs                     full
% 3.16/1.01  --res_forward_subs_resolution           true
% 3.16/1.01  --res_backward_subs_resolution          true
% 3.16/1.01  --res_orphan_elimination                true
% 3.16/1.01  --res_time_limit                        2.
% 3.16/1.01  --res_out_proof                         true
% 3.16/1.01  
% 3.16/1.01  ------ Superposition Options
% 3.16/1.01  
% 3.16/1.01  --superposition_flag                    true
% 3.16/1.01  --sup_passive_queue_type                priority_queues
% 3.16/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.16/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.16/1.01  --demod_completeness_check              fast
% 3.16/1.01  --demod_use_ground                      true
% 3.16/1.01  --sup_to_prop_solver                    passive
% 3.16/1.01  --sup_prop_simpl_new                    true
% 3.16/1.01  --sup_prop_simpl_given                  true
% 3.16/1.01  --sup_fun_splitting                     false
% 3.16/1.01  --sup_smt_interval                      50000
% 3.16/1.01  
% 3.16/1.01  ------ Superposition Simplification Setup
% 3.16/1.01  
% 3.16/1.01  --sup_indices_passive                   []
% 3.16/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.16/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/1.01  --sup_full_bw                           [BwDemod]
% 3.16/1.01  --sup_immed_triv                        [TrivRules]
% 3.16/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.16/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/1.01  --sup_immed_bw_main                     []
% 3.16/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.16/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.16/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.16/1.01  
% 3.16/1.01  ------ Combination Options
% 3.16/1.01  
% 3.16/1.01  --comb_res_mult                         3
% 3.16/1.01  --comb_sup_mult                         2
% 3.16/1.01  --comb_inst_mult                        10
% 3.16/1.01  
% 3.16/1.01  ------ Debug Options
% 3.16/1.01  
% 3.16/1.01  --dbg_backtrace                         false
% 3.16/1.01  --dbg_dump_prop_clauses                 false
% 3.16/1.01  --dbg_dump_prop_clauses_file            -
% 3.16/1.01  --dbg_out_stat                          false
% 3.16/1.01  ------ Parsing...
% 3.16/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.16/1.01  
% 3.16/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.16/1.01  
% 3.16/1.01  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.16/1.01  
% 3.16/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.16/1.01  ------ Proving...
% 3.16/1.01  ------ Problem Properties 
% 3.16/1.01  
% 3.16/1.01  
% 3.16/1.01  clauses                                 21
% 3.16/1.01  conjectures                             6
% 3.16/1.01  EPR                                     6
% 3.16/1.01  Horn                                    20
% 3.16/1.01  unary                                   9
% 3.16/1.01  binary                                  4
% 3.16/1.01  lits                                    66
% 3.16/1.01  lits eq                                 9
% 3.16/1.01  fd_pure                                 0
% 3.16/1.01  fd_pseudo                               0
% 3.16/1.01  fd_cond                                 2
% 3.16/1.01  fd_pseudo_cond                          0
% 3.16/1.01  AC symbols                              0
% 3.16/1.01  
% 3.16/1.01  ------ Schedule dynamic 5 is on 
% 3.16/1.01  
% 3.16/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.16/1.01  
% 3.16/1.01  
% 3.16/1.01  ------ 
% 3.16/1.01  Current options:
% 3.16/1.01  ------ 
% 3.16/1.01  
% 3.16/1.01  ------ Input Options
% 3.16/1.01  
% 3.16/1.01  --out_options                           all
% 3.16/1.01  --tptp_safe_out                         true
% 3.16/1.01  --problem_path                          ""
% 3.16/1.01  --include_path                          ""
% 3.16/1.01  --clausifier                            res/vclausify_rel
% 3.16/1.01  --clausifier_options                    --mode clausify
% 3.16/1.01  --stdin                                 false
% 3.16/1.01  --stats_out                             all
% 3.16/1.01  
% 3.16/1.01  ------ General Options
% 3.16/1.01  
% 3.16/1.01  --fof                                   false
% 3.16/1.01  --time_out_real                         305.
% 3.16/1.01  --time_out_virtual                      -1.
% 3.16/1.01  --symbol_type_check                     false
% 3.16/1.01  --clausify_out                          false
% 3.16/1.01  --sig_cnt_out                           false
% 3.16/1.01  --trig_cnt_out                          false
% 3.16/1.01  --trig_cnt_out_tolerance                1.
% 3.16/1.01  --trig_cnt_out_sk_spl                   false
% 3.16/1.01  --abstr_cl_out                          false
% 3.16/1.01  
% 3.16/1.01  ------ Global Options
% 3.16/1.01  
% 3.16/1.01  --schedule                              default
% 3.16/1.01  --add_important_lit                     false
% 3.16/1.01  --prop_solver_per_cl                    1000
% 3.16/1.01  --min_unsat_core                        false
% 3.16/1.01  --soft_assumptions                      false
% 3.16/1.01  --soft_lemma_size                       3
% 3.16/1.01  --prop_impl_unit_size                   0
% 3.16/1.01  --prop_impl_unit                        []
% 3.16/1.01  --share_sel_clauses                     true
% 3.16/1.01  --reset_solvers                         false
% 3.16/1.01  --bc_imp_inh                            [conj_cone]
% 3.16/1.01  --conj_cone_tolerance                   3.
% 3.16/1.01  --extra_neg_conj                        none
% 3.16/1.01  --large_theory_mode                     true
% 3.16/1.01  --prolific_symb_bound                   200
% 3.16/1.01  --lt_threshold                          2000
% 3.16/1.01  --clause_weak_htbl                      true
% 3.16/1.01  --gc_record_bc_elim                     false
% 3.16/1.01  
% 3.16/1.01  ------ Preprocessing Options
% 3.16/1.01  
% 3.16/1.01  --preprocessing_flag                    true
% 3.16/1.01  --time_out_prep_mult                    0.1
% 3.16/1.01  --splitting_mode                        input
% 3.16/1.01  --splitting_grd                         true
% 3.16/1.01  --splitting_cvd                         false
% 3.16/1.01  --splitting_cvd_svl                     false
% 3.16/1.01  --splitting_nvd                         32
% 3.16/1.01  --sub_typing                            true
% 3.16/1.01  --prep_gs_sim                           true
% 3.16/1.01  --prep_unflatten                        true
% 3.16/1.01  --prep_res_sim                          true
% 3.16/1.01  --prep_upred                            true
% 3.16/1.01  --prep_sem_filter                       exhaustive
% 3.16/1.01  --prep_sem_filter_out                   false
% 3.16/1.01  --pred_elim                             true
% 3.16/1.01  --res_sim_input                         true
% 3.16/1.01  --eq_ax_congr_red                       true
% 3.16/1.01  --pure_diseq_elim                       true
% 3.16/1.01  --brand_transform                       false
% 3.16/1.01  --non_eq_to_eq                          false
% 3.16/1.01  --prep_def_merge                        true
% 3.16/1.01  --prep_def_merge_prop_impl              false
% 3.16/1.01  --prep_def_merge_mbd                    true
% 3.16/1.01  --prep_def_merge_tr_red                 false
% 3.16/1.01  --prep_def_merge_tr_cl                  false
% 3.16/1.01  --smt_preprocessing                     true
% 3.16/1.01  --smt_ac_axioms                         fast
% 3.16/1.01  --preprocessed_out                      false
% 3.16/1.01  --preprocessed_stats                    false
% 3.16/1.01  
% 3.16/1.01  ------ Abstraction refinement Options
% 3.16/1.01  
% 3.16/1.01  --abstr_ref                             []
% 3.16/1.01  --abstr_ref_prep                        false
% 3.16/1.01  --abstr_ref_until_sat                   false
% 3.16/1.01  --abstr_ref_sig_restrict                funpre
% 3.16/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.16/1.01  --abstr_ref_under                       []
% 3.16/1.01  
% 3.16/1.01  ------ SAT Options
% 3.16/1.01  
% 3.16/1.01  --sat_mode                              false
% 3.16/1.01  --sat_fm_restart_options                ""
% 3.16/1.01  --sat_gr_def                            false
% 3.16/1.01  --sat_epr_types                         true
% 3.16/1.01  --sat_non_cyclic_types                  false
% 3.16/1.01  --sat_finite_models                     false
% 3.16/1.01  --sat_fm_lemmas                         false
% 3.16/1.01  --sat_fm_prep                           false
% 3.16/1.01  --sat_fm_uc_incr                        true
% 3.16/1.01  --sat_out_model                         small
% 3.16/1.01  --sat_out_clauses                       false
% 3.16/1.01  
% 3.16/1.01  ------ QBF Options
% 3.16/1.01  
% 3.16/1.01  --qbf_mode                              false
% 3.16/1.01  --qbf_elim_univ                         false
% 3.16/1.01  --qbf_dom_inst                          none
% 3.16/1.01  --qbf_dom_pre_inst                      false
% 3.16/1.01  --qbf_sk_in                             false
% 3.16/1.01  --qbf_pred_elim                         true
% 3.16/1.01  --qbf_split                             512
% 3.16/1.01  
% 3.16/1.01  ------ BMC1 Options
% 3.16/1.01  
% 3.16/1.01  --bmc1_incremental                      false
% 3.16/1.01  --bmc1_axioms                           reachable_all
% 3.16/1.01  --bmc1_min_bound                        0
% 3.16/1.01  --bmc1_max_bound                        -1
% 3.16/1.01  --bmc1_max_bound_default                -1
% 3.16/1.01  --bmc1_symbol_reachability              true
% 3.16/1.01  --bmc1_property_lemmas                  false
% 3.16/1.01  --bmc1_k_induction                      false
% 3.16/1.01  --bmc1_non_equiv_states                 false
% 3.16/1.01  --bmc1_deadlock                         false
% 3.16/1.01  --bmc1_ucm                              false
% 3.16/1.01  --bmc1_add_unsat_core                   none
% 3.16/1.01  --bmc1_unsat_core_children              false
% 3.16/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.16/1.01  --bmc1_out_stat                         full
% 3.16/1.01  --bmc1_ground_init                      false
% 3.16/1.01  --bmc1_pre_inst_next_state              false
% 3.16/1.01  --bmc1_pre_inst_state                   false
% 3.16/1.01  --bmc1_pre_inst_reach_state             false
% 3.16/1.01  --bmc1_out_unsat_core                   false
% 3.16/1.01  --bmc1_aig_witness_out                  false
% 3.16/1.01  --bmc1_verbose                          false
% 3.16/1.01  --bmc1_dump_clauses_tptp                false
% 3.16/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.16/1.01  --bmc1_dump_file                        -
% 3.16/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.16/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.16/1.01  --bmc1_ucm_extend_mode                  1
% 3.16/1.01  --bmc1_ucm_init_mode                    2
% 3.16/1.01  --bmc1_ucm_cone_mode                    none
% 3.16/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.16/1.01  --bmc1_ucm_relax_model                  4
% 3.16/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.16/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.16/1.01  --bmc1_ucm_layered_model                none
% 3.16/1.01  --bmc1_ucm_max_lemma_size               10
% 3.16/1.01  
% 3.16/1.01  ------ AIG Options
% 3.16/1.01  
% 3.16/1.01  --aig_mode                              false
% 3.16/1.01  
% 3.16/1.01  ------ Instantiation Options
% 3.16/1.01  
% 3.16/1.01  --instantiation_flag                    true
% 3.16/1.01  --inst_sos_flag                         false
% 3.16/1.01  --inst_sos_phase                        true
% 3.16/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.16/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.16/1.01  --inst_lit_sel_side                     none
% 3.16/1.01  --inst_solver_per_active                1400
% 3.16/1.01  --inst_solver_calls_frac                1.
% 3.16/1.01  --inst_passive_queue_type               priority_queues
% 3.16/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.16/1.01  --inst_passive_queues_freq              [25;2]
% 3.16/1.01  --inst_dismatching                      true
% 3.16/1.01  --inst_eager_unprocessed_to_passive     true
% 3.16/1.01  --inst_prop_sim_given                   true
% 3.16/1.01  --inst_prop_sim_new                     false
% 3.16/1.01  --inst_subs_new                         false
% 3.16/1.01  --inst_eq_res_simp                      false
% 3.16/1.01  --inst_subs_given                       false
% 3.16/1.01  --inst_orphan_elimination               true
% 3.16/1.01  --inst_learning_loop_flag               true
% 3.16/1.01  --inst_learning_start                   3000
% 3.16/1.01  --inst_learning_factor                  2
% 3.16/1.01  --inst_start_prop_sim_after_learn       3
% 3.16/1.01  --inst_sel_renew                        solver
% 3.16/1.01  --inst_lit_activity_flag                true
% 3.16/1.01  --inst_restr_to_given                   false
% 3.16/1.01  --inst_activity_threshold               500
% 3.16/1.01  --inst_out_proof                        true
% 3.16/1.01  
% 3.16/1.01  ------ Resolution Options
% 3.16/1.01  
% 3.16/1.01  --resolution_flag                       false
% 3.16/1.01  --res_lit_sel                           adaptive
% 3.16/1.01  --res_lit_sel_side                      none
% 3.16/1.01  --res_ordering                          kbo
% 3.16/1.01  --res_to_prop_solver                    active
% 3.16/1.01  --res_prop_simpl_new                    false
% 3.16/1.01  --res_prop_simpl_given                  true
% 3.16/1.01  --res_passive_queue_type                priority_queues
% 3.16/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.16/1.01  --res_passive_queues_freq               [15;5]
% 3.16/1.01  --res_forward_subs                      full
% 3.16/1.01  --res_backward_subs                     full
% 3.16/1.01  --res_forward_subs_resolution           true
% 3.16/1.01  --res_backward_subs_resolution          true
% 3.16/1.01  --res_orphan_elimination                true
% 3.16/1.01  --res_time_limit                        2.
% 3.16/1.01  --res_out_proof                         true
% 3.16/1.01  
% 3.16/1.01  ------ Superposition Options
% 3.16/1.01  
% 3.16/1.01  --superposition_flag                    true
% 3.16/1.01  --sup_passive_queue_type                priority_queues
% 3.16/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.16/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.16/1.01  --demod_completeness_check              fast
% 3.16/1.01  --demod_use_ground                      true
% 3.16/1.01  --sup_to_prop_solver                    passive
% 3.16/1.01  --sup_prop_simpl_new                    true
% 3.16/1.01  --sup_prop_simpl_given                  true
% 3.16/1.01  --sup_fun_splitting                     false
% 3.16/1.01  --sup_smt_interval                      50000
% 3.16/1.01  
% 3.16/1.01  ------ Superposition Simplification Setup
% 3.16/1.01  
% 3.16/1.01  --sup_indices_passive                   []
% 3.16/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.16/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/1.01  --sup_full_bw                           [BwDemod]
% 3.16/1.01  --sup_immed_triv                        [TrivRules]
% 3.16/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.16/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/1.01  --sup_immed_bw_main                     []
% 3.16/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.16/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.16/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.16/1.01  
% 3.16/1.01  ------ Combination Options
% 3.16/1.01  
% 3.16/1.01  --comb_res_mult                         3
% 3.16/1.01  --comb_sup_mult                         2
% 3.16/1.01  --comb_inst_mult                        10
% 3.16/1.01  
% 3.16/1.01  ------ Debug Options
% 3.16/1.01  
% 3.16/1.01  --dbg_backtrace                         false
% 3.16/1.01  --dbg_dump_prop_clauses                 false
% 3.16/1.01  --dbg_dump_prop_clauses_file            -
% 3.16/1.01  --dbg_out_stat                          false
% 3.16/1.01  
% 3.16/1.01  
% 3.16/1.01  
% 3.16/1.01  
% 3.16/1.01  ------ Proving...
% 3.16/1.01  
% 3.16/1.01  
% 3.16/1.01  % SZS status Theorem for theBenchmark.p
% 3.16/1.01  
% 3.16/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.16/1.01  
% 3.16/1.01  fof(f1,axiom,(
% 3.16/1.01    v1_xboole_0(k1_xboole_0)),
% 3.16/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.01  
% 3.16/1.01  fof(f41,plain,(
% 3.16/1.01    v1_xboole_0(k1_xboole_0)),
% 3.16/1.01    inference(cnf_transformation,[],[f1])).
% 3.16/1.01  
% 3.16/1.01  fof(f11,axiom,(
% 3.16/1.01    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 3.16/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.01  
% 3.16/1.01  fof(f17,plain,(
% 3.16/1.01    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.16/1.01    inference(pure_predicate_removal,[],[f11])).
% 3.16/1.01  
% 3.16/1.01  fof(f54,plain,(
% 3.16/1.01    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.16/1.01    inference(cnf_transformation,[],[f17])).
% 3.16/1.01  
% 3.16/1.01  fof(f6,axiom,(
% 3.16/1.01    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 3.16/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.01  
% 3.16/1.01  fof(f22,plain,(
% 3.16/1.01    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 3.16/1.01    inference(ennf_transformation,[],[f6])).
% 3.16/1.01  
% 3.16/1.01  fof(f46,plain,(
% 3.16/1.01    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 3.16/1.01    inference(cnf_transformation,[],[f22])).
% 3.16/1.01  
% 3.16/1.01  fof(f2,axiom,(
% 3.16/1.01    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.16/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.01  
% 3.16/1.01  fof(f19,plain,(
% 3.16/1.01    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.16/1.01    inference(ennf_transformation,[],[f2])).
% 3.16/1.01  
% 3.16/1.01  fof(f42,plain,(
% 3.16/1.01    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 3.16/1.01    inference(cnf_transformation,[],[f19])).
% 3.16/1.01  
% 3.16/1.01  fof(f3,axiom,(
% 3.16/1.01    ! [X0] : v2_funct_1(k6_relat_1(X0))),
% 3.16/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.01  
% 3.16/1.01  fof(f43,plain,(
% 3.16/1.01    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 3.16/1.01    inference(cnf_transformation,[],[f3])).
% 3.16/1.01  
% 3.16/1.01  fof(f12,axiom,(
% 3.16/1.01    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.16/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.01  
% 3.16/1.01  fof(f55,plain,(
% 3.16/1.01    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.16/1.01    inference(cnf_transformation,[],[f12])).
% 3.16/1.01  
% 3.16/1.01  fof(f67,plain,(
% 3.16/1.01    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 3.16/1.01    inference(definition_unfolding,[],[f43,f55])).
% 3.16/1.01  
% 3.16/1.01  fof(f10,axiom,(
% 3.16/1.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 3.16/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.01  
% 3.16/1.01  fof(f28,plain,(
% 3.16/1.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.16/1.01    inference(ennf_transformation,[],[f10])).
% 3.16/1.01  
% 3.16/1.01  fof(f29,plain,(
% 3.16/1.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.16/1.01    inference(flattening,[],[f28])).
% 3.16/1.01  
% 3.16/1.01  fof(f53,plain,(
% 3.16/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.16/1.01    inference(cnf_transformation,[],[f29])).
% 3.16/1.01  
% 3.16/1.01  fof(f8,axiom,(
% 3.16/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.16/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.01  
% 3.16/1.01  fof(f24,plain,(
% 3.16/1.01    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.16/1.01    inference(ennf_transformation,[],[f8])).
% 3.16/1.01  
% 3.16/1.01  fof(f25,plain,(
% 3.16/1.01    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.16/1.01    inference(flattening,[],[f24])).
% 3.16/1.01  
% 3.16/1.01  fof(f36,plain,(
% 3.16/1.01    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.16/1.01    inference(nnf_transformation,[],[f25])).
% 3.16/1.01  
% 3.16/1.01  fof(f48,plain,(
% 3.16/1.01    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.16/1.01    inference(cnf_transformation,[],[f36])).
% 3.16/1.01  
% 3.16/1.01  fof(f15,conjecture,(
% 3.16/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 3.16/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.01  
% 3.16/1.01  fof(f16,negated_conjecture,(
% 3.16/1.01    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 3.16/1.01    inference(negated_conjecture,[],[f15])).
% 3.16/1.01  
% 3.16/1.01  fof(f34,plain,(
% 3.16/1.01    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.16/1.01    inference(ennf_transformation,[],[f16])).
% 3.16/1.01  
% 3.16/1.01  fof(f35,plain,(
% 3.16/1.01    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.16/1.01    inference(flattening,[],[f34])).
% 3.16/1.01  
% 3.16/1.01  fof(f39,plain,(
% 3.16/1.01    ( ! [X2,X0,X1] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((~v2_funct_2(sK3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 3.16/1.01    introduced(choice_axiom,[])).
% 3.16/1.01  
% 3.16/1.01  fof(f38,plain,(
% 3.16/1.01    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 3.16/1.01    introduced(choice_axiom,[])).
% 3.16/1.01  
% 3.16/1.01  fof(f40,plain,(
% 3.16/1.01    ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 3.16/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f35,f39,f38])).
% 3.16/1.01  
% 3.16/1.01  fof(f65,plain,(
% 3.16/1.01    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 3.16/1.01    inference(cnf_transformation,[],[f40])).
% 3.16/1.01  
% 3.16/1.01  fof(f59,plain,(
% 3.16/1.01    v1_funct_1(sK2)),
% 3.16/1.01    inference(cnf_transformation,[],[f40])).
% 3.16/1.01  
% 3.16/1.01  fof(f61,plain,(
% 3.16/1.01    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.16/1.01    inference(cnf_transformation,[],[f40])).
% 3.16/1.01  
% 3.16/1.01  fof(f62,plain,(
% 3.16/1.01    v1_funct_1(sK3)),
% 3.16/1.01    inference(cnf_transformation,[],[f40])).
% 3.16/1.01  
% 3.16/1.01  fof(f64,plain,(
% 3.16/1.01    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 3.16/1.01    inference(cnf_transformation,[],[f40])).
% 3.16/1.01  
% 3.16/1.01  fof(f14,axiom,(
% 3.16/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 3.16/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.01  
% 3.16/1.01  fof(f32,plain,(
% 3.16/1.01    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.16/1.01    inference(ennf_transformation,[],[f14])).
% 3.16/1.01  
% 3.16/1.01  fof(f33,plain,(
% 3.16/1.01    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.16/1.01    inference(flattening,[],[f32])).
% 3.16/1.01  
% 3.16/1.01  fof(f57,plain,(
% 3.16/1.01    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X3) | k1_xboole_0 = X2 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.16/1.01    inference(cnf_transformation,[],[f33])).
% 3.16/1.01  
% 3.16/1.01  fof(f60,plain,(
% 3.16/1.01    v1_funct_2(sK2,sK0,sK1)),
% 3.16/1.01    inference(cnf_transformation,[],[f40])).
% 3.16/1.01  
% 3.16/1.01  fof(f63,plain,(
% 3.16/1.01    v1_funct_2(sK3,sK1,sK0)),
% 3.16/1.01    inference(cnf_transformation,[],[f40])).
% 3.16/1.01  
% 3.16/1.01  fof(f13,axiom,(
% 3.16/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 3.16/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.01  
% 3.16/1.01  fof(f30,plain,(
% 3.16/1.01    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.16/1.01    inference(ennf_transformation,[],[f13])).
% 3.16/1.01  
% 3.16/1.01  fof(f31,plain,(
% 3.16/1.01    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.16/1.01    inference(flattening,[],[f30])).
% 3.16/1.01  
% 3.16/1.01  fof(f56,plain,(
% 3.16/1.01    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.16/1.01    inference(cnf_transformation,[],[f31])).
% 3.16/1.01  
% 3.16/1.01  fof(f7,axiom,(
% 3.16/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 3.16/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.01  
% 3.16/1.01  fof(f23,plain,(
% 3.16/1.01    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.16/1.01    inference(ennf_transformation,[],[f7])).
% 3.16/1.01  
% 3.16/1.01  fof(f47,plain,(
% 3.16/1.01    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.16/1.01    inference(cnf_transformation,[],[f23])).
% 3.16/1.01  
% 3.16/1.01  fof(f5,axiom,(
% 3.16/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.16/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.01  
% 3.16/1.01  fof(f18,plain,(
% 3.16/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.16/1.01    inference(pure_predicate_removal,[],[f5])).
% 3.16/1.01  
% 3.16/1.01  fof(f21,plain,(
% 3.16/1.01    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.16/1.01    inference(ennf_transformation,[],[f18])).
% 3.16/1.01  
% 3.16/1.01  fof(f45,plain,(
% 3.16/1.01    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.16/1.01    inference(cnf_transformation,[],[f21])).
% 3.16/1.01  
% 3.16/1.01  fof(f9,axiom,(
% 3.16/1.01    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 3.16/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.01  
% 3.16/1.01  fof(f26,plain,(
% 3.16/1.01    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.16/1.01    inference(ennf_transformation,[],[f9])).
% 3.16/1.01  
% 3.16/1.01  fof(f27,plain,(
% 3.16/1.01    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.16/1.01    inference(flattening,[],[f26])).
% 3.16/1.01  
% 3.16/1.01  fof(f37,plain,(
% 3.16/1.01    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.16/1.01    inference(nnf_transformation,[],[f27])).
% 3.16/1.01  
% 3.16/1.01  fof(f51,plain,(
% 3.16/1.01    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.16/1.01    inference(cnf_transformation,[],[f37])).
% 3.16/1.01  
% 3.16/1.01  fof(f69,plain,(
% 3.16/1.01    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.16/1.01    inference(equality_resolution,[],[f51])).
% 3.16/1.01  
% 3.16/1.01  fof(f4,axiom,(
% 3.16/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.16/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.01  
% 3.16/1.01  fof(f20,plain,(
% 3.16/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.16/1.01    inference(ennf_transformation,[],[f4])).
% 3.16/1.01  
% 3.16/1.01  fof(f44,plain,(
% 3.16/1.01    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.16/1.01    inference(cnf_transformation,[],[f20])).
% 3.16/1.01  
% 3.16/1.01  fof(f66,plain,(
% 3.16/1.01    ~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)),
% 3.16/1.01    inference(cnf_transformation,[],[f40])).
% 3.16/1.01  
% 3.16/1.01  cnf(c_0,plain,
% 3.16/1.01      ( v1_xboole_0(k1_xboole_0) ),
% 3.16/1.01      inference(cnf_transformation,[],[f41]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_643,plain,
% 3.16/1.01      ( v1_xboole_0(k1_xboole_0) ),
% 3.16/1.01      inference(subtyping,[status(esa)],[c_0]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_1056,plain,
% 3.16/1.01      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.16/1.01      inference(predicate_to_equality,[status(thm)],[c_643]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_13,plain,
% 3.16/1.01      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.16/1.01      inference(cnf_transformation,[],[f54]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_636,plain,
% 3.16/1.01      ( m1_subset_1(k6_partfun1(X0_48),k1_zfmisc_1(k2_zfmisc_1(X0_48,X0_48))) ),
% 3.16/1.01      inference(subtyping,[status(esa)],[c_13]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_1063,plain,
% 3.16/1.01      ( m1_subset_1(k6_partfun1(X0_48),k1_zfmisc_1(k2_zfmisc_1(X0_48,X0_48))) = iProver_top ),
% 3.16/1.01      inference(predicate_to_equality,[status(thm)],[c_636]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_5,plain,
% 3.16/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.16/1.01      | ~ v1_xboole_0(X1)
% 3.16/1.01      | v1_xboole_0(X0) ),
% 3.16/1.01      inference(cnf_transformation,[],[f46]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_640,plain,
% 3.16/1.01      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
% 3.16/1.01      | ~ v1_xboole_0(X1_48)
% 3.16/1.01      | v1_xboole_0(X0_48) ),
% 3.16/1.01      inference(subtyping,[status(esa)],[c_5]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_1059,plain,
% 3.16/1.01      ( m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48))) != iProver_top
% 3.16/1.01      | v1_xboole_0(X1_48) != iProver_top
% 3.16/1.01      | v1_xboole_0(X0_48) = iProver_top ),
% 3.16/1.01      inference(predicate_to_equality,[status(thm)],[c_640]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_2049,plain,
% 3.16/1.01      ( v1_xboole_0(X0_48) != iProver_top
% 3.16/1.01      | v1_xboole_0(k6_partfun1(X0_48)) = iProver_top ),
% 3.16/1.01      inference(superposition,[status(thm)],[c_1063,c_1059]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_1,plain,
% 3.16/1.01      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 3.16/1.01      inference(cnf_transformation,[],[f42]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_642,plain,
% 3.16/1.01      ( ~ v1_xboole_0(X0_48) | k1_xboole_0 = X0_48 ),
% 3.16/1.01      inference(subtyping,[status(esa)],[c_1]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_1057,plain,
% 3.16/1.01      ( k1_xboole_0 = X0_48 | v1_xboole_0(X0_48) != iProver_top ),
% 3.16/1.01      inference(predicate_to_equality,[status(thm)],[c_642]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_3474,plain,
% 3.16/1.01      ( k6_partfun1(X0_48) = k1_xboole_0
% 3.16/1.01      | v1_xboole_0(X0_48) != iProver_top ),
% 3.16/1.01      inference(superposition,[status(thm)],[c_2049,c_1057]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_3521,plain,
% 3.16/1.01      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 3.16/1.01      inference(superposition,[status(thm)],[c_1056,c_3474]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_2,plain,
% 3.16/1.01      ( v2_funct_1(k6_partfun1(X0)) ),
% 3.16/1.01      inference(cnf_transformation,[],[f67]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_641,plain,
% 3.16/1.01      ( v2_funct_1(k6_partfun1(X0_48)) ),
% 3.16/1.01      inference(subtyping,[status(esa)],[c_2]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_1058,plain,
% 3.16/1.01      ( v2_funct_1(k6_partfun1(X0_48)) = iProver_top ),
% 3.16/1.01      inference(predicate_to_equality,[status(thm)],[c_641]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_3536,plain,
% 3.16/1.01      ( v2_funct_1(k1_xboole_0) = iProver_top ),
% 3.16/1.01      inference(superposition,[status(thm)],[c_3521,c_1058]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_11,plain,
% 3.16/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.16/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.16/1.01      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.16/1.01      | ~ v1_funct_1(X0)
% 3.16/1.01      | ~ v1_funct_1(X3) ),
% 3.16/1.01      inference(cnf_transformation,[],[f53]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_638,plain,
% 3.16/1.01      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
% 3.16/1.01      | ~ m1_subset_1(X3_48,k1_zfmisc_1(k2_zfmisc_1(X4_48,X5_48)))
% 3.16/1.01      | m1_subset_1(k1_partfun1(X4_48,X5_48,X1_48,X2_48,X3_48,X0_48),k1_zfmisc_1(k2_zfmisc_1(X4_48,X2_48)))
% 3.16/1.01      | ~ v1_funct_1(X0_48)
% 3.16/1.01      | ~ v1_funct_1(X3_48) ),
% 3.16/1.01      inference(subtyping,[status(esa)],[c_11]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_1061,plain,
% 3.16/1.01      ( m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48))) != iProver_top
% 3.16/1.01      | m1_subset_1(X3_48,k1_zfmisc_1(k2_zfmisc_1(X4_48,X5_48))) != iProver_top
% 3.16/1.01      | m1_subset_1(k1_partfun1(X4_48,X5_48,X1_48,X2_48,X3_48,X0_48),k1_zfmisc_1(k2_zfmisc_1(X4_48,X2_48))) = iProver_top
% 3.16/1.01      | v1_funct_1(X3_48) != iProver_top
% 3.16/1.01      | v1_funct_1(X0_48) != iProver_top ),
% 3.16/1.01      inference(predicate_to_equality,[status(thm)],[c_638]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_8,plain,
% 3.16/1.01      ( ~ r2_relset_1(X0,X1,X2,X3)
% 3.16/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.16/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.16/1.01      | X3 = X2 ),
% 3.16/1.01      inference(cnf_transformation,[],[f48]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_18,negated_conjecture,
% 3.16/1.01      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 3.16/1.01      inference(cnf_transformation,[],[f65]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_415,plain,
% 3.16/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.16/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.16/1.01      | X3 = X0
% 3.16/1.01      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 3.16/1.01      | k6_partfun1(sK0) != X3
% 3.16/1.01      | sK0 != X2
% 3.16/1.01      | sK0 != X1 ),
% 3.16/1.01      inference(resolution_lifted,[status(thm)],[c_8,c_18]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_416,plain,
% 3.16/1.01      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.16/1.01      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.16/1.01      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.16/1.01      inference(unflattening,[status(thm)],[c_415]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_43,plain,
% 3.16/1.01      ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.16/1.01      inference(instantiation,[status(thm)],[c_13]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_418,plain,
% 3.16/1.01      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.16/1.01      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.16/1.01      inference(global_propositional_subsumption,
% 3.16/1.01                [status(thm)],
% 3.16/1.01                [c_416,c_43]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_625,plain,
% 3.16/1.01      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.16/1.01      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.16/1.01      inference(subtyping,[status(esa)],[c_418]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_1075,plain,
% 3.16/1.01      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.16/1.01      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.16/1.01      inference(predicate_to_equality,[status(thm)],[c_625]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_2109,plain,
% 3.16/1.01      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
% 3.16/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.16/1.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.16/1.01      | v1_funct_1(sK2) != iProver_top
% 3.16/1.01      | v1_funct_1(sK3) != iProver_top ),
% 3.16/1.01      inference(superposition,[status(thm)],[c_1061,c_1075]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_24,negated_conjecture,
% 3.16/1.01      ( v1_funct_1(sK2) ),
% 3.16/1.01      inference(cnf_transformation,[],[f59]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_25,plain,
% 3.16/1.01      ( v1_funct_1(sK2) = iProver_top ),
% 3.16/1.01      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_22,negated_conjecture,
% 3.16/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.16/1.01      inference(cnf_transformation,[],[f61]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_27,plain,
% 3.16/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.16/1.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_21,negated_conjecture,
% 3.16/1.01      ( v1_funct_1(sK3) ),
% 3.16/1.01      inference(cnf_transformation,[],[f62]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_28,plain,
% 3.16/1.01      ( v1_funct_1(sK3) = iProver_top ),
% 3.16/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_19,negated_conjecture,
% 3.16/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 3.16/1.01      inference(cnf_transformation,[],[f64]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_30,plain,
% 3.16/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.16/1.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_2364,plain,
% 3.16/1.01      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
% 3.16/1.01      inference(global_propositional_subsumption,
% 3.16/1.01                [status(thm)],
% 3.16/1.01                [c_2109,c_25,c_27,c_28,c_30]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_16,plain,
% 3.16/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 3.16/1.01      | ~ v1_funct_2(X3,X4,X1)
% 3.16/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 3.16/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.16/1.01      | ~ v1_funct_1(X0)
% 3.16/1.01      | ~ v1_funct_1(X3)
% 3.16/1.01      | v2_funct_1(X3)
% 3.16/1.01      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 3.16/1.01      | k1_xboole_0 = X2 ),
% 3.16/1.01      inference(cnf_transformation,[],[f57]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_634,plain,
% 3.16/1.01      ( ~ v1_funct_2(X0_48,X1_48,X2_48)
% 3.16/1.01      | ~ v1_funct_2(X3_48,X4_48,X1_48)
% 3.16/1.01      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
% 3.16/1.01      | ~ m1_subset_1(X3_48,k1_zfmisc_1(k2_zfmisc_1(X4_48,X1_48)))
% 3.16/1.01      | ~ v1_funct_1(X0_48)
% 3.16/1.01      | ~ v1_funct_1(X3_48)
% 3.16/1.01      | v2_funct_1(X3_48)
% 3.16/1.01      | ~ v2_funct_1(k1_partfun1(X4_48,X1_48,X1_48,X2_48,X3_48,X0_48))
% 3.16/1.01      | k1_xboole_0 = X2_48 ),
% 3.16/1.01      inference(subtyping,[status(esa)],[c_16]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_1065,plain,
% 3.16/1.01      ( k1_xboole_0 = X0_48
% 3.16/1.01      | v1_funct_2(X1_48,X2_48,X0_48) != iProver_top
% 3.16/1.01      | v1_funct_2(X3_48,X4_48,X2_48) != iProver_top
% 3.16/1.01      | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_48,X0_48))) != iProver_top
% 3.16/1.01      | m1_subset_1(X3_48,k1_zfmisc_1(k2_zfmisc_1(X4_48,X2_48))) != iProver_top
% 3.16/1.01      | v1_funct_1(X3_48) != iProver_top
% 3.16/1.01      | v1_funct_1(X1_48) != iProver_top
% 3.16/1.01      | v2_funct_1(X3_48) = iProver_top
% 3.16/1.01      | v2_funct_1(k1_partfun1(X4_48,X2_48,X2_48,X0_48,X3_48,X1_48)) != iProver_top ),
% 3.16/1.01      inference(predicate_to_equality,[status(thm)],[c_634]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_2390,plain,
% 3.16/1.01      ( sK0 = k1_xboole_0
% 3.16/1.01      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 3.16/1.01      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 3.16/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.16/1.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.16/1.01      | v1_funct_1(sK2) != iProver_top
% 3.16/1.01      | v1_funct_1(sK3) != iProver_top
% 3.16/1.01      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 3.16/1.01      | v2_funct_1(sK2) = iProver_top ),
% 3.16/1.01      inference(superposition,[status(thm)],[c_2364,c_1065]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_23,negated_conjecture,
% 3.16/1.01      ( v1_funct_2(sK2,sK0,sK1) ),
% 3.16/1.01      inference(cnf_transformation,[],[f60]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_26,plain,
% 3.16/1.01      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 3.16/1.01      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_20,negated_conjecture,
% 3.16/1.01      ( v1_funct_2(sK3,sK1,sK0) ),
% 3.16/1.01      inference(cnf_transformation,[],[f63]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_29,plain,
% 3.16/1.01      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 3.16/1.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_73,plain,
% 3.16/1.01      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 3.16/1.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_75,plain,
% 3.16/1.01      ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
% 3.16/1.01      inference(instantiation,[status(thm)],[c_73]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_14,plain,
% 3.16/1.01      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.16/1.01      | ~ v1_funct_2(X2,X0,X1)
% 3.16/1.01      | ~ v1_funct_2(X3,X1,X0)
% 3.16/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.16/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.16/1.01      | ~ v1_funct_1(X2)
% 3.16/1.01      | ~ v1_funct_1(X3)
% 3.16/1.01      | k2_relset_1(X1,X0,X3) = X0 ),
% 3.16/1.01      inference(cnf_transformation,[],[f56]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_429,plain,
% 3.16/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 3.16/1.01      | ~ v1_funct_2(X3,X2,X1)
% 3.16/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.16/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.16/1.01      | ~ v1_funct_1(X3)
% 3.16/1.01      | ~ v1_funct_1(X0)
% 3.16/1.01      | k1_partfun1(X1,X2,X2,X1,X0,X3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.16/1.01      | k2_relset_1(X2,X1,X3) = X1
% 3.16/1.01      | k6_partfun1(X1) != k6_partfun1(sK0)
% 3.16/1.01      | sK0 != X1 ),
% 3.16/1.01      inference(resolution_lifted,[status(thm)],[c_14,c_18]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_430,plain,
% 3.16/1.01      ( ~ v1_funct_2(X0,X1,sK0)
% 3.16/1.01      | ~ v1_funct_2(X2,sK0,X1)
% 3.16/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 3.16/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 3.16/1.01      | ~ v1_funct_1(X2)
% 3.16/1.01      | ~ v1_funct_1(X0)
% 3.16/1.01      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.16/1.01      | k2_relset_1(X1,sK0,X0) = sK0
% 3.16/1.01      | k6_partfun1(sK0) != k6_partfun1(sK0) ),
% 3.16/1.01      inference(unflattening,[status(thm)],[c_429]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_504,plain,
% 3.16/1.01      ( ~ v1_funct_2(X0,X1,sK0)
% 3.16/1.01      | ~ v1_funct_2(X2,sK0,X1)
% 3.16/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 3.16/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 3.16/1.01      | ~ v1_funct_1(X0)
% 3.16/1.01      | ~ v1_funct_1(X2)
% 3.16/1.01      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.16/1.01      | k2_relset_1(X1,sK0,X0) = sK0 ),
% 3.16/1.01      inference(equality_resolution_simp,[status(thm)],[c_430]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_624,plain,
% 3.16/1.01      ( ~ v1_funct_2(X0_48,X1_48,sK0)
% 3.16/1.01      | ~ v1_funct_2(X2_48,sK0,X1_48)
% 3.16/1.01      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,sK0)))
% 3.16/1.01      | ~ m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(sK0,X1_48)))
% 3.16/1.01      | ~ v1_funct_1(X0_48)
% 3.16/1.01      | ~ v1_funct_1(X2_48)
% 3.16/1.01      | k1_partfun1(sK0,X1_48,X1_48,sK0,X2_48,X0_48) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.16/1.01      | k2_relset_1(X1_48,sK0,X0_48) = sK0 ),
% 3.16/1.01      inference(subtyping,[status(esa)],[c_504]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_1076,plain,
% 3.16/1.01      ( k1_partfun1(sK0,X0_48,X0_48,sK0,X1_48,X2_48) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.16/1.01      | k2_relset_1(X0_48,sK0,X2_48) = sK0
% 3.16/1.01      | v1_funct_2(X2_48,X0_48,sK0) != iProver_top
% 3.16/1.01      | v1_funct_2(X1_48,sK0,X0_48) != iProver_top
% 3.16/1.01      | m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,sK0))) != iProver_top
% 3.16/1.01      | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_48))) != iProver_top
% 3.16/1.01      | v1_funct_1(X2_48) != iProver_top
% 3.16/1.01      | v1_funct_1(X1_48) != iProver_top ),
% 3.16/1.01      inference(predicate_to_equality,[status(thm)],[c_624]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_1921,plain,
% 3.16/1.01      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 3.16/1.01      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 3.16/1.01      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 3.16/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.16/1.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.16/1.01      | v1_funct_1(sK2) != iProver_top
% 3.16/1.01      | v1_funct_1(sK3) != iProver_top ),
% 3.16/1.01      inference(equality_resolution,[status(thm)],[c_1076]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_633,negated_conjecture,
% 3.16/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 3.16/1.01      inference(subtyping,[status(esa)],[c_19]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_1066,plain,
% 3.16/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.16/1.01      inference(predicate_to_equality,[status(thm)],[c_633]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_6,plain,
% 3.16/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.16/1.01      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.16/1.01      inference(cnf_transformation,[],[f47]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_639,plain,
% 3.16/1.01      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
% 3.16/1.01      | k2_relset_1(X1_48,X2_48,X0_48) = k2_relat_1(X0_48) ),
% 3.16/1.01      inference(subtyping,[status(esa)],[c_6]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_1060,plain,
% 3.16/1.01      ( k2_relset_1(X0_48,X1_48,X2_48) = k2_relat_1(X2_48)
% 3.16/1.01      | m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top ),
% 3.16/1.01      inference(predicate_to_equality,[status(thm)],[c_639]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_1606,plain,
% 3.16/1.01      ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 3.16/1.01      inference(superposition,[status(thm)],[c_1066,c_1060]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_1922,plain,
% 3.16/1.01      ( k2_relat_1(sK3) = sK0
% 3.16/1.01      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 3.16/1.01      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 3.16/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.16/1.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.16/1.01      | v1_funct_1(sK2) != iProver_top
% 3.16/1.01      | v1_funct_1(sK3) != iProver_top ),
% 3.16/1.01      inference(demodulation,[status(thm)],[c_1921,c_1606]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_1925,plain,
% 3.16/1.01      ( k2_relat_1(sK3) = sK0 ),
% 3.16/1.01      inference(global_propositional_subsumption,
% 3.16/1.01                [status(thm)],
% 3.16/1.01                [c_1922,c_25,c_26,c_27,c_28,c_29,c_30]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_4,plain,
% 3.16/1.01      ( v5_relat_1(X0,X1)
% 3.16/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.16/1.01      inference(cnf_transformation,[],[f45]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_9,plain,
% 3.16/1.01      ( v2_funct_2(X0,k2_relat_1(X0))
% 3.16/1.01      | ~ v5_relat_1(X0,k2_relat_1(X0))
% 3.16/1.01      | ~ v1_relat_1(X0) ),
% 3.16/1.01      inference(cnf_transformation,[],[f69]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_333,plain,
% 3.16/1.01      ( v2_funct_2(X0,k2_relat_1(X0))
% 3.16/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.16/1.01      | ~ v1_relat_1(X0)
% 3.16/1.01      | X0 != X1
% 3.16/1.01      | k2_relat_1(X0) != X3 ),
% 3.16/1.01      inference(resolution_lifted,[status(thm)],[c_4,c_9]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_334,plain,
% 3.16/1.01      ( v2_funct_2(X0,k2_relat_1(X0))
% 3.16/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
% 3.16/1.01      | ~ v1_relat_1(X0) ),
% 3.16/1.01      inference(unflattening,[status(thm)],[c_333]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_3,plain,
% 3.16/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.16/1.01      | v1_relat_1(X0) ),
% 3.16/1.01      inference(cnf_transformation,[],[f44]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_344,plain,
% 3.16/1.01      ( v2_funct_2(X0,k2_relat_1(X0))
% 3.16/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0)))) ),
% 3.16/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_334,c_3]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_17,negated_conjecture,
% 3.16/1.01      ( ~ v2_funct_2(sK3,sK0) | ~ v2_funct_1(sK2) ),
% 3.16/1.01      inference(cnf_transformation,[],[f66]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_359,plain,
% 3.16/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
% 3.16/1.01      | ~ v2_funct_1(sK2)
% 3.16/1.01      | k2_relat_1(X0) != sK0
% 3.16/1.01      | sK3 != X0 ),
% 3.16/1.01      inference(resolution_lifted,[status(thm)],[c_344,c_17]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_360,plain,
% 3.16/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3))))
% 3.16/1.01      | ~ v2_funct_1(sK2)
% 3.16/1.01      | k2_relat_1(sK3) != sK0 ),
% 3.16/1.01      inference(unflattening,[status(thm)],[c_359]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_627,plain,
% 3.16/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_48,k2_relat_1(sK3))))
% 3.16/1.01      | ~ v2_funct_1(sK2)
% 3.16/1.01      | k2_relat_1(sK3) != sK0 ),
% 3.16/1.01      inference(subtyping,[status(esa)],[c_360]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_645,plain,
% 3.16/1.01      ( ~ v2_funct_1(sK2) | sP0_iProver_split | k2_relat_1(sK3) != sK0 ),
% 3.16/1.01      inference(splitting,
% 3.16/1.01                [splitting(split),new_symbols(definition,[])],
% 3.16/1.01                [c_627]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_1072,plain,
% 3.16/1.01      ( k2_relat_1(sK3) != sK0
% 3.16/1.01      | v2_funct_1(sK2) != iProver_top
% 3.16/1.01      | sP0_iProver_split = iProver_top ),
% 3.16/1.01      inference(predicate_to_equality,[status(thm)],[c_645]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_1930,plain,
% 3.16/1.01      ( sK0 != sK0
% 3.16/1.01      | v2_funct_1(sK2) != iProver_top
% 3.16/1.01      | sP0_iProver_split = iProver_top ),
% 3.16/1.01      inference(demodulation,[status(thm)],[c_1925,c_1072]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_1931,plain,
% 3.16/1.01      ( v2_funct_1(sK2) != iProver_top
% 3.16/1.01      | sP0_iProver_split = iProver_top ),
% 3.16/1.01      inference(equality_resolution_simp,[status(thm)],[c_1930]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_644,plain,
% 3.16/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_48,k2_relat_1(sK3))))
% 3.16/1.01      | ~ sP0_iProver_split ),
% 3.16/1.01      inference(splitting,
% 3.16/1.01                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 3.16/1.01                [c_627]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_1073,plain,
% 3.16/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_48,k2_relat_1(sK3)))) != iProver_top
% 3.16/1.01      | sP0_iProver_split != iProver_top ),
% 3.16/1.01      inference(predicate_to_equality,[status(thm)],[c_644]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_1929,plain,
% 3.16/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_48,sK0))) != iProver_top
% 3.16/1.01      | sP0_iProver_split != iProver_top ),
% 3.16/1.01      inference(demodulation,[status(thm)],[c_1925,c_1073]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_1994,plain,
% 3.16/1.01      ( sP0_iProver_split != iProver_top ),
% 3.16/1.01      inference(superposition,[status(thm)],[c_1066,c_1929]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_3010,plain,
% 3.16/1.01      ( sK0 = k1_xboole_0 ),
% 3.16/1.01      inference(global_propositional_subsumption,
% 3.16/1.01                [status(thm)],
% 3.16/1.01                [c_2390,c_25,c_26,c_27,c_28,c_29,c_30,c_75,c_1931,c_1994]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_630,negated_conjecture,
% 3.16/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.16/1.01      inference(subtyping,[status(esa)],[c_22]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_1069,plain,
% 3.16/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.16/1.01      inference(predicate_to_equality,[status(thm)],[c_630]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_2048,plain,
% 3.16/1.01      ( v1_xboole_0(sK2) = iProver_top
% 3.16/1.01      | v1_xboole_0(sK0) != iProver_top ),
% 3.16/1.01      inference(superposition,[status(thm)],[c_1069,c_1059]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_3016,plain,
% 3.16/1.01      ( v1_xboole_0(sK2) = iProver_top
% 3.16/1.01      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.16/1.01      inference(demodulation,[status(thm)],[c_3010,c_2048]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_79,plain,
% 3.16/1.01      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.16/1.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_651,plain,
% 3.16/1.01      ( ~ v1_xboole_0(X0_48) | v1_xboole_0(X1_48) | X1_48 != X0_48 ),
% 3.16/1.01      theory(equality) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_1387,plain,
% 3.16/1.01      ( v1_xboole_0(X0_48)
% 3.16/1.01      | ~ v1_xboole_0(k1_xboole_0)
% 3.16/1.01      | X0_48 != k1_xboole_0 ),
% 3.16/1.01      inference(instantiation,[status(thm)],[c_651]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_1388,plain,
% 3.16/1.01      ( X0_48 != k1_xboole_0
% 3.16/1.01      | v1_xboole_0(X0_48) = iProver_top
% 3.16/1.01      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.16/1.01      inference(predicate_to_equality,[status(thm)],[c_1387]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_1390,plain,
% 3.16/1.01      ( sK0 != k1_xboole_0
% 3.16/1.01      | v1_xboole_0(sK0) = iProver_top
% 3.16/1.01      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.16/1.01      inference(instantiation,[status(thm)],[c_1388]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_3158,plain,
% 3.16/1.01      ( v1_xboole_0(sK2) = iProver_top ),
% 3.16/1.01      inference(global_propositional_subsumption,
% 3.16/1.01                [status(thm)],
% 3.16/1.01                [c_3016,c_25,c_26,c_27,c_28,c_29,c_30,c_75,c_79,c_1390,
% 3.16/1.01                 c_1931,c_1994,c_2048,c_2390]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_3163,plain,
% 3.16/1.01      ( sK2 = k1_xboole_0 ),
% 3.16/1.01      inference(superposition,[status(thm)],[c_3158,c_1057]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_2427,plain,
% 3.16/1.01      ( v2_funct_1(sK2) != iProver_top ),
% 3.16/1.01      inference(global_propositional_subsumption,
% 3.16/1.01                [status(thm)],
% 3.16/1.01                [c_1931,c_1994]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_3169,plain,
% 3.16/1.01      ( v2_funct_1(k1_xboole_0) != iProver_top ),
% 3.16/1.01      inference(demodulation,[status(thm)],[c_3163,c_2427]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(contradiction,plain,
% 3.16/1.01      ( $false ),
% 3.16/1.01      inference(minisat,[status(thm)],[c_3536,c_3169]) ).
% 3.16/1.01  
% 3.16/1.01  
% 3.16/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.16/1.01  
% 3.16/1.01  ------                               Statistics
% 3.16/1.01  
% 3.16/1.01  ------ General
% 3.16/1.01  
% 3.16/1.01  abstr_ref_over_cycles:                  0
% 3.16/1.01  abstr_ref_under_cycles:                 0
% 3.16/1.01  gc_basic_clause_elim:                   0
% 3.16/1.01  forced_gc_time:                         0
% 3.16/1.01  parsing_time:                           0.013
% 3.16/1.01  unif_index_cands_time:                  0.
% 3.16/1.01  unif_index_add_time:                    0.
% 3.16/1.01  orderings_time:                         0.
% 3.16/1.01  out_proof_time:                         0.013
% 3.16/1.01  total_time:                             0.18
% 3.16/1.01  num_of_symbols:                         52
% 3.16/1.01  num_of_terms:                           6749
% 3.16/1.01  
% 3.16/1.01  ------ Preprocessing
% 3.16/1.01  
% 3.16/1.01  num_of_splits:                          1
% 3.16/1.01  num_of_split_atoms:                     1
% 3.16/1.01  num_of_reused_defs:                     0
% 3.16/1.01  num_eq_ax_congr_red:                    10
% 3.16/1.01  num_of_sem_filtered_clauses:            1
% 3.16/1.01  num_of_subtypes:                        3
% 3.16/1.01  monotx_restored_types:                  1
% 3.16/1.01  sat_num_of_epr_types:                   0
% 3.16/1.01  sat_num_of_non_cyclic_types:            0
% 3.16/1.01  sat_guarded_non_collapsed_types:        1
% 3.16/1.01  num_pure_diseq_elim:                    0
% 3.16/1.01  simp_replaced_by:                       0
% 3.16/1.01  res_preprocessed:                       118
% 3.16/1.01  prep_upred:                             0
% 3.16/1.01  prep_unflattend:                        17
% 3.16/1.01  smt_new_axioms:                         0
% 3.16/1.01  pred_elim_cands:                        5
% 3.16/1.01  pred_elim:                              4
% 3.16/1.01  pred_elim_cl:                           5
% 3.16/1.01  pred_elim_cycles:                       7
% 3.16/1.01  merged_defs:                            0
% 3.16/1.01  merged_defs_ncl:                        0
% 3.16/1.01  bin_hyper_res:                          0
% 3.16/1.01  prep_cycles:                            4
% 3.16/1.01  pred_elim_time:                         0.005
% 3.16/1.01  splitting_time:                         0.
% 3.16/1.01  sem_filter_time:                        0.
% 3.16/1.01  monotx_time:                            0.001
% 3.16/1.01  subtype_inf_time:                       0.001
% 3.16/1.01  
% 3.16/1.01  ------ Problem properties
% 3.16/1.01  
% 3.16/1.01  clauses:                                21
% 3.16/1.01  conjectures:                            6
% 3.16/1.01  epr:                                    6
% 3.16/1.01  horn:                                   20
% 3.16/1.01  ground:                                 9
% 3.16/1.01  unary:                                  9
% 3.16/1.01  binary:                                 4
% 3.16/1.01  lits:                                   66
% 3.16/1.01  lits_eq:                                9
% 3.16/1.01  fd_pure:                                0
% 3.16/1.01  fd_pseudo:                              0
% 3.16/1.01  fd_cond:                                2
% 3.16/1.01  fd_pseudo_cond:                         0
% 3.16/1.01  ac_symbols:                             0
% 3.16/1.01  
% 3.16/1.01  ------ Propositional Solver
% 3.16/1.01  
% 3.16/1.01  prop_solver_calls:                      26
% 3.16/1.01  prop_fast_solver_calls:                 881
% 3.16/1.01  smt_solver_calls:                       0
% 3.16/1.01  smt_fast_solver_calls:                  0
% 3.16/1.01  prop_num_of_clauses:                    1474
% 3.16/1.01  prop_preprocess_simplified:             4569
% 3.16/1.01  prop_fo_subsumed:                       25
% 3.16/1.01  prop_solver_time:                       0.
% 3.16/1.01  smt_solver_time:                        0.
% 3.16/1.01  smt_fast_solver_time:                   0.
% 3.16/1.01  prop_fast_solver_time:                  0.
% 3.16/1.01  prop_unsat_core_time:                   0.
% 3.16/1.01  
% 3.16/1.01  ------ QBF
% 3.16/1.01  
% 3.16/1.01  qbf_q_res:                              0
% 3.16/1.01  qbf_num_tautologies:                    0
% 3.16/1.01  qbf_prep_cycles:                        0
% 3.16/1.01  
% 3.16/1.01  ------ BMC1
% 3.16/1.01  
% 3.16/1.01  bmc1_current_bound:                     -1
% 3.16/1.01  bmc1_last_solved_bound:                 -1
% 3.16/1.01  bmc1_unsat_core_size:                   -1
% 3.16/1.01  bmc1_unsat_core_parents_size:           -1
% 3.16/1.01  bmc1_merge_next_fun:                    0
% 3.16/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.16/1.01  
% 3.16/1.01  ------ Instantiation
% 3.16/1.01  
% 3.16/1.01  inst_num_of_clauses:                    389
% 3.16/1.01  inst_num_in_passive:                    78
% 3.16/1.01  inst_num_in_active:                     234
% 3.16/1.01  inst_num_in_unprocessed:                77
% 3.16/1.01  inst_num_of_loops:                      250
% 3.16/1.01  inst_num_of_learning_restarts:          0
% 3.16/1.01  inst_num_moves_active_passive:          13
% 3.16/1.01  inst_lit_activity:                      0
% 3.16/1.01  inst_lit_activity_moves:                0
% 3.16/1.01  inst_num_tautologies:                   0
% 3.16/1.01  inst_num_prop_implied:                  0
% 3.16/1.01  inst_num_existing_simplified:           0
% 3.16/1.01  inst_num_eq_res_simplified:             0
% 3.16/1.01  inst_num_child_elim:                    0
% 3.16/1.01  inst_num_of_dismatching_blockings:      16
% 3.16/1.01  inst_num_of_non_proper_insts:           220
% 3.16/1.01  inst_num_of_duplicates:                 0
% 3.16/1.01  inst_inst_num_from_inst_to_res:         0
% 3.16/1.01  inst_dismatching_checking_time:         0.
% 3.16/1.01  
% 3.16/1.01  ------ Resolution
% 3.16/1.01  
% 3.16/1.01  res_num_of_clauses:                     0
% 3.16/1.01  res_num_in_passive:                     0
% 3.16/1.01  res_num_in_active:                      0
% 3.16/1.01  res_num_of_loops:                       122
% 3.16/1.01  res_forward_subset_subsumed:            19
% 3.16/1.01  res_backward_subset_subsumed:           0
% 3.16/1.01  res_forward_subsumed:                   0
% 3.16/1.01  res_backward_subsumed:                  0
% 3.16/1.01  res_forward_subsumption_resolution:     3
% 3.16/1.01  res_backward_subsumption_resolution:    0
% 3.16/1.01  res_clause_to_clause_subsumption:       72
% 3.16/1.01  res_orphan_elimination:                 0
% 3.16/1.01  res_tautology_del:                      12
% 3.16/1.01  res_num_eq_res_simplified:              1
% 3.16/1.01  res_num_sel_changes:                    0
% 3.16/1.01  res_moves_from_active_to_pass:          0
% 3.16/1.01  
% 3.16/1.01  ------ Superposition
% 3.16/1.01  
% 3.16/1.01  sup_time_total:                         0.
% 3.16/1.01  sup_time_generating:                    0.
% 3.16/1.01  sup_time_sim_full:                      0.
% 3.16/1.01  sup_time_sim_immed:                     0.
% 3.16/1.01  
% 3.16/1.01  sup_num_of_clauses:                     37
% 3.16/1.01  sup_num_in_active:                      26
% 3.16/1.01  sup_num_in_passive:                     11
% 3.16/1.01  sup_num_of_loops:                       49
% 3.16/1.01  sup_fw_superposition:                   11
% 3.16/1.01  sup_bw_superposition:                   18
% 3.16/1.01  sup_immediate_simplified:               3
% 3.16/1.01  sup_given_eliminated:                   0
% 3.16/1.01  comparisons_done:                       0
% 3.16/1.01  comparisons_avoided:                    0
% 3.16/1.01  
% 3.16/1.01  ------ Simplifications
% 3.16/1.01  
% 3.16/1.01  
% 3.16/1.01  sim_fw_subset_subsumed:                 1
% 3.16/1.01  sim_bw_subset_subsumed:                 0
% 3.16/1.01  sim_fw_subsumed:                        1
% 3.16/1.01  sim_bw_subsumed:                        0
% 3.16/1.01  sim_fw_subsumption_res:                 0
% 3.16/1.01  sim_bw_subsumption_res:                 0
% 3.16/1.01  sim_tautology_del:                      2
% 3.16/1.01  sim_eq_tautology_del:                   2
% 3.16/1.01  sim_eq_res_simp:                        1
% 3.16/1.01  sim_fw_demodulated:                     1
% 3.16/1.01  sim_bw_demodulated:                     24
% 3.16/1.01  sim_light_normalised:                   1
% 3.16/1.01  sim_joinable_taut:                      0
% 3.16/1.01  sim_joinable_simp:                      0
% 3.16/1.01  sim_ac_normalised:                      0
% 3.16/1.01  sim_smt_subsumption:                    0
% 3.16/1.01  
%------------------------------------------------------------------------------
