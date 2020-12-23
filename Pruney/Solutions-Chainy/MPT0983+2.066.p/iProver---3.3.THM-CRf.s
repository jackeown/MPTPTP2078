%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:01:58 EST 2020

% Result     : Theorem 3.68s
% Output     : CNFRefutation 3.68s
% Verified   : 
% Statistics : Number of formulae       :  174 (1239 expanded)
%              Number of clauses        :   96 ( 341 expanded)
%              Number of leaves         :   20 ( 311 expanded)
%              Depth                    :   19
%              Number of atoms          :  617 (7967 expanded)
%              Number of equality atoms :  201 ( 542 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f48,plain,(
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

fof(f47,plain,
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

fof(f49,plain,
    ( ( ~ v2_funct_2(sK3,sK0)
      | ~ v2_funct_1(sK2) )
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f41,f48,f47])).

fof(f77,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f49])).

fof(f80,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f49])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f36])).

fof(f72,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f78,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f30])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f81,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f49])).

fof(f14,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f71,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f75,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f34])).

fof(f70,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X0))
           => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
      | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f4,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f16,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f84,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f56,f73])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f52,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => v2_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_funct_1(X1)
          | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_funct_1(X1)
          | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f17])).

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
    inference(flattening,[],[f38])).

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
    inference(cnf_transformation,[],[f39])).

fof(f76,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f79,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f89,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f68])).

fof(f82,plain,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f7,axiom,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f85,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f60,f73])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1119,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1122,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1123,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3174,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1122,c_1123])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_35,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3243,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3174,c_35])).

cnf(c_3244,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_3243])).

cnf(c_3251,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1119,c_3244])).

cnf(c_16,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_25,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_457,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_25])).

cnf(c_458,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_457])).

cnf(c_21,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_47,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_460,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_458,c_47])).

cnf(c_1112,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_460])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1169,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_1628,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1112,c_31,c_29,c_28,c_26,c_47,c_458,c_1169])).

cnf(c_3252,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3251,c_1628])).

cnf(c_32,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_3505,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3252,c_32])).

cnf(c_8,plain,
    ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k1_relat_1(k5_relat_1(X0,X1)) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1131,plain,
    ( k1_relat_1(k5_relat_1(X0,X1)) != k1_relat_1(X0)
    | r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3507,plain,
    ( k1_relat_1(k6_partfun1(sK0)) != k1_relat_1(sK2)
    | r1_tarski(k2_relat_1(sK2),k1_relat_1(sK3)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3505,c_1131])).

cnf(c_7,plain,
    ( k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_3510,plain,
    ( k1_relat_1(sK2) != sK0
    | r1_tarski(k2_relat_1(sK2),k1_relat_1(sK3)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3507,c_7])).

cnf(c_34,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_37,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1215,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1231,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1215])).

cnf(c_1232,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1231])).

cnf(c_1364,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1545,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1364])).

cnf(c_1546,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1545])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v4_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_4,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_335,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_13,c_4])).

cnf(c_339,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_335,c_11])).

cnf(c_340,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_339])).

cnf(c_1116,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_340])).

cnf(c_2106,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1119,c_1116])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1134,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2486,plain,
    ( k1_relat_1(sK2) = sK0
    | r1_tarski(sK0,k1_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2106,c_1134])).

cnf(c_5,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1132,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3508,plain,
    ( r1_tarski(k1_relat_1(k6_partfun1(sK0)),k1_relat_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3505,c_1132])).

cnf(c_3509,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3508,c_7])).

cnf(c_3815,plain,
    ( r1_tarski(k2_relat_1(sK2),k1_relat_1(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3510,c_32,c_34,c_35,c_37,c_1232,c_1546,c_2486,c_3509])).

cnf(c_9,plain,
    ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
    | v2_funct_1(X0)
    | ~ v2_funct_1(k5_relat_1(X0,X1))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1130,plain,
    ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) != iProver_top
    | v2_funct_1(X0) = iProver_top
    | v2_funct_1(k5_relat_1(X0,X1)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3820,plain,
    ( v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
    | v2_funct_1(sK2) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3815,c_1130])).

cnf(c_3821,plain,
    ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK2) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3820,c_3505])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1127,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2165,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1122,c_1127])).

cnf(c_23,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_471,plain,
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
    inference(resolution_lifted,[status(thm)],[c_23,c_25])).

cnf(c_472,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0
    | k6_partfun1(sK0) != k6_partfun1(sK0) ),
    inference(unflattening,[status(thm)],[c_471])).

cnf(c_549,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_472])).

cnf(c_1111,plain,
    ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X0,sK0,X2) = sK0
    | v1_funct_2(X2,X0,sK0) != iProver_top
    | v1_funct_2(X1,sK0,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_549])).

cnf(c_1767,plain,
    ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k6_partfun1(sK0)
    | k2_relset_1(X0,sK0,X2) = sK0
    | v1_funct_2(X2,X0,sK0) != iProver_top
    | v1_funct_2(X1,sK0,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1111,c_1628])).

cnf(c_1771,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1628,c_1767])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_33,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_36,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_1774,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1771,c_32,c_33,c_34,c_35,c_36,c_37])).

cnf(c_2167,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_2165,c_1774])).

cnf(c_12,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_17,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_375,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X0)
    | X0 != X1
    | k2_relat_1(X0) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_17])).

cnf(c_376,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_375])).

cnf(c_386,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0)))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_376,c_11])).

cnf(c_24,negated_conjecture,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_401,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
    | ~ v2_funct_1(sK2)
    | k2_relat_1(X0) != sK0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_386,c_24])).

cnf(c_402,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3))))
    | ~ v2_funct_1(sK2)
    | k2_relat_1(sK3) != sK0 ),
    inference(unflattening,[status(thm)],[c_401])).

cnf(c_686,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3))))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_402])).

cnf(c_1115,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3)))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_686])).

cnf(c_2555,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(demodulation,[status(thm)],[c_2167,c_1115])).

cnf(c_2716,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_1122,c_2555])).

cnf(c_687,plain,
    ( ~ v2_funct_1(sK2)
    | sP0_iProver_split
    | k2_relat_1(sK3) != sK0 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_402])).

cnf(c_1114,plain,
    ( k2_relat_1(sK3) != sK0
    | v2_funct_1(sK2) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_687])).

cnf(c_2556,plain,
    ( sK0 != sK0
    | v2_funct_1(sK2) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_2167,c_1114])).

cnf(c_2557,plain,
    ( v2_funct_1(sK2) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2556])).

cnf(c_10,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_79,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_81,plain,
    ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_79])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3821,c_2716,c_2557,c_1546,c_1232,c_81,c_37,c_35,c_34,c_32])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:39:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.68/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.68/0.99  
% 3.68/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.68/0.99  
% 3.68/0.99  ------  iProver source info
% 3.68/0.99  
% 3.68/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.68/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.68/0.99  git: non_committed_changes: false
% 3.68/0.99  git: last_make_outside_of_git: false
% 3.68/0.99  
% 3.68/0.99  ------ 
% 3.68/0.99  
% 3.68/0.99  ------ Input Options
% 3.68/0.99  
% 3.68/0.99  --out_options                           all
% 3.68/0.99  --tptp_safe_out                         true
% 3.68/0.99  --problem_path                          ""
% 3.68/0.99  --include_path                          ""
% 3.68/0.99  --clausifier                            res/vclausify_rel
% 3.68/0.99  --clausifier_options                    ""
% 3.68/0.99  --stdin                                 false
% 3.68/0.99  --stats_out                             all
% 3.68/0.99  
% 3.68/0.99  ------ General Options
% 3.68/0.99  
% 3.68/0.99  --fof                                   false
% 3.68/0.99  --time_out_real                         305.
% 3.68/0.99  --time_out_virtual                      -1.
% 3.68/0.99  --symbol_type_check                     false
% 3.68/0.99  --clausify_out                          false
% 3.68/0.99  --sig_cnt_out                           false
% 3.68/0.99  --trig_cnt_out                          false
% 3.68/0.99  --trig_cnt_out_tolerance                1.
% 3.68/0.99  --trig_cnt_out_sk_spl                   false
% 3.68/0.99  --abstr_cl_out                          false
% 3.68/0.99  
% 3.68/0.99  ------ Global Options
% 3.68/0.99  
% 3.68/0.99  --schedule                              default
% 3.68/0.99  --add_important_lit                     false
% 3.68/0.99  --prop_solver_per_cl                    1000
% 3.68/0.99  --min_unsat_core                        false
% 3.68/0.99  --soft_assumptions                      false
% 3.68/0.99  --soft_lemma_size                       3
% 3.68/0.99  --prop_impl_unit_size                   0
% 3.68/0.99  --prop_impl_unit                        []
% 3.68/0.99  --share_sel_clauses                     true
% 3.68/0.99  --reset_solvers                         false
% 3.68/0.99  --bc_imp_inh                            [conj_cone]
% 3.68/0.99  --conj_cone_tolerance                   3.
% 3.68/0.99  --extra_neg_conj                        none
% 3.68/0.99  --large_theory_mode                     true
% 3.68/0.99  --prolific_symb_bound                   200
% 3.68/0.99  --lt_threshold                          2000
% 3.68/0.99  --clause_weak_htbl                      true
% 3.68/0.99  --gc_record_bc_elim                     false
% 3.68/0.99  
% 3.68/0.99  ------ Preprocessing Options
% 3.68/0.99  
% 3.68/0.99  --preprocessing_flag                    true
% 3.68/0.99  --time_out_prep_mult                    0.1
% 3.68/0.99  --splitting_mode                        input
% 3.68/0.99  --splitting_grd                         true
% 3.68/0.99  --splitting_cvd                         false
% 3.68/0.99  --splitting_cvd_svl                     false
% 3.68/0.99  --splitting_nvd                         32
% 3.68/0.99  --sub_typing                            true
% 3.68/0.99  --prep_gs_sim                           true
% 3.68/0.99  --prep_unflatten                        true
% 3.68/0.99  --prep_res_sim                          true
% 3.68/0.99  --prep_upred                            true
% 3.68/0.99  --prep_sem_filter                       exhaustive
% 3.68/0.99  --prep_sem_filter_out                   false
% 3.68/0.99  --pred_elim                             true
% 3.68/0.99  --res_sim_input                         true
% 3.68/0.99  --eq_ax_congr_red                       true
% 3.68/0.99  --pure_diseq_elim                       true
% 3.68/0.99  --brand_transform                       false
% 3.68/0.99  --non_eq_to_eq                          false
% 3.68/0.99  --prep_def_merge                        true
% 3.68/0.99  --prep_def_merge_prop_impl              false
% 3.68/0.99  --prep_def_merge_mbd                    true
% 3.68/0.99  --prep_def_merge_tr_red                 false
% 3.68/0.99  --prep_def_merge_tr_cl                  false
% 3.68/0.99  --smt_preprocessing                     true
% 3.68/0.99  --smt_ac_axioms                         fast
% 3.68/0.99  --preprocessed_out                      false
% 3.68/0.99  --preprocessed_stats                    false
% 3.68/0.99  
% 3.68/0.99  ------ Abstraction refinement Options
% 3.68/0.99  
% 3.68/0.99  --abstr_ref                             []
% 3.68/0.99  --abstr_ref_prep                        false
% 3.68/0.99  --abstr_ref_until_sat                   false
% 3.68/0.99  --abstr_ref_sig_restrict                funpre
% 3.68/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.68/0.99  --abstr_ref_under                       []
% 3.68/0.99  
% 3.68/0.99  ------ SAT Options
% 3.68/0.99  
% 3.68/0.99  --sat_mode                              false
% 3.68/0.99  --sat_fm_restart_options                ""
% 3.68/0.99  --sat_gr_def                            false
% 3.68/0.99  --sat_epr_types                         true
% 3.68/0.99  --sat_non_cyclic_types                  false
% 3.68/0.99  --sat_finite_models                     false
% 3.68/0.99  --sat_fm_lemmas                         false
% 3.68/0.99  --sat_fm_prep                           false
% 3.68/0.99  --sat_fm_uc_incr                        true
% 3.68/0.99  --sat_out_model                         small
% 3.68/0.99  --sat_out_clauses                       false
% 3.68/0.99  
% 3.68/0.99  ------ QBF Options
% 3.68/0.99  
% 3.68/0.99  --qbf_mode                              false
% 3.68/0.99  --qbf_elim_univ                         false
% 3.68/0.99  --qbf_dom_inst                          none
% 3.68/0.99  --qbf_dom_pre_inst                      false
% 3.68/0.99  --qbf_sk_in                             false
% 3.68/0.99  --qbf_pred_elim                         true
% 3.68/0.99  --qbf_split                             512
% 3.68/0.99  
% 3.68/0.99  ------ BMC1 Options
% 3.68/0.99  
% 3.68/0.99  --bmc1_incremental                      false
% 3.68/0.99  --bmc1_axioms                           reachable_all
% 3.68/0.99  --bmc1_min_bound                        0
% 3.68/0.99  --bmc1_max_bound                        -1
% 3.68/0.99  --bmc1_max_bound_default                -1
% 3.68/0.99  --bmc1_symbol_reachability              true
% 3.68/0.99  --bmc1_property_lemmas                  false
% 3.68/0.99  --bmc1_k_induction                      false
% 3.68/0.99  --bmc1_non_equiv_states                 false
% 3.68/0.99  --bmc1_deadlock                         false
% 3.68/0.99  --bmc1_ucm                              false
% 3.68/0.99  --bmc1_add_unsat_core                   none
% 3.68/0.99  --bmc1_unsat_core_children              false
% 3.68/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.68/0.99  --bmc1_out_stat                         full
% 3.68/0.99  --bmc1_ground_init                      false
% 3.68/0.99  --bmc1_pre_inst_next_state              false
% 3.68/0.99  --bmc1_pre_inst_state                   false
% 3.68/0.99  --bmc1_pre_inst_reach_state             false
% 3.68/0.99  --bmc1_out_unsat_core                   false
% 3.68/0.99  --bmc1_aig_witness_out                  false
% 3.68/0.99  --bmc1_verbose                          false
% 3.68/0.99  --bmc1_dump_clauses_tptp                false
% 3.68/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.68/0.99  --bmc1_dump_file                        -
% 3.68/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.68/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.68/0.99  --bmc1_ucm_extend_mode                  1
% 3.68/0.99  --bmc1_ucm_init_mode                    2
% 3.68/0.99  --bmc1_ucm_cone_mode                    none
% 3.68/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.68/0.99  --bmc1_ucm_relax_model                  4
% 3.68/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.68/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.68/0.99  --bmc1_ucm_layered_model                none
% 3.68/0.99  --bmc1_ucm_max_lemma_size               10
% 3.68/0.99  
% 3.68/0.99  ------ AIG Options
% 3.68/0.99  
% 3.68/0.99  --aig_mode                              false
% 3.68/0.99  
% 3.68/0.99  ------ Instantiation Options
% 3.68/0.99  
% 3.68/0.99  --instantiation_flag                    true
% 3.68/0.99  --inst_sos_flag                         true
% 3.68/0.99  --inst_sos_phase                        true
% 3.68/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.68/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.68/0.99  --inst_lit_sel_side                     num_symb
% 3.68/0.99  --inst_solver_per_active                1400
% 3.68/0.99  --inst_solver_calls_frac                1.
% 3.68/0.99  --inst_passive_queue_type               priority_queues
% 3.68/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.68/0.99  --inst_passive_queues_freq              [25;2]
% 3.68/0.99  --inst_dismatching                      true
% 3.68/0.99  --inst_eager_unprocessed_to_passive     true
% 3.68/0.99  --inst_prop_sim_given                   true
% 3.68/0.99  --inst_prop_sim_new                     false
% 3.68/0.99  --inst_subs_new                         false
% 3.68/0.99  --inst_eq_res_simp                      false
% 3.68/0.99  --inst_subs_given                       false
% 3.68/0.99  --inst_orphan_elimination               true
% 3.68/0.99  --inst_learning_loop_flag               true
% 3.68/0.99  --inst_learning_start                   3000
% 3.68/0.99  --inst_learning_factor                  2
% 3.68/0.99  --inst_start_prop_sim_after_learn       3
% 3.68/0.99  --inst_sel_renew                        solver
% 3.68/0.99  --inst_lit_activity_flag                true
% 3.68/0.99  --inst_restr_to_given                   false
% 3.68/0.99  --inst_activity_threshold               500
% 3.68/0.99  --inst_out_proof                        true
% 3.68/0.99  
% 3.68/0.99  ------ Resolution Options
% 3.68/0.99  
% 3.68/0.99  --resolution_flag                       true
% 3.68/0.99  --res_lit_sel                           adaptive
% 3.68/0.99  --res_lit_sel_side                      none
% 3.68/0.99  --res_ordering                          kbo
% 3.68/0.99  --res_to_prop_solver                    active
% 3.68/0.99  --res_prop_simpl_new                    false
% 3.68/0.99  --res_prop_simpl_given                  true
% 3.68/0.99  --res_passive_queue_type                priority_queues
% 3.68/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.68/0.99  --res_passive_queues_freq               [15;5]
% 3.68/0.99  --res_forward_subs                      full
% 3.68/0.99  --res_backward_subs                     full
% 3.68/0.99  --res_forward_subs_resolution           true
% 3.68/0.99  --res_backward_subs_resolution          true
% 3.68/0.99  --res_orphan_elimination                true
% 3.68/0.99  --res_time_limit                        2.
% 3.68/0.99  --res_out_proof                         true
% 3.68/0.99  
% 3.68/0.99  ------ Superposition Options
% 3.68/0.99  
% 3.68/0.99  --superposition_flag                    true
% 3.68/0.99  --sup_passive_queue_type                priority_queues
% 3.68/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.68/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.68/0.99  --demod_completeness_check              fast
% 3.68/0.99  --demod_use_ground                      true
% 3.68/0.99  --sup_to_prop_solver                    passive
% 3.68/0.99  --sup_prop_simpl_new                    true
% 3.68/0.99  --sup_prop_simpl_given                  true
% 3.68/0.99  --sup_fun_splitting                     true
% 3.68/0.99  --sup_smt_interval                      50000
% 3.68/0.99  
% 3.68/0.99  ------ Superposition Simplification Setup
% 3.68/0.99  
% 3.68/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.68/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.68/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.68/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.68/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.68/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.68/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.68/0.99  --sup_immed_triv                        [TrivRules]
% 3.68/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.68/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.68/0.99  --sup_immed_bw_main                     []
% 3.68/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.68/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.68/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.68/0.99  --sup_input_bw                          []
% 3.68/0.99  
% 3.68/0.99  ------ Combination Options
% 3.68/0.99  
% 3.68/0.99  --comb_res_mult                         3
% 3.68/0.99  --comb_sup_mult                         2
% 3.68/0.99  --comb_inst_mult                        10
% 3.68/0.99  
% 3.68/0.99  ------ Debug Options
% 3.68/0.99  
% 3.68/0.99  --dbg_backtrace                         false
% 3.68/0.99  --dbg_dump_prop_clauses                 false
% 3.68/0.99  --dbg_dump_prop_clauses_file            -
% 3.68/0.99  --dbg_out_stat                          false
% 3.68/0.99  ------ Parsing...
% 3.68/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.68/0.99  
% 3.68/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.68/0.99  
% 3.68/0.99  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.68/0.99  
% 3.68/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.68/0.99  ------ Proving...
% 3.68/0.99  ------ Problem Properties 
% 3.68/0.99  
% 3.68/0.99  
% 3.68/0.99  clauses                                 26
% 3.68/0.99  conjectures                             6
% 3.68/0.99  EPR                                     6
% 3.68/0.99  Horn                                    26
% 3.68/0.99  unary                                   11
% 3.68/0.99  binary                                  5
% 3.68/0.99  lits                                    74
% 3.68/0.99  lits eq                                 12
% 3.68/0.99  fd_pure                                 0
% 3.68/0.99  fd_pseudo                               0
% 3.68/0.99  fd_cond                                 0
% 3.68/0.99  fd_pseudo_cond                          1
% 3.68/0.99  AC symbols                              0
% 3.68/0.99  
% 3.68/0.99  ------ Schedule dynamic 5 is on 
% 3.68/0.99  
% 3.68/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.68/0.99  
% 3.68/0.99  
% 3.68/0.99  ------ 
% 3.68/0.99  Current options:
% 3.68/0.99  ------ 
% 3.68/0.99  
% 3.68/0.99  ------ Input Options
% 3.68/0.99  
% 3.68/0.99  --out_options                           all
% 3.68/0.99  --tptp_safe_out                         true
% 3.68/0.99  --problem_path                          ""
% 3.68/0.99  --include_path                          ""
% 3.68/0.99  --clausifier                            res/vclausify_rel
% 3.68/0.99  --clausifier_options                    ""
% 3.68/0.99  --stdin                                 false
% 3.68/0.99  --stats_out                             all
% 3.68/0.99  
% 3.68/0.99  ------ General Options
% 3.68/0.99  
% 3.68/0.99  --fof                                   false
% 3.68/0.99  --time_out_real                         305.
% 3.68/0.99  --time_out_virtual                      -1.
% 3.68/0.99  --symbol_type_check                     false
% 3.68/0.99  --clausify_out                          false
% 3.68/0.99  --sig_cnt_out                           false
% 3.68/0.99  --trig_cnt_out                          false
% 3.68/0.99  --trig_cnt_out_tolerance                1.
% 3.68/0.99  --trig_cnt_out_sk_spl                   false
% 3.68/0.99  --abstr_cl_out                          false
% 3.68/0.99  
% 3.68/0.99  ------ Global Options
% 3.68/0.99  
% 3.68/0.99  --schedule                              default
% 3.68/0.99  --add_important_lit                     false
% 3.68/0.99  --prop_solver_per_cl                    1000
% 3.68/0.99  --min_unsat_core                        false
% 3.68/0.99  --soft_assumptions                      false
% 3.68/0.99  --soft_lemma_size                       3
% 3.68/0.99  --prop_impl_unit_size                   0
% 3.68/0.99  --prop_impl_unit                        []
% 3.68/0.99  --share_sel_clauses                     true
% 3.68/0.99  --reset_solvers                         false
% 3.68/0.99  --bc_imp_inh                            [conj_cone]
% 3.68/0.99  --conj_cone_tolerance                   3.
% 3.68/0.99  --extra_neg_conj                        none
% 3.68/0.99  --large_theory_mode                     true
% 3.68/0.99  --prolific_symb_bound                   200
% 3.68/0.99  --lt_threshold                          2000
% 3.68/0.99  --clause_weak_htbl                      true
% 3.68/0.99  --gc_record_bc_elim                     false
% 3.68/0.99  
% 3.68/0.99  ------ Preprocessing Options
% 3.68/0.99  
% 3.68/0.99  --preprocessing_flag                    true
% 3.68/0.99  --time_out_prep_mult                    0.1
% 3.68/0.99  --splitting_mode                        input
% 3.68/0.99  --splitting_grd                         true
% 3.68/0.99  --splitting_cvd                         false
% 3.68/0.99  --splitting_cvd_svl                     false
% 3.68/0.99  --splitting_nvd                         32
% 3.68/0.99  --sub_typing                            true
% 3.68/0.99  --prep_gs_sim                           true
% 3.68/0.99  --prep_unflatten                        true
% 3.68/0.99  --prep_res_sim                          true
% 3.68/0.99  --prep_upred                            true
% 3.68/0.99  --prep_sem_filter                       exhaustive
% 3.68/0.99  --prep_sem_filter_out                   false
% 3.68/0.99  --pred_elim                             true
% 3.68/0.99  --res_sim_input                         true
% 3.68/0.99  --eq_ax_congr_red                       true
% 3.68/0.99  --pure_diseq_elim                       true
% 3.68/0.99  --brand_transform                       false
% 3.68/0.99  --non_eq_to_eq                          false
% 3.68/0.99  --prep_def_merge                        true
% 3.68/0.99  --prep_def_merge_prop_impl              false
% 3.68/0.99  --prep_def_merge_mbd                    true
% 3.68/0.99  --prep_def_merge_tr_red                 false
% 3.68/0.99  --prep_def_merge_tr_cl                  false
% 3.68/0.99  --smt_preprocessing                     true
% 3.68/0.99  --smt_ac_axioms                         fast
% 3.68/0.99  --preprocessed_out                      false
% 3.68/0.99  --preprocessed_stats                    false
% 3.68/0.99  
% 3.68/0.99  ------ Abstraction refinement Options
% 3.68/0.99  
% 3.68/0.99  --abstr_ref                             []
% 3.68/0.99  --abstr_ref_prep                        false
% 3.68/0.99  --abstr_ref_until_sat                   false
% 3.68/0.99  --abstr_ref_sig_restrict                funpre
% 3.68/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.68/0.99  --abstr_ref_under                       []
% 3.68/0.99  
% 3.68/0.99  ------ SAT Options
% 3.68/0.99  
% 3.68/0.99  --sat_mode                              false
% 3.68/0.99  --sat_fm_restart_options                ""
% 3.68/0.99  --sat_gr_def                            false
% 3.68/0.99  --sat_epr_types                         true
% 3.68/0.99  --sat_non_cyclic_types                  false
% 3.68/0.99  --sat_finite_models                     false
% 3.68/0.99  --sat_fm_lemmas                         false
% 3.68/0.99  --sat_fm_prep                           false
% 3.68/0.99  --sat_fm_uc_incr                        true
% 3.68/0.99  --sat_out_model                         small
% 3.68/0.99  --sat_out_clauses                       false
% 3.68/0.99  
% 3.68/0.99  ------ QBF Options
% 3.68/0.99  
% 3.68/0.99  --qbf_mode                              false
% 3.68/0.99  --qbf_elim_univ                         false
% 3.68/0.99  --qbf_dom_inst                          none
% 3.68/0.99  --qbf_dom_pre_inst                      false
% 3.68/0.99  --qbf_sk_in                             false
% 3.68/0.99  --qbf_pred_elim                         true
% 3.68/0.99  --qbf_split                             512
% 3.68/0.99  
% 3.68/0.99  ------ BMC1 Options
% 3.68/0.99  
% 3.68/0.99  --bmc1_incremental                      false
% 3.68/0.99  --bmc1_axioms                           reachable_all
% 3.68/0.99  --bmc1_min_bound                        0
% 3.68/0.99  --bmc1_max_bound                        -1
% 3.68/0.99  --bmc1_max_bound_default                -1
% 3.68/0.99  --bmc1_symbol_reachability              true
% 3.68/0.99  --bmc1_property_lemmas                  false
% 3.68/0.99  --bmc1_k_induction                      false
% 3.68/0.99  --bmc1_non_equiv_states                 false
% 3.68/0.99  --bmc1_deadlock                         false
% 3.68/0.99  --bmc1_ucm                              false
% 3.68/0.99  --bmc1_add_unsat_core                   none
% 3.68/0.99  --bmc1_unsat_core_children              false
% 3.68/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.68/0.99  --bmc1_out_stat                         full
% 3.68/0.99  --bmc1_ground_init                      false
% 3.68/0.99  --bmc1_pre_inst_next_state              false
% 3.68/0.99  --bmc1_pre_inst_state                   false
% 3.68/0.99  --bmc1_pre_inst_reach_state             false
% 3.68/0.99  --bmc1_out_unsat_core                   false
% 3.68/0.99  --bmc1_aig_witness_out                  false
% 3.68/0.99  --bmc1_verbose                          false
% 3.68/0.99  --bmc1_dump_clauses_tptp                false
% 3.68/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.68/0.99  --bmc1_dump_file                        -
% 3.68/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.68/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.68/0.99  --bmc1_ucm_extend_mode                  1
% 3.68/0.99  --bmc1_ucm_init_mode                    2
% 3.68/0.99  --bmc1_ucm_cone_mode                    none
% 3.68/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.68/0.99  --bmc1_ucm_relax_model                  4
% 3.68/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.68/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.68/0.99  --bmc1_ucm_layered_model                none
% 3.68/0.99  --bmc1_ucm_max_lemma_size               10
% 3.68/0.99  
% 3.68/0.99  ------ AIG Options
% 3.68/0.99  
% 3.68/0.99  --aig_mode                              false
% 3.68/0.99  
% 3.68/0.99  ------ Instantiation Options
% 3.68/0.99  
% 3.68/0.99  --instantiation_flag                    true
% 3.68/0.99  --inst_sos_flag                         true
% 3.68/0.99  --inst_sos_phase                        true
% 3.68/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.68/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.68/0.99  --inst_lit_sel_side                     none
% 3.68/0.99  --inst_solver_per_active                1400
% 3.68/0.99  --inst_solver_calls_frac                1.
% 3.68/0.99  --inst_passive_queue_type               priority_queues
% 3.68/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.68/0.99  --inst_passive_queues_freq              [25;2]
% 3.68/0.99  --inst_dismatching                      true
% 3.68/0.99  --inst_eager_unprocessed_to_passive     true
% 3.68/0.99  --inst_prop_sim_given                   true
% 3.68/0.99  --inst_prop_sim_new                     false
% 3.68/0.99  --inst_subs_new                         false
% 3.68/0.99  --inst_eq_res_simp                      false
% 3.68/0.99  --inst_subs_given                       false
% 3.68/0.99  --inst_orphan_elimination               true
% 3.68/0.99  --inst_learning_loop_flag               true
% 3.68/0.99  --inst_learning_start                   3000
% 3.68/0.99  --inst_learning_factor                  2
% 3.68/0.99  --inst_start_prop_sim_after_learn       3
% 3.68/0.99  --inst_sel_renew                        solver
% 3.68/0.99  --inst_lit_activity_flag                true
% 3.68/0.99  --inst_restr_to_given                   false
% 3.68/0.99  --inst_activity_threshold               500
% 3.68/0.99  --inst_out_proof                        true
% 3.68/0.99  
% 3.68/0.99  ------ Resolution Options
% 3.68/0.99  
% 3.68/0.99  --resolution_flag                       false
% 3.68/0.99  --res_lit_sel                           adaptive
% 3.68/0.99  --res_lit_sel_side                      none
% 3.68/0.99  --res_ordering                          kbo
% 3.68/0.99  --res_to_prop_solver                    active
% 3.68/0.99  --res_prop_simpl_new                    false
% 3.68/0.99  --res_prop_simpl_given                  true
% 3.68/0.99  --res_passive_queue_type                priority_queues
% 3.68/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.68/0.99  --res_passive_queues_freq               [15;5]
% 3.68/0.99  --res_forward_subs                      full
% 3.68/0.99  --res_backward_subs                     full
% 3.68/0.99  --res_forward_subs_resolution           true
% 3.68/0.99  --res_backward_subs_resolution          true
% 3.68/0.99  --res_orphan_elimination                true
% 3.68/0.99  --res_time_limit                        2.
% 3.68/0.99  --res_out_proof                         true
% 3.68/0.99  
% 3.68/0.99  ------ Superposition Options
% 3.68/0.99  
% 3.68/0.99  --superposition_flag                    true
% 3.68/0.99  --sup_passive_queue_type                priority_queues
% 3.68/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.68/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.68/0.99  --demod_completeness_check              fast
% 3.68/0.99  --demod_use_ground                      true
% 3.68/0.99  --sup_to_prop_solver                    passive
% 3.68/0.99  --sup_prop_simpl_new                    true
% 3.68/0.99  --sup_prop_simpl_given                  true
% 3.68/0.99  --sup_fun_splitting                     true
% 3.68/0.99  --sup_smt_interval                      50000
% 3.68/0.99  
% 3.68/0.99  ------ Superposition Simplification Setup
% 3.68/0.99  
% 3.68/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.68/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.68/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.68/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.68/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.68/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.68/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.68/0.99  --sup_immed_triv                        [TrivRules]
% 3.68/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.68/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.68/0.99  --sup_immed_bw_main                     []
% 3.68/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.68/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.68/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.68/0.99  --sup_input_bw                          []
% 3.68/0.99  
% 3.68/0.99  ------ Combination Options
% 3.68/0.99  
% 3.68/0.99  --comb_res_mult                         3
% 3.68/0.99  --comb_sup_mult                         2
% 3.68/0.99  --comb_inst_mult                        10
% 3.68/0.99  
% 3.68/0.99  ------ Debug Options
% 3.68/0.99  
% 3.68/0.99  --dbg_backtrace                         false
% 3.68/0.99  --dbg_dump_prop_clauses                 false
% 3.68/0.99  --dbg_dump_prop_clauses_file            -
% 3.68/0.99  --dbg_out_stat                          false
% 3.68/0.99  
% 3.68/0.99  
% 3.68/0.99  
% 3.68/0.99  
% 3.68/0.99  ------ Proving...
% 3.68/0.99  
% 3.68/0.99  
% 3.68/0.99  % SZS status Theorem for theBenchmark.p
% 3.68/0.99  
% 3.68/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.68/0.99  
% 3.68/0.99  fof(f18,conjecture,(
% 3.68/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 3.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/0.99  
% 3.68/0.99  fof(f19,negated_conjecture,(
% 3.68/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 3.68/0.99    inference(negated_conjecture,[],[f18])).
% 3.68/0.99  
% 3.68/0.99  fof(f40,plain,(
% 3.68/0.99    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.68/0.99    inference(ennf_transformation,[],[f19])).
% 3.68/0.99  
% 3.68/0.99  fof(f41,plain,(
% 3.68/0.99    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.68/0.99    inference(flattening,[],[f40])).
% 3.68/0.99  
% 3.68/0.99  fof(f48,plain,(
% 3.68/0.99    ( ! [X2,X0,X1] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((~v2_funct_2(sK3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 3.68/0.99    introduced(choice_axiom,[])).
% 3.68/0.99  
% 3.68/0.99  fof(f47,plain,(
% 3.68/0.99    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 3.68/0.99    introduced(choice_axiom,[])).
% 3.68/0.99  
% 3.68/0.99  fof(f49,plain,(
% 3.68/0.99    ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 3.68/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f41,f48,f47])).
% 3.68/0.99  
% 3.68/0.99  fof(f77,plain,(
% 3.68/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.68/0.99    inference(cnf_transformation,[],[f49])).
% 3.68/0.99  
% 3.68/0.99  fof(f80,plain,(
% 3.68/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 3.68/0.99    inference(cnf_transformation,[],[f49])).
% 3.68/0.99  
% 3.68/0.99  fof(f15,axiom,(
% 3.68/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/0.99  
% 3.68/0.99  fof(f36,plain,(
% 3.68/0.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.68/0.99    inference(ennf_transformation,[],[f15])).
% 3.68/0.99  
% 3.68/0.99  fof(f37,plain,(
% 3.68/0.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.68/0.99    inference(flattening,[],[f36])).
% 3.68/0.99  
% 3.68/0.99  fof(f72,plain,(
% 3.68/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.68/0.99    inference(cnf_transformation,[],[f37])).
% 3.68/0.99  
% 3.68/0.99  fof(f78,plain,(
% 3.68/0.99    v1_funct_1(sK3)),
% 3.68/0.99    inference(cnf_transformation,[],[f49])).
% 3.68/0.99  
% 3.68/0.99  fof(f11,axiom,(
% 3.68/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/0.99  
% 3.68/0.99  fof(f30,plain,(
% 3.68/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.68/0.99    inference(ennf_transformation,[],[f11])).
% 3.68/0.99  
% 3.68/0.99  fof(f31,plain,(
% 3.68/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.68/0.99    inference(flattening,[],[f30])).
% 3.68/0.99  
% 3.68/0.99  fof(f45,plain,(
% 3.68/0.99    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.68/0.99    inference(nnf_transformation,[],[f31])).
% 3.68/0.99  
% 3.68/0.99  fof(f65,plain,(
% 3.68/0.99    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.68/0.99    inference(cnf_transformation,[],[f45])).
% 3.68/0.99  
% 3.68/0.99  fof(f81,plain,(
% 3.68/0.99    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 3.68/0.99    inference(cnf_transformation,[],[f49])).
% 3.68/0.99  
% 3.68/0.99  fof(f14,axiom,(
% 3.68/0.99    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 3.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/0.99  
% 3.68/0.99  fof(f20,plain,(
% 3.68/0.99    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.68/0.99    inference(pure_predicate_removal,[],[f14])).
% 3.68/0.99  
% 3.68/0.99  fof(f71,plain,(
% 3.68/0.99    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.68/0.99    inference(cnf_transformation,[],[f20])).
% 3.68/0.99  
% 3.68/0.99  fof(f75,plain,(
% 3.68/0.99    v1_funct_1(sK2)),
% 3.68/0.99    inference(cnf_transformation,[],[f49])).
% 3.68/0.99  
% 3.68/0.99  fof(f13,axiom,(
% 3.68/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 3.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/0.99  
% 3.68/0.99  fof(f34,plain,(
% 3.68/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.68/0.99    inference(ennf_transformation,[],[f13])).
% 3.68/0.99  
% 3.68/0.99  fof(f35,plain,(
% 3.68/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.68/0.99    inference(flattening,[],[f34])).
% 3.68/0.99  
% 3.68/0.99  fof(f70,plain,(
% 3.68/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.68/0.99    inference(cnf_transformation,[],[f35])).
% 3.68/0.99  
% 3.68/0.99  fof(f5,axiom,(
% 3.68/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X0)) => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)))))),
% 3.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/0.99  
% 3.68/0.99  fof(f23,plain,(
% 3.68/0.99    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.68/0.99    inference(ennf_transformation,[],[f5])).
% 3.68/0.99  
% 3.68/0.99  fof(f24,plain,(
% 3.68/0.99    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.68/0.99    inference(flattening,[],[f23])).
% 3.68/0.99  
% 3.68/0.99  fof(f58,plain,(
% 3.68/0.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.68/0.99    inference(cnf_transformation,[],[f24])).
% 3.68/0.99  
% 3.68/0.99  fof(f4,axiom,(
% 3.68/0.99    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/0.99  
% 3.68/0.99  fof(f56,plain,(
% 3.68/0.99    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 3.68/0.99    inference(cnf_transformation,[],[f4])).
% 3.68/0.99  
% 3.68/0.99  fof(f16,axiom,(
% 3.68/0.99    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/0.99  
% 3.68/0.99  fof(f73,plain,(
% 3.68/0.99    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.68/0.99    inference(cnf_transformation,[],[f16])).
% 3.68/0.99  
% 3.68/0.99  fof(f84,plain,(
% 3.68/0.99    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 3.68/0.99    inference(definition_unfolding,[],[f56,f73])).
% 3.68/0.99  
% 3.68/0.99  fof(f8,axiom,(
% 3.68/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/0.99  
% 3.68/0.99  fof(f27,plain,(
% 3.68/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.68/0.99    inference(ennf_transformation,[],[f8])).
% 3.68/0.99  
% 3.68/0.99  fof(f61,plain,(
% 3.68/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.68/0.99    inference(cnf_transformation,[],[f27])).
% 3.68/0.99  
% 3.68/0.99  fof(f9,axiom,(
% 3.68/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/0.99  
% 3.68/0.99  fof(f28,plain,(
% 3.68/0.99    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.68/0.99    inference(ennf_transformation,[],[f9])).
% 3.68/0.99  
% 3.68/0.99  fof(f62,plain,(
% 3.68/0.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.68/0.99    inference(cnf_transformation,[],[f28])).
% 3.68/0.99  
% 3.68/0.99  fof(f2,axiom,(
% 3.68/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/0.99  
% 3.68/0.99  fof(f21,plain,(
% 3.68/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.68/0.99    inference(ennf_transformation,[],[f2])).
% 3.68/0.99  
% 3.68/0.99  fof(f44,plain,(
% 3.68/0.99    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.68/0.99    inference(nnf_transformation,[],[f21])).
% 3.68/0.99  
% 3.68/0.99  fof(f53,plain,(
% 3.68/0.99    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.68/0.99    inference(cnf_transformation,[],[f44])).
% 3.68/0.99  
% 3.68/0.99  fof(f1,axiom,(
% 3.68/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/0.99  
% 3.68/0.99  fof(f42,plain,(
% 3.68/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.68/0.99    inference(nnf_transformation,[],[f1])).
% 3.68/0.99  
% 3.68/0.99  fof(f43,plain,(
% 3.68/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.68/0.99    inference(flattening,[],[f42])).
% 3.68/0.99  
% 3.68/0.99  fof(f52,plain,(
% 3.68/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.68/0.99    inference(cnf_transformation,[],[f43])).
% 3.68/0.99  
% 3.68/0.99  fof(f3,axiom,(
% 3.68/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 3.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/0.99  
% 3.68/0.99  fof(f22,plain,(
% 3.68/0.99    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.68/0.99    inference(ennf_transformation,[],[f3])).
% 3.68/0.99  
% 3.68/0.99  fof(f55,plain,(
% 3.68/0.99    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.68/0.99    inference(cnf_transformation,[],[f22])).
% 3.68/0.99  
% 3.68/0.99  fof(f6,axiom,(
% 3.68/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) & v2_funct_1(k5_relat_1(X1,X0))) => v2_funct_1(X1))))),
% 3.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/0.99  
% 3.68/0.99  fof(f25,plain,(
% 3.68/0.99    ! [X0] : (! [X1] : ((v2_funct_1(X1) | (~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.68/0.99    inference(ennf_transformation,[],[f6])).
% 3.68/0.99  
% 3.68/0.99  fof(f26,plain,(
% 3.68/0.99    ! [X0] : (! [X1] : (v2_funct_1(X1) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.68/0.99    inference(flattening,[],[f25])).
% 3.68/0.99  
% 3.68/0.99  fof(f59,plain,(
% 3.68/0.99    ( ! [X0,X1] : (v2_funct_1(X1) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.68/0.99    inference(cnf_transformation,[],[f26])).
% 3.68/0.99  
% 3.68/0.99  fof(f10,axiom,(
% 3.68/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/0.99  
% 3.68/0.99  fof(f29,plain,(
% 3.68/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.68/0.99    inference(ennf_transformation,[],[f10])).
% 3.68/0.99  
% 3.68/0.99  fof(f64,plain,(
% 3.68/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.68/0.99    inference(cnf_transformation,[],[f29])).
% 3.68/0.99  
% 3.68/0.99  fof(f17,axiom,(
% 3.68/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 3.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/0.99  
% 3.68/0.99  fof(f38,plain,(
% 3.68/0.99    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.68/0.99    inference(ennf_transformation,[],[f17])).
% 3.68/0.99  
% 3.68/0.99  fof(f39,plain,(
% 3.68/0.99    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.68/0.99    inference(flattening,[],[f38])).
% 3.68/0.99  
% 3.68/0.99  fof(f74,plain,(
% 3.68/0.99    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.68/0.99    inference(cnf_transformation,[],[f39])).
% 3.68/0.99  
% 3.68/0.99  fof(f76,plain,(
% 3.68/0.99    v1_funct_2(sK2,sK0,sK1)),
% 3.68/0.99    inference(cnf_transformation,[],[f49])).
% 3.68/0.99  
% 3.68/0.99  fof(f79,plain,(
% 3.68/0.99    v1_funct_2(sK3,sK1,sK0)),
% 3.68/0.99    inference(cnf_transformation,[],[f49])).
% 3.68/0.99  
% 3.68/0.99  fof(f63,plain,(
% 3.68/0.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.68/0.99    inference(cnf_transformation,[],[f28])).
% 3.68/0.99  
% 3.68/0.99  fof(f12,axiom,(
% 3.68/0.99    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 3.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/0.99  
% 3.68/0.99  fof(f32,plain,(
% 3.68/0.99    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.68/0.99    inference(ennf_transformation,[],[f12])).
% 3.68/0.99  
% 3.68/0.99  fof(f33,plain,(
% 3.68/0.99    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.68/0.99    inference(flattening,[],[f32])).
% 3.68/0.99  
% 3.68/0.99  fof(f46,plain,(
% 3.68/0.99    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.68/0.99    inference(nnf_transformation,[],[f33])).
% 3.68/0.99  
% 3.68/0.99  fof(f68,plain,(
% 3.68/0.99    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.68/0.99    inference(cnf_transformation,[],[f46])).
% 3.68/0.99  
% 3.68/0.99  fof(f89,plain,(
% 3.68/0.99    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.68/0.99    inference(equality_resolution,[],[f68])).
% 3.68/0.99  
% 3.68/0.99  fof(f82,plain,(
% 3.68/0.99    ~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)),
% 3.68/0.99    inference(cnf_transformation,[],[f49])).
% 3.68/0.99  
% 3.68/0.99  fof(f7,axiom,(
% 3.68/0.99    ! [X0] : v2_funct_1(k6_relat_1(X0))),
% 3.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.68/0.99  
% 3.68/0.99  fof(f60,plain,(
% 3.68/0.99    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 3.68/0.99    inference(cnf_transformation,[],[f7])).
% 3.68/0.99  
% 3.68/0.99  fof(f85,plain,(
% 3.68/0.99    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 3.68/0.99    inference(definition_unfolding,[],[f60,f73])).
% 3.68/0.99  
% 3.68/0.99  cnf(c_29,negated_conjecture,
% 3.68/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.68/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1119,plain,
% 3.68/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_26,negated_conjecture,
% 3.68/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 3.68/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1122,plain,
% 3.68/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_22,plain,
% 3.68/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.68/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.68/0.99      | ~ v1_funct_1(X0)
% 3.68/0.99      | ~ v1_funct_1(X3)
% 3.68/0.99      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.68/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1123,plain,
% 3.68/0.99      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 3.68/0.99      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 3.68/0.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.68/0.99      | v1_funct_1(X4) != iProver_top
% 3.68/0.99      | v1_funct_1(X5) != iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_3174,plain,
% 3.68/0.99      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 3.68/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.68/0.99      | v1_funct_1(X2) != iProver_top
% 3.68/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_1122,c_1123]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_28,negated_conjecture,
% 3.68/0.99      ( v1_funct_1(sK3) ),
% 3.68/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_35,plain,
% 3.68/0.99      ( v1_funct_1(sK3) = iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_3243,plain,
% 3.68/0.99      ( v1_funct_1(X2) != iProver_top
% 3.68/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.68/0.99      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 3.68/0.99      inference(global_propositional_subsumption,
% 3.68/0.99                [status(thm)],
% 3.68/0.99                [c_3174,c_35]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_3244,plain,
% 3.68/0.99      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 3.68/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.68/0.99      | v1_funct_1(X2) != iProver_top ),
% 3.68/0.99      inference(renaming,[status(thm)],[c_3243]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_3251,plain,
% 3.68/0.99      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 3.68/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_1119,c_3244]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_16,plain,
% 3.68/0.99      ( ~ r2_relset_1(X0,X1,X2,X3)
% 3.68/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.68/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.68/0.99      | X3 = X2 ),
% 3.68/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_25,negated_conjecture,
% 3.68/0.99      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 3.68/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_457,plain,
% 3.68/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.68/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.68/0.99      | X3 = X0
% 3.68/0.99      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 3.68/0.99      | k6_partfun1(sK0) != X3
% 3.68/0.99      | sK0 != X2
% 3.68/0.99      | sK0 != X1 ),
% 3.68/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_25]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_458,plain,
% 3.68/0.99      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.68/0.99      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.68/0.99      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.68/0.99      inference(unflattening,[status(thm)],[c_457]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_21,plain,
% 3.68/0.99      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.68/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_47,plain,
% 3.68/0.99      ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.68/0.99      inference(instantiation,[status(thm)],[c_21]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_460,plain,
% 3.68/0.99      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.68/0.99      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.68/0.99      inference(global_propositional_subsumption,
% 3.68/0.99                [status(thm)],
% 3.68/0.99                [c_458,c_47]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1112,plain,
% 3.68/0.99      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.68/0.99      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_460]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_31,negated_conjecture,
% 3.68/0.99      ( v1_funct_1(sK2) ),
% 3.68/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_19,plain,
% 3.68/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.68/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.68/0.99      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.68/0.99      | ~ v1_funct_1(X0)
% 3.68/0.99      | ~ v1_funct_1(X3) ),
% 3.68/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1169,plain,
% 3.68/0.99      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.68/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.68/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.68/0.99      | ~ v1_funct_1(sK2)
% 3.68/0.99      | ~ v1_funct_1(sK3) ),
% 3.68/0.99      inference(instantiation,[status(thm)],[c_19]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1628,plain,
% 3.68/0.99      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.68/0.99      inference(global_propositional_subsumption,
% 3.68/0.99                [status(thm)],
% 3.68/0.99                [c_1112,c_31,c_29,c_28,c_26,c_47,c_458,c_1169]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_3252,plain,
% 3.68/0.99      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 3.68/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.68/0.99      inference(light_normalisation,[status(thm)],[c_3251,c_1628]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_32,plain,
% 3.68/0.99      ( v1_funct_1(sK2) = iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_3505,plain,
% 3.68/0.99      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 3.68/0.99      inference(global_propositional_subsumption,
% 3.68/0.99                [status(thm)],
% 3.68/0.99                [c_3252,c_32]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_8,plain,
% 3.68/0.99      ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
% 3.68/0.99      | ~ v1_funct_1(X0)
% 3.68/0.99      | ~ v1_funct_1(X1)
% 3.68/0.99      | ~ v1_relat_1(X0)
% 3.68/0.99      | ~ v1_relat_1(X1)
% 3.68/0.99      | k1_relat_1(k5_relat_1(X0,X1)) != k1_relat_1(X0) ),
% 3.68/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1131,plain,
% 3.68/0.99      ( k1_relat_1(k5_relat_1(X0,X1)) != k1_relat_1(X0)
% 3.68/0.99      | r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) = iProver_top
% 3.68/0.99      | v1_funct_1(X0) != iProver_top
% 3.68/0.99      | v1_funct_1(X1) != iProver_top
% 3.68/0.99      | v1_relat_1(X0) != iProver_top
% 3.68/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_3507,plain,
% 3.68/0.99      ( k1_relat_1(k6_partfun1(sK0)) != k1_relat_1(sK2)
% 3.68/0.99      | r1_tarski(k2_relat_1(sK2),k1_relat_1(sK3)) = iProver_top
% 3.68/0.99      | v1_funct_1(sK2) != iProver_top
% 3.68/0.99      | v1_funct_1(sK3) != iProver_top
% 3.68/0.99      | v1_relat_1(sK2) != iProver_top
% 3.68/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_3505,c_1131]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_7,plain,
% 3.68/0.99      ( k1_relat_1(k6_partfun1(X0)) = X0 ),
% 3.68/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_3510,plain,
% 3.68/0.99      ( k1_relat_1(sK2) != sK0
% 3.68/0.99      | r1_tarski(k2_relat_1(sK2),k1_relat_1(sK3)) = iProver_top
% 3.68/0.99      | v1_funct_1(sK2) != iProver_top
% 3.68/0.99      | v1_funct_1(sK3) != iProver_top
% 3.68/0.99      | v1_relat_1(sK2) != iProver_top
% 3.68/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.68/0.99      inference(demodulation,[status(thm)],[c_3507,c_7]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_34,plain,
% 3.68/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_37,plain,
% 3.68/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_11,plain,
% 3.68/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.68/0.99      | v1_relat_1(X0) ),
% 3.68/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1215,plain,
% 3.68/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.68/0.99      | v1_relat_1(sK2) ),
% 3.68/0.99      inference(instantiation,[status(thm)],[c_11]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1231,plain,
% 3.68/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.68/0.99      | v1_relat_1(sK2) ),
% 3.68/0.99      inference(instantiation,[status(thm)],[c_1215]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1232,plain,
% 3.68/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.68/0.99      | v1_relat_1(sK2) = iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_1231]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1364,plain,
% 3.68/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.68/0.99      | v1_relat_1(sK3) ),
% 3.68/0.99      inference(instantiation,[status(thm)],[c_11]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1545,plain,
% 3.68/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.68/0.99      | v1_relat_1(sK3) ),
% 3.68/0.99      inference(instantiation,[status(thm)],[c_1364]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1546,plain,
% 3.68/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.68/0.99      | v1_relat_1(sK3) = iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_1545]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_13,plain,
% 3.68/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.68/0.99      | v4_relat_1(X0,X1) ),
% 3.68/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_4,plain,
% 3.68/0.99      ( ~ v4_relat_1(X0,X1)
% 3.68/0.99      | r1_tarski(k1_relat_1(X0),X1)
% 3.68/0.99      | ~ v1_relat_1(X0) ),
% 3.68/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_335,plain,
% 3.68/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.68/0.99      | r1_tarski(k1_relat_1(X0),X1)
% 3.68/0.99      | ~ v1_relat_1(X0) ),
% 3.68/0.99      inference(resolution,[status(thm)],[c_13,c_4]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_339,plain,
% 3.68/0.99      ( r1_tarski(k1_relat_1(X0),X1)
% 3.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.68/0.99      inference(global_propositional_subsumption,
% 3.68/0.99                [status(thm)],
% 3.68/0.99                [c_335,c_11]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_340,plain,
% 3.68/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.68/0.99      | r1_tarski(k1_relat_1(X0),X1) ),
% 3.68/0.99      inference(renaming,[status(thm)],[c_339]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1116,plain,
% 3.68/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.68/0.99      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_340]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_2106,plain,
% 3.68/0.99      ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_1119,c_1116]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_0,plain,
% 3.68/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.68/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1134,plain,
% 3.68/0.99      ( X0 = X1
% 3.68/0.99      | r1_tarski(X0,X1) != iProver_top
% 3.68/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_2486,plain,
% 3.68/0.99      ( k1_relat_1(sK2) = sK0
% 3.68/0.99      | r1_tarski(sK0,k1_relat_1(sK2)) != iProver_top ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_2106,c_1134]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_5,plain,
% 3.68/0.99      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
% 3.68/0.99      | ~ v1_relat_1(X1)
% 3.68/0.99      | ~ v1_relat_1(X0) ),
% 3.68/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1132,plain,
% 3.68/0.99      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) = iProver_top
% 3.68/0.99      | v1_relat_1(X0) != iProver_top
% 3.68/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_3508,plain,
% 3.68/0.99      ( r1_tarski(k1_relat_1(k6_partfun1(sK0)),k1_relat_1(sK2)) = iProver_top
% 3.68/0.99      | v1_relat_1(sK2) != iProver_top
% 3.68/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_3505,c_1132]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_3509,plain,
% 3.68/0.99      ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top
% 3.68/0.99      | v1_relat_1(sK2) != iProver_top
% 3.68/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.68/0.99      inference(demodulation,[status(thm)],[c_3508,c_7]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_3815,plain,
% 3.68/0.99      ( r1_tarski(k2_relat_1(sK2),k1_relat_1(sK3)) = iProver_top ),
% 3.68/0.99      inference(global_propositional_subsumption,
% 3.68/0.99                [status(thm)],
% 3.68/0.99                [c_3510,c_32,c_34,c_35,c_37,c_1232,c_1546,c_2486,c_3509]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_9,plain,
% 3.68/0.99      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
% 3.68/0.99      | v2_funct_1(X0)
% 3.68/0.99      | ~ v2_funct_1(k5_relat_1(X0,X1))
% 3.68/0.99      | ~ v1_funct_1(X0)
% 3.68/0.99      | ~ v1_funct_1(X1)
% 3.68/0.99      | ~ v1_relat_1(X0)
% 3.68/0.99      | ~ v1_relat_1(X1) ),
% 3.68/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1130,plain,
% 3.68/0.99      ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) != iProver_top
% 3.68/0.99      | v2_funct_1(X0) = iProver_top
% 3.68/0.99      | v2_funct_1(k5_relat_1(X0,X1)) != iProver_top
% 3.68/0.99      | v1_funct_1(X0) != iProver_top
% 3.68/0.99      | v1_funct_1(X1) != iProver_top
% 3.68/0.99      | v1_relat_1(X0) != iProver_top
% 3.68/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_3820,plain,
% 3.68/0.99      ( v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
% 3.68/0.99      | v2_funct_1(sK2) = iProver_top
% 3.68/0.99      | v1_funct_1(sK2) != iProver_top
% 3.68/0.99      | v1_funct_1(sK3) != iProver_top
% 3.68/0.99      | v1_relat_1(sK2) != iProver_top
% 3.68/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_3815,c_1130]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_3821,plain,
% 3.68/0.99      ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 3.68/0.99      | v2_funct_1(sK2) = iProver_top
% 3.68/0.99      | v1_funct_1(sK2) != iProver_top
% 3.68/0.99      | v1_funct_1(sK3) != iProver_top
% 3.68/0.99      | v1_relat_1(sK2) != iProver_top
% 3.68/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.68/0.99      inference(light_normalisation,[status(thm)],[c_3820,c_3505]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_14,plain,
% 3.68/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.68/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.68/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1127,plain,
% 3.68/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.68/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_2165,plain,
% 3.68/0.99      ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_1122,c_1127]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_23,plain,
% 3.68/0.99      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.68/0.99      | ~ v1_funct_2(X2,X0,X1)
% 3.68/0.99      | ~ v1_funct_2(X3,X1,X0)
% 3.68/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.68/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.68/0.99      | ~ v1_funct_1(X2)
% 3.68/0.99      | ~ v1_funct_1(X3)
% 3.68/0.99      | k2_relset_1(X1,X0,X3) = X0 ),
% 3.68/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_471,plain,
% 3.68/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.68/0.99      | ~ v1_funct_2(X3,X2,X1)
% 3.68/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.68/0.99      | ~ v1_funct_1(X0)
% 3.68/0.99      | ~ v1_funct_1(X3)
% 3.68/0.99      | k1_partfun1(X2,X1,X1,X2,X3,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.68/0.99      | k2_relset_1(X1,X2,X0) = X2
% 3.68/0.99      | k6_partfun1(X2) != k6_partfun1(sK0)
% 3.68/0.99      | sK0 != X2 ),
% 3.68/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_25]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_472,plain,
% 3.68/0.99      ( ~ v1_funct_2(X0,X1,sK0)
% 3.68/0.99      | ~ v1_funct_2(X2,sK0,X1)
% 3.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 3.68/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 3.68/0.99      | ~ v1_funct_1(X0)
% 3.68/0.99      | ~ v1_funct_1(X2)
% 3.68/0.99      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.68/0.99      | k2_relset_1(X1,sK0,X0) = sK0
% 3.68/0.99      | k6_partfun1(sK0) != k6_partfun1(sK0) ),
% 3.68/0.99      inference(unflattening,[status(thm)],[c_471]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_549,plain,
% 3.68/0.99      ( ~ v1_funct_2(X0,X1,sK0)
% 3.68/0.99      | ~ v1_funct_2(X2,sK0,X1)
% 3.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 3.68/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 3.68/0.99      | ~ v1_funct_1(X0)
% 3.68/0.99      | ~ v1_funct_1(X2)
% 3.68/0.99      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.68/0.99      | k2_relset_1(X1,sK0,X0) = sK0 ),
% 3.68/0.99      inference(equality_resolution_simp,[status(thm)],[c_472]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1111,plain,
% 3.68/0.99      ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.68/0.99      | k2_relset_1(X0,sK0,X2) = sK0
% 3.68/0.99      | v1_funct_2(X2,X0,sK0) != iProver_top
% 3.68/0.99      | v1_funct_2(X1,sK0,X0) != iProver_top
% 3.68/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 3.68/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 3.68/0.99      | v1_funct_1(X1) != iProver_top
% 3.68/0.99      | v1_funct_1(X2) != iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_549]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1767,plain,
% 3.68/0.99      ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k6_partfun1(sK0)
% 3.68/0.99      | k2_relset_1(X0,sK0,X2) = sK0
% 3.68/0.99      | v1_funct_2(X2,X0,sK0) != iProver_top
% 3.68/0.99      | v1_funct_2(X1,sK0,X0) != iProver_top
% 3.68/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 3.68/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 3.68/0.99      | v1_funct_1(X2) != iProver_top
% 3.68/0.99      | v1_funct_1(X1) != iProver_top ),
% 3.68/0.99      inference(light_normalisation,[status(thm)],[c_1111,c_1628]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1771,plain,
% 3.68/0.99      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 3.68/0.99      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 3.68/0.99      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 3.68/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.68/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.68/0.99      | v1_funct_1(sK2) != iProver_top
% 3.68/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_1628,c_1767]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_30,negated_conjecture,
% 3.68/0.99      ( v1_funct_2(sK2,sK0,sK1) ),
% 3.68/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_33,plain,
% 3.68/0.99      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_27,negated_conjecture,
% 3.68/0.99      ( v1_funct_2(sK3,sK1,sK0) ),
% 3.68/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_36,plain,
% 3.68/0.99      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1774,plain,
% 3.68/0.99      ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 3.68/0.99      inference(global_propositional_subsumption,
% 3.68/0.99                [status(thm)],
% 3.68/0.99                [c_1771,c_32,c_33,c_34,c_35,c_36,c_37]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_2167,plain,
% 3.68/0.99      ( k2_relat_1(sK3) = sK0 ),
% 3.68/0.99      inference(light_normalisation,[status(thm)],[c_2165,c_1774]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_12,plain,
% 3.68/0.99      ( v5_relat_1(X0,X1)
% 3.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.68/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_17,plain,
% 3.68/0.99      ( v2_funct_2(X0,k2_relat_1(X0))
% 3.68/0.99      | ~ v5_relat_1(X0,k2_relat_1(X0))
% 3.68/0.99      | ~ v1_relat_1(X0) ),
% 3.68/0.99      inference(cnf_transformation,[],[f89]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_375,plain,
% 3.68/0.99      ( v2_funct_2(X0,k2_relat_1(X0))
% 3.68/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.68/0.99      | ~ v1_relat_1(X0)
% 3.68/0.99      | X0 != X1
% 3.68/0.99      | k2_relat_1(X0) != X3 ),
% 3.68/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_17]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_376,plain,
% 3.68/0.99      ( v2_funct_2(X0,k2_relat_1(X0))
% 3.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
% 3.68/0.99      | ~ v1_relat_1(X0) ),
% 3.68/0.99      inference(unflattening,[status(thm)],[c_375]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_386,plain,
% 3.68/0.99      ( v2_funct_2(X0,k2_relat_1(X0))
% 3.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0)))) ),
% 3.68/0.99      inference(forward_subsumption_resolution,
% 3.68/0.99                [status(thm)],
% 3.68/0.99                [c_376,c_11]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_24,negated_conjecture,
% 3.68/0.99      ( ~ v2_funct_2(sK3,sK0) | ~ v2_funct_1(sK2) ),
% 3.68/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_401,plain,
% 3.68/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
% 3.68/0.99      | ~ v2_funct_1(sK2)
% 3.68/0.99      | k2_relat_1(X0) != sK0
% 3.68/0.99      | sK3 != X0 ),
% 3.68/0.99      inference(resolution_lifted,[status(thm)],[c_386,c_24]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_402,plain,
% 3.68/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3))))
% 3.68/0.99      | ~ v2_funct_1(sK2)
% 3.68/0.99      | k2_relat_1(sK3) != sK0 ),
% 3.68/0.99      inference(unflattening,[status(thm)],[c_401]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_686,plain,
% 3.68/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3))))
% 3.68/0.99      | ~ sP0_iProver_split ),
% 3.68/0.99      inference(splitting,
% 3.68/0.99                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 3.68/0.99                [c_402]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1115,plain,
% 3.68/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3)))) != iProver_top
% 3.68/0.99      | sP0_iProver_split != iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_686]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_2555,plain,
% 3.68/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 3.68/0.99      | sP0_iProver_split != iProver_top ),
% 3.68/0.99      inference(demodulation,[status(thm)],[c_2167,c_1115]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_2716,plain,
% 3.68/0.99      ( sP0_iProver_split != iProver_top ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_1122,c_2555]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_687,plain,
% 3.68/0.99      ( ~ v2_funct_1(sK2) | sP0_iProver_split | k2_relat_1(sK3) != sK0 ),
% 3.68/0.99      inference(splitting,
% 3.68/0.99                [splitting(split),new_symbols(definition,[])],
% 3.68/0.99                [c_402]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1114,plain,
% 3.68/0.99      ( k2_relat_1(sK3) != sK0
% 3.68/0.99      | v2_funct_1(sK2) != iProver_top
% 3.68/0.99      | sP0_iProver_split = iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_687]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_2556,plain,
% 3.68/0.99      ( sK0 != sK0
% 3.68/0.99      | v2_funct_1(sK2) != iProver_top
% 3.68/0.99      | sP0_iProver_split = iProver_top ),
% 3.68/0.99      inference(demodulation,[status(thm)],[c_2167,c_1114]) ).
% 3.68/0.99  
% 3.68/1.00  cnf(c_2557,plain,
% 3.68/1.00      ( v2_funct_1(sK2) != iProver_top
% 3.68/1.00      | sP0_iProver_split = iProver_top ),
% 3.68/1.00      inference(equality_resolution_simp,[status(thm)],[c_2556]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_10,plain,
% 3.68/1.00      ( v2_funct_1(k6_partfun1(X0)) ),
% 3.68/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_79,plain,
% 3.68/1.00      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 3.68/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(c_81,plain,
% 3.68/1.00      ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
% 3.68/1.00      inference(instantiation,[status(thm)],[c_79]) ).
% 3.68/1.00  
% 3.68/1.00  cnf(contradiction,plain,
% 3.68/1.00      ( $false ),
% 3.68/1.00      inference(minisat,
% 3.68/1.00                [status(thm)],
% 3.68/1.00                [c_3821,c_2716,c_2557,c_1546,c_1232,c_81,c_37,c_35,c_34,
% 3.68/1.00                 c_32]) ).
% 3.68/1.00  
% 3.68/1.00  
% 3.68/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.68/1.00  
% 3.68/1.00  ------                               Statistics
% 3.68/1.00  
% 3.68/1.00  ------ General
% 3.68/1.00  
% 3.68/1.00  abstr_ref_over_cycles:                  0
% 3.68/1.00  abstr_ref_under_cycles:                 0
% 3.68/1.00  gc_basic_clause_elim:                   0
% 3.68/1.00  forced_gc_time:                         0
% 3.68/1.00  parsing_time:                           0.014
% 3.68/1.00  unif_index_cands_time:                  0.
% 3.68/1.00  unif_index_add_time:                    0.
% 3.68/1.00  orderings_time:                         0.
% 3.68/1.00  out_proof_time:                         0.012
% 3.68/1.00  total_time:                             0.178
% 3.68/1.00  num_of_symbols:                         54
% 3.68/1.00  num_of_terms:                           6132
% 3.68/1.00  
% 3.68/1.00  ------ Preprocessing
% 3.68/1.00  
% 3.68/1.00  num_of_splits:                          1
% 3.68/1.00  num_of_split_atoms:                     1
% 3.68/1.00  num_of_reused_defs:                     0
% 3.68/1.00  num_eq_ax_congr_red:                    19
% 3.68/1.00  num_of_sem_filtered_clauses:            1
% 3.68/1.00  num_of_subtypes:                        0
% 3.68/1.00  monotx_restored_types:                  0
% 3.68/1.00  sat_num_of_epr_types:                   0
% 3.68/1.00  sat_num_of_non_cyclic_types:            0
% 3.68/1.00  sat_guarded_non_collapsed_types:        0
% 3.68/1.00  num_pure_diseq_elim:                    0
% 3.68/1.00  simp_replaced_by:                       0
% 3.68/1.00  res_preprocessed:                       137
% 3.68/1.00  prep_upred:                             0
% 3.68/1.00  prep_unflattend:                        17
% 3.68/1.00  smt_new_axioms:                         0
% 3.68/1.00  pred_elim_cands:                        6
% 3.68/1.00  pred_elim:                              4
% 3.68/1.00  pred_elim_cl:                           6
% 3.68/1.00  pred_elim_cycles:                       6
% 3.68/1.00  merged_defs:                            0
% 3.68/1.00  merged_defs_ncl:                        0
% 3.68/1.00  bin_hyper_res:                          0
% 3.68/1.00  prep_cycles:                            4
% 3.68/1.00  pred_elim_time:                         0.005
% 3.68/1.00  splitting_time:                         0.
% 3.68/1.00  sem_filter_time:                        0.
% 3.68/1.00  monotx_time:                            0.
% 3.68/1.00  subtype_inf_time:                       0.
% 3.68/1.00  
% 3.68/1.00  ------ Problem properties
% 3.68/1.00  
% 3.68/1.00  clauses:                                26
% 3.68/1.00  conjectures:                            6
% 3.68/1.00  epr:                                    6
% 3.68/1.00  horn:                                   26
% 3.68/1.00  ground:                                 8
% 3.68/1.00  unary:                                  11
% 3.68/1.00  binary:                                 5
% 3.68/1.00  lits:                                   74
% 3.68/1.00  lits_eq:                                12
% 3.68/1.00  fd_pure:                                0
% 3.68/1.00  fd_pseudo:                              0
% 3.68/1.00  fd_cond:                                0
% 3.68/1.00  fd_pseudo_cond:                         1
% 3.68/1.00  ac_symbols:                             0
% 3.68/1.00  
% 3.68/1.00  ------ Propositional Solver
% 3.68/1.00  
% 3.68/1.00  prop_solver_calls:                      30
% 3.68/1.00  prop_fast_solver_calls:                 971
% 3.68/1.00  smt_solver_calls:                       0
% 3.68/1.00  smt_fast_solver_calls:                  0
% 3.68/1.00  prop_num_of_clauses:                    1795
% 3.68/1.00  prop_preprocess_simplified:             6130
% 3.68/1.00  prop_fo_subsumed:                       23
% 3.68/1.00  prop_solver_time:                       0.
% 3.68/1.00  smt_solver_time:                        0.
% 3.68/1.00  smt_fast_solver_time:                   0.
% 3.68/1.00  prop_fast_solver_time:                  0.
% 3.68/1.00  prop_unsat_core_time:                   0.
% 3.68/1.00  
% 3.68/1.00  ------ QBF
% 3.68/1.00  
% 3.68/1.00  qbf_q_res:                              0
% 3.68/1.00  qbf_num_tautologies:                    0
% 3.68/1.00  qbf_prep_cycles:                        0
% 3.68/1.00  
% 3.68/1.00  ------ BMC1
% 3.68/1.00  
% 3.68/1.00  bmc1_current_bound:                     -1
% 3.68/1.00  bmc1_last_solved_bound:                 -1
% 3.68/1.00  bmc1_unsat_core_size:                   -1
% 3.68/1.00  bmc1_unsat_core_parents_size:           -1
% 3.68/1.00  bmc1_merge_next_fun:                    0
% 3.68/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.68/1.00  
% 3.68/1.00  ------ Instantiation
% 3.68/1.00  
% 3.68/1.00  inst_num_of_clauses:                    468
% 3.68/1.00  inst_num_in_passive:                    226
% 3.68/1.00  inst_num_in_active:                     227
% 3.68/1.00  inst_num_in_unprocessed:                15
% 3.68/1.00  inst_num_of_loops:                      250
% 3.68/1.00  inst_num_of_learning_restarts:          0
% 3.68/1.00  inst_num_moves_active_passive:          20
% 3.68/1.00  inst_lit_activity:                      0
% 3.68/1.00  inst_lit_activity_moves:                0
% 3.68/1.00  inst_num_tautologies:                   0
% 3.68/1.00  inst_num_prop_implied:                  0
% 3.68/1.00  inst_num_existing_simplified:           0
% 3.68/1.00  inst_num_eq_res_simplified:             0
% 3.68/1.00  inst_num_child_elim:                    0
% 3.68/1.00  inst_num_of_dismatching_blockings:      49
% 3.68/1.00  inst_num_of_non_proper_insts:           512
% 3.68/1.00  inst_num_of_duplicates:                 0
% 3.68/1.00  inst_inst_num_from_inst_to_res:         0
% 3.68/1.00  inst_dismatching_checking_time:         0.
% 3.68/1.00  
% 3.68/1.00  ------ Resolution
% 3.68/1.00  
% 3.68/1.00  res_num_of_clauses:                     0
% 3.68/1.00  res_num_in_passive:                     0
% 3.68/1.00  res_num_in_active:                      0
% 3.68/1.00  res_num_of_loops:                       141
% 3.68/1.00  res_forward_subset_subsumed:            36
% 3.68/1.00  res_backward_subset_subsumed:           0
% 3.68/1.00  res_forward_subsumed:                   0
% 3.68/1.00  res_backward_subsumed:                  0
% 3.68/1.00  res_forward_subsumption_resolution:     3
% 3.68/1.00  res_backward_subsumption_resolution:    0
% 3.68/1.00  res_clause_to_clause_subsumption:       128
% 3.68/1.00  res_orphan_elimination:                 0
% 3.68/1.00  res_tautology_del:                      32
% 3.68/1.00  res_num_eq_res_simplified:              1
% 3.68/1.00  res_num_sel_changes:                    0
% 3.68/1.00  res_moves_from_active_to_pass:          0
% 3.68/1.00  
% 3.68/1.00  ------ Superposition
% 3.68/1.00  
% 3.68/1.00  sup_time_total:                         0.
% 3.68/1.00  sup_time_generating:                    0.
% 3.68/1.00  sup_time_sim_full:                      0.
% 3.68/1.00  sup_time_sim_immed:                     0.
% 3.68/1.00  
% 3.68/1.00  sup_num_of_clauses:                     69
% 3.68/1.00  sup_num_in_active:                      45
% 3.68/1.00  sup_num_in_passive:                     24
% 3.68/1.00  sup_num_of_loops:                       49
% 3.68/1.00  sup_fw_superposition:                   31
% 3.68/1.00  sup_bw_superposition:                   20
% 3.68/1.00  sup_immediate_simplified:               12
% 3.68/1.00  sup_given_eliminated:                   1
% 3.68/1.00  comparisons_done:                       0
% 3.68/1.00  comparisons_avoided:                    0
% 3.68/1.00  
% 3.68/1.00  ------ Simplifications
% 3.68/1.00  
% 3.68/1.00  
% 3.68/1.00  sim_fw_subset_subsumed:                 2
% 3.68/1.00  sim_bw_subset_subsumed:                 1
% 3.68/1.00  sim_fw_subsumed:                        2
% 3.68/1.00  sim_bw_subsumed:                        1
% 3.68/1.00  sim_fw_subsumption_res:                 0
% 3.68/1.00  sim_bw_subsumption_res:                 0
% 3.68/1.00  sim_tautology_del:                      0
% 3.68/1.00  sim_eq_tautology_del:                   0
% 3.68/1.00  sim_eq_res_simp:                        1
% 3.68/1.00  sim_fw_demodulated:                     3
% 3.68/1.00  sim_bw_demodulated:                     3
% 3.68/1.00  sim_light_normalised:                   6
% 3.68/1.00  sim_joinable_taut:                      0
% 3.68/1.00  sim_joinable_simp:                      0
% 3.68/1.00  sim_ac_normalised:                      0
% 3.68/1.00  sim_smt_subsumption:                    0
% 3.68/1.00  
%------------------------------------------------------------------------------
