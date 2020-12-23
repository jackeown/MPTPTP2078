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
% DateTime   : Thu Dec  3 12:07:15 EST 2020

% Result     : Theorem 3.23s
% Output     : CNFRefutation 3.23s
% Verified   : 
% Statistics : Number of formulae       :  187 ( 680 expanded)
%              Number of clauses        :  116 ( 205 expanded)
%              Number of leaves         :   19 ( 168 expanded)
%              Depth                    :   21
%              Number of atoms          :  659 (4755 expanded)
%              Number of equality atoms :  224 ( 334 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f24])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v3_funct_2(X2,X0,X0)
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
           => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v3_funct_2(X2,X0,X0)
              & v1_funct_2(X2,X0,X0)
              & v1_funct_1(X2) )
           => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
             => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f38,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f39,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f38])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
     => ( ~ r2_relset_1(X0,X0,sK2,k2_funct_2(X0,X1))
        & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,sK2),k6_partfun1(X0))
        & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(sK2,X0,X0)
        & v1_funct_2(sK2,X0,X0)
        & v1_funct_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
            & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v3_funct_2(X2,X0,X0)
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ? [X2] :
          ( ~ r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1))
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
          & v3_funct_2(X2,sK0,sK0)
          & v1_funct_2(X2,sK0,sK0)
          & v1_funct_1(X2) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v3_funct_2(sK1,sK0,sK0)
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK2,sK0,sK0)
    & v1_funct_2(sK2,sK0,sK0)
    & v1_funct_1(sK2)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK1,sK0,sK0)
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f39,f43,f42])).

fof(f72,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f44])).

fof(f10,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f59,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f64,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f67,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f44])).

fof(f68,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f71,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f44])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f30])).

fof(f58,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f32])).

fof(f60,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
              & k2_relat_1(X0) = k1_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
      | k2_relat_1(X0) != k1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f13,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
      | k2_relat_1(X0) != k1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f47,f62])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f26])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f66,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f65,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f4])).

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

fof(f69,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f75,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f51])).

fof(f73,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f44])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_1(X1) = k2_funct_2(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_782,plain,
    ( ~ m1_subset_1(X0_50,X0_52)
    | m1_subset_1(X1_50,X1_52)
    | X1_52 != X0_52
    | X1_50 != X0_50 ),
    theory(equality)).

cnf(c_1280,plain,
    ( m1_subset_1(X0_50,X0_52)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | X0_52 != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | X0_50 != sK2 ),
    inference(instantiation,[status(thm)],[c_782])).

cnf(c_4540,plain,
    ( m1_subset_1(k2_funct_1(sK1),X0_52)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | X0_52 != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | k2_funct_1(sK1) != sK2 ),
    inference(instantiation,[status(thm)],[c_1280])).

cnf(c_7109,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | k2_funct_1(sK1) != sK2 ),
    inference(instantiation,[status(thm)],[c_4540])).

cnf(c_6,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_19,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_349,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_19])).

cnf(c_350,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) ),
    inference(unflattening,[status(thm)],[c_349])).

cnf(c_14,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_48,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_352,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_350,c_48])).

cnf(c_761,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) ),
    inference(subtyping,[status(esa)],[c_352])).

cnf(c_1121,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2)
    | m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_761])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_23,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_770,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51)))
    | m1_subset_1(k1_partfun1(X2_51,X3_51,X0_51,X1_51,X1_50,X0_50),k1_zfmisc_1(k2_zfmisc_1(X2_51,X1_51)))
    | ~ v1_funct_1(X0_50)
    | ~ v1_funct_1(X1_50) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1295,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_770])).

cnf(c_2067,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1121,c_27,c_24,c_23,c_20,c_761,c_1295])).

cnf(c_764,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1118,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_764])).

cnf(c_766,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1116,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_766])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_767,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51)))
    | ~ v1_funct_1(X0_50)
    | ~ v1_funct_1(X1_50)
    | k1_partfun1(X2_51,X3_51,X0_51,X1_51,X1_50,X0_50) = k5_relat_1(X1_50,X0_50) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1115,plain,
    ( k1_partfun1(X0_51,X1_51,X2_51,X3_51,X0_50,X1_50) = k5_relat_1(X0_50,X1_50)
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_funct_1(X1_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_767])).

cnf(c_1737,plain,
    ( k1_partfun1(X0_51,X1_51,sK0,sK0,X0_50,sK2) = k5_relat_1(X0_50,sK2)
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1116,c_1115])).

cnf(c_32,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1854,plain,
    ( v1_funct_1(X0_50) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | k1_partfun1(X0_51,X1_51,sK0,sK0,X0_50,sK2) = k5_relat_1(X0_50,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1737,c_32])).

cnf(c_1855,plain,
    ( k1_partfun1(X0_51,X1_51,sK0,sK0,X0_50,sK2) = k5_relat_1(X0_50,sK2)
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(renaming,[status(thm)],[c_1854])).

cnf(c_1864,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2)
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1118,c_1855])).

cnf(c_28,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_31,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1782,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2)
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1737])).

cnf(c_1987,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1864,c_28,c_31,c_32,c_1782])).

cnf(c_2070,plain,
    ( k5_relat_1(sK1,sK2) = k6_partfun1(sK0) ),
    inference(demodulation,[status(thm)],[c_2067,c_1987])).

cnf(c_2,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X1,X0) != k6_partfun1(k1_relat_1(X1))
    | k2_relat_1(X1) != k1_relat_1(X0)
    | k2_funct_1(X1) = X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_8,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_25,negated_conjecture,
    ( v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_533,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | sK1 != X0
    | sK0 != X1
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_25])).

cnf(c_534,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | v2_funct_1(sK1) ),
    inference(unflattening,[status(thm)],[c_533])).

cnf(c_536,plain,
    ( v2_funct_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_534,c_27,c_24])).

cnf(c_584,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X1,X0) != k6_partfun1(k1_relat_1(X1))
    | k2_relat_1(X1) != k1_relat_1(X0)
    | k2_funct_1(X1) = X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_536])).

cnf(c_585,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK1)
    | k5_relat_1(sK1,X0) != k6_partfun1(k1_relat_1(sK1))
    | k2_relat_1(sK1) != k1_relat_1(X0)
    | k2_funct_1(sK1) = X0 ),
    inference(unflattening,[status(thm)],[c_584])).

cnf(c_589,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK1)
    | k5_relat_1(sK1,X0) != k6_partfun1(k1_relat_1(sK1))
    | k2_relat_1(sK1) != k1_relat_1(X0)
    | k2_funct_1(sK1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_585,c_27])).

cnf(c_753,plain,
    ( ~ v1_funct_1(X0_50)
    | ~ v1_relat_1(X0_50)
    | ~ v1_relat_1(sK1)
    | k2_relat_1(sK1) != k1_relat_1(X0_50)
    | k5_relat_1(sK1,X0_50) != k6_partfun1(k1_relat_1(sK1))
    | k2_funct_1(sK1) = X0_50 ),
    inference(subtyping,[status(esa)],[c_589])).

cnf(c_1125,plain,
    ( k2_relat_1(sK1) != k1_relat_1(X0_50)
    | k5_relat_1(sK1,X0_50) != k6_partfun1(k1_relat_1(sK1))
    | k2_funct_1(sK1) = X0_50
    | v1_funct_1(X0_50) != iProver_top
    | v1_relat_1(X0_50) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_753])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_84,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_86,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_84])).

cnf(c_836,plain,
    ( k2_relat_1(sK1) != k1_relat_1(X0_50)
    | k5_relat_1(sK1,X0_50) != k6_partfun1(k1_relat_1(sK1))
    | k2_funct_1(sK1) = X0_50
    | v1_funct_1(X0_50) != iProver_top
    | v1_relat_1(X0_50) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_753])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_773,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(X1_50))
    | ~ v1_relat_1(X1_50)
    | v1_relat_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1273,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | v1_relat_1(X0_50)
    | ~ v1_relat_1(k2_zfmisc_1(X0_51,X1_51)) ),
    inference(instantiation,[status(thm)],[c_773])).

cnf(c_1274,plain,
    ( m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_relat_1(X0_50) = iProver_top
    | v1_relat_1(k2_zfmisc_1(X0_51,X1_51)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1273])).

cnf(c_1276,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
    | v1_relat_1(sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1274])).

cnf(c_3063,plain,
    ( v1_relat_1(X0_50) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | k2_funct_1(sK1) = X0_50
    | k5_relat_1(sK1,X0_50) != k6_partfun1(k1_relat_1(sK1))
    | k2_relat_1(sK1) != k1_relat_1(X0_50) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1125,c_31,c_86,c_836,c_1276])).

cnf(c_3064,plain,
    ( k2_relat_1(sK1) != k1_relat_1(X0_50)
    | k5_relat_1(sK1,X0_50) != k6_partfun1(k1_relat_1(sK1))
    | k2_funct_1(sK1) = X0_50
    | v1_funct_1(X0_50) != iProver_top
    | v1_relat_1(X0_50) != iProver_top ),
    inference(renaming,[status(thm)],[c_3063])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_771,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | k1_relset_1(X0_51,X1_51,X0_50) = k1_relat_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1111,plain,
    ( k1_relset_1(X0_51,X1_51,X0_50) = k1_relat_1(X0_50)
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_771])).

cnf(c_1426,plain,
    ( k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_1118,c_1111])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(X1,X1,X0) = X1 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_474,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(X1,X1,X0) = X1
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_26])).

cnf(c_475,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | k1_relset_1(sK0,sK0,sK1) = sK0 ),
    inference(unflattening,[status(thm)],[c_474])).

cnf(c_477,plain,
    ( k1_relset_1(sK0,sK0,sK1) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_475,c_27,c_24])).

cnf(c_758,plain,
    ( k1_relset_1(sK0,sK0,sK1) = sK0 ),
    inference(subtyping,[status(esa)],[c_477])).

cnf(c_1431,plain,
    ( k1_relat_1(sK1) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_1426,c_758])).

cnf(c_7,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | v2_funct_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_11,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_424,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ v5_relat_1(X3,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X3)
    | X3 != X0
    | X4 != X2
    | k2_relat_1(X3) = X4 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_11])).

cnf(c_425,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ v5_relat_1(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(unflattening,[status(thm)],[c_424])).

cnf(c_3,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_441,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_425,c_3])).

cnf(c_519,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X2
    | sK1 != X0
    | sK0 != X1
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_441,c_25])).

cnf(c_520,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k2_relat_1(sK1) = sK0 ),
    inference(unflattening,[status(thm)],[c_519])).

cnf(c_522,plain,
    ( ~ v1_relat_1(sK1)
    | k2_relat_1(sK1) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_520,c_27,c_24])).

cnf(c_755,plain,
    ( ~ v1_relat_1(sK1)
    | k2_relat_1(sK1) = sK0 ),
    inference(subtyping,[status(esa)],[c_522])).

cnf(c_1123,plain,
    ( k2_relat_1(sK1) = sK0
    | v1_relat_1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_755])).

cnf(c_85,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1275,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_1273])).

cnf(c_1548,plain,
    ( k2_relat_1(sK1) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1123,c_24,c_85,c_755,c_1275])).

cnf(c_3067,plain,
    ( k1_relat_1(X0_50) != sK0
    | k5_relat_1(sK1,X0_50) != k6_partfun1(sK0)
    | k2_funct_1(sK1) = X0_50
    | v1_funct_1(X0_50) != iProver_top
    | v1_relat_1(X0_50) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3064,c_1431,c_1548])).

cnf(c_3076,plain,
    ( k1_relat_1(sK2) != sK0
    | k2_funct_1(sK1) = sK2
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2070,c_3067])).

cnf(c_1425,plain,
    ( k1_relset_1(sK0,sK0,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1116,c_1111])).

cnf(c_22,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_458,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(X1,X1,X0) = X1
    | sK2 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_22])).

cnf(c_459,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | k1_relset_1(sK0,sK0,sK2) = sK0 ),
    inference(unflattening,[status(thm)],[c_458])).

cnf(c_461,plain,
    ( k1_relset_1(sK0,sK0,sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_459,c_23,c_20])).

cnf(c_760,plain,
    ( k1_relset_1(sK0,sK0,sK2) = sK0 ),
    inference(subtyping,[status(esa)],[c_461])).

cnf(c_1434,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_1425,c_760])).

cnf(c_3077,plain,
    ( sK0 != sK0
    | k2_funct_1(sK1) = sK2
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3076,c_1434])).

cnf(c_3078,plain,
    ( k2_funct_1(sK1) = sK2
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3077])).

cnf(c_1346,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ v1_relat_1(k2_zfmisc_1(X0_51,X1_51))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1273])).

cnf(c_1347,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(X0_51,X1_51)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1346])).

cnf(c_1349,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1347])).

cnf(c_777,plain,
    ( X0_52 = X0_52 ),
    theory(equality)).

cnf(c_1327,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_777])).

cnf(c_5,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_18,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_339,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_funct_2(sK0,sK1) != X0
    | sK2 != X0
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_18])).

cnf(c_340,plain,
    ( ~ m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK2 != k2_funct_2(sK0,sK1) ),
    inference(unflattening,[status(thm)],[c_339])).

cnf(c_762,plain,
    ( ~ m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK2 != k2_funct_2(sK0,sK1) ),
    inference(subtyping,[status(esa)],[c_340])).

cnf(c_1120,plain,
    ( sK2 != k2_funct_2(sK0,sK1)
    | m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_762])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_482,plain,
    ( ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0)
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_26])).

cnf(c_483,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(unflattening,[status(thm)],[c_482])).

cnf(c_485,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_483,c_27,c_25,c_24])).

cnf(c_757,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(subtyping,[status(esa)],[c_485])).

cnf(c_1164,plain,
    ( k2_funct_1(sK1) != sK2
    | m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1120,c_757])).

cnf(c_1247,plain,
    ( ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k2_funct_1(sK1) != sK2 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1164])).

cnf(c_35,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7109,c_3078,c_1349,c_1327,c_1247,c_86,c_35,c_20,c_32])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:45:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.23/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.23/1.00  
% 3.23/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.23/1.00  
% 3.23/1.00  ------  iProver source info
% 3.23/1.00  
% 3.23/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.23/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.23/1.00  git: non_committed_changes: false
% 3.23/1.00  git: last_make_outside_of_git: false
% 3.23/1.00  
% 3.23/1.00  ------ 
% 3.23/1.00  
% 3.23/1.00  ------ Input Options
% 3.23/1.00  
% 3.23/1.00  --out_options                           all
% 3.23/1.00  --tptp_safe_out                         true
% 3.23/1.00  --problem_path                          ""
% 3.23/1.00  --include_path                          ""
% 3.23/1.00  --clausifier                            res/vclausify_rel
% 3.23/1.00  --clausifier_options                    --mode clausify
% 3.23/1.00  --stdin                                 false
% 3.23/1.00  --stats_out                             all
% 3.23/1.00  
% 3.23/1.00  ------ General Options
% 3.23/1.00  
% 3.23/1.00  --fof                                   false
% 3.23/1.00  --time_out_real                         305.
% 3.23/1.00  --time_out_virtual                      -1.
% 3.23/1.00  --symbol_type_check                     false
% 3.23/1.00  --clausify_out                          false
% 3.23/1.00  --sig_cnt_out                           false
% 3.23/1.00  --trig_cnt_out                          false
% 3.23/1.00  --trig_cnt_out_tolerance                1.
% 3.23/1.00  --trig_cnt_out_sk_spl                   false
% 3.23/1.00  --abstr_cl_out                          false
% 3.23/1.00  
% 3.23/1.00  ------ Global Options
% 3.23/1.00  
% 3.23/1.00  --schedule                              default
% 3.23/1.00  --add_important_lit                     false
% 3.23/1.00  --prop_solver_per_cl                    1000
% 3.23/1.00  --min_unsat_core                        false
% 3.23/1.00  --soft_assumptions                      false
% 3.23/1.00  --soft_lemma_size                       3
% 3.23/1.00  --prop_impl_unit_size                   0
% 3.23/1.00  --prop_impl_unit                        []
% 3.23/1.00  --share_sel_clauses                     true
% 3.23/1.00  --reset_solvers                         false
% 3.23/1.00  --bc_imp_inh                            [conj_cone]
% 3.23/1.00  --conj_cone_tolerance                   3.
% 3.23/1.00  --extra_neg_conj                        none
% 3.23/1.00  --large_theory_mode                     true
% 3.23/1.00  --prolific_symb_bound                   200
% 3.23/1.00  --lt_threshold                          2000
% 3.23/1.00  --clause_weak_htbl                      true
% 3.23/1.00  --gc_record_bc_elim                     false
% 3.23/1.00  
% 3.23/1.00  ------ Preprocessing Options
% 3.23/1.00  
% 3.23/1.00  --preprocessing_flag                    true
% 3.23/1.00  --time_out_prep_mult                    0.1
% 3.23/1.00  --splitting_mode                        input
% 3.23/1.00  --splitting_grd                         true
% 3.23/1.00  --splitting_cvd                         false
% 3.23/1.00  --splitting_cvd_svl                     false
% 3.23/1.00  --splitting_nvd                         32
% 3.23/1.00  --sub_typing                            true
% 3.23/1.00  --prep_gs_sim                           true
% 3.23/1.00  --prep_unflatten                        true
% 3.23/1.00  --prep_res_sim                          true
% 3.23/1.00  --prep_upred                            true
% 3.23/1.00  --prep_sem_filter                       exhaustive
% 3.23/1.00  --prep_sem_filter_out                   false
% 3.23/1.00  --pred_elim                             true
% 3.23/1.00  --res_sim_input                         true
% 3.23/1.00  --eq_ax_congr_red                       true
% 3.23/1.00  --pure_diseq_elim                       true
% 3.23/1.00  --brand_transform                       false
% 3.23/1.00  --non_eq_to_eq                          false
% 3.23/1.00  --prep_def_merge                        true
% 3.23/1.00  --prep_def_merge_prop_impl              false
% 3.23/1.00  --prep_def_merge_mbd                    true
% 3.23/1.00  --prep_def_merge_tr_red                 false
% 3.23/1.00  --prep_def_merge_tr_cl                  false
% 3.23/1.00  --smt_preprocessing                     true
% 3.23/1.00  --smt_ac_axioms                         fast
% 3.23/1.00  --preprocessed_out                      false
% 3.23/1.00  --preprocessed_stats                    false
% 3.23/1.00  
% 3.23/1.00  ------ Abstraction refinement Options
% 3.23/1.00  
% 3.23/1.00  --abstr_ref                             []
% 3.23/1.00  --abstr_ref_prep                        false
% 3.23/1.00  --abstr_ref_until_sat                   false
% 3.23/1.00  --abstr_ref_sig_restrict                funpre
% 3.23/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.23/1.00  --abstr_ref_under                       []
% 3.23/1.00  
% 3.23/1.00  ------ SAT Options
% 3.23/1.00  
% 3.23/1.00  --sat_mode                              false
% 3.23/1.00  --sat_fm_restart_options                ""
% 3.23/1.00  --sat_gr_def                            false
% 3.23/1.00  --sat_epr_types                         true
% 3.23/1.00  --sat_non_cyclic_types                  false
% 3.23/1.00  --sat_finite_models                     false
% 3.23/1.00  --sat_fm_lemmas                         false
% 3.23/1.00  --sat_fm_prep                           false
% 3.23/1.00  --sat_fm_uc_incr                        true
% 3.23/1.00  --sat_out_model                         small
% 3.23/1.00  --sat_out_clauses                       false
% 3.23/1.00  
% 3.23/1.00  ------ QBF Options
% 3.23/1.00  
% 3.23/1.00  --qbf_mode                              false
% 3.23/1.00  --qbf_elim_univ                         false
% 3.23/1.00  --qbf_dom_inst                          none
% 3.23/1.00  --qbf_dom_pre_inst                      false
% 3.23/1.00  --qbf_sk_in                             false
% 3.23/1.00  --qbf_pred_elim                         true
% 3.23/1.00  --qbf_split                             512
% 3.23/1.00  
% 3.23/1.00  ------ BMC1 Options
% 3.23/1.00  
% 3.23/1.00  --bmc1_incremental                      false
% 3.23/1.00  --bmc1_axioms                           reachable_all
% 3.23/1.00  --bmc1_min_bound                        0
% 3.23/1.00  --bmc1_max_bound                        -1
% 3.23/1.00  --bmc1_max_bound_default                -1
% 3.23/1.00  --bmc1_symbol_reachability              true
% 3.23/1.00  --bmc1_property_lemmas                  false
% 3.23/1.00  --bmc1_k_induction                      false
% 3.23/1.00  --bmc1_non_equiv_states                 false
% 3.23/1.00  --bmc1_deadlock                         false
% 3.23/1.00  --bmc1_ucm                              false
% 3.23/1.00  --bmc1_add_unsat_core                   none
% 3.23/1.00  --bmc1_unsat_core_children              false
% 3.23/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.23/1.00  --bmc1_out_stat                         full
% 3.23/1.00  --bmc1_ground_init                      false
% 3.23/1.00  --bmc1_pre_inst_next_state              false
% 3.23/1.00  --bmc1_pre_inst_state                   false
% 3.23/1.00  --bmc1_pre_inst_reach_state             false
% 3.23/1.00  --bmc1_out_unsat_core                   false
% 3.23/1.00  --bmc1_aig_witness_out                  false
% 3.23/1.00  --bmc1_verbose                          false
% 3.23/1.00  --bmc1_dump_clauses_tptp                false
% 3.23/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.23/1.00  --bmc1_dump_file                        -
% 3.23/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.23/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.23/1.00  --bmc1_ucm_extend_mode                  1
% 3.23/1.00  --bmc1_ucm_init_mode                    2
% 3.23/1.00  --bmc1_ucm_cone_mode                    none
% 3.23/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.23/1.00  --bmc1_ucm_relax_model                  4
% 3.23/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.23/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.23/1.00  --bmc1_ucm_layered_model                none
% 3.23/1.00  --bmc1_ucm_max_lemma_size               10
% 3.23/1.00  
% 3.23/1.00  ------ AIG Options
% 3.23/1.00  
% 3.23/1.00  --aig_mode                              false
% 3.23/1.00  
% 3.23/1.00  ------ Instantiation Options
% 3.23/1.00  
% 3.23/1.00  --instantiation_flag                    true
% 3.23/1.00  --inst_sos_flag                         false
% 3.23/1.00  --inst_sos_phase                        true
% 3.23/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.23/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.23/1.00  --inst_lit_sel_side                     num_symb
% 3.23/1.00  --inst_solver_per_active                1400
% 3.23/1.00  --inst_solver_calls_frac                1.
% 3.23/1.00  --inst_passive_queue_type               priority_queues
% 3.23/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.23/1.00  --inst_passive_queues_freq              [25;2]
% 3.23/1.00  --inst_dismatching                      true
% 3.23/1.00  --inst_eager_unprocessed_to_passive     true
% 3.23/1.00  --inst_prop_sim_given                   true
% 3.23/1.00  --inst_prop_sim_new                     false
% 3.23/1.00  --inst_subs_new                         false
% 3.23/1.00  --inst_eq_res_simp                      false
% 3.23/1.00  --inst_subs_given                       false
% 3.23/1.00  --inst_orphan_elimination               true
% 3.23/1.00  --inst_learning_loop_flag               true
% 3.23/1.00  --inst_learning_start                   3000
% 3.23/1.00  --inst_learning_factor                  2
% 3.23/1.00  --inst_start_prop_sim_after_learn       3
% 3.23/1.00  --inst_sel_renew                        solver
% 3.23/1.00  --inst_lit_activity_flag                true
% 3.23/1.00  --inst_restr_to_given                   false
% 3.23/1.00  --inst_activity_threshold               500
% 3.23/1.00  --inst_out_proof                        true
% 3.23/1.00  
% 3.23/1.00  ------ Resolution Options
% 3.23/1.00  
% 3.23/1.00  --resolution_flag                       true
% 3.23/1.00  --res_lit_sel                           adaptive
% 3.23/1.00  --res_lit_sel_side                      none
% 3.23/1.00  --res_ordering                          kbo
% 3.23/1.00  --res_to_prop_solver                    active
% 3.23/1.00  --res_prop_simpl_new                    false
% 3.23/1.00  --res_prop_simpl_given                  true
% 3.23/1.00  --res_passive_queue_type                priority_queues
% 3.23/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.23/1.00  --res_passive_queues_freq               [15;5]
% 3.23/1.00  --res_forward_subs                      full
% 3.23/1.00  --res_backward_subs                     full
% 3.23/1.00  --res_forward_subs_resolution           true
% 3.23/1.00  --res_backward_subs_resolution          true
% 3.23/1.00  --res_orphan_elimination                true
% 3.23/1.00  --res_time_limit                        2.
% 3.23/1.00  --res_out_proof                         true
% 3.23/1.00  
% 3.23/1.00  ------ Superposition Options
% 3.23/1.00  
% 3.23/1.00  --superposition_flag                    true
% 3.23/1.00  --sup_passive_queue_type                priority_queues
% 3.23/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.23/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.23/1.00  --demod_completeness_check              fast
% 3.23/1.00  --demod_use_ground                      true
% 3.23/1.00  --sup_to_prop_solver                    passive
% 3.23/1.00  --sup_prop_simpl_new                    true
% 3.23/1.00  --sup_prop_simpl_given                  true
% 3.23/1.00  --sup_fun_splitting                     false
% 3.23/1.00  --sup_smt_interval                      50000
% 3.23/1.00  
% 3.23/1.00  ------ Superposition Simplification Setup
% 3.23/1.00  
% 3.23/1.00  --sup_indices_passive                   []
% 3.23/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.23/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.23/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.23/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.23/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.23/1.00  --sup_full_bw                           [BwDemod]
% 3.23/1.00  --sup_immed_triv                        [TrivRules]
% 3.23/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.23/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.23/1.00  --sup_immed_bw_main                     []
% 3.23/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.23/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.23/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.23/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.23/1.00  
% 3.23/1.00  ------ Combination Options
% 3.23/1.00  
% 3.23/1.00  --comb_res_mult                         3
% 3.23/1.00  --comb_sup_mult                         2
% 3.23/1.00  --comb_inst_mult                        10
% 3.23/1.00  
% 3.23/1.00  ------ Debug Options
% 3.23/1.00  
% 3.23/1.00  --dbg_backtrace                         false
% 3.23/1.00  --dbg_dump_prop_clauses                 false
% 3.23/1.00  --dbg_dump_prop_clauses_file            -
% 3.23/1.00  --dbg_out_stat                          false
% 3.23/1.00  ------ Parsing...
% 3.23/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.23/1.00  
% 3.23/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 3.23/1.00  
% 3.23/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.23/1.00  
% 3.23/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.23/1.00  ------ Proving...
% 3.23/1.00  ------ Problem Properties 
% 3.23/1.00  
% 3.23/1.00  
% 3.23/1.00  clauses                                 22
% 3.23/1.00  conjectures                             4
% 3.23/1.00  EPR                                     2
% 3.23/1.00  Horn                                    22
% 3.23/1.00  unary                                   10
% 3.23/1.00  binary                                  6
% 3.23/1.00  lits                                    52
% 3.23/1.00  lits eq                                 18
% 3.23/1.00  fd_pure                                 0
% 3.23/1.00  fd_pseudo                               0
% 3.23/1.00  fd_cond                                 2
% 3.23/1.00  fd_pseudo_cond                          0
% 3.23/1.00  AC symbols                              0
% 3.23/1.00  
% 3.23/1.00  ------ Schedule dynamic 5 is on 
% 3.23/1.00  
% 3.23/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.23/1.00  
% 3.23/1.00  
% 3.23/1.00  ------ 
% 3.23/1.00  Current options:
% 3.23/1.00  ------ 
% 3.23/1.00  
% 3.23/1.00  ------ Input Options
% 3.23/1.00  
% 3.23/1.00  --out_options                           all
% 3.23/1.00  --tptp_safe_out                         true
% 3.23/1.00  --problem_path                          ""
% 3.23/1.00  --include_path                          ""
% 3.23/1.00  --clausifier                            res/vclausify_rel
% 3.23/1.00  --clausifier_options                    --mode clausify
% 3.23/1.00  --stdin                                 false
% 3.23/1.00  --stats_out                             all
% 3.23/1.00  
% 3.23/1.00  ------ General Options
% 3.23/1.00  
% 3.23/1.00  --fof                                   false
% 3.23/1.00  --time_out_real                         305.
% 3.23/1.00  --time_out_virtual                      -1.
% 3.23/1.00  --symbol_type_check                     false
% 3.23/1.00  --clausify_out                          false
% 3.23/1.00  --sig_cnt_out                           false
% 3.23/1.00  --trig_cnt_out                          false
% 3.23/1.00  --trig_cnt_out_tolerance                1.
% 3.23/1.00  --trig_cnt_out_sk_spl                   false
% 3.23/1.00  --abstr_cl_out                          false
% 3.23/1.00  
% 3.23/1.00  ------ Global Options
% 3.23/1.00  
% 3.23/1.00  --schedule                              default
% 3.23/1.00  --add_important_lit                     false
% 3.23/1.00  --prop_solver_per_cl                    1000
% 3.23/1.00  --min_unsat_core                        false
% 3.23/1.00  --soft_assumptions                      false
% 3.23/1.00  --soft_lemma_size                       3
% 3.23/1.00  --prop_impl_unit_size                   0
% 3.23/1.00  --prop_impl_unit                        []
% 3.23/1.00  --share_sel_clauses                     true
% 3.23/1.00  --reset_solvers                         false
% 3.23/1.00  --bc_imp_inh                            [conj_cone]
% 3.23/1.00  --conj_cone_tolerance                   3.
% 3.23/1.00  --extra_neg_conj                        none
% 3.23/1.00  --large_theory_mode                     true
% 3.23/1.00  --prolific_symb_bound                   200
% 3.23/1.00  --lt_threshold                          2000
% 3.23/1.00  --clause_weak_htbl                      true
% 3.23/1.00  --gc_record_bc_elim                     false
% 3.23/1.00  
% 3.23/1.00  ------ Preprocessing Options
% 3.23/1.00  
% 3.23/1.00  --preprocessing_flag                    true
% 3.23/1.00  --time_out_prep_mult                    0.1
% 3.23/1.00  --splitting_mode                        input
% 3.23/1.00  --splitting_grd                         true
% 3.23/1.00  --splitting_cvd                         false
% 3.23/1.00  --splitting_cvd_svl                     false
% 3.23/1.00  --splitting_nvd                         32
% 3.23/1.00  --sub_typing                            true
% 3.23/1.00  --prep_gs_sim                           true
% 3.23/1.00  --prep_unflatten                        true
% 3.23/1.00  --prep_res_sim                          true
% 3.23/1.00  --prep_upred                            true
% 3.23/1.00  --prep_sem_filter                       exhaustive
% 3.23/1.00  --prep_sem_filter_out                   false
% 3.23/1.00  --pred_elim                             true
% 3.23/1.00  --res_sim_input                         true
% 3.23/1.00  --eq_ax_congr_red                       true
% 3.23/1.00  --pure_diseq_elim                       true
% 3.23/1.00  --brand_transform                       false
% 3.23/1.00  --non_eq_to_eq                          false
% 3.23/1.00  --prep_def_merge                        true
% 3.23/1.00  --prep_def_merge_prop_impl              false
% 3.23/1.00  --prep_def_merge_mbd                    true
% 3.23/1.00  --prep_def_merge_tr_red                 false
% 3.23/1.00  --prep_def_merge_tr_cl                  false
% 3.23/1.00  --smt_preprocessing                     true
% 3.23/1.00  --smt_ac_axioms                         fast
% 3.23/1.00  --preprocessed_out                      false
% 3.23/1.00  --preprocessed_stats                    false
% 3.23/1.00  
% 3.23/1.00  ------ Abstraction refinement Options
% 3.23/1.00  
% 3.23/1.00  --abstr_ref                             []
% 3.23/1.00  --abstr_ref_prep                        false
% 3.23/1.00  --abstr_ref_until_sat                   false
% 3.23/1.00  --abstr_ref_sig_restrict                funpre
% 3.23/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.23/1.00  --abstr_ref_under                       []
% 3.23/1.00  
% 3.23/1.00  ------ SAT Options
% 3.23/1.00  
% 3.23/1.00  --sat_mode                              false
% 3.23/1.00  --sat_fm_restart_options                ""
% 3.23/1.00  --sat_gr_def                            false
% 3.23/1.00  --sat_epr_types                         true
% 3.23/1.00  --sat_non_cyclic_types                  false
% 3.23/1.00  --sat_finite_models                     false
% 3.23/1.00  --sat_fm_lemmas                         false
% 3.23/1.00  --sat_fm_prep                           false
% 3.23/1.00  --sat_fm_uc_incr                        true
% 3.23/1.00  --sat_out_model                         small
% 3.23/1.00  --sat_out_clauses                       false
% 3.23/1.00  
% 3.23/1.00  ------ QBF Options
% 3.23/1.00  
% 3.23/1.00  --qbf_mode                              false
% 3.23/1.00  --qbf_elim_univ                         false
% 3.23/1.00  --qbf_dom_inst                          none
% 3.23/1.00  --qbf_dom_pre_inst                      false
% 3.23/1.00  --qbf_sk_in                             false
% 3.23/1.00  --qbf_pred_elim                         true
% 3.23/1.00  --qbf_split                             512
% 3.23/1.00  
% 3.23/1.00  ------ BMC1 Options
% 3.23/1.00  
% 3.23/1.00  --bmc1_incremental                      false
% 3.23/1.00  --bmc1_axioms                           reachable_all
% 3.23/1.00  --bmc1_min_bound                        0
% 3.23/1.00  --bmc1_max_bound                        -1
% 3.23/1.00  --bmc1_max_bound_default                -1
% 3.23/1.00  --bmc1_symbol_reachability              true
% 3.23/1.00  --bmc1_property_lemmas                  false
% 3.23/1.00  --bmc1_k_induction                      false
% 3.23/1.00  --bmc1_non_equiv_states                 false
% 3.23/1.00  --bmc1_deadlock                         false
% 3.23/1.00  --bmc1_ucm                              false
% 3.23/1.00  --bmc1_add_unsat_core                   none
% 3.23/1.00  --bmc1_unsat_core_children              false
% 3.23/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.23/1.00  --bmc1_out_stat                         full
% 3.23/1.00  --bmc1_ground_init                      false
% 3.23/1.00  --bmc1_pre_inst_next_state              false
% 3.23/1.00  --bmc1_pre_inst_state                   false
% 3.23/1.00  --bmc1_pre_inst_reach_state             false
% 3.23/1.00  --bmc1_out_unsat_core                   false
% 3.23/1.00  --bmc1_aig_witness_out                  false
% 3.23/1.00  --bmc1_verbose                          false
% 3.23/1.00  --bmc1_dump_clauses_tptp                false
% 3.23/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.23/1.00  --bmc1_dump_file                        -
% 3.23/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.23/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.23/1.00  --bmc1_ucm_extend_mode                  1
% 3.23/1.00  --bmc1_ucm_init_mode                    2
% 3.23/1.00  --bmc1_ucm_cone_mode                    none
% 3.23/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.23/1.00  --bmc1_ucm_relax_model                  4
% 3.23/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.23/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.23/1.00  --bmc1_ucm_layered_model                none
% 3.23/1.00  --bmc1_ucm_max_lemma_size               10
% 3.23/1.00  
% 3.23/1.00  ------ AIG Options
% 3.23/1.00  
% 3.23/1.00  --aig_mode                              false
% 3.23/1.00  
% 3.23/1.00  ------ Instantiation Options
% 3.23/1.00  
% 3.23/1.00  --instantiation_flag                    true
% 3.23/1.00  --inst_sos_flag                         false
% 3.23/1.00  --inst_sos_phase                        true
% 3.23/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.23/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.23/1.00  --inst_lit_sel_side                     none
% 3.23/1.00  --inst_solver_per_active                1400
% 3.23/1.00  --inst_solver_calls_frac                1.
% 3.23/1.00  --inst_passive_queue_type               priority_queues
% 3.23/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.23/1.00  --inst_passive_queues_freq              [25;2]
% 3.23/1.00  --inst_dismatching                      true
% 3.23/1.00  --inst_eager_unprocessed_to_passive     true
% 3.23/1.00  --inst_prop_sim_given                   true
% 3.23/1.00  --inst_prop_sim_new                     false
% 3.23/1.00  --inst_subs_new                         false
% 3.23/1.00  --inst_eq_res_simp                      false
% 3.23/1.00  --inst_subs_given                       false
% 3.23/1.00  --inst_orphan_elimination               true
% 3.23/1.00  --inst_learning_loop_flag               true
% 3.23/1.00  --inst_learning_start                   3000
% 3.23/1.00  --inst_learning_factor                  2
% 3.23/1.00  --inst_start_prop_sim_after_learn       3
% 3.23/1.00  --inst_sel_renew                        solver
% 3.23/1.00  --inst_lit_activity_flag                true
% 3.23/1.00  --inst_restr_to_given                   false
% 3.23/1.00  --inst_activity_threshold               500
% 3.23/1.00  --inst_out_proof                        true
% 3.23/1.00  
% 3.23/1.00  ------ Resolution Options
% 3.23/1.00  
% 3.23/1.00  --resolution_flag                       false
% 3.23/1.00  --res_lit_sel                           adaptive
% 3.23/1.00  --res_lit_sel_side                      none
% 3.23/1.00  --res_ordering                          kbo
% 3.23/1.00  --res_to_prop_solver                    active
% 3.23/1.00  --res_prop_simpl_new                    false
% 3.23/1.00  --res_prop_simpl_given                  true
% 3.23/1.00  --res_passive_queue_type                priority_queues
% 3.23/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.23/1.00  --res_passive_queues_freq               [15;5]
% 3.23/1.00  --res_forward_subs                      full
% 3.23/1.00  --res_backward_subs                     full
% 3.23/1.00  --res_forward_subs_resolution           true
% 3.23/1.00  --res_backward_subs_resolution          true
% 3.23/1.00  --res_orphan_elimination                true
% 3.23/1.00  --res_time_limit                        2.
% 3.23/1.00  --res_out_proof                         true
% 3.23/1.00  
% 3.23/1.00  ------ Superposition Options
% 3.23/1.00  
% 3.23/1.00  --superposition_flag                    true
% 3.23/1.00  --sup_passive_queue_type                priority_queues
% 3.23/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.23/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.23/1.00  --demod_completeness_check              fast
% 3.23/1.00  --demod_use_ground                      true
% 3.23/1.00  --sup_to_prop_solver                    passive
% 3.23/1.00  --sup_prop_simpl_new                    true
% 3.23/1.00  --sup_prop_simpl_given                  true
% 3.23/1.00  --sup_fun_splitting                     false
% 3.23/1.00  --sup_smt_interval                      50000
% 3.23/1.00  
% 3.23/1.00  ------ Superposition Simplification Setup
% 3.23/1.00  
% 3.23/1.00  --sup_indices_passive                   []
% 3.23/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.23/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.23/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.23/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.23/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.23/1.00  --sup_full_bw                           [BwDemod]
% 3.23/1.00  --sup_immed_triv                        [TrivRules]
% 3.23/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.23/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.23/1.00  --sup_immed_bw_main                     []
% 3.23/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.23/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.23/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.23/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.23/1.00  
% 3.23/1.00  ------ Combination Options
% 3.23/1.00  
% 3.23/1.00  --comb_res_mult                         3
% 3.23/1.00  --comb_sup_mult                         2
% 3.23/1.00  --comb_inst_mult                        10
% 3.23/1.00  
% 3.23/1.00  ------ Debug Options
% 3.23/1.00  
% 3.23/1.00  --dbg_backtrace                         false
% 3.23/1.00  --dbg_dump_prop_clauses                 false
% 3.23/1.00  --dbg_dump_prop_clauses_file            -
% 3.23/1.00  --dbg_out_stat                          false
% 3.23/1.00  
% 3.23/1.00  
% 3.23/1.00  
% 3.23/1.00  
% 3.23/1.00  ------ Proving...
% 3.23/1.00  
% 3.23/1.00  
% 3.23/1.00  % SZS status Theorem for theBenchmark.p
% 3.23/1.00  
% 3.23/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.23/1.00  
% 3.23/1.00  fof(f6,axiom,(
% 3.23/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.23/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.23/1.00  
% 3.23/1.00  fof(f24,plain,(
% 3.23/1.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.23/1.00    inference(ennf_transformation,[],[f6])).
% 3.23/1.00  
% 3.23/1.00  fof(f25,plain,(
% 3.23/1.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.23/1.00    inference(flattening,[],[f24])).
% 3.23/1.00  
% 3.23/1.00  fof(f40,plain,(
% 3.23/1.00    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.23/1.00    inference(nnf_transformation,[],[f25])).
% 3.23/1.00  
% 3.23/1.00  fof(f50,plain,(
% 3.23/1.00    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.23/1.00    inference(cnf_transformation,[],[f40])).
% 3.23/1.00  
% 3.23/1.00  fof(f15,conjecture,(
% 3.23/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 3.23/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.23/1.00  
% 3.23/1.00  fof(f16,negated_conjecture,(
% 3.23/1.00    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 3.23/1.00    inference(negated_conjecture,[],[f15])).
% 3.23/1.00  
% 3.23/1.00  fof(f38,plain,(
% 3.23/1.00    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 3.23/1.00    inference(ennf_transformation,[],[f16])).
% 3.23/1.00  
% 3.23/1.00  fof(f39,plain,(
% 3.23/1.00    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 3.23/1.00    inference(flattening,[],[f38])).
% 3.23/1.00  
% 3.23/1.00  fof(f43,plain,(
% 3.23/1.00    ( ! [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (~r2_relset_1(X0,X0,sK2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,sK2),k6_partfun1(X0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(sK2,X0,X0) & v1_funct_2(sK2,X0,X0) & v1_funct_1(sK2))) )),
% 3.23/1.00    introduced(choice_axiom,[])).
% 3.23/1.00  
% 3.23/1.00  fof(f42,plain,(
% 3.23/1.00    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(X2,sK0,sK0) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 3.23/1.00    introduced(choice_axiom,[])).
% 3.23/1.00  
% 3.23/1.00  fof(f44,plain,(
% 3.23/1.00    (~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 3.23/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f39,f43,f42])).
% 3.23/1.00  
% 3.23/1.00  fof(f72,plain,(
% 3.23/1.00    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))),
% 3.23/1.00    inference(cnf_transformation,[],[f44])).
% 3.23/1.00  
% 3.23/1.00  fof(f10,axiom,(
% 3.23/1.00    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 3.23/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.23/1.00  
% 3.23/1.00  fof(f17,plain,(
% 3.23/1.00    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.23/1.00    inference(pure_predicate_removal,[],[f10])).
% 3.23/1.00  
% 3.23/1.00  fof(f59,plain,(
% 3.23/1.00    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.23/1.00    inference(cnf_transformation,[],[f17])).
% 3.23/1.00  
% 3.23/1.00  fof(f64,plain,(
% 3.23/1.00    v1_funct_1(sK1)),
% 3.23/1.00    inference(cnf_transformation,[],[f44])).
% 3.23/1.00  
% 3.23/1.00  fof(f67,plain,(
% 3.23/1.00    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.23/1.00    inference(cnf_transformation,[],[f44])).
% 3.23/1.00  
% 3.23/1.00  fof(f68,plain,(
% 3.23/1.00    v1_funct_1(sK2)),
% 3.23/1.00    inference(cnf_transformation,[],[f44])).
% 3.23/1.00  
% 3.23/1.00  fof(f71,plain,(
% 3.23/1.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.23/1.00    inference(cnf_transformation,[],[f44])).
% 3.23/1.00  
% 3.23/1.00  fof(f9,axiom,(
% 3.23/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 3.23/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.23/1.00  
% 3.23/1.00  fof(f30,plain,(
% 3.23/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.23/1.00    inference(ennf_transformation,[],[f9])).
% 3.23/1.00  
% 3.23/1.00  fof(f31,plain,(
% 3.23/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.23/1.00    inference(flattening,[],[f30])).
% 3.23/1.00  
% 3.23/1.00  fof(f58,plain,(
% 3.23/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.23/1.00    inference(cnf_transformation,[],[f31])).
% 3.23/1.00  
% 3.23/1.00  fof(f11,axiom,(
% 3.23/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.23/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.23/1.00  
% 3.23/1.00  fof(f32,plain,(
% 3.23/1.00    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.23/1.00    inference(ennf_transformation,[],[f11])).
% 3.23/1.00  
% 3.23/1.00  fof(f33,plain,(
% 3.23/1.00    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.23/1.00    inference(flattening,[],[f32])).
% 3.23/1.00  
% 3.23/1.00  fof(f60,plain,(
% 3.23/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.23/1.00    inference(cnf_transformation,[],[f33])).
% 3.23/1.00  
% 3.23/1.00  fof(f3,axiom,(
% 3.23/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 3.23/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.23/1.00  
% 3.23/1.00  fof(f20,plain,(
% 3.23/1.00    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.23/1.00    inference(ennf_transformation,[],[f3])).
% 3.23/1.00  
% 3.23/1.00  fof(f21,plain,(
% 3.23/1.00    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.23/1.00    inference(flattening,[],[f20])).
% 3.23/1.00  
% 3.23/1.00  fof(f47,plain,(
% 3.23/1.00    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.23/1.00    inference(cnf_transformation,[],[f21])).
% 3.23/1.00  
% 3.23/1.00  fof(f13,axiom,(
% 3.23/1.00    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.23/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.23/1.00  
% 3.23/1.00  fof(f62,plain,(
% 3.23/1.00    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.23/1.00    inference(cnf_transformation,[],[f13])).
% 3.23/1.00  
% 3.23/1.00  fof(f74,plain,(
% 3.23/1.00    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0)) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.23/1.00    inference(definition_unfolding,[],[f47,f62])).
% 3.23/1.00  
% 3.23/1.00  fof(f7,axiom,(
% 3.23/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 3.23/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.23/1.00  
% 3.23/1.00  fof(f26,plain,(
% 3.23/1.00    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.23/1.00    inference(ennf_transformation,[],[f7])).
% 3.23/1.00  
% 3.23/1.00  fof(f27,plain,(
% 3.23/1.00    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.23/1.00    inference(flattening,[],[f26])).
% 3.23/1.00  
% 3.23/1.00  fof(f53,plain,(
% 3.23/1.00    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.23/1.00    inference(cnf_transformation,[],[f27])).
% 3.23/1.00  
% 3.23/1.00  fof(f66,plain,(
% 3.23/1.00    v3_funct_2(sK1,sK0,sK0)),
% 3.23/1.00    inference(cnf_transformation,[],[f44])).
% 3.23/1.00  
% 3.23/1.00  fof(f2,axiom,(
% 3.23/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.23/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.23/1.00  
% 3.23/1.00  fof(f46,plain,(
% 3.23/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.23/1.00    inference(cnf_transformation,[],[f2])).
% 3.23/1.00  
% 3.23/1.00  fof(f1,axiom,(
% 3.23/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.23/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.23/1.00  
% 3.23/1.00  fof(f19,plain,(
% 3.23/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.23/1.00    inference(ennf_transformation,[],[f1])).
% 3.23/1.00  
% 3.23/1.00  fof(f45,plain,(
% 3.23/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.23/1.00    inference(cnf_transformation,[],[f19])).
% 3.23/1.00  
% 3.23/1.00  fof(f5,axiom,(
% 3.23/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.23/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.23/1.00  
% 3.23/1.00  fof(f23,plain,(
% 3.23/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.23/1.00    inference(ennf_transformation,[],[f5])).
% 3.23/1.00  
% 3.23/1.00  fof(f49,plain,(
% 3.23/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.23/1.00    inference(cnf_transformation,[],[f23])).
% 3.23/1.00  
% 3.23/1.00  fof(f14,axiom,(
% 3.23/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 3.23/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.23/1.00  
% 3.23/1.00  fof(f36,plain,(
% 3.23/1.00    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.23/1.00    inference(ennf_transformation,[],[f14])).
% 3.23/1.00  
% 3.23/1.00  fof(f37,plain,(
% 3.23/1.00    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.23/1.00    inference(flattening,[],[f36])).
% 3.23/1.00  
% 3.23/1.00  fof(f63,plain,(
% 3.23/1.00    ( ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.23/1.00    inference(cnf_transformation,[],[f37])).
% 3.23/1.00  
% 3.23/1.00  fof(f65,plain,(
% 3.23/1.00    v1_funct_2(sK1,sK0,sK0)),
% 3.23/1.00    inference(cnf_transformation,[],[f44])).
% 3.23/1.00  
% 3.23/1.00  fof(f54,plain,(
% 3.23/1.00    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.23/1.00    inference(cnf_transformation,[],[f27])).
% 3.23/1.00  
% 3.23/1.00  fof(f8,axiom,(
% 3.23/1.00    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 3.23/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.23/1.00  
% 3.23/1.00  fof(f28,plain,(
% 3.23/1.00    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.23/1.00    inference(ennf_transformation,[],[f8])).
% 3.23/1.00  
% 3.23/1.00  fof(f29,plain,(
% 3.23/1.00    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.23/1.00    inference(flattening,[],[f28])).
% 3.23/1.00  
% 3.23/1.00  fof(f41,plain,(
% 3.23/1.00    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.23/1.00    inference(nnf_transformation,[],[f29])).
% 3.23/1.00  
% 3.23/1.00  fof(f55,plain,(
% 3.23/1.00    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.23/1.00    inference(cnf_transformation,[],[f41])).
% 3.23/1.00  
% 3.23/1.00  fof(f4,axiom,(
% 3.23/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.23/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.23/1.00  
% 3.23/1.00  fof(f18,plain,(
% 3.23/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.23/1.00    inference(pure_predicate_removal,[],[f4])).
% 3.23/1.00  
% 3.23/1.00  fof(f22,plain,(
% 3.23/1.00    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.23/1.00    inference(ennf_transformation,[],[f18])).
% 3.23/1.00  
% 3.23/1.00  fof(f48,plain,(
% 3.23/1.00    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.23/1.00    inference(cnf_transformation,[],[f22])).
% 3.23/1.00  
% 3.23/1.00  fof(f69,plain,(
% 3.23/1.00    v1_funct_2(sK2,sK0,sK0)),
% 3.23/1.00    inference(cnf_transformation,[],[f44])).
% 3.23/1.00  
% 3.23/1.00  fof(f51,plain,(
% 3.23/1.00    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.23/1.00    inference(cnf_transformation,[],[f40])).
% 3.23/1.00  
% 3.23/1.00  fof(f75,plain,(
% 3.23/1.00    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.23/1.00    inference(equality_resolution,[],[f51])).
% 3.23/1.00  
% 3.23/1.00  fof(f73,plain,(
% 3.23/1.00    ~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))),
% 3.23/1.00    inference(cnf_transformation,[],[f44])).
% 3.23/1.00  
% 3.23/1.00  fof(f12,axiom,(
% 3.23/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_1(X1) = k2_funct_2(X0,X1))),
% 3.23/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.23/1.00  
% 3.23/1.00  fof(f34,plain,(
% 3.23/1.00    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.23/1.00    inference(ennf_transformation,[],[f12])).
% 3.23/1.00  
% 3.23/1.00  fof(f35,plain,(
% 3.23/1.00    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.23/1.00    inference(flattening,[],[f34])).
% 3.23/1.00  
% 3.23/1.00  fof(f61,plain,(
% 3.23/1.00    ( ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.23/1.00    inference(cnf_transformation,[],[f35])).
% 3.23/1.00  
% 3.23/1.00  cnf(c_782,plain,
% 3.23/1.00      ( ~ m1_subset_1(X0_50,X0_52)
% 3.23/1.00      | m1_subset_1(X1_50,X1_52)
% 3.23/1.00      | X1_52 != X0_52
% 3.23/1.00      | X1_50 != X0_50 ),
% 3.23/1.00      theory(equality) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1280,plain,
% 3.23/1.00      ( m1_subset_1(X0_50,X0_52)
% 3.23/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.23/1.00      | X0_52 != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
% 3.23/1.00      | X0_50 != sK2 ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_782]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_4540,plain,
% 3.23/1.00      ( m1_subset_1(k2_funct_1(sK1),X0_52)
% 3.23/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.23/1.00      | X0_52 != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
% 3.23/1.00      | k2_funct_1(sK1) != sK2 ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_1280]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_7109,plain,
% 3.23/1.00      ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.23/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.23/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
% 3.23/1.00      | k2_funct_1(sK1) != sK2 ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_4540]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_6,plain,
% 3.23/1.00      ( ~ r2_relset_1(X0,X1,X2,X3)
% 3.23/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.23/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.23/1.00      | X3 = X2 ),
% 3.23/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_19,negated_conjecture,
% 3.23/1.00      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
% 3.23/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_349,plain,
% 3.23/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.23/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.23/1.00      | X3 = X0
% 3.23/1.00      | k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) != X0
% 3.23/1.00      | k6_partfun1(sK0) != X3
% 3.23/1.00      | sK0 != X2
% 3.23/1.00      | sK0 != X1 ),
% 3.23/1.00      inference(resolution_lifted,[status(thm)],[c_6,c_19]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_350,plain,
% 3.23/1.00      ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.23/1.00      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.23/1.00      | k6_partfun1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) ),
% 3.23/1.00      inference(unflattening,[status(thm)],[c_349]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_14,plain,
% 3.23/1.00      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.23/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_48,plain,
% 3.23/1.00      ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_14]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_352,plain,
% 3.23/1.00      ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.23/1.00      | k6_partfun1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) ),
% 3.23/1.00      inference(global_propositional_subsumption,
% 3.23/1.00                [status(thm)],
% 3.23/1.00                [c_350,c_48]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_761,plain,
% 3.23/1.00      ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.23/1.00      | k6_partfun1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) ),
% 3.23/1.00      inference(subtyping,[status(esa)],[c_352]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1121,plain,
% 3.23/1.00      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2)
% 3.23/1.00      | m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_761]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_27,negated_conjecture,
% 3.23/1.00      ( v1_funct_1(sK1) ),
% 3.23/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_24,negated_conjecture,
% 3.23/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.23/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_23,negated_conjecture,
% 3.23/1.00      ( v1_funct_1(sK2) ),
% 3.23/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_20,negated_conjecture,
% 3.23/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.23/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_12,plain,
% 3.23/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.23/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.23/1.00      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.23/1.00      | ~ v1_funct_1(X0)
% 3.23/1.00      | ~ v1_funct_1(X3) ),
% 3.23/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_770,plain,
% 3.23/1.00      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 3.23/1.00      | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51)))
% 3.23/1.00      | m1_subset_1(k1_partfun1(X2_51,X3_51,X0_51,X1_51,X1_50,X0_50),k1_zfmisc_1(k2_zfmisc_1(X2_51,X1_51)))
% 3.23/1.00      | ~ v1_funct_1(X0_50)
% 3.23/1.00      | ~ v1_funct_1(X1_50) ),
% 3.23/1.00      inference(subtyping,[status(esa)],[c_12]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1295,plain,
% 3.23/1.00      ( m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.23/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.23/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.23/1.00      | ~ v1_funct_1(sK1)
% 3.23/1.00      | ~ v1_funct_1(sK2) ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_770]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_2067,plain,
% 3.23/1.00      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) ),
% 3.23/1.00      inference(global_propositional_subsumption,
% 3.23/1.00                [status(thm)],
% 3.23/1.00                [c_1121,c_27,c_24,c_23,c_20,c_761,c_1295]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_764,negated_conjecture,
% 3.23/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.23/1.00      inference(subtyping,[status(esa)],[c_24]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1118,plain,
% 3.23/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_764]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_766,negated_conjecture,
% 3.23/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.23/1.00      inference(subtyping,[status(esa)],[c_20]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1116,plain,
% 3.23/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_766]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_15,plain,
% 3.23/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.23/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.23/1.00      | ~ v1_funct_1(X0)
% 3.23/1.00      | ~ v1_funct_1(X3)
% 3.23/1.00      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.23/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_767,plain,
% 3.23/1.00      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 3.23/1.00      | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51)))
% 3.23/1.00      | ~ v1_funct_1(X0_50)
% 3.23/1.00      | ~ v1_funct_1(X1_50)
% 3.23/1.00      | k1_partfun1(X2_51,X3_51,X0_51,X1_51,X1_50,X0_50) = k5_relat_1(X1_50,X0_50) ),
% 3.23/1.00      inference(subtyping,[status(esa)],[c_15]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1115,plain,
% 3.23/1.00      ( k1_partfun1(X0_51,X1_51,X2_51,X3_51,X0_50,X1_50) = k5_relat_1(X0_50,X1_50)
% 3.23/1.00      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 3.23/1.00      | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51))) != iProver_top
% 3.23/1.00      | v1_funct_1(X0_50) != iProver_top
% 3.23/1.00      | v1_funct_1(X1_50) != iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_767]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1737,plain,
% 3.23/1.00      ( k1_partfun1(X0_51,X1_51,sK0,sK0,X0_50,sK2) = k5_relat_1(X0_50,sK2)
% 3.23/1.00      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 3.23/1.00      | v1_funct_1(X0_50) != iProver_top
% 3.23/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.23/1.00      inference(superposition,[status(thm)],[c_1116,c_1115]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_32,plain,
% 3.23/1.00      ( v1_funct_1(sK2) = iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1854,plain,
% 3.23/1.00      ( v1_funct_1(X0_50) != iProver_top
% 3.23/1.00      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 3.23/1.00      | k1_partfun1(X0_51,X1_51,sK0,sK0,X0_50,sK2) = k5_relat_1(X0_50,sK2) ),
% 3.23/1.00      inference(global_propositional_subsumption,
% 3.23/1.00                [status(thm)],
% 3.23/1.00                [c_1737,c_32]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1855,plain,
% 3.23/1.00      ( k1_partfun1(X0_51,X1_51,sK0,sK0,X0_50,sK2) = k5_relat_1(X0_50,sK2)
% 3.23/1.00      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 3.23/1.00      | v1_funct_1(X0_50) != iProver_top ),
% 3.23/1.00      inference(renaming,[status(thm)],[c_1854]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1864,plain,
% 3.23/1.00      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2)
% 3.23/1.00      | v1_funct_1(sK1) != iProver_top ),
% 3.23/1.00      inference(superposition,[status(thm)],[c_1118,c_1855]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_28,plain,
% 3.23/1.00      ( v1_funct_1(sK1) = iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_31,plain,
% 3.23/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1782,plain,
% 3.23/1.00      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2)
% 3.23/1.00      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.23/1.00      | v1_funct_1(sK1) != iProver_top
% 3.23/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_1737]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1987,plain,
% 3.23/1.00      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2) ),
% 3.23/1.00      inference(global_propositional_subsumption,
% 3.23/1.00                [status(thm)],
% 3.23/1.00                [c_1864,c_28,c_31,c_32,c_1782]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_2070,plain,
% 3.23/1.00      ( k5_relat_1(sK1,sK2) = k6_partfun1(sK0) ),
% 3.23/1.00      inference(demodulation,[status(thm)],[c_2067,c_1987]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_2,plain,
% 3.23/1.00      ( ~ v1_funct_1(X0)
% 3.23/1.00      | ~ v1_funct_1(X1)
% 3.23/1.00      | ~ v2_funct_1(X1)
% 3.23/1.00      | ~ v1_relat_1(X1)
% 3.23/1.00      | ~ v1_relat_1(X0)
% 3.23/1.00      | k5_relat_1(X1,X0) != k6_partfun1(k1_relat_1(X1))
% 3.23/1.00      | k2_relat_1(X1) != k1_relat_1(X0)
% 3.23/1.00      | k2_funct_1(X1) = X0 ),
% 3.23/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_8,plain,
% 3.23/1.00      ( ~ v3_funct_2(X0,X1,X2)
% 3.23/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.23/1.00      | ~ v1_funct_1(X0)
% 3.23/1.00      | v2_funct_1(X0) ),
% 3.23/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_25,negated_conjecture,
% 3.23/1.00      ( v3_funct_2(sK1,sK0,sK0) ),
% 3.23/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_533,plain,
% 3.23/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.23/1.00      | ~ v1_funct_1(X0)
% 3.23/1.00      | v2_funct_1(X0)
% 3.23/1.00      | sK1 != X0
% 3.23/1.00      | sK0 != X1
% 3.23/1.00      | sK0 != X2 ),
% 3.23/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_25]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_534,plain,
% 3.23/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.23/1.00      | ~ v1_funct_1(sK1)
% 3.23/1.00      | v2_funct_1(sK1) ),
% 3.23/1.00      inference(unflattening,[status(thm)],[c_533]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_536,plain,
% 3.23/1.00      ( v2_funct_1(sK1) ),
% 3.23/1.00      inference(global_propositional_subsumption,
% 3.23/1.00                [status(thm)],
% 3.23/1.00                [c_534,c_27,c_24]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_584,plain,
% 3.23/1.00      ( ~ v1_funct_1(X0)
% 3.23/1.00      | ~ v1_funct_1(X1)
% 3.23/1.00      | ~ v1_relat_1(X1)
% 3.23/1.00      | ~ v1_relat_1(X0)
% 3.23/1.00      | k5_relat_1(X1,X0) != k6_partfun1(k1_relat_1(X1))
% 3.23/1.00      | k2_relat_1(X1) != k1_relat_1(X0)
% 3.23/1.00      | k2_funct_1(X1) = X0
% 3.23/1.00      | sK1 != X1 ),
% 3.23/1.00      inference(resolution_lifted,[status(thm)],[c_2,c_536]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_585,plain,
% 3.23/1.00      ( ~ v1_funct_1(X0)
% 3.23/1.00      | ~ v1_funct_1(sK1)
% 3.23/1.00      | ~ v1_relat_1(X0)
% 3.23/1.00      | ~ v1_relat_1(sK1)
% 3.23/1.00      | k5_relat_1(sK1,X0) != k6_partfun1(k1_relat_1(sK1))
% 3.23/1.00      | k2_relat_1(sK1) != k1_relat_1(X0)
% 3.23/1.00      | k2_funct_1(sK1) = X0 ),
% 3.23/1.00      inference(unflattening,[status(thm)],[c_584]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_589,plain,
% 3.23/1.00      ( ~ v1_funct_1(X0)
% 3.23/1.00      | ~ v1_relat_1(X0)
% 3.23/1.00      | ~ v1_relat_1(sK1)
% 3.23/1.00      | k5_relat_1(sK1,X0) != k6_partfun1(k1_relat_1(sK1))
% 3.23/1.00      | k2_relat_1(sK1) != k1_relat_1(X0)
% 3.23/1.00      | k2_funct_1(sK1) = X0 ),
% 3.23/1.00      inference(global_propositional_subsumption,
% 3.23/1.00                [status(thm)],
% 3.23/1.00                [c_585,c_27]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_753,plain,
% 3.23/1.00      ( ~ v1_funct_1(X0_50)
% 3.23/1.00      | ~ v1_relat_1(X0_50)
% 3.23/1.00      | ~ v1_relat_1(sK1)
% 3.23/1.00      | k2_relat_1(sK1) != k1_relat_1(X0_50)
% 3.23/1.00      | k5_relat_1(sK1,X0_50) != k6_partfun1(k1_relat_1(sK1))
% 3.23/1.00      | k2_funct_1(sK1) = X0_50 ),
% 3.23/1.00      inference(subtyping,[status(esa)],[c_589]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1125,plain,
% 3.23/1.00      ( k2_relat_1(sK1) != k1_relat_1(X0_50)
% 3.23/1.00      | k5_relat_1(sK1,X0_50) != k6_partfun1(k1_relat_1(sK1))
% 3.23/1.00      | k2_funct_1(sK1) = X0_50
% 3.23/1.00      | v1_funct_1(X0_50) != iProver_top
% 3.23/1.00      | v1_relat_1(X0_50) != iProver_top
% 3.23/1.00      | v1_relat_1(sK1) != iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_753]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1,plain,
% 3.23/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.23/1.00      inference(cnf_transformation,[],[f46]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_84,plain,
% 3.23/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_86,plain,
% 3.23/1.00      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) = iProver_top ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_84]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_836,plain,
% 3.23/1.00      ( k2_relat_1(sK1) != k1_relat_1(X0_50)
% 3.23/1.00      | k5_relat_1(sK1,X0_50) != k6_partfun1(k1_relat_1(sK1))
% 3.23/1.00      | k2_funct_1(sK1) = X0_50
% 3.23/1.00      | v1_funct_1(X0_50) != iProver_top
% 3.23/1.00      | v1_relat_1(X0_50) != iProver_top
% 3.23/1.00      | v1_relat_1(sK1) != iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_753]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_0,plain,
% 3.23/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.23/1.00      | ~ v1_relat_1(X1)
% 3.23/1.00      | v1_relat_1(X0) ),
% 3.23/1.00      inference(cnf_transformation,[],[f45]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_773,plain,
% 3.23/1.00      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(X1_50))
% 3.23/1.00      | ~ v1_relat_1(X1_50)
% 3.23/1.00      | v1_relat_1(X0_50) ),
% 3.23/1.00      inference(subtyping,[status(esa)],[c_0]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1273,plain,
% 3.23/1.00      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 3.23/1.00      | v1_relat_1(X0_50)
% 3.23/1.00      | ~ v1_relat_1(k2_zfmisc_1(X0_51,X1_51)) ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_773]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1274,plain,
% 3.23/1.00      ( m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 3.23/1.00      | v1_relat_1(X0_50) = iProver_top
% 3.23/1.00      | v1_relat_1(k2_zfmisc_1(X0_51,X1_51)) != iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_1273]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1276,plain,
% 3.23/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.23/1.00      | v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
% 3.23/1.00      | v1_relat_1(sK1) = iProver_top ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_1274]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_3063,plain,
% 3.23/1.00      ( v1_relat_1(X0_50) != iProver_top
% 3.23/1.00      | v1_funct_1(X0_50) != iProver_top
% 3.23/1.00      | k2_funct_1(sK1) = X0_50
% 3.23/1.00      | k5_relat_1(sK1,X0_50) != k6_partfun1(k1_relat_1(sK1))
% 3.23/1.00      | k2_relat_1(sK1) != k1_relat_1(X0_50) ),
% 3.23/1.00      inference(global_propositional_subsumption,
% 3.23/1.00                [status(thm)],
% 3.23/1.00                [c_1125,c_31,c_86,c_836,c_1276]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_3064,plain,
% 3.23/1.00      ( k2_relat_1(sK1) != k1_relat_1(X0_50)
% 3.23/1.00      | k5_relat_1(sK1,X0_50) != k6_partfun1(k1_relat_1(sK1))
% 3.23/1.00      | k2_funct_1(sK1) = X0_50
% 3.23/1.00      | v1_funct_1(X0_50) != iProver_top
% 3.23/1.00      | v1_relat_1(X0_50) != iProver_top ),
% 3.23/1.00      inference(renaming,[status(thm)],[c_3063]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_4,plain,
% 3.23/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.23/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.23/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_771,plain,
% 3.23/1.00      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 3.23/1.00      | k1_relset_1(X0_51,X1_51,X0_50) = k1_relat_1(X0_50) ),
% 3.23/1.00      inference(subtyping,[status(esa)],[c_4]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1111,plain,
% 3.23/1.00      ( k1_relset_1(X0_51,X1_51,X0_50) = k1_relat_1(X0_50)
% 3.23/1.00      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_771]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1426,plain,
% 3.23/1.00      ( k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) ),
% 3.23/1.00      inference(superposition,[status(thm)],[c_1118,c_1111]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_17,plain,
% 3.23/1.00      ( ~ v1_funct_2(X0,X1,X1)
% 3.23/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.23/1.00      | ~ v1_funct_1(X0)
% 3.23/1.00      | k1_relset_1(X1,X1,X0) = X1 ),
% 3.23/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_26,negated_conjecture,
% 3.23/1.00      ( v1_funct_2(sK1,sK0,sK0) ),
% 3.23/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_474,plain,
% 3.23/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.23/1.00      | ~ v1_funct_1(X0)
% 3.23/1.00      | k1_relset_1(X1,X1,X0) = X1
% 3.23/1.00      | sK1 != X0
% 3.23/1.00      | sK0 != X1 ),
% 3.23/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_26]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_475,plain,
% 3.23/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.23/1.00      | ~ v1_funct_1(sK1)
% 3.23/1.00      | k1_relset_1(sK0,sK0,sK1) = sK0 ),
% 3.23/1.00      inference(unflattening,[status(thm)],[c_474]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_477,plain,
% 3.23/1.00      ( k1_relset_1(sK0,sK0,sK1) = sK0 ),
% 3.23/1.00      inference(global_propositional_subsumption,
% 3.23/1.00                [status(thm)],
% 3.23/1.00                [c_475,c_27,c_24]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_758,plain,
% 3.23/1.00      ( k1_relset_1(sK0,sK0,sK1) = sK0 ),
% 3.23/1.00      inference(subtyping,[status(esa)],[c_477]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1431,plain,
% 3.23/1.00      ( k1_relat_1(sK1) = sK0 ),
% 3.23/1.00      inference(light_normalisation,[status(thm)],[c_1426,c_758]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_7,plain,
% 3.23/1.00      ( ~ v3_funct_2(X0,X1,X2)
% 3.23/1.00      | v2_funct_2(X0,X2)
% 3.23/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.23/1.00      | ~ v1_funct_1(X0) ),
% 3.23/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_11,plain,
% 3.23/1.00      ( ~ v2_funct_2(X0,X1)
% 3.23/1.00      | ~ v5_relat_1(X0,X1)
% 3.23/1.00      | ~ v1_relat_1(X0)
% 3.23/1.00      | k2_relat_1(X0) = X1 ),
% 3.23/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_424,plain,
% 3.23/1.00      ( ~ v3_funct_2(X0,X1,X2)
% 3.23/1.00      | ~ v5_relat_1(X3,X4)
% 3.23/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.23/1.00      | ~ v1_funct_1(X0)
% 3.23/1.00      | ~ v1_relat_1(X3)
% 3.23/1.00      | X3 != X0
% 3.23/1.00      | X4 != X2
% 3.23/1.00      | k2_relat_1(X3) = X4 ),
% 3.23/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_11]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_425,plain,
% 3.23/1.00      ( ~ v3_funct_2(X0,X1,X2)
% 3.23/1.00      | ~ v5_relat_1(X0,X2)
% 3.23/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.23/1.00      | ~ v1_funct_1(X0)
% 3.23/1.00      | ~ v1_relat_1(X0)
% 3.23/1.00      | k2_relat_1(X0) = X2 ),
% 3.23/1.00      inference(unflattening,[status(thm)],[c_424]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_3,plain,
% 3.23/1.00      ( v5_relat_1(X0,X1)
% 3.23/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.23/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_441,plain,
% 3.23/1.00      ( ~ v3_funct_2(X0,X1,X2)
% 3.23/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.23/1.00      | ~ v1_funct_1(X0)
% 3.23/1.00      | ~ v1_relat_1(X0)
% 3.23/1.00      | k2_relat_1(X0) = X2 ),
% 3.23/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_425,c_3]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_519,plain,
% 3.23/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.23/1.00      | ~ v1_funct_1(X0)
% 3.23/1.00      | ~ v1_relat_1(X0)
% 3.23/1.00      | k2_relat_1(X0) = X2
% 3.23/1.00      | sK1 != X0
% 3.23/1.00      | sK0 != X1
% 3.23/1.00      | sK0 != X2 ),
% 3.23/1.00      inference(resolution_lifted,[status(thm)],[c_441,c_25]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_520,plain,
% 3.23/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.23/1.00      | ~ v1_funct_1(sK1)
% 3.23/1.00      | ~ v1_relat_1(sK1)
% 3.23/1.00      | k2_relat_1(sK1) = sK0 ),
% 3.23/1.00      inference(unflattening,[status(thm)],[c_519]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_522,plain,
% 3.23/1.00      ( ~ v1_relat_1(sK1) | k2_relat_1(sK1) = sK0 ),
% 3.23/1.00      inference(global_propositional_subsumption,
% 3.23/1.00                [status(thm)],
% 3.23/1.00                [c_520,c_27,c_24]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_755,plain,
% 3.23/1.00      ( ~ v1_relat_1(sK1) | k2_relat_1(sK1) = sK0 ),
% 3.23/1.00      inference(subtyping,[status(esa)],[c_522]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1123,plain,
% 3.23/1.00      ( k2_relat_1(sK1) = sK0 | v1_relat_1(sK1) != iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_755]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_85,plain,
% 3.23/1.00      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1275,plain,
% 3.23/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.23/1.00      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
% 3.23/1.00      | v1_relat_1(sK1) ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_1273]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1548,plain,
% 3.23/1.00      ( k2_relat_1(sK1) = sK0 ),
% 3.23/1.00      inference(global_propositional_subsumption,
% 3.23/1.00                [status(thm)],
% 3.23/1.00                [c_1123,c_24,c_85,c_755,c_1275]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_3067,plain,
% 3.23/1.00      ( k1_relat_1(X0_50) != sK0
% 3.23/1.00      | k5_relat_1(sK1,X0_50) != k6_partfun1(sK0)
% 3.23/1.00      | k2_funct_1(sK1) = X0_50
% 3.23/1.00      | v1_funct_1(X0_50) != iProver_top
% 3.23/1.00      | v1_relat_1(X0_50) != iProver_top ),
% 3.23/1.00      inference(light_normalisation,[status(thm)],[c_3064,c_1431,c_1548]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_3076,plain,
% 3.23/1.00      ( k1_relat_1(sK2) != sK0
% 3.23/1.00      | k2_funct_1(sK1) = sK2
% 3.23/1.00      | v1_funct_1(sK2) != iProver_top
% 3.23/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.23/1.00      inference(superposition,[status(thm)],[c_2070,c_3067]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1425,plain,
% 3.23/1.00      ( k1_relset_1(sK0,sK0,sK2) = k1_relat_1(sK2) ),
% 3.23/1.00      inference(superposition,[status(thm)],[c_1116,c_1111]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_22,negated_conjecture,
% 3.23/1.00      ( v1_funct_2(sK2,sK0,sK0) ),
% 3.23/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_458,plain,
% 3.23/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.23/1.00      | ~ v1_funct_1(X0)
% 3.23/1.00      | k1_relset_1(X1,X1,X0) = X1
% 3.23/1.00      | sK2 != X0
% 3.23/1.00      | sK0 != X1 ),
% 3.23/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_22]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_459,plain,
% 3.23/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.23/1.00      | ~ v1_funct_1(sK2)
% 3.23/1.00      | k1_relset_1(sK0,sK0,sK2) = sK0 ),
% 3.23/1.00      inference(unflattening,[status(thm)],[c_458]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_461,plain,
% 3.23/1.00      ( k1_relset_1(sK0,sK0,sK2) = sK0 ),
% 3.23/1.00      inference(global_propositional_subsumption,
% 3.23/1.00                [status(thm)],
% 3.23/1.00                [c_459,c_23,c_20]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_760,plain,
% 3.23/1.00      ( k1_relset_1(sK0,sK0,sK2) = sK0 ),
% 3.23/1.00      inference(subtyping,[status(esa)],[c_461]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1434,plain,
% 3.23/1.00      ( k1_relat_1(sK2) = sK0 ),
% 3.23/1.00      inference(light_normalisation,[status(thm)],[c_1425,c_760]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_3077,plain,
% 3.23/1.00      ( sK0 != sK0
% 3.23/1.00      | k2_funct_1(sK1) = sK2
% 3.23/1.00      | v1_funct_1(sK2) != iProver_top
% 3.23/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.23/1.00      inference(light_normalisation,[status(thm)],[c_3076,c_1434]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_3078,plain,
% 3.23/1.00      ( k2_funct_1(sK1) = sK2
% 3.23/1.00      | v1_funct_1(sK2) != iProver_top
% 3.23/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.23/1.00      inference(equality_resolution_simp,[status(thm)],[c_3077]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1346,plain,
% 3.23/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 3.23/1.00      | ~ v1_relat_1(k2_zfmisc_1(X0_51,X1_51))
% 3.23/1.00      | v1_relat_1(sK2) ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_1273]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1347,plain,
% 3.23/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 3.23/1.00      | v1_relat_1(k2_zfmisc_1(X0_51,X1_51)) != iProver_top
% 3.23/1.00      | v1_relat_1(sK2) = iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_1346]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1349,plain,
% 3.23/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.23/1.00      | v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
% 3.23/1.00      | v1_relat_1(sK2) = iProver_top ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_1347]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_777,plain,( X0_52 = X0_52 ),theory(equality) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1327,plain,
% 3.23/1.00      ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
% 3.23/1.00      inference(instantiation,[status(thm)],[c_777]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_5,plain,
% 3.23/1.00      ( r2_relset_1(X0,X1,X2,X2)
% 3.23/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.23/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_18,negated_conjecture,
% 3.23/1.00      ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
% 3.23/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_339,plain,
% 3.23/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.23/1.00      | k2_funct_2(sK0,sK1) != X0
% 3.23/1.00      | sK2 != X0
% 3.23/1.00      | sK0 != X2
% 3.23/1.00      | sK0 != X1 ),
% 3.23/1.00      inference(resolution_lifted,[status(thm)],[c_5,c_18]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_340,plain,
% 3.23/1.00      ( ~ m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.23/1.00      | sK2 != k2_funct_2(sK0,sK1) ),
% 3.23/1.00      inference(unflattening,[status(thm)],[c_339]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_762,plain,
% 3.23/1.00      ( ~ m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.23/1.00      | sK2 != k2_funct_2(sK0,sK1) ),
% 3.23/1.00      inference(subtyping,[status(esa)],[c_340]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1120,plain,
% 3.23/1.00      ( sK2 != k2_funct_2(sK0,sK1)
% 3.23/1.00      | m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_762]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_16,plain,
% 3.23/1.00      ( ~ v1_funct_2(X0,X1,X1)
% 3.23/1.00      | ~ v3_funct_2(X0,X1,X1)
% 3.23/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.23/1.00      | ~ v1_funct_1(X0)
% 3.23/1.00      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 3.23/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_482,plain,
% 3.23/1.00      ( ~ v3_funct_2(X0,X1,X1)
% 3.23/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.23/1.00      | ~ v1_funct_1(X0)
% 3.23/1.00      | k2_funct_2(X1,X0) = k2_funct_1(X0)
% 3.23/1.00      | sK1 != X0
% 3.23/1.00      | sK0 != X1 ),
% 3.23/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_26]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_483,plain,
% 3.23/1.00      ( ~ v3_funct_2(sK1,sK0,sK0)
% 3.23/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.23/1.00      | ~ v1_funct_1(sK1)
% 3.23/1.00      | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 3.23/1.00      inference(unflattening,[status(thm)],[c_482]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_485,plain,
% 3.23/1.00      ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 3.23/1.00      inference(global_propositional_subsumption,
% 3.23/1.00                [status(thm)],
% 3.23/1.00                [c_483,c_27,c_25,c_24]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_757,plain,
% 3.23/1.00      ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 3.23/1.00      inference(subtyping,[status(esa)],[c_485]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1164,plain,
% 3.23/1.00      ( k2_funct_1(sK1) != sK2
% 3.23/1.00      | m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.23/1.00      inference(light_normalisation,[status(thm)],[c_1120,c_757]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_1247,plain,
% 3.23/1.00      ( ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.23/1.00      | k2_funct_1(sK1) != sK2 ),
% 3.23/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1164]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(c_35,plain,
% 3.23/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.23/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.23/1.00  
% 3.23/1.00  cnf(contradiction,plain,
% 3.23/1.00      ( $false ),
% 3.23/1.00      inference(minisat,
% 3.23/1.00                [status(thm)],
% 3.23/1.00                [c_7109,c_3078,c_1349,c_1327,c_1247,c_86,c_35,c_20,c_32]) ).
% 3.23/1.00  
% 3.23/1.00  
% 3.23/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.23/1.00  
% 3.23/1.00  ------                               Statistics
% 3.23/1.00  
% 3.23/1.00  ------ General
% 3.23/1.00  
% 3.23/1.00  abstr_ref_over_cycles:                  0
% 3.23/1.00  abstr_ref_under_cycles:                 0
% 3.23/1.00  gc_basic_clause_elim:                   0
% 3.23/1.00  forced_gc_time:                         0
% 3.23/1.00  parsing_time:                           0.014
% 3.23/1.00  unif_index_cands_time:                  0.
% 3.23/1.00  unif_index_add_time:                    0.
% 3.23/1.00  orderings_time:                         0.
% 3.23/1.00  out_proof_time:                         0.013
% 3.23/1.00  total_time:                             0.233
% 3.23/1.00  num_of_symbols:                         56
% 3.23/1.00  num_of_terms:                           4110
% 3.23/1.00  
% 3.23/1.00  ------ Preprocessing
% 3.23/1.00  
% 3.23/1.00  num_of_splits:                          0
% 3.23/1.00  num_of_split_atoms:                     0
% 3.23/1.00  num_of_reused_defs:                     0
% 3.23/1.00  num_eq_ax_congr_red:                    13
% 3.23/1.00  num_of_sem_filtered_clauses:            1
% 3.23/1.00  num_of_subtypes:                        3
% 3.23/1.00  monotx_restored_types:                  0
% 3.23/1.00  sat_num_of_epr_types:                   0
% 3.23/1.00  sat_num_of_non_cyclic_types:            0
% 3.23/1.00  sat_guarded_non_collapsed_types:        1
% 3.23/1.00  num_pure_diseq_elim:                    0
% 3.23/1.00  simp_replaced_by:                       0
% 3.23/1.00  res_preprocessed:                       130
% 3.23/1.00  prep_upred:                             0
% 3.23/1.00  prep_unflattend:                        40
% 3.23/1.00  smt_new_axioms:                         0
% 3.23/1.00  pred_elim_cands:                        3
% 3.23/1.00  pred_elim:                              6
% 3.23/1.00  pred_elim_cl:                           5
% 3.23/1.00  pred_elim_cycles:                       10
% 3.23/1.00  merged_defs:                            0
% 3.23/1.00  merged_defs_ncl:                        0
% 3.23/1.00  bin_hyper_res:                          0
% 3.23/1.00  prep_cycles:                            4
% 3.23/1.00  pred_elim_time:                         0.008
% 3.23/1.00  splitting_time:                         0.
% 3.23/1.00  sem_filter_time:                        0.
% 3.23/1.00  monotx_time:                            0.
% 3.23/1.00  subtype_inf_time:                       0.
% 3.23/1.00  
% 3.23/1.00  ------ Problem properties
% 3.23/1.00  
% 3.23/1.00  clauses:                                22
% 3.23/1.00  conjectures:                            4
% 3.23/1.00  epr:                                    2
% 3.23/1.00  horn:                                   22
% 3.23/1.00  ground:                                 13
% 3.23/1.00  unary:                                  10
% 3.23/1.00  binary:                                 6
% 3.23/1.00  lits:                                   52
% 3.23/1.00  lits_eq:                                18
% 3.23/1.00  fd_pure:                                0
% 3.23/1.00  fd_pseudo:                              0
% 3.23/1.00  fd_cond:                                2
% 3.23/1.00  fd_pseudo_cond:                         0
% 3.23/1.00  ac_symbols:                             0
% 3.23/1.00  
% 3.23/1.00  ------ Propositional Solver
% 3.23/1.00  
% 3.23/1.00  prop_solver_calls:                      31
% 3.23/1.00  prop_fast_solver_calls:                 1137
% 3.23/1.00  smt_solver_calls:                       0
% 3.23/1.00  smt_fast_solver_calls:                  0
% 3.23/1.00  prop_num_of_clauses:                    1716
% 3.23/1.00  prop_preprocess_simplified:             5354
% 3.23/1.00  prop_fo_subsumed:                       96
% 3.23/1.00  prop_solver_time:                       0.
% 3.23/1.00  smt_solver_time:                        0.
% 3.23/1.00  smt_fast_solver_time:                   0.
% 3.23/1.00  prop_fast_solver_time:                  0.
% 3.23/1.00  prop_unsat_core_time:                   0.
% 3.23/1.00  
% 3.23/1.00  ------ QBF
% 3.23/1.00  
% 3.23/1.00  qbf_q_res:                              0
% 3.23/1.00  qbf_num_tautologies:                    0
% 3.23/1.00  qbf_prep_cycles:                        0
% 3.23/1.00  
% 3.23/1.00  ------ BMC1
% 3.23/1.00  
% 3.23/1.00  bmc1_current_bound:                     -1
% 3.23/1.00  bmc1_last_solved_bound:                 -1
% 3.23/1.00  bmc1_unsat_core_size:                   -1
% 3.23/1.00  bmc1_unsat_core_parents_size:           -1
% 3.23/1.00  bmc1_merge_next_fun:                    0
% 3.23/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.23/1.00  
% 3.23/1.00  ------ Instantiation
% 3.23/1.00  
% 3.23/1.00  inst_num_of_clauses:                    671
% 3.23/1.00  inst_num_in_passive:                    213
% 3.23/1.00  inst_num_in_active:                     457
% 3.23/1.00  inst_num_in_unprocessed:                0
% 3.23/1.00  inst_num_of_loops:                      477
% 3.23/1.00  inst_num_of_learning_restarts:          0
% 3.23/1.00  inst_num_moves_active_passive:          11
% 3.23/1.00  inst_lit_activity:                      0
% 3.23/1.00  inst_lit_activity_moves:                0
% 3.23/1.00  inst_num_tautologies:                   0
% 3.23/1.00  inst_num_prop_implied:                  0
% 3.23/1.00  inst_num_existing_simplified:           0
% 3.23/1.00  inst_num_eq_res_simplified:             0
% 3.23/1.00  inst_num_child_elim:                    0
% 3.23/1.00  inst_num_of_dismatching_blockings:      330
% 3.23/1.00  inst_num_of_non_proper_insts:           944
% 3.23/1.00  inst_num_of_duplicates:                 0
% 3.23/1.00  inst_inst_num_from_inst_to_res:         0
% 3.23/1.00  inst_dismatching_checking_time:         0.
% 3.23/1.00  
% 3.23/1.00  ------ Resolution
% 3.23/1.00  
% 3.23/1.00  res_num_of_clauses:                     0
% 3.23/1.00  res_num_in_passive:                     0
% 3.23/1.00  res_num_in_active:                      0
% 3.23/1.00  res_num_of_loops:                       134
% 3.23/1.00  res_forward_subset_subsumed:            242
% 3.23/1.00  res_backward_subset_subsumed:           4
% 3.23/1.00  res_forward_subsumed:                   0
% 3.23/1.00  res_backward_subsumed:                  0
% 3.23/1.00  res_forward_subsumption_resolution:     1
% 3.23/1.00  res_backward_subsumption_resolution:    0
% 3.23/1.00  res_clause_to_clause_subsumption:       556
% 3.23/1.00  res_orphan_elimination:                 0
% 3.23/1.00  res_tautology_del:                      237
% 3.23/1.00  res_num_eq_res_simplified:              1
% 3.23/1.00  res_num_sel_changes:                    0
% 3.23/1.00  res_moves_from_active_to_pass:          0
% 3.23/1.00  
% 3.23/1.00  ------ Superposition
% 3.23/1.00  
% 3.23/1.00  sup_time_total:                         0.
% 3.23/1.00  sup_time_generating:                    0.
% 3.23/1.00  sup_time_sim_full:                      0.
% 3.23/1.00  sup_time_sim_immed:                     0.
% 3.23/1.00  
% 3.23/1.00  sup_num_of_clauses:                     213
% 3.23/1.00  sup_num_in_active:                      92
% 3.23/1.00  sup_num_in_passive:                     121
% 3.23/1.00  sup_num_of_loops:                       94
% 3.23/1.00  sup_fw_superposition:                   138
% 3.23/1.00  sup_bw_superposition:                   72
% 3.23/1.00  sup_immediate_simplified:               47
% 3.23/1.00  sup_given_eliminated:                   0
% 3.23/1.00  comparisons_done:                       0
% 3.23/1.00  comparisons_avoided:                    0
% 3.23/1.00  
% 3.23/1.00  ------ Simplifications
% 3.23/1.00  
% 3.23/1.00  
% 3.23/1.00  sim_fw_subset_subsumed:                 4
% 3.23/1.00  sim_bw_subset_subsumed:                 0
% 3.23/1.00  sim_fw_subsumed:                        3
% 3.23/1.00  sim_bw_subsumed:                        0
% 3.23/1.00  sim_fw_subsumption_res:                 4
% 3.23/1.00  sim_bw_subsumption_res:                 0
% 3.23/1.00  sim_tautology_del:                      0
% 3.23/1.00  sim_eq_tautology_del:                   10
% 3.23/1.00  sim_eq_res_simp:                        1
% 3.23/1.00  sim_fw_demodulated:                     1
% 3.23/1.00  sim_bw_demodulated:                     2
% 3.23/1.00  sim_light_normalised:                   50
% 3.23/1.00  sim_joinable_taut:                      0
% 3.23/1.00  sim_joinable_simp:                      0
% 3.23/1.00  sim_ac_normalised:                      0
% 3.23/1.00  sim_smt_subsumption:                    0
% 3.23/1.00  
%------------------------------------------------------------------------------
