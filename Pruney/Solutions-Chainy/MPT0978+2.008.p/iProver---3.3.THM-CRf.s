%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:01:34 EST 2020

% Result     : Theorem 3.88s
% Output     : CNFRefutation 3.88s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 561 expanded)
%              Number of clauses        :   83 ( 165 expanded)
%              Number of leaves         :   17 ( 127 expanded)
%              Depth                    :   22
%              Number of atoms          :  457 (2760 expanded)
%              Number of equality atoms :  195 ( 602 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_1(X1) ) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f14,conjecture,(
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

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
             => k2_relset_1(X0,X1,X2) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f16,plain,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_1(X3) )
           => ( r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
             => k2_relset_1(X0,X1,X2) = X1 ) ) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f32,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_relset_1(X0,X1,X2) != X1
          & r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f33,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_relset_1(X0,X1,X2) != X1
          & r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( k2_relset_1(X0,X1,X2) != X1
          & r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_1(X3) )
     => ( k2_relset_1(X0,X1,X2) != X1
        & r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,sK3,X2),k6_partfun1(X1))
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( k2_relset_1(X0,X1,X2) != X1
            & r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k2_relset_1(sK0,sK1,sK2) != sK1
          & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK0,sK0,sK1,X3,sK2),k6_partfun1(sK1))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( k2_relset_1(sK0,sK1,sK2) != sK1
    & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k6_partfun1(sK1))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f33,f39,f38])).

fof(f61,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f34])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f70,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f41])).

fof(f64,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f40])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f28])).

fof(f57,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f63,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f62,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f40])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f24])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f65,plain,(
    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f40])).

fof(f10,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f56,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f26])).

fof(f55,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f5,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f12,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f67,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f49,f58])).

fof(f66,plain,(
    k2_relset_1(sK0,sK1,sK2) != sK1 ),
    inference(cnf_transformation,[],[f40])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f43,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_17,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_703,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_699,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_711,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_702,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_704,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2711,plain,
    ( k1_partfun1(X0,X1,k1_relat_1(X2),X3,X4,X2) = k5_relat_1(X4,X2)
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | r1_tarski(k2_relat_1(X2),X3) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_703,c_704])).

cnf(c_11697,plain,
    ( k1_partfun1(sK1,sK0,k1_relat_1(X0),X1,sK3,X0) = k5_relat_1(sK3,X0)
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_702,c_2711])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_27,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_12008,plain,
    ( v1_funct_1(X0) != iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | k1_partfun1(sK1,sK0,k1_relat_1(X0),X1,sK3,X0) = k5_relat_1(sK3,X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11697,c_27])).

cnf(c_12009,plain,
    ( k1_partfun1(sK1,sK0,k1_relat_1(X0),X1,sK3,X0) = k5_relat_1(sK3,X0)
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_12008])).

cnf(c_12018,plain,
    ( k1_partfun1(sK1,sK0,k1_relat_1(X0),k2_relat_1(X0),sK3,X0) = k5_relat_1(sK3,X0)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_711,c_12009])).

cnf(c_13256,plain,
    ( k1_partfun1(sK1,sK0,k1_relat_1(sK2),k2_relat_1(sK2),sK3,sK2) = k5_relat_1(sK3,sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_699,c_12018])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_700,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2713,plain,
    ( k1_partfun1(X0,X1,sK0,sK1,X2,sK2) = k5_relat_1(X2,sK2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_700,c_704])).

cnf(c_25,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3287,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK0,sK1,X2,sK2) = k5_relat_1(X2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2713,c_25])).

cnf(c_3288,plain,
    ( k1_partfun1(X0,X1,sK0,sK1,X2,sK2) = k5_relat_1(X2,sK2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_3287])).

cnf(c_3299,plain,
    ( k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) = k5_relat_1(sK3,sK2)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_702,c_3288])).

cnf(c_935,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(X1,X2,X3,X4,X0,sK2) = k5_relat_1(X0,sK2) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1049,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(X0,X1,X2,X3,sK3,sK2) = k5_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_935])).

cnf(c_1409,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(sK1,sK0,X0,X1,sK3,sK2) = k5_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_1049])).

cnf(c_2227,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) = k5_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_1409])).

cnf(c_3355,plain,
    ( k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) = k5_relat_1(sK3,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3299,c_24,c_23,c_22,c_21,c_2227])).

cnf(c_12,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_20,negated_conjecture,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_261,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) != X0
    | k6_partfun1(sK1) != X3
    | sK1 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_20])).

cnf(c_262,plain,
    ( ~ m1_subset_1(k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k6_partfun1(sK1) = k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) ),
    inference(unflattening,[status(thm)],[c_261])).

cnf(c_15,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_38,plain,
    ( m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_264,plain,
    ( ~ m1_subset_1(k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k6_partfun1(sK1) = k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_262,c_38])).

cnf(c_697,plain,
    ( k6_partfun1(sK1) = k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2)
    | m1_subset_1(k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_264])).

cnf(c_3358,plain,
    ( k5_relat_1(sK3,sK2) = k6_partfun1(sK1)
    | m1_subset_1(k5_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3355,c_697])).

cnf(c_26,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_28,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_707,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3360,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3355,c_707])).

cnf(c_3420,plain,
    ( k5_relat_1(sK3,sK2) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3358,c_25,c_26,c_27,c_28,c_3360])).

cnf(c_13278,plain,
    ( k1_partfun1(sK1,sK0,k1_relat_1(sK2),k2_relat_1(sK2),sK3,sK2) = k6_partfun1(sK1)
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13256,c_3420])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_836,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1227,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_836])).

cnf(c_1228,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1227])).

cnf(c_6,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1370,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1371,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1370])).

cnf(c_13527,plain,
    ( k1_partfun1(sK1,sK0,k1_relat_1(sK2),k2_relat_1(sK2),sK3,sK2) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13278,c_26,c_1228,c_1371])).

cnf(c_9,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_5,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_240,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_9,c_5])).

cnf(c_698,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_240])).

cnf(c_2647,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | r1_tarski(k2_relat_1(k1_partfun1(X4,X5,X1,X2,X3,X0)),X2) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_relat_1(k1_partfun1(X4,X5,X1,X2,X3,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_707,c_698])).

cnf(c_710,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2645,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_relat_1(k1_partfun1(X4,X5,X1,X2,X3,X0)) = iProver_top
    | v1_relat_1(k2_zfmisc_1(X4,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_707,c_710])).

cnf(c_709,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_5701,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_relat_1(k1_partfun1(X4,X5,X1,X2,X3,X0)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2645,c_709])).

cnf(c_8013,plain,
    ( v1_funct_1(X3) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | r1_tarski(k2_relat_1(k1_partfun1(X4,X5,X1,X2,X3,X0)),X2) = iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2647,c_5701])).

cnf(c_8014,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | r1_tarski(k2_relat_1(k1_partfun1(X4,X5,X1,X2,X3,X0)),X2) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(renaming,[status(thm)],[c_8013])).

cnf(c_13530,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | r1_tarski(k2_relat_1(k6_partfun1(sK1)),k2_relat_1(sK2)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_13527,c_8014])).

cnf(c_7,plain,
    ( k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_13554,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | r1_tarski(sK1,k2_relat_1(sK2)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_13530,c_7])).

cnf(c_19,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) != sK1 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_872,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_392,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_859,plain,
    ( k2_relset_1(sK0,sK1,sK2) != X0
    | k2_relset_1(sK0,sK1,sK2) = sK1
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_392])).

cnf(c_992,plain,
    ( k2_relset_1(sK0,sK1,sK2) != k2_relat_1(sK2)
    | k2_relset_1(sK0,sK1,sK2) = sK1
    | sK1 != k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_859])).

cnf(c_1139,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_700,c_698])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1526,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1)
    | ~ r1_tarski(sK1,k2_relat_1(sK2))
    | sK1 = k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1527,plain,
    ( sK1 = k2_relat_1(sK2)
    | r1_tarski(k2_relat_1(sK2),sK1) != iProver_top
    | r1_tarski(sK1,k2_relat_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1526])).

cnf(c_14238,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13554,c_25,c_23,c_26,c_27,c_28,c_19,c_872,c_992,c_1139,c_1228,c_1371,c_1527])).

cnf(c_14243,plain,
    ( r1_tarski(k2_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_703,c_14238])).

cnf(c_7287,plain,
    ( r1_tarski(k2_relat_1(sK2),k2_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_7290,plain,
    ( r1_tarski(k2_relat_1(sK2),k2_relat_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7287])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14243,c_7290,c_1371,c_1228,c_26,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:47:44 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.88/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.88/0.99  
% 3.88/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.88/0.99  
% 3.88/0.99  ------  iProver source info
% 3.88/0.99  
% 3.88/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.88/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.88/0.99  git: non_committed_changes: false
% 3.88/0.99  git: last_make_outside_of_git: false
% 3.88/0.99  
% 3.88/0.99  ------ 
% 3.88/0.99  
% 3.88/0.99  ------ Input Options
% 3.88/0.99  
% 3.88/0.99  --out_options                           all
% 3.88/0.99  --tptp_safe_out                         true
% 3.88/0.99  --problem_path                          ""
% 3.88/0.99  --include_path                          ""
% 3.88/0.99  --clausifier                            res/vclausify_rel
% 3.88/0.99  --clausifier_options                    --mode clausify
% 3.88/0.99  --stdin                                 false
% 3.88/0.99  --stats_out                             all
% 3.88/0.99  
% 3.88/0.99  ------ General Options
% 3.88/0.99  
% 3.88/0.99  --fof                                   false
% 3.88/0.99  --time_out_real                         305.
% 3.88/0.99  --time_out_virtual                      -1.
% 3.88/0.99  --symbol_type_check                     false
% 3.88/0.99  --clausify_out                          false
% 3.88/0.99  --sig_cnt_out                           false
% 3.88/0.99  --trig_cnt_out                          false
% 3.88/0.99  --trig_cnt_out_tolerance                1.
% 3.88/0.99  --trig_cnt_out_sk_spl                   false
% 3.88/0.99  --abstr_cl_out                          false
% 3.88/0.99  
% 3.88/0.99  ------ Global Options
% 3.88/0.99  
% 3.88/0.99  --schedule                              default
% 3.88/0.99  --add_important_lit                     false
% 3.88/0.99  --prop_solver_per_cl                    1000
% 3.88/0.99  --min_unsat_core                        false
% 3.88/0.99  --soft_assumptions                      false
% 3.88/0.99  --soft_lemma_size                       3
% 3.88/0.99  --prop_impl_unit_size                   0
% 3.88/0.99  --prop_impl_unit                        []
% 3.88/0.99  --share_sel_clauses                     true
% 3.88/0.99  --reset_solvers                         false
% 3.88/0.99  --bc_imp_inh                            [conj_cone]
% 3.88/0.99  --conj_cone_tolerance                   3.
% 3.88/0.99  --extra_neg_conj                        none
% 3.88/0.99  --large_theory_mode                     true
% 3.88/0.99  --prolific_symb_bound                   200
% 3.88/0.99  --lt_threshold                          2000
% 3.88/0.99  --clause_weak_htbl                      true
% 3.88/0.99  --gc_record_bc_elim                     false
% 3.88/0.99  
% 3.88/0.99  ------ Preprocessing Options
% 3.88/0.99  
% 3.88/0.99  --preprocessing_flag                    true
% 3.88/0.99  --time_out_prep_mult                    0.1
% 3.88/0.99  --splitting_mode                        input
% 3.88/0.99  --splitting_grd                         true
% 3.88/0.99  --splitting_cvd                         false
% 3.88/0.99  --splitting_cvd_svl                     false
% 3.88/0.99  --splitting_nvd                         32
% 3.88/0.99  --sub_typing                            true
% 3.88/0.99  --prep_gs_sim                           true
% 3.88/0.99  --prep_unflatten                        true
% 3.88/0.99  --prep_res_sim                          true
% 3.88/0.99  --prep_upred                            true
% 3.88/0.99  --prep_sem_filter                       exhaustive
% 3.88/0.99  --prep_sem_filter_out                   false
% 3.88/0.99  --pred_elim                             true
% 3.88/0.99  --res_sim_input                         true
% 3.88/0.99  --eq_ax_congr_red                       true
% 3.88/0.99  --pure_diseq_elim                       true
% 3.88/0.99  --brand_transform                       false
% 3.88/0.99  --non_eq_to_eq                          false
% 3.88/0.99  --prep_def_merge                        true
% 3.88/0.99  --prep_def_merge_prop_impl              false
% 3.88/0.99  --prep_def_merge_mbd                    true
% 3.88/0.99  --prep_def_merge_tr_red                 false
% 3.88/0.99  --prep_def_merge_tr_cl                  false
% 3.88/0.99  --smt_preprocessing                     true
% 3.88/0.99  --smt_ac_axioms                         fast
% 3.88/0.99  --preprocessed_out                      false
% 3.88/0.99  --preprocessed_stats                    false
% 3.88/0.99  
% 3.88/0.99  ------ Abstraction refinement Options
% 3.88/0.99  
% 3.88/0.99  --abstr_ref                             []
% 3.88/0.99  --abstr_ref_prep                        false
% 3.88/0.99  --abstr_ref_until_sat                   false
% 3.88/0.99  --abstr_ref_sig_restrict                funpre
% 3.88/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.88/0.99  --abstr_ref_under                       []
% 3.88/0.99  
% 3.88/0.99  ------ SAT Options
% 3.88/0.99  
% 3.88/0.99  --sat_mode                              false
% 3.88/0.99  --sat_fm_restart_options                ""
% 3.88/0.99  --sat_gr_def                            false
% 3.88/0.99  --sat_epr_types                         true
% 3.88/0.99  --sat_non_cyclic_types                  false
% 3.88/0.99  --sat_finite_models                     false
% 3.88/0.99  --sat_fm_lemmas                         false
% 3.88/0.99  --sat_fm_prep                           false
% 3.88/0.99  --sat_fm_uc_incr                        true
% 3.88/0.99  --sat_out_model                         small
% 3.88/0.99  --sat_out_clauses                       false
% 3.88/0.99  
% 3.88/0.99  ------ QBF Options
% 3.88/0.99  
% 3.88/0.99  --qbf_mode                              false
% 3.88/0.99  --qbf_elim_univ                         false
% 3.88/0.99  --qbf_dom_inst                          none
% 3.88/0.99  --qbf_dom_pre_inst                      false
% 3.88/0.99  --qbf_sk_in                             false
% 3.88/0.99  --qbf_pred_elim                         true
% 3.88/0.99  --qbf_split                             512
% 3.88/0.99  
% 3.88/0.99  ------ BMC1 Options
% 3.88/0.99  
% 3.88/0.99  --bmc1_incremental                      false
% 3.88/0.99  --bmc1_axioms                           reachable_all
% 3.88/0.99  --bmc1_min_bound                        0
% 3.88/0.99  --bmc1_max_bound                        -1
% 3.88/0.99  --bmc1_max_bound_default                -1
% 3.88/0.99  --bmc1_symbol_reachability              true
% 3.88/0.99  --bmc1_property_lemmas                  false
% 3.88/0.99  --bmc1_k_induction                      false
% 3.88/0.99  --bmc1_non_equiv_states                 false
% 3.88/0.99  --bmc1_deadlock                         false
% 3.88/0.99  --bmc1_ucm                              false
% 3.88/0.99  --bmc1_add_unsat_core                   none
% 3.88/0.99  --bmc1_unsat_core_children              false
% 3.88/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.88/0.99  --bmc1_out_stat                         full
% 3.88/0.99  --bmc1_ground_init                      false
% 3.88/0.99  --bmc1_pre_inst_next_state              false
% 3.88/0.99  --bmc1_pre_inst_state                   false
% 3.88/0.99  --bmc1_pre_inst_reach_state             false
% 3.88/0.99  --bmc1_out_unsat_core                   false
% 3.88/0.99  --bmc1_aig_witness_out                  false
% 3.88/0.99  --bmc1_verbose                          false
% 3.88/0.99  --bmc1_dump_clauses_tptp                false
% 3.88/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.88/0.99  --bmc1_dump_file                        -
% 3.88/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.88/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.88/0.99  --bmc1_ucm_extend_mode                  1
% 3.88/0.99  --bmc1_ucm_init_mode                    2
% 3.88/0.99  --bmc1_ucm_cone_mode                    none
% 3.88/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.88/0.99  --bmc1_ucm_relax_model                  4
% 3.88/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.88/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.88/0.99  --bmc1_ucm_layered_model                none
% 3.88/0.99  --bmc1_ucm_max_lemma_size               10
% 3.88/0.99  
% 3.88/0.99  ------ AIG Options
% 3.88/0.99  
% 3.88/0.99  --aig_mode                              false
% 3.88/0.99  
% 3.88/0.99  ------ Instantiation Options
% 3.88/0.99  
% 3.88/0.99  --instantiation_flag                    true
% 3.88/0.99  --inst_sos_flag                         false
% 3.88/0.99  --inst_sos_phase                        true
% 3.88/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.88/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.88/0.99  --inst_lit_sel_side                     num_symb
% 3.88/0.99  --inst_solver_per_active                1400
% 3.88/0.99  --inst_solver_calls_frac                1.
% 3.88/0.99  --inst_passive_queue_type               priority_queues
% 3.88/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.88/0.99  --inst_passive_queues_freq              [25;2]
% 3.88/0.99  --inst_dismatching                      true
% 3.88/0.99  --inst_eager_unprocessed_to_passive     true
% 3.88/0.99  --inst_prop_sim_given                   true
% 3.88/0.99  --inst_prop_sim_new                     false
% 3.88/0.99  --inst_subs_new                         false
% 3.88/0.99  --inst_eq_res_simp                      false
% 3.88/0.99  --inst_subs_given                       false
% 3.88/0.99  --inst_orphan_elimination               true
% 3.88/0.99  --inst_learning_loop_flag               true
% 3.88/0.99  --inst_learning_start                   3000
% 3.88/0.99  --inst_learning_factor                  2
% 3.88/0.99  --inst_start_prop_sim_after_learn       3
% 3.88/0.99  --inst_sel_renew                        solver
% 3.88/0.99  --inst_lit_activity_flag                true
% 3.88/0.99  --inst_restr_to_given                   false
% 3.88/0.99  --inst_activity_threshold               500
% 3.88/0.99  --inst_out_proof                        true
% 3.88/0.99  
% 3.88/0.99  ------ Resolution Options
% 3.88/0.99  
% 3.88/0.99  --resolution_flag                       true
% 3.88/0.99  --res_lit_sel                           adaptive
% 3.88/0.99  --res_lit_sel_side                      none
% 3.88/0.99  --res_ordering                          kbo
% 3.88/0.99  --res_to_prop_solver                    active
% 3.88/0.99  --res_prop_simpl_new                    false
% 3.88/0.99  --res_prop_simpl_given                  true
% 3.88/0.99  --res_passive_queue_type                priority_queues
% 3.88/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.88/0.99  --res_passive_queues_freq               [15;5]
% 3.88/0.99  --res_forward_subs                      full
% 3.88/0.99  --res_backward_subs                     full
% 3.88/0.99  --res_forward_subs_resolution           true
% 3.88/0.99  --res_backward_subs_resolution          true
% 3.88/0.99  --res_orphan_elimination                true
% 3.88/0.99  --res_time_limit                        2.
% 3.88/0.99  --res_out_proof                         true
% 3.88/0.99  
% 3.88/0.99  ------ Superposition Options
% 3.88/0.99  
% 3.88/0.99  --superposition_flag                    true
% 3.88/0.99  --sup_passive_queue_type                priority_queues
% 3.88/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.88/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.88/0.99  --demod_completeness_check              fast
% 3.88/0.99  --demod_use_ground                      true
% 3.88/0.99  --sup_to_prop_solver                    passive
% 3.88/0.99  --sup_prop_simpl_new                    true
% 3.88/0.99  --sup_prop_simpl_given                  true
% 3.88/0.99  --sup_fun_splitting                     false
% 3.88/0.99  --sup_smt_interval                      50000
% 3.88/0.99  
% 3.88/0.99  ------ Superposition Simplification Setup
% 3.88/0.99  
% 3.88/0.99  --sup_indices_passive                   []
% 3.88/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.88/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.88/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.88/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.88/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.88/0.99  --sup_full_bw                           [BwDemod]
% 3.88/0.99  --sup_immed_triv                        [TrivRules]
% 3.88/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.88/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.88/0.99  --sup_immed_bw_main                     []
% 3.88/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.88/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.88/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.88/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.88/0.99  
% 3.88/0.99  ------ Combination Options
% 3.88/0.99  
% 3.88/0.99  --comb_res_mult                         3
% 3.88/0.99  --comb_sup_mult                         2
% 3.88/0.99  --comb_inst_mult                        10
% 3.88/0.99  
% 3.88/0.99  ------ Debug Options
% 3.88/0.99  
% 3.88/0.99  --dbg_backtrace                         false
% 3.88/0.99  --dbg_dump_prop_clauses                 false
% 3.88/0.99  --dbg_dump_prop_clauses_file            -
% 3.88/0.99  --dbg_out_stat                          false
% 3.88/0.99  ------ Parsing...
% 3.88/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.88/0.99  
% 3.88/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.88/0.99  
% 3.88/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.88/0.99  
% 3.88/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.88/0.99  ------ Proving...
% 3.88/0.99  ------ Problem Properties 
% 3.88/0.99  
% 3.88/0.99  
% 3.88/0.99  clauses                                 19
% 3.88/0.99  conjectures                             5
% 3.88/0.99  EPR                                     4
% 3.88/0.99  Horn                                    19
% 3.88/0.99  unary                                   10
% 3.88/0.99  binary                                  2
% 3.88/0.99  lits                                    42
% 3.88/0.99  lits eq                                 7
% 3.88/0.99  fd_pure                                 0
% 3.88/0.99  fd_pseudo                               0
% 3.88/0.99  fd_cond                                 0
% 3.88/0.99  fd_pseudo_cond                          1
% 3.88/0.99  AC symbols                              0
% 3.88/0.99  
% 3.88/0.99  ------ Schedule dynamic 5 is on 
% 3.88/0.99  
% 3.88/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.88/0.99  
% 3.88/0.99  
% 3.88/0.99  ------ 
% 3.88/0.99  Current options:
% 3.88/0.99  ------ 
% 3.88/0.99  
% 3.88/0.99  ------ Input Options
% 3.88/0.99  
% 3.88/0.99  --out_options                           all
% 3.88/0.99  --tptp_safe_out                         true
% 3.88/0.99  --problem_path                          ""
% 3.88/0.99  --include_path                          ""
% 3.88/0.99  --clausifier                            res/vclausify_rel
% 3.88/0.99  --clausifier_options                    --mode clausify
% 3.88/0.99  --stdin                                 false
% 3.88/0.99  --stats_out                             all
% 3.88/0.99  
% 3.88/0.99  ------ General Options
% 3.88/0.99  
% 3.88/0.99  --fof                                   false
% 3.88/0.99  --time_out_real                         305.
% 3.88/0.99  --time_out_virtual                      -1.
% 3.88/0.99  --symbol_type_check                     false
% 3.88/0.99  --clausify_out                          false
% 3.88/0.99  --sig_cnt_out                           false
% 3.88/0.99  --trig_cnt_out                          false
% 3.88/0.99  --trig_cnt_out_tolerance                1.
% 3.88/0.99  --trig_cnt_out_sk_spl                   false
% 3.88/0.99  --abstr_cl_out                          false
% 3.88/0.99  
% 3.88/0.99  ------ Global Options
% 3.88/0.99  
% 3.88/0.99  --schedule                              default
% 3.88/0.99  --add_important_lit                     false
% 3.88/0.99  --prop_solver_per_cl                    1000
% 3.88/0.99  --min_unsat_core                        false
% 3.88/0.99  --soft_assumptions                      false
% 3.88/0.99  --soft_lemma_size                       3
% 3.88/0.99  --prop_impl_unit_size                   0
% 3.88/0.99  --prop_impl_unit                        []
% 3.88/0.99  --share_sel_clauses                     true
% 3.88/0.99  --reset_solvers                         false
% 3.88/0.99  --bc_imp_inh                            [conj_cone]
% 3.88/0.99  --conj_cone_tolerance                   3.
% 3.88/0.99  --extra_neg_conj                        none
% 3.88/0.99  --large_theory_mode                     true
% 3.88/0.99  --prolific_symb_bound                   200
% 3.88/0.99  --lt_threshold                          2000
% 3.88/0.99  --clause_weak_htbl                      true
% 3.88/0.99  --gc_record_bc_elim                     false
% 3.88/0.99  
% 3.88/0.99  ------ Preprocessing Options
% 3.88/0.99  
% 3.88/0.99  --preprocessing_flag                    true
% 3.88/0.99  --time_out_prep_mult                    0.1
% 3.88/0.99  --splitting_mode                        input
% 3.88/0.99  --splitting_grd                         true
% 3.88/0.99  --splitting_cvd                         false
% 3.88/0.99  --splitting_cvd_svl                     false
% 3.88/0.99  --splitting_nvd                         32
% 3.88/0.99  --sub_typing                            true
% 3.88/0.99  --prep_gs_sim                           true
% 3.88/0.99  --prep_unflatten                        true
% 3.88/0.99  --prep_res_sim                          true
% 3.88/0.99  --prep_upred                            true
% 3.88/0.99  --prep_sem_filter                       exhaustive
% 3.88/0.99  --prep_sem_filter_out                   false
% 3.88/0.99  --pred_elim                             true
% 3.88/0.99  --res_sim_input                         true
% 3.88/0.99  --eq_ax_congr_red                       true
% 3.88/0.99  --pure_diseq_elim                       true
% 3.88/0.99  --brand_transform                       false
% 3.88/0.99  --non_eq_to_eq                          false
% 3.88/0.99  --prep_def_merge                        true
% 3.88/0.99  --prep_def_merge_prop_impl              false
% 3.88/0.99  --prep_def_merge_mbd                    true
% 3.88/0.99  --prep_def_merge_tr_red                 false
% 3.88/0.99  --prep_def_merge_tr_cl                  false
% 3.88/0.99  --smt_preprocessing                     true
% 3.88/0.99  --smt_ac_axioms                         fast
% 3.88/0.99  --preprocessed_out                      false
% 3.88/0.99  --preprocessed_stats                    false
% 3.88/0.99  
% 3.88/0.99  ------ Abstraction refinement Options
% 3.88/0.99  
% 3.88/0.99  --abstr_ref                             []
% 3.88/0.99  --abstr_ref_prep                        false
% 3.88/0.99  --abstr_ref_until_sat                   false
% 3.88/0.99  --abstr_ref_sig_restrict                funpre
% 3.88/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.88/0.99  --abstr_ref_under                       []
% 3.88/0.99  
% 3.88/0.99  ------ SAT Options
% 3.88/0.99  
% 3.88/0.99  --sat_mode                              false
% 3.88/0.99  --sat_fm_restart_options                ""
% 3.88/0.99  --sat_gr_def                            false
% 3.88/0.99  --sat_epr_types                         true
% 3.88/0.99  --sat_non_cyclic_types                  false
% 3.88/0.99  --sat_finite_models                     false
% 3.88/0.99  --sat_fm_lemmas                         false
% 3.88/0.99  --sat_fm_prep                           false
% 3.88/0.99  --sat_fm_uc_incr                        true
% 3.88/0.99  --sat_out_model                         small
% 3.88/0.99  --sat_out_clauses                       false
% 3.88/0.99  
% 3.88/0.99  ------ QBF Options
% 3.88/0.99  
% 3.88/0.99  --qbf_mode                              false
% 3.88/0.99  --qbf_elim_univ                         false
% 3.88/0.99  --qbf_dom_inst                          none
% 3.88/0.99  --qbf_dom_pre_inst                      false
% 3.88/0.99  --qbf_sk_in                             false
% 3.88/0.99  --qbf_pred_elim                         true
% 3.88/0.99  --qbf_split                             512
% 3.88/0.99  
% 3.88/0.99  ------ BMC1 Options
% 3.88/0.99  
% 3.88/0.99  --bmc1_incremental                      false
% 3.88/0.99  --bmc1_axioms                           reachable_all
% 3.88/0.99  --bmc1_min_bound                        0
% 3.88/0.99  --bmc1_max_bound                        -1
% 3.88/0.99  --bmc1_max_bound_default                -1
% 3.88/0.99  --bmc1_symbol_reachability              true
% 3.88/0.99  --bmc1_property_lemmas                  false
% 3.88/0.99  --bmc1_k_induction                      false
% 3.88/0.99  --bmc1_non_equiv_states                 false
% 3.88/0.99  --bmc1_deadlock                         false
% 3.88/0.99  --bmc1_ucm                              false
% 3.88/0.99  --bmc1_add_unsat_core                   none
% 3.88/0.99  --bmc1_unsat_core_children              false
% 3.88/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.88/0.99  --bmc1_out_stat                         full
% 3.88/0.99  --bmc1_ground_init                      false
% 3.88/0.99  --bmc1_pre_inst_next_state              false
% 3.88/0.99  --bmc1_pre_inst_state                   false
% 3.88/0.99  --bmc1_pre_inst_reach_state             false
% 3.88/0.99  --bmc1_out_unsat_core                   false
% 3.88/0.99  --bmc1_aig_witness_out                  false
% 3.88/0.99  --bmc1_verbose                          false
% 3.88/0.99  --bmc1_dump_clauses_tptp                false
% 3.88/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.88/0.99  --bmc1_dump_file                        -
% 3.88/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.88/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.88/0.99  --bmc1_ucm_extend_mode                  1
% 3.88/0.99  --bmc1_ucm_init_mode                    2
% 3.88/0.99  --bmc1_ucm_cone_mode                    none
% 3.88/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.88/0.99  --bmc1_ucm_relax_model                  4
% 3.88/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.88/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.88/0.99  --bmc1_ucm_layered_model                none
% 3.88/0.99  --bmc1_ucm_max_lemma_size               10
% 3.88/0.99  
% 3.88/0.99  ------ AIG Options
% 3.88/0.99  
% 3.88/0.99  --aig_mode                              false
% 3.88/0.99  
% 3.88/0.99  ------ Instantiation Options
% 3.88/0.99  
% 3.88/0.99  --instantiation_flag                    true
% 3.88/0.99  --inst_sos_flag                         false
% 3.88/0.99  --inst_sos_phase                        true
% 3.88/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.88/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.88/0.99  --inst_lit_sel_side                     none
% 3.88/0.99  --inst_solver_per_active                1400
% 3.88/0.99  --inst_solver_calls_frac                1.
% 3.88/0.99  --inst_passive_queue_type               priority_queues
% 3.88/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.88/0.99  --inst_passive_queues_freq              [25;2]
% 3.88/0.99  --inst_dismatching                      true
% 3.88/0.99  --inst_eager_unprocessed_to_passive     true
% 3.88/0.99  --inst_prop_sim_given                   true
% 3.88/0.99  --inst_prop_sim_new                     false
% 3.88/0.99  --inst_subs_new                         false
% 3.88/0.99  --inst_eq_res_simp                      false
% 3.88/0.99  --inst_subs_given                       false
% 3.88/0.99  --inst_orphan_elimination               true
% 3.88/0.99  --inst_learning_loop_flag               true
% 3.88/0.99  --inst_learning_start                   3000
% 3.88/0.99  --inst_learning_factor                  2
% 3.88/0.99  --inst_start_prop_sim_after_learn       3
% 3.88/0.99  --inst_sel_renew                        solver
% 3.88/0.99  --inst_lit_activity_flag                true
% 3.88/0.99  --inst_restr_to_given                   false
% 3.88/0.99  --inst_activity_threshold               500
% 3.88/0.99  --inst_out_proof                        true
% 3.88/0.99  
% 3.88/0.99  ------ Resolution Options
% 3.88/0.99  
% 3.88/0.99  --resolution_flag                       false
% 3.88/0.99  --res_lit_sel                           adaptive
% 3.88/0.99  --res_lit_sel_side                      none
% 3.88/0.99  --res_ordering                          kbo
% 3.88/0.99  --res_to_prop_solver                    active
% 3.88/0.99  --res_prop_simpl_new                    false
% 3.88/0.99  --res_prop_simpl_given                  true
% 3.88/0.99  --res_passive_queue_type                priority_queues
% 3.88/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.88/0.99  --res_passive_queues_freq               [15;5]
% 3.88/0.99  --res_forward_subs                      full
% 3.88/0.99  --res_backward_subs                     full
% 3.88/0.99  --res_forward_subs_resolution           true
% 3.88/0.99  --res_backward_subs_resolution          true
% 3.88/0.99  --res_orphan_elimination                true
% 3.88/0.99  --res_time_limit                        2.
% 3.88/0.99  --res_out_proof                         true
% 3.88/0.99  
% 3.88/0.99  ------ Superposition Options
% 3.88/0.99  
% 3.88/0.99  --superposition_flag                    true
% 3.88/0.99  --sup_passive_queue_type                priority_queues
% 3.88/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.88/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.88/0.99  --demod_completeness_check              fast
% 3.88/0.99  --demod_use_ground                      true
% 3.88/0.99  --sup_to_prop_solver                    passive
% 3.88/0.99  --sup_prop_simpl_new                    true
% 3.88/0.99  --sup_prop_simpl_given                  true
% 3.88/0.99  --sup_fun_splitting                     false
% 3.88/0.99  --sup_smt_interval                      50000
% 3.88/0.99  
% 3.88/0.99  ------ Superposition Simplification Setup
% 3.88/0.99  
% 3.88/0.99  --sup_indices_passive                   []
% 3.88/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.88/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.88/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.88/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.88/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.88/0.99  --sup_full_bw                           [BwDemod]
% 3.88/0.99  --sup_immed_triv                        [TrivRules]
% 3.88/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.88/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.88/0.99  --sup_immed_bw_main                     []
% 3.88/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.88/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.88/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.88/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.88/0.99  
% 3.88/0.99  ------ Combination Options
% 3.88/0.99  
% 3.88/0.99  --comb_res_mult                         3
% 3.88/0.99  --comb_sup_mult                         2
% 3.88/0.99  --comb_inst_mult                        10
% 3.88/0.99  
% 3.88/0.99  ------ Debug Options
% 3.88/0.99  
% 3.88/0.99  --dbg_backtrace                         false
% 3.88/0.99  --dbg_dump_prop_clauses                 false
% 3.88/0.99  --dbg_dump_prop_clauses_file            -
% 3.88/0.99  --dbg_out_stat                          false
% 3.88/0.99  
% 3.88/0.99  
% 3.88/0.99  
% 3.88/0.99  
% 3.88/0.99  ------ Proving...
% 3.88/0.99  
% 3.88/0.99  
% 3.88/0.99  % SZS status Theorem for theBenchmark.p
% 3.88/0.99  
% 3.88/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.88/0.99  
% 3.88/0.99  fof(f13,axiom,(
% 3.88/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 3.88/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/0.99  
% 3.88/0.99  fof(f17,plain,(
% 3.88/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_1(X1))))),
% 3.88/0.99    inference(pure_predicate_removal,[],[f13])).
% 3.88/0.99  
% 3.88/0.99  fof(f30,plain,(
% 3.88/0.99    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.88/0.99    inference(ennf_transformation,[],[f17])).
% 3.88/0.99  
% 3.88/0.99  fof(f31,plain,(
% 3.88/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.88/0.99    inference(flattening,[],[f30])).
% 3.88/0.99  
% 3.88/0.99  fof(f60,plain,(
% 3.88/0.99    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.88/0.99    inference(cnf_transformation,[],[f31])).
% 3.88/0.99  
% 3.88/0.99  fof(f14,conjecture,(
% 3.88/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 3.88/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/0.99  
% 3.88/0.99  fof(f15,negated_conjecture,(
% 3.88/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 3.88/0.99    inference(negated_conjecture,[],[f14])).
% 3.88/0.99  
% 3.88/0.99  fof(f16,plain,(
% 3.88/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 3.88/0.99    inference(pure_predicate_removal,[],[f15])).
% 3.88/0.99  
% 3.88/0.99  fof(f32,plain,(
% 3.88/0.99    ? [X0,X1,X2] : (? [X3] : ((k2_relset_1(X0,X1,X2) != X1 & r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 3.88/0.99    inference(ennf_transformation,[],[f16])).
% 3.88/0.99  
% 3.88/0.99  fof(f33,plain,(
% 3.88/0.99    ? [X0,X1,X2] : (? [X3] : (k2_relset_1(X0,X1,X2) != X1 & r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 3.88/0.99    inference(flattening,[],[f32])).
% 3.88/0.99  
% 3.88/0.99  fof(f39,plain,(
% 3.88/0.99    ( ! [X2,X0,X1] : (? [X3] : (k2_relset_1(X0,X1,X2) != X1 & r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) => (k2_relset_1(X0,X1,X2) != X1 & r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,sK3,X2),k6_partfun1(X1)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(sK3))) )),
% 3.88/0.99    introduced(choice_axiom,[])).
% 3.88/0.99  
% 3.88/0.99  fof(f38,plain,(
% 3.88/0.99    ? [X0,X1,X2] : (? [X3] : (k2_relset_1(X0,X1,X2) != X1 & r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (? [X3] : (k2_relset_1(sK0,sK1,sK2) != sK1 & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK0,sK0,sK1,X3,sK2),k6_partfun1(sK1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2))),
% 3.88/0.99    introduced(choice_axiom,[])).
% 3.88/0.99  
% 3.88/0.99  fof(f40,plain,(
% 3.88/0.99    (k2_relset_1(sK0,sK1,sK2) != sK1 & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k6_partfun1(sK1)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2)),
% 3.88/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f33,f39,f38])).
% 3.88/0.99  
% 3.88/0.99  fof(f61,plain,(
% 3.88/0.99    v1_funct_1(sK2)),
% 3.88/0.99    inference(cnf_transformation,[],[f40])).
% 3.88/0.99  
% 3.88/0.99  fof(f1,axiom,(
% 3.88/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.88/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/0.99  
% 3.88/0.99  fof(f34,plain,(
% 3.88/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.88/0.99    inference(nnf_transformation,[],[f1])).
% 3.88/0.99  
% 3.88/0.99  fof(f35,plain,(
% 3.88/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.88/0.99    inference(flattening,[],[f34])).
% 3.88/0.99  
% 3.88/0.99  fof(f41,plain,(
% 3.88/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.88/0.99    inference(cnf_transformation,[],[f35])).
% 3.88/0.99  
% 3.88/0.99  fof(f70,plain,(
% 3.88/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.88/0.99    inference(equality_resolution,[],[f41])).
% 3.88/0.99  
% 3.88/0.99  fof(f64,plain,(
% 3.88/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 3.88/0.99    inference(cnf_transformation,[],[f40])).
% 3.88/0.99  
% 3.88/0.99  fof(f11,axiom,(
% 3.88/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 3.88/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/0.99  
% 3.88/0.99  fof(f28,plain,(
% 3.88/0.99    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.88/0.99    inference(ennf_transformation,[],[f11])).
% 3.88/0.99  
% 3.88/0.99  fof(f29,plain,(
% 3.88/0.99    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.88/0.99    inference(flattening,[],[f28])).
% 3.88/0.99  
% 3.88/0.99  fof(f57,plain,(
% 3.88/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.88/0.99    inference(cnf_transformation,[],[f29])).
% 3.88/0.99  
% 3.88/0.99  fof(f63,plain,(
% 3.88/0.99    v1_funct_1(sK3)),
% 3.88/0.99    inference(cnf_transformation,[],[f40])).
% 3.88/0.99  
% 3.88/0.99  fof(f62,plain,(
% 3.88/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.88/0.99    inference(cnf_transformation,[],[f40])).
% 3.88/0.99  
% 3.88/0.99  fof(f8,axiom,(
% 3.88/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.88/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/0.99  
% 3.88/0.99  fof(f24,plain,(
% 3.88/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.88/0.99    inference(ennf_transformation,[],[f8])).
% 3.88/0.99  
% 3.88/0.99  fof(f25,plain,(
% 3.88/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.88/0.99    inference(flattening,[],[f24])).
% 3.88/0.99  
% 3.88/0.99  fof(f37,plain,(
% 3.88/0.99    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.88/0.99    inference(nnf_transformation,[],[f25])).
% 3.88/0.99  
% 3.88/0.99  fof(f52,plain,(
% 3.88/0.99    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.88/0.99    inference(cnf_transformation,[],[f37])).
% 3.88/0.99  
% 3.88/0.99  fof(f65,plain,(
% 3.88/0.99    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k6_partfun1(sK1))),
% 3.88/0.99    inference(cnf_transformation,[],[f40])).
% 3.88/0.99  
% 3.88/0.99  fof(f10,axiom,(
% 3.88/0.99    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 3.88/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/0.99  
% 3.88/0.99  fof(f18,plain,(
% 3.88/0.99    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.88/0.99    inference(pure_predicate_removal,[],[f10])).
% 3.88/0.99  
% 3.88/0.99  fof(f56,plain,(
% 3.88/0.99    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.88/0.99    inference(cnf_transformation,[],[f18])).
% 3.88/0.99  
% 3.88/0.99  fof(f9,axiom,(
% 3.88/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 3.88/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/0.99  
% 3.88/0.99  fof(f26,plain,(
% 3.88/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.88/0.99    inference(ennf_transformation,[],[f9])).
% 3.88/0.99  
% 3.88/0.99  fof(f27,plain,(
% 3.88/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.88/0.99    inference(flattening,[],[f26])).
% 3.88/0.99  
% 3.88/0.99  fof(f55,plain,(
% 3.88/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.88/0.99    inference(cnf_transformation,[],[f27])).
% 3.88/0.99  
% 3.88/0.99  fof(f2,axiom,(
% 3.88/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.88/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/0.99  
% 3.88/0.99  fof(f20,plain,(
% 3.88/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.88/0.99    inference(ennf_transformation,[],[f2])).
% 3.88/0.99  
% 3.88/0.99  fof(f44,plain,(
% 3.88/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.88/0.99    inference(cnf_transformation,[],[f20])).
% 3.88/0.99  
% 3.88/0.99  fof(f4,axiom,(
% 3.88/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.88/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/0.99  
% 3.88/0.99  fof(f47,plain,(
% 3.88/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.88/0.99    inference(cnf_transformation,[],[f4])).
% 3.88/0.99  
% 3.88/0.99  fof(f6,axiom,(
% 3.88/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.88/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/0.99  
% 3.88/0.99  fof(f19,plain,(
% 3.88/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.88/0.99    inference(pure_predicate_removal,[],[f6])).
% 3.88/0.99  
% 3.88/0.99  fof(f22,plain,(
% 3.88/0.99    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.88/0.99    inference(ennf_transformation,[],[f19])).
% 3.88/0.99  
% 3.88/0.99  fof(f50,plain,(
% 3.88/0.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.88/0.99    inference(cnf_transformation,[],[f22])).
% 3.88/0.99  
% 3.88/0.99  fof(f3,axiom,(
% 3.88/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.88/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/0.99  
% 3.88/0.99  fof(f21,plain,(
% 3.88/0.99    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.88/0.99    inference(ennf_transformation,[],[f3])).
% 3.88/0.99  
% 3.88/0.99  fof(f36,plain,(
% 3.88/0.99    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.88/0.99    inference(nnf_transformation,[],[f21])).
% 3.88/0.99  
% 3.88/0.99  fof(f45,plain,(
% 3.88/0.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.88/0.99    inference(cnf_transformation,[],[f36])).
% 3.88/0.99  
% 3.88/0.99  fof(f5,axiom,(
% 3.88/0.99    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.88/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/0.99  
% 3.88/0.99  fof(f49,plain,(
% 3.88/0.99    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 3.88/0.99    inference(cnf_transformation,[],[f5])).
% 3.88/0.99  
% 3.88/0.99  fof(f12,axiom,(
% 3.88/0.99    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.88/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/0.99  
% 3.88/0.99  fof(f58,plain,(
% 3.88/0.99    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.88/0.99    inference(cnf_transformation,[],[f12])).
% 3.88/0.99  
% 3.88/0.99  fof(f67,plain,(
% 3.88/0.99    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 3.88/0.99    inference(definition_unfolding,[],[f49,f58])).
% 3.88/0.99  
% 3.88/0.99  fof(f66,plain,(
% 3.88/0.99    k2_relset_1(sK0,sK1,sK2) != sK1),
% 3.88/0.99    inference(cnf_transformation,[],[f40])).
% 3.88/0.99  
% 3.88/0.99  fof(f7,axiom,(
% 3.88/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.88/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/0.99  
% 3.88/0.99  fof(f23,plain,(
% 3.88/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.88/0.99    inference(ennf_transformation,[],[f7])).
% 3.88/0.99  
% 3.88/0.99  fof(f51,plain,(
% 3.88/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.88/0.99    inference(cnf_transformation,[],[f23])).
% 3.88/0.99  
% 3.88/0.99  fof(f43,plain,(
% 3.88/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.88/0.99    inference(cnf_transformation,[],[f35])).
% 3.88/0.99  
% 3.88/0.99  cnf(c_17,plain,
% 3.88/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.88/0.99      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.88/0.99      | ~ v1_funct_1(X0)
% 3.88/0.99      | ~ v1_relat_1(X0) ),
% 3.88/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_703,plain,
% 3.88/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
% 3.88/0.99      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 3.88/0.99      | v1_funct_1(X0) != iProver_top
% 3.88/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_24,negated_conjecture,
% 3.88/0.99      ( v1_funct_1(sK2) ),
% 3.88/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_699,plain,
% 3.88/0.99      ( v1_funct_1(sK2) = iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_2,plain,
% 3.88/0.99      ( r1_tarski(X0,X0) ),
% 3.88/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_711,plain,
% 3.88/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_21,negated_conjecture,
% 3.88/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 3.88/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_702,plain,
% 3.88/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_16,plain,
% 3.88/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.88/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.88/0.99      | ~ v1_funct_1(X0)
% 3.88/0.99      | ~ v1_funct_1(X3)
% 3.88/0.99      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.88/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_704,plain,
% 3.88/0.99      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 3.88/0.99      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 3.88/0.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.88/0.99      | v1_funct_1(X5) != iProver_top
% 3.88/0.99      | v1_funct_1(X4) != iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_2711,plain,
% 3.88/0.99      ( k1_partfun1(X0,X1,k1_relat_1(X2),X3,X4,X2) = k5_relat_1(X4,X2)
% 3.88/0.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.88/0.99      | r1_tarski(k2_relat_1(X2),X3) != iProver_top
% 3.88/0.99      | v1_funct_1(X2) != iProver_top
% 3.88/0.99      | v1_funct_1(X4) != iProver_top
% 3.88/0.99      | v1_relat_1(X2) != iProver_top ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_703,c_704]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_11697,plain,
% 3.88/0.99      ( k1_partfun1(sK1,sK0,k1_relat_1(X0),X1,sK3,X0) = k5_relat_1(sK3,X0)
% 3.88/0.99      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 3.88/0.99      | v1_funct_1(X0) != iProver_top
% 3.88/0.99      | v1_funct_1(sK3) != iProver_top
% 3.88/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_702,c_2711]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_22,negated_conjecture,
% 3.88/0.99      ( v1_funct_1(sK3) ),
% 3.88/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_27,plain,
% 3.88/0.99      ( v1_funct_1(sK3) = iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_12008,plain,
% 3.88/0.99      ( v1_funct_1(X0) != iProver_top
% 3.88/0.99      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 3.88/0.99      | k1_partfun1(sK1,sK0,k1_relat_1(X0),X1,sK3,X0) = k5_relat_1(sK3,X0)
% 3.88/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.88/0.99      inference(global_propositional_subsumption,
% 3.88/0.99                [status(thm)],
% 3.88/0.99                [c_11697,c_27]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_12009,plain,
% 3.88/0.99      ( k1_partfun1(sK1,sK0,k1_relat_1(X0),X1,sK3,X0) = k5_relat_1(sK3,X0)
% 3.88/0.99      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 3.88/0.99      | v1_funct_1(X0) != iProver_top
% 3.88/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.88/0.99      inference(renaming,[status(thm)],[c_12008]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_12018,plain,
% 3.88/0.99      ( k1_partfun1(sK1,sK0,k1_relat_1(X0),k2_relat_1(X0),sK3,X0) = k5_relat_1(sK3,X0)
% 3.88/0.99      | v1_funct_1(X0) != iProver_top
% 3.88/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_711,c_12009]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_13256,plain,
% 3.88/0.99      ( k1_partfun1(sK1,sK0,k1_relat_1(sK2),k2_relat_1(sK2),sK3,sK2) = k5_relat_1(sK3,sK2)
% 3.88/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_699,c_12018]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_23,negated_conjecture,
% 3.88/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.88/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_700,plain,
% 3.88/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_2713,plain,
% 3.88/0.99      ( k1_partfun1(X0,X1,sK0,sK1,X2,sK2) = k5_relat_1(X2,sK2)
% 3.88/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.88/0.99      | v1_funct_1(X2) != iProver_top
% 3.88/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_700,c_704]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_25,plain,
% 3.88/0.99      ( v1_funct_1(sK2) = iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_3287,plain,
% 3.88/0.99      ( v1_funct_1(X2) != iProver_top
% 3.88/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.88/0.99      | k1_partfun1(X0,X1,sK0,sK1,X2,sK2) = k5_relat_1(X2,sK2) ),
% 3.88/0.99      inference(global_propositional_subsumption,
% 3.88/0.99                [status(thm)],
% 3.88/0.99                [c_2713,c_25]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_3288,plain,
% 3.88/0.99      ( k1_partfun1(X0,X1,sK0,sK1,X2,sK2) = k5_relat_1(X2,sK2)
% 3.88/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.88/0.99      | v1_funct_1(X2) != iProver_top ),
% 3.88/0.99      inference(renaming,[status(thm)],[c_3287]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_3299,plain,
% 3.88/0.99      ( k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) = k5_relat_1(sK3,sK2)
% 3.88/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_702,c_3288]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_935,plain,
% 3.88/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.88/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 3.88/0.99      | ~ v1_funct_1(X0)
% 3.88/0.99      | ~ v1_funct_1(sK2)
% 3.88/0.99      | k1_partfun1(X1,X2,X3,X4,X0,sK2) = k5_relat_1(X0,sK2) ),
% 3.88/0.99      inference(instantiation,[status(thm)],[c_16]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_1049,plain,
% 3.88/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.88/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.88/0.99      | ~ v1_funct_1(sK3)
% 3.88/0.99      | ~ v1_funct_1(sK2)
% 3.88/0.99      | k1_partfun1(X0,X1,X2,X3,sK3,sK2) = k5_relat_1(sK3,sK2) ),
% 3.88/0.99      inference(instantiation,[status(thm)],[c_935]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_1409,plain,
% 3.88/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.88/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.88/0.99      | ~ v1_funct_1(sK3)
% 3.88/0.99      | ~ v1_funct_1(sK2)
% 3.88/0.99      | k1_partfun1(sK1,sK0,X0,X1,sK3,sK2) = k5_relat_1(sK3,sK2) ),
% 3.88/0.99      inference(instantiation,[status(thm)],[c_1049]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_2227,plain,
% 3.88/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.88/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.88/0.99      | ~ v1_funct_1(sK3)
% 3.88/0.99      | ~ v1_funct_1(sK2)
% 3.88/0.99      | k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) = k5_relat_1(sK3,sK2) ),
% 3.88/0.99      inference(instantiation,[status(thm)],[c_1409]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_3355,plain,
% 3.88/0.99      ( k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) = k5_relat_1(sK3,sK2) ),
% 3.88/0.99      inference(global_propositional_subsumption,
% 3.88/0.99                [status(thm)],
% 3.88/0.99                [c_3299,c_24,c_23,c_22,c_21,c_2227]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_12,plain,
% 3.88/0.99      ( ~ r2_relset_1(X0,X1,X2,X3)
% 3.88/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.88/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.88/0.99      | X3 = X2 ),
% 3.88/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_20,negated_conjecture,
% 3.88/0.99      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k6_partfun1(sK1)) ),
% 3.88/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_261,plain,
% 3.88/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.88/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.88/0.99      | X3 = X0
% 3.88/0.99      | k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) != X0
% 3.88/0.99      | k6_partfun1(sK1) != X3
% 3.88/0.99      | sK1 != X2
% 3.88/0.99      | sK1 != X1 ),
% 3.88/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_20]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_262,plain,
% 3.88/0.99      ( ~ m1_subset_1(k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.88/0.99      | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.88/0.99      | k6_partfun1(sK1) = k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) ),
% 3.88/0.99      inference(unflattening,[status(thm)],[c_261]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_15,plain,
% 3.88/0.99      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.88/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_38,plain,
% 3.88/0.99      ( m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 3.88/0.99      inference(instantiation,[status(thm)],[c_15]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_264,plain,
% 3.88/0.99      ( ~ m1_subset_1(k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.88/0.99      | k6_partfun1(sK1) = k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) ),
% 3.88/0.99      inference(global_propositional_subsumption,
% 3.88/0.99                [status(thm)],
% 3.88/0.99                [c_262,c_38]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_697,plain,
% 3.88/0.99      ( k6_partfun1(sK1) = k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2)
% 3.88/0.99      | m1_subset_1(k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_264]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_3358,plain,
% 3.88/0.99      ( k5_relat_1(sK3,sK2) = k6_partfun1(sK1)
% 3.88/0.99      | m1_subset_1(k5_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
% 3.88/0.99      inference(demodulation,[status(thm)],[c_3355,c_697]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_26,plain,
% 3.88/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_28,plain,
% 3.88/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_13,plain,
% 3.88/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.88/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.88/0.99      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.88/0.99      | ~ v1_funct_1(X0)
% 3.88/0.99      | ~ v1_funct_1(X3) ),
% 3.88/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_707,plain,
% 3.88/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.88/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 3.88/0.99      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 3.88/0.99      | v1_funct_1(X0) != iProver_top
% 3.88/0.99      | v1_funct_1(X3) != iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_3360,plain,
% 3.88/0.99      ( m1_subset_1(k5_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
% 3.88/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.88/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.88/0.99      | v1_funct_1(sK3) != iProver_top
% 3.88/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_3355,c_707]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_3420,plain,
% 3.88/0.99      ( k5_relat_1(sK3,sK2) = k6_partfun1(sK1) ),
% 3.88/0.99      inference(global_propositional_subsumption,
% 3.88/0.99                [status(thm)],
% 3.88/0.99                [c_3358,c_25,c_26,c_27,c_28,c_3360]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_13278,plain,
% 3.88/0.99      ( k1_partfun1(sK1,sK0,k1_relat_1(sK2),k2_relat_1(sK2),sK3,sK2) = k6_partfun1(sK1)
% 3.88/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.88/0.99      inference(light_normalisation,[status(thm)],[c_13256,c_3420]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_3,plain,
% 3.88/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.88/0.99      | ~ v1_relat_1(X1)
% 3.88/0.99      | v1_relat_1(X0) ),
% 3.88/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_836,plain,
% 3.88/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.88/0.99      | v1_relat_1(X0)
% 3.88/0.99      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 3.88/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_1227,plain,
% 3.88/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.88/0.99      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
% 3.88/0.99      | v1_relat_1(sK2) ),
% 3.88/0.99      inference(instantiation,[status(thm)],[c_836]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_1228,plain,
% 3.88/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.88/0.99      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 3.88/0.99      | v1_relat_1(sK2) = iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_1227]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_6,plain,
% 3.88/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.88/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_1370,plain,
% 3.88/0.99      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 3.88/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_1371,plain,
% 3.88/0.99      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_1370]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_13527,plain,
% 3.88/0.99      ( k1_partfun1(sK1,sK0,k1_relat_1(sK2),k2_relat_1(sK2),sK3,sK2) = k6_partfun1(sK1) ),
% 3.88/0.99      inference(global_propositional_subsumption,
% 3.88/0.99                [status(thm)],
% 3.88/0.99                [c_13278,c_26,c_1228,c_1371]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_9,plain,
% 3.88/0.99      ( v5_relat_1(X0,X1)
% 3.88/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.88/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_5,plain,
% 3.88/0.99      ( ~ v5_relat_1(X0,X1)
% 3.88/0.99      | r1_tarski(k2_relat_1(X0),X1)
% 3.88/0.99      | ~ v1_relat_1(X0) ),
% 3.88/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_240,plain,
% 3.88/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.88/0.99      | r1_tarski(k2_relat_1(X0),X2)
% 3.88/0.99      | ~ v1_relat_1(X0) ),
% 3.88/0.99      inference(resolution,[status(thm)],[c_9,c_5]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_698,plain,
% 3.88/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.88/0.99      | r1_tarski(k2_relat_1(X0),X2) = iProver_top
% 3.88/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_240]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_2647,plain,
% 3.88/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.88/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 3.88/0.99      | r1_tarski(k2_relat_1(k1_partfun1(X4,X5,X1,X2,X3,X0)),X2) = iProver_top
% 3.88/0.99      | v1_funct_1(X0) != iProver_top
% 3.88/0.99      | v1_funct_1(X3) != iProver_top
% 3.88/0.99      | v1_relat_1(k1_partfun1(X4,X5,X1,X2,X3,X0)) != iProver_top ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_707,c_698]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_710,plain,
% 3.88/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.88/0.99      | v1_relat_1(X1) != iProver_top
% 3.88/0.99      | v1_relat_1(X0) = iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_2645,plain,
% 3.88/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.88/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 3.88/0.99      | v1_funct_1(X0) != iProver_top
% 3.88/0.99      | v1_funct_1(X3) != iProver_top
% 3.88/0.99      | v1_relat_1(k1_partfun1(X4,X5,X1,X2,X3,X0)) = iProver_top
% 3.88/0.99      | v1_relat_1(k2_zfmisc_1(X4,X2)) != iProver_top ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_707,c_710]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_709,plain,
% 3.88/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_5701,plain,
% 3.88/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.88/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 3.88/0.99      | v1_funct_1(X0) != iProver_top
% 3.88/0.99      | v1_funct_1(X3) != iProver_top
% 3.88/0.99      | v1_relat_1(k1_partfun1(X4,X5,X1,X2,X3,X0)) = iProver_top ),
% 3.88/0.99      inference(forward_subsumption_resolution,
% 3.88/0.99                [status(thm)],
% 3.88/0.99                [c_2645,c_709]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_8013,plain,
% 3.88/0.99      ( v1_funct_1(X3) != iProver_top
% 3.88/0.99      | v1_funct_1(X0) != iProver_top
% 3.88/0.99      | r1_tarski(k2_relat_1(k1_partfun1(X4,X5,X1,X2,X3,X0)),X2) = iProver_top
% 3.88/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 3.88/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 3.88/0.99      inference(global_propositional_subsumption,
% 3.88/0.99                [status(thm)],
% 3.88/0.99                [c_2647,c_5701]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_8014,plain,
% 3.88/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.88/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 3.88/0.99      | r1_tarski(k2_relat_1(k1_partfun1(X4,X5,X1,X2,X3,X0)),X2) = iProver_top
% 3.88/0.99      | v1_funct_1(X0) != iProver_top
% 3.88/0.99      | v1_funct_1(X3) != iProver_top ),
% 3.88/0.99      inference(renaming,[status(thm)],[c_8013]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_13530,plain,
% 3.88/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.88/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 3.88/0.99      | r1_tarski(k2_relat_1(k6_partfun1(sK1)),k2_relat_1(sK2)) = iProver_top
% 3.88/0.99      | v1_funct_1(sK3) != iProver_top
% 3.88/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_13527,c_8014]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_7,plain,
% 3.88/0.99      ( k2_relat_1(k6_partfun1(X0)) = X0 ),
% 3.88/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_13554,plain,
% 3.88/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.88/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 3.88/0.99      | r1_tarski(sK1,k2_relat_1(sK2)) = iProver_top
% 3.88/0.99      | v1_funct_1(sK3) != iProver_top
% 3.88/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.88/0.99      inference(demodulation,[status(thm)],[c_13530,c_7]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_19,negated_conjecture,
% 3.88/0.99      ( k2_relset_1(sK0,sK1,sK2) != sK1 ),
% 3.88/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_10,plain,
% 3.88/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.88/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.88/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_872,plain,
% 3.88/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.88/0.99      | k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 3.88/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_392,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_859,plain,
% 3.88/0.99      ( k2_relset_1(sK0,sK1,sK2) != X0
% 3.88/0.99      | k2_relset_1(sK0,sK1,sK2) = sK1
% 3.88/0.99      | sK1 != X0 ),
% 3.88/0.99      inference(instantiation,[status(thm)],[c_392]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_992,plain,
% 3.88/0.99      ( k2_relset_1(sK0,sK1,sK2) != k2_relat_1(sK2)
% 3.88/0.99      | k2_relset_1(sK0,sK1,sK2) = sK1
% 3.88/0.99      | sK1 != k2_relat_1(sK2) ),
% 3.88/0.99      inference(instantiation,[status(thm)],[c_859]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_1139,plain,
% 3.88/0.99      ( r1_tarski(k2_relat_1(sK2),sK1) = iProver_top
% 3.88/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_700,c_698]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_0,plain,
% 3.88/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.88/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_1526,plain,
% 3.88/0.99      ( ~ r1_tarski(k2_relat_1(sK2),sK1)
% 3.88/0.99      | ~ r1_tarski(sK1,k2_relat_1(sK2))
% 3.88/0.99      | sK1 = k2_relat_1(sK2) ),
% 3.88/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_1527,plain,
% 3.88/0.99      ( sK1 = k2_relat_1(sK2)
% 3.88/0.99      | r1_tarski(k2_relat_1(sK2),sK1) != iProver_top
% 3.88/0.99      | r1_tarski(sK1,k2_relat_1(sK2)) != iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_1526]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_14238,plain,
% 3.88/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top ),
% 3.88/0.99      inference(global_propositional_subsumption,
% 3.88/0.99                [status(thm)],
% 3.88/0.99                [c_13554,c_25,c_23,c_26,c_27,c_28,c_19,c_872,c_992,
% 3.88/0.99                 c_1139,c_1228,c_1371,c_1527]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_14243,plain,
% 3.88/0.99      ( r1_tarski(k2_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 3.88/0.99      | v1_funct_1(sK2) != iProver_top
% 3.88/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.88/0.99      inference(superposition,[status(thm)],[c_703,c_14238]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_7287,plain,
% 3.88/0.99      ( r1_tarski(k2_relat_1(sK2),k2_relat_1(sK2)) ),
% 3.88/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(c_7290,plain,
% 3.88/0.99      ( r1_tarski(k2_relat_1(sK2),k2_relat_1(sK2)) = iProver_top ),
% 3.88/0.99      inference(predicate_to_equality,[status(thm)],[c_7287]) ).
% 3.88/0.99  
% 3.88/0.99  cnf(contradiction,plain,
% 3.88/0.99      ( $false ),
% 3.88/0.99      inference(minisat,
% 3.88/0.99                [status(thm)],
% 3.88/0.99                [c_14243,c_7290,c_1371,c_1228,c_26,c_25]) ).
% 3.88/0.99  
% 3.88/0.99  
% 3.88/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.88/0.99  
% 3.88/0.99  ------                               Statistics
% 3.88/0.99  
% 3.88/0.99  ------ General
% 3.88/0.99  
% 3.88/0.99  abstr_ref_over_cycles:                  0
% 3.88/0.99  abstr_ref_under_cycles:                 0
% 3.88/0.99  gc_basic_clause_elim:                   0
% 3.88/0.99  forced_gc_time:                         0
% 3.88/0.99  parsing_time:                           0.008
% 3.88/0.99  unif_index_cands_time:                  0.
% 3.88/0.99  unif_index_add_time:                    0.
% 3.88/0.99  orderings_time:                         0.
% 3.88/0.99  out_proof_time:                         0.014
% 3.88/0.99  total_time:                             0.427
% 3.88/0.99  num_of_symbols:                         49
% 3.88/0.99  num_of_terms:                           15814
% 3.88/0.99  
% 3.88/0.99  ------ Preprocessing
% 3.88/0.99  
% 3.88/0.99  num_of_splits:                          0
% 3.88/0.99  num_of_split_atoms:                     0
% 3.88/0.99  num_of_reused_defs:                     0
% 3.88/0.99  num_eq_ax_congr_red:                    11
% 3.88/0.99  num_of_sem_filtered_clauses:            1
% 3.88/0.99  num_of_subtypes:                        0
% 3.88/0.99  monotx_restored_types:                  0
% 3.88/0.99  sat_num_of_epr_types:                   0
% 3.88/0.99  sat_num_of_non_cyclic_types:            0
% 3.88/0.99  sat_guarded_non_collapsed_types:        0
% 3.88/0.99  num_pure_diseq_elim:                    0
% 3.88/0.99  simp_replaced_by:                       0
% 3.88/0.99  res_preprocessed:                       107
% 3.88/0.99  prep_upred:                             0
% 3.88/0.99  prep_unflattend:                        8
% 3.88/0.99  smt_new_axioms:                         0
% 3.88/0.99  pred_elim_cands:                        4
% 3.88/0.99  pred_elim:                              2
% 3.88/0.99  pred_elim_cl:                           4
% 3.88/0.99  pred_elim_cycles:                       4
% 3.88/0.99  merged_defs:                            0
% 3.88/0.99  merged_defs_ncl:                        0
% 3.88/0.99  bin_hyper_res:                          0
% 3.88/0.99  prep_cycles:                            4
% 3.88/0.99  pred_elim_time:                         0.001
% 3.88/0.99  splitting_time:                         0.
% 3.88/0.99  sem_filter_time:                        0.
% 3.88/0.99  monotx_time:                            0.001
% 3.88/0.99  subtype_inf_time:                       0.
% 3.88/0.99  
% 3.88/0.99  ------ Problem properties
% 3.88/0.99  
% 3.88/0.99  clauses:                                19
% 3.88/0.99  conjectures:                            5
% 3.88/0.99  epr:                                    4
% 3.88/0.99  horn:                                   19
% 3.88/0.99  ground:                                 6
% 3.88/0.99  unary:                                  10
% 3.88/0.99  binary:                                 2
% 3.88/0.99  lits:                                   42
% 3.88/0.99  lits_eq:                                7
% 3.88/0.99  fd_pure:                                0
% 3.88/0.99  fd_pseudo:                              0
% 3.88/0.99  fd_cond:                                0
% 3.88/0.99  fd_pseudo_cond:                         1
% 3.88/0.99  ac_symbols:                             0
% 3.88/0.99  
% 3.88/0.99  ------ Propositional Solver
% 3.88/0.99  
% 3.88/0.99  prop_solver_calls:                      29
% 3.88/0.99  prop_fast_solver_calls:                 1092
% 3.88/0.99  smt_solver_calls:                       0
% 3.88/0.99  smt_fast_solver_calls:                  0
% 3.88/0.99  prop_num_of_clauses:                    6886
% 3.88/0.99  prop_preprocess_simplified:             12683
% 3.88/0.99  prop_fo_subsumed:                       115
% 3.88/0.99  prop_solver_time:                       0.
% 3.88/0.99  smt_solver_time:                        0.
% 3.88/0.99  smt_fast_solver_time:                   0.
% 3.88/0.99  prop_fast_solver_time:                  0.
% 3.88/0.99  prop_unsat_core_time:                   0.001
% 3.88/0.99  
% 3.88/0.99  ------ QBF
% 3.88/0.99  
% 3.88/0.99  qbf_q_res:                              0
% 3.88/0.99  qbf_num_tautologies:                    0
% 3.88/0.99  qbf_prep_cycles:                        0
% 3.88/0.99  
% 3.88/0.99  ------ BMC1
% 3.88/0.99  
% 3.88/0.99  bmc1_current_bound:                     -1
% 3.88/0.99  bmc1_last_solved_bound:                 -1
% 3.88/0.99  bmc1_unsat_core_size:                   -1
% 3.88/0.99  bmc1_unsat_core_parents_size:           -1
% 3.88/0.99  bmc1_merge_next_fun:                    0
% 3.88/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.88/0.99  
% 3.88/0.99  ------ Instantiation
% 3.88/0.99  
% 3.88/0.99  inst_num_of_clauses:                    1646
% 3.88/0.99  inst_num_in_passive:                    462
% 3.88/0.99  inst_num_in_active:                     699
% 3.88/0.99  inst_num_in_unprocessed:                486
% 3.88/0.99  inst_num_of_loops:                      730
% 3.88/0.99  inst_num_of_learning_restarts:          0
% 3.88/0.99  inst_num_moves_active_passive:          30
% 3.88/0.99  inst_lit_activity:                      0
% 3.88/0.99  inst_lit_activity_moves:                1
% 3.88/0.99  inst_num_tautologies:                   0
% 3.88/0.99  inst_num_prop_implied:                  0
% 3.88/0.99  inst_num_existing_simplified:           0
% 3.88/0.99  inst_num_eq_res_simplified:             0
% 3.88/0.99  inst_num_child_elim:                    0
% 3.88/0.99  inst_num_of_dismatching_blockings:      84
% 3.88/0.99  inst_num_of_non_proper_insts:           1008
% 3.88/0.99  inst_num_of_duplicates:                 0
% 3.88/0.99  inst_inst_num_from_inst_to_res:         0
% 3.88/0.99  inst_dismatching_checking_time:         0.
% 3.88/0.99  
% 3.88/0.99  ------ Resolution
% 3.88/0.99  
% 3.88/0.99  res_num_of_clauses:                     0
% 3.88/0.99  res_num_in_passive:                     0
% 3.88/0.99  res_num_in_active:                      0
% 3.88/0.99  res_num_of_loops:                       111
% 3.88/0.99  res_forward_subset_subsumed:            40
% 3.88/0.99  res_backward_subset_subsumed:           2
% 3.88/0.99  res_forward_subsumed:                   0
% 3.88/0.99  res_backward_subsumed:                  0
% 3.88/0.99  res_forward_subsumption_resolution:     0
% 3.88/0.99  res_backward_subsumption_resolution:    0
% 3.88/0.99  res_clause_to_clause_subsumption:       1080
% 3.88/0.99  res_orphan_elimination:                 0
% 3.88/0.99  res_tautology_del:                      37
% 3.88/0.99  res_num_eq_res_simplified:              0
% 3.88/0.99  res_num_sel_changes:                    0
% 3.88/0.99  res_moves_from_active_to_pass:          0
% 3.88/0.99  
% 3.88/0.99  ------ Superposition
% 3.88/0.99  
% 3.88/0.99  sup_time_total:                         0.
% 3.88/0.99  sup_time_generating:                    0.
% 3.88/0.99  sup_time_sim_full:                      0.
% 3.88/0.99  sup_time_sim_immed:                     0.
% 3.88/0.99  
% 3.88/0.99  sup_num_of_clauses:                     394
% 3.88/0.99  sup_num_in_active:                      143
% 3.88/0.99  sup_num_in_passive:                     251
% 3.88/0.99  sup_num_of_loops:                       145
% 3.88/0.99  sup_fw_superposition:                   259
% 3.88/0.99  sup_bw_superposition:                   184
% 3.88/0.99  sup_immediate_simplified:               79
% 3.88/0.99  sup_given_eliminated:                   0
% 3.88/0.99  comparisons_done:                       0
% 3.88/0.99  comparisons_avoided:                    0
% 3.88/0.99  
% 3.88/0.99  ------ Simplifications
% 3.88/0.99  
% 3.88/0.99  
% 3.88/0.99  sim_fw_subset_subsumed:                 18
% 3.88/0.99  sim_bw_subset_subsumed:                 7
% 3.88/0.99  sim_fw_subsumed:                        7
% 3.88/0.99  sim_bw_subsumed:                        4
% 3.88/0.99  sim_fw_subsumption_res:                 7
% 3.88/0.99  sim_bw_subsumption_res:                 0
% 3.88/0.99  sim_tautology_del:                      4
% 3.88/0.99  sim_eq_tautology_del:                   8
% 3.88/0.99  sim_eq_res_simp:                        0
% 3.88/0.99  sim_fw_demodulated:                     8
% 3.88/0.99  sim_bw_demodulated:                     3
% 3.88/0.99  sim_light_normalised:                   49
% 3.88/0.99  sim_joinable_taut:                      0
% 3.88/0.99  sim_joinable_simp:                      0
% 3.88/0.99  sim_ac_normalised:                      0
% 3.88/0.99  sim_smt_subsumption:                    0
% 3.88/0.99  
%------------------------------------------------------------------------------
