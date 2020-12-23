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
% DateTime   : Thu Dec  3 12:01:33 EST 2020

% Result     : Theorem 3.78s
% Output     : CNFRefutation 3.78s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 381 expanded)
%              Number of clauses        :   69 ( 110 expanded)
%              Number of leaves         :   16 (  86 expanded)
%              Depth                    :   19
%              Number of atoms          :  389 (1815 expanded)
%              Number of equality atoms :  148 ( 382 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
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

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f15,plain,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_1(X3) )
           => ( r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
             => k2_relset_1(X0,X1,X2) = X1 ) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f31,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_relset_1(X0,X1,X2) != X1
          & r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f32,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_relset_1(X0,X1,X2) != X1
          & r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f38,plain,(
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

fof(f37,plain,
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

fof(f39,plain,
    ( k2_relset_1(sK0,sK1,sK2) != sK1
    & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k6_partfun1(sK1))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f32,f38,f37])).

fof(f59,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f62,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f39])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_1(X0) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f29,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f30,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f58,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f27])).

fof(f55,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f61,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f60,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f39])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f23])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f63,plain,(
    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f39])).

fof(f9,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f54,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f26,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f25])).

fof(f53,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f11,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f65,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f46,f56])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f33])).

fof(f42,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f64,plain,(
    k2_relset_1(sK0,sK1,sK2) != sK1 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_23,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_682,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_685,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_16,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_686,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_687,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1602,plain,
    ( k1_partfun1(X0,X1,k1_relat_1(X2),k2_relat_1(X2),X3,X2) = k5_relat_1(X3,X2)
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_686,c_687])).

cnf(c_4423,plain,
    ( k1_partfun1(sK1,sK0,k1_relat_1(X0),k2_relat_1(X0),sK3,X0) = k5_relat_1(sK3,X0)
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_685,c_1602])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_26,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4780,plain,
    ( v1_funct_1(X0) != iProver_top
    | k1_partfun1(sK1,sK0,k1_relat_1(X0),k2_relat_1(X0),sK3,X0) = k5_relat_1(sK3,X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4423,c_26])).

cnf(c_4781,plain,
    ( k1_partfun1(sK1,sK0,k1_relat_1(X0),k2_relat_1(X0),sK3,X0) = k5_relat_1(sK3,X0)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4780])).

cnf(c_4788,plain,
    ( k1_partfun1(sK1,sK0,k1_relat_1(sK2),k2_relat_1(sK2),sK3,sK2) = k5_relat_1(sK3,sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_682,c_4781])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_683,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1604,plain,
    ( k1_partfun1(X0,X1,sK0,sK1,X2,sK2) = k5_relat_1(X2,sK2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_683,c_687])).

cnf(c_24,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1807,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK0,sK1,X2,sK2) = k5_relat_1(X2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1604,c_24])).

cnf(c_1808,plain,
    ( k1_partfun1(X0,X1,sK0,sK1,X2,sK2) = k5_relat_1(X2,sK2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_1807])).

cnf(c_1815,plain,
    ( k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) = k5_relat_1(sK3,sK2)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_685,c_1808])).

cnf(c_11,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_19,negated_conjecture,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_272,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) != X0
    | k6_partfun1(sK1) != X3
    | sK1 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_19])).

cnf(c_273,plain,
    ( ~ m1_subset_1(k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k6_partfun1(sK1) = k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) ),
    inference(unflattening,[status(thm)],[c_272])).

cnf(c_14,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_37,plain,
    ( m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_275,plain,
    ( ~ m1_subset_1(k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k6_partfun1(sK1) = k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_273,c_37])).

cnf(c_680,plain,
    ( k6_partfun1(sK1) = k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2)
    | m1_subset_1(k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_275])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_719,plain,
    ( m1_subset_1(k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_853,plain,
    ( k6_partfun1(sK1) = k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_680,c_23,c_22,c_21,c_20,c_37,c_273,c_719])).

cnf(c_1817,plain,
    ( k5_relat_1(sK3,sK2) = k6_partfun1(sK1)
    | v1_funct_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1815,c_853])).

cnf(c_2026,plain,
    ( k5_relat_1(sK3,sK2) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1817,c_26])).

cnf(c_4794,plain,
    ( k1_partfun1(sK1,sK0,k1_relat_1(sK2),k2_relat_1(sK2),sK3,sK2) = k6_partfun1(sK1)
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4788,c_2026])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_692,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1026,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_683,c_692])).

cnf(c_5099,plain,
    ( k1_partfun1(sK1,sK0,k1_relat_1(sK2),k2_relat_1(sK2),sK3,sK2) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4794,c_1026])).

cnf(c_690,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v5_relat_1(X0,X2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_232,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X3),X4)
    | ~ v1_relat_1(X3)
    | X0 != X3
    | X2 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_8])).

cnf(c_233,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_232])).

cnf(c_237,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_233,c_7])).

cnf(c_238,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_237])).

cnf(c_681,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_238])).

cnf(c_2096,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | r1_tarski(k2_relat_1(k1_partfun1(X4,X5,X1,X2,X3,X0)),X2) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(superposition,[status(thm)],[c_690,c_681])).

cnf(c_10939,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | r1_tarski(k2_relat_1(k6_partfun1(sK1)),k2_relat_1(sK2)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5099,c_2096])).

cnf(c_5,plain,
    ( k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_10968,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | r1_tarski(sK1,k2_relat_1(sK2)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10939,c_5])).

cnf(c_2968,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_2969,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2968])).

cnf(c_789,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(instantiation,[status(thm)],[c_238])).

cnf(c_891,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(instantiation,[status(thm)],[c_789])).

cnf(c_892,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | r1_tarski(k2_relat_1(sK2),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_891])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_823,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_741,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1)
    | ~ r1_tarski(sK1,k2_relat_1(sK2))
    | sK1 = k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_742,plain,
    ( sK1 = k2_relat_1(sK2)
    | r1_tarski(k2_relat_1(sK2),sK1) != iProver_top
    | r1_tarski(sK1,k2_relat_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_741])).

cnf(c_413,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_718,plain,
    ( k2_relset_1(sK0,sK1,sK2) != X0
    | k2_relset_1(sK0,sK1,sK2) = sK1
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_413])).

cnf(c_733,plain,
    ( k2_relset_1(sK0,sK1,sK2) != k2_relat_1(sK2)
    | k2_relset_1(sK0,sK1,sK2) = sK1
    | sK1 != k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_718])).

cnf(c_18,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) != sK1 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_27,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_25,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10968,c_2969,c_1026,c_892,c_823,c_742,c_733,c_18,c_27,c_26,c_25,c_22,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:50:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.78/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.78/0.99  
% 3.78/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.78/0.99  
% 3.78/0.99  ------  iProver source info
% 3.78/0.99  
% 3.78/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.78/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.78/0.99  git: non_committed_changes: false
% 3.78/0.99  git: last_make_outside_of_git: false
% 3.78/0.99  
% 3.78/0.99  ------ 
% 3.78/0.99  
% 3.78/0.99  ------ Input Options
% 3.78/0.99  
% 3.78/0.99  --out_options                           all
% 3.78/0.99  --tptp_safe_out                         true
% 3.78/0.99  --problem_path                          ""
% 3.78/0.99  --include_path                          ""
% 3.78/0.99  --clausifier                            res/vclausify_rel
% 3.78/0.99  --clausifier_options                    ""
% 3.78/0.99  --stdin                                 false
% 3.78/0.99  --stats_out                             all
% 3.78/0.99  
% 3.78/0.99  ------ General Options
% 3.78/0.99  
% 3.78/0.99  --fof                                   false
% 3.78/0.99  --time_out_real                         305.
% 3.78/0.99  --time_out_virtual                      -1.
% 3.78/0.99  --symbol_type_check                     false
% 3.78/0.99  --clausify_out                          false
% 3.78/0.99  --sig_cnt_out                           false
% 3.78/0.99  --trig_cnt_out                          false
% 3.78/0.99  --trig_cnt_out_tolerance                1.
% 3.78/0.99  --trig_cnt_out_sk_spl                   false
% 3.78/0.99  --abstr_cl_out                          false
% 3.78/0.99  
% 3.78/0.99  ------ Global Options
% 3.78/0.99  
% 3.78/0.99  --schedule                              default
% 3.78/0.99  --add_important_lit                     false
% 3.78/0.99  --prop_solver_per_cl                    1000
% 3.78/0.99  --min_unsat_core                        false
% 3.78/0.99  --soft_assumptions                      false
% 3.78/0.99  --soft_lemma_size                       3
% 3.78/0.99  --prop_impl_unit_size                   0
% 3.78/0.99  --prop_impl_unit                        []
% 3.78/0.99  --share_sel_clauses                     true
% 3.78/0.99  --reset_solvers                         false
% 3.78/0.99  --bc_imp_inh                            [conj_cone]
% 3.78/0.99  --conj_cone_tolerance                   3.
% 3.78/0.99  --extra_neg_conj                        none
% 3.78/0.99  --large_theory_mode                     true
% 3.78/0.99  --prolific_symb_bound                   200
% 3.78/0.99  --lt_threshold                          2000
% 3.78/0.99  --clause_weak_htbl                      true
% 3.78/0.99  --gc_record_bc_elim                     false
% 3.78/0.99  
% 3.78/0.99  ------ Preprocessing Options
% 3.78/0.99  
% 3.78/0.99  --preprocessing_flag                    true
% 3.78/0.99  --time_out_prep_mult                    0.1
% 3.78/0.99  --splitting_mode                        input
% 3.78/0.99  --splitting_grd                         true
% 3.78/0.99  --splitting_cvd                         false
% 3.78/0.99  --splitting_cvd_svl                     false
% 3.78/0.99  --splitting_nvd                         32
% 3.78/0.99  --sub_typing                            true
% 3.78/0.99  --prep_gs_sim                           true
% 3.78/0.99  --prep_unflatten                        true
% 3.78/0.99  --prep_res_sim                          true
% 3.78/0.99  --prep_upred                            true
% 3.78/0.99  --prep_sem_filter                       exhaustive
% 3.78/0.99  --prep_sem_filter_out                   false
% 3.78/0.99  --pred_elim                             true
% 3.78/0.99  --res_sim_input                         true
% 3.78/0.99  --eq_ax_congr_red                       true
% 3.78/0.99  --pure_diseq_elim                       true
% 3.78/0.99  --brand_transform                       false
% 3.78/0.99  --non_eq_to_eq                          false
% 3.78/0.99  --prep_def_merge                        true
% 3.78/0.99  --prep_def_merge_prop_impl              false
% 3.78/0.99  --prep_def_merge_mbd                    true
% 3.78/0.99  --prep_def_merge_tr_red                 false
% 3.78/0.99  --prep_def_merge_tr_cl                  false
% 3.78/0.99  --smt_preprocessing                     true
% 3.78/0.99  --smt_ac_axioms                         fast
% 3.78/0.99  --preprocessed_out                      false
% 3.78/0.99  --preprocessed_stats                    false
% 3.78/0.99  
% 3.78/0.99  ------ Abstraction refinement Options
% 3.78/0.99  
% 3.78/0.99  --abstr_ref                             []
% 3.78/0.99  --abstr_ref_prep                        false
% 3.78/0.99  --abstr_ref_until_sat                   false
% 3.78/0.99  --abstr_ref_sig_restrict                funpre
% 3.78/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.78/0.99  --abstr_ref_under                       []
% 3.78/0.99  
% 3.78/0.99  ------ SAT Options
% 3.78/0.99  
% 3.78/0.99  --sat_mode                              false
% 3.78/0.99  --sat_fm_restart_options                ""
% 3.78/0.99  --sat_gr_def                            false
% 3.78/0.99  --sat_epr_types                         true
% 3.78/0.99  --sat_non_cyclic_types                  false
% 3.78/0.99  --sat_finite_models                     false
% 3.78/0.99  --sat_fm_lemmas                         false
% 3.78/0.99  --sat_fm_prep                           false
% 3.78/0.99  --sat_fm_uc_incr                        true
% 3.78/0.99  --sat_out_model                         small
% 3.78/0.99  --sat_out_clauses                       false
% 3.78/0.99  
% 3.78/0.99  ------ QBF Options
% 3.78/0.99  
% 3.78/0.99  --qbf_mode                              false
% 3.78/0.99  --qbf_elim_univ                         false
% 3.78/0.99  --qbf_dom_inst                          none
% 3.78/0.99  --qbf_dom_pre_inst                      false
% 3.78/0.99  --qbf_sk_in                             false
% 3.78/0.99  --qbf_pred_elim                         true
% 3.78/0.99  --qbf_split                             512
% 3.78/0.99  
% 3.78/0.99  ------ BMC1 Options
% 3.78/0.99  
% 3.78/0.99  --bmc1_incremental                      false
% 3.78/0.99  --bmc1_axioms                           reachable_all
% 3.78/0.99  --bmc1_min_bound                        0
% 3.78/0.99  --bmc1_max_bound                        -1
% 3.78/0.99  --bmc1_max_bound_default                -1
% 3.78/0.99  --bmc1_symbol_reachability              true
% 3.78/0.99  --bmc1_property_lemmas                  false
% 3.78/0.99  --bmc1_k_induction                      false
% 3.78/0.99  --bmc1_non_equiv_states                 false
% 3.78/0.99  --bmc1_deadlock                         false
% 3.78/0.99  --bmc1_ucm                              false
% 3.78/0.99  --bmc1_add_unsat_core                   none
% 3.78/0.99  --bmc1_unsat_core_children              false
% 3.78/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.78/0.99  --bmc1_out_stat                         full
% 3.78/0.99  --bmc1_ground_init                      false
% 3.78/0.99  --bmc1_pre_inst_next_state              false
% 3.78/0.99  --bmc1_pre_inst_state                   false
% 3.78/0.99  --bmc1_pre_inst_reach_state             false
% 3.78/0.99  --bmc1_out_unsat_core                   false
% 3.78/0.99  --bmc1_aig_witness_out                  false
% 3.78/0.99  --bmc1_verbose                          false
% 3.78/0.99  --bmc1_dump_clauses_tptp                false
% 3.78/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.78/0.99  --bmc1_dump_file                        -
% 3.78/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.78/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.78/0.99  --bmc1_ucm_extend_mode                  1
% 3.78/0.99  --bmc1_ucm_init_mode                    2
% 3.78/0.99  --bmc1_ucm_cone_mode                    none
% 3.78/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.78/0.99  --bmc1_ucm_relax_model                  4
% 3.78/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.78/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.78/0.99  --bmc1_ucm_layered_model                none
% 3.78/0.99  --bmc1_ucm_max_lemma_size               10
% 3.78/0.99  
% 3.78/0.99  ------ AIG Options
% 3.78/0.99  
% 3.78/0.99  --aig_mode                              false
% 3.78/0.99  
% 3.78/0.99  ------ Instantiation Options
% 3.78/0.99  
% 3.78/0.99  --instantiation_flag                    true
% 3.78/0.99  --inst_sos_flag                         true
% 3.78/0.99  --inst_sos_phase                        true
% 3.78/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.78/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.78/0.99  --inst_lit_sel_side                     num_symb
% 3.78/0.99  --inst_solver_per_active                1400
% 3.78/0.99  --inst_solver_calls_frac                1.
% 3.78/0.99  --inst_passive_queue_type               priority_queues
% 3.78/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.78/0.99  --inst_passive_queues_freq              [25;2]
% 3.78/0.99  --inst_dismatching                      true
% 3.78/0.99  --inst_eager_unprocessed_to_passive     true
% 3.78/0.99  --inst_prop_sim_given                   true
% 3.78/0.99  --inst_prop_sim_new                     false
% 3.78/0.99  --inst_subs_new                         false
% 3.78/0.99  --inst_eq_res_simp                      false
% 3.78/0.99  --inst_subs_given                       false
% 3.78/0.99  --inst_orphan_elimination               true
% 3.78/0.99  --inst_learning_loop_flag               true
% 3.78/0.99  --inst_learning_start                   3000
% 3.78/0.99  --inst_learning_factor                  2
% 3.78/0.99  --inst_start_prop_sim_after_learn       3
% 3.78/0.99  --inst_sel_renew                        solver
% 3.78/0.99  --inst_lit_activity_flag                true
% 3.78/0.99  --inst_restr_to_given                   false
% 3.78/0.99  --inst_activity_threshold               500
% 3.78/0.99  --inst_out_proof                        true
% 3.78/0.99  
% 3.78/0.99  ------ Resolution Options
% 3.78/0.99  
% 3.78/0.99  --resolution_flag                       true
% 3.78/0.99  --res_lit_sel                           adaptive
% 3.78/0.99  --res_lit_sel_side                      none
% 3.78/0.99  --res_ordering                          kbo
% 3.78/0.99  --res_to_prop_solver                    active
% 3.78/0.99  --res_prop_simpl_new                    false
% 3.78/0.99  --res_prop_simpl_given                  true
% 3.78/0.99  --res_passive_queue_type                priority_queues
% 3.78/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.78/0.99  --res_passive_queues_freq               [15;5]
% 3.78/0.99  --res_forward_subs                      full
% 3.78/0.99  --res_backward_subs                     full
% 3.78/0.99  --res_forward_subs_resolution           true
% 3.78/0.99  --res_backward_subs_resolution          true
% 3.78/0.99  --res_orphan_elimination                true
% 3.78/0.99  --res_time_limit                        2.
% 3.78/0.99  --res_out_proof                         true
% 3.78/0.99  
% 3.78/0.99  ------ Superposition Options
% 3.78/0.99  
% 3.78/0.99  --superposition_flag                    true
% 3.78/0.99  --sup_passive_queue_type                priority_queues
% 3.78/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.78/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.78/0.99  --demod_completeness_check              fast
% 3.78/0.99  --demod_use_ground                      true
% 3.78/0.99  --sup_to_prop_solver                    passive
% 3.78/0.99  --sup_prop_simpl_new                    true
% 3.78/0.99  --sup_prop_simpl_given                  true
% 3.78/0.99  --sup_fun_splitting                     true
% 3.78/0.99  --sup_smt_interval                      50000
% 3.78/0.99  
% 3.78/0.99  ------ Superposition Simplification Setup
% 3.78/0.99  
% 3.78/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.78/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.78/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.78/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.78/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.78/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.78/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.78/0.99  --sup_immed_triv                        [TrivRules]
% 3.78/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.78/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.78/0.99  --sup_immed_bw_main                     []
% 3.78/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.78/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.78/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.78/0.99  --sup_input_bw                          []
% 3.78/0.99  
% 3.78/0.99  ------ Combination Options
% 3.78/0.99  
% 3.78/0.99  --comb_res_mult                         3
% 3.78/0.99  --comb_sup_mult                         2
% 3.78/0.99  --comb_inst_mult                        10
% 3.78/0.99  
% 3.78/0.99  ------ Debug Options
% 3.78/0.99  
% 3.78/0.99  --dbg_backtrace                         false
% 3.78/0.99  --dbg_dump_prop_clauses                 false
% 3.78/0.99  --dbg_dump_prop_clauses_file            -
% 3.78/0.99  --dbg_out_stat                          false
% 3.78/0.99  ------ Parsing...
% 3.78/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.78/0.99  
% 3.78/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.78/0.99  
% 3.78/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.78/0.99  
% 3.78/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.78/0.99  ------ Proving...
% 3.78/0.99  ------ Problem Properties 
% 3.78/0.99  
% 3.78/0.99  
% 3.78/0.99  clauses                                 18
% 3.78/0.99  conjectures                             5
% 3.78/0.99  EPR                                     4
% 3.78/0.99  Horn                                    18
% 3.78/0.99  unary                                   9
% 3.78/0.99  binary                                  4
% 3.78/0.99  lits                                    38
% 3.78/0.99  lits eq                                 7
% 3.78/0.99  fd_pure                                 0
% 3.78/0.99  fd_pseudo                               0
% 3.78/0.99  fd_cond                                 0
% 3.78/0.99  fd_pseudo_cond                          1
% 3.78/0.99  AC symbols                              0
% 3.78/0.99  
% 3.78/0.99  ------ Schedule dynamic 5 is on 
% 3.78/0.99  
% 3.78/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.78/0.99  
% 3.78/0.99  
% 3.78/0.99  ------ 
% 3.78/0.99  Current options:
% 3.78/0.99  ------ 
% 3.78/0.99  
% 3.78/0.99  ------ Input Options
% 3.78/0.99  
% 3.78/0.99  --out_options                           all
% 3.78/0.99  --tptp_safe_out                         true
% 3.78/0.99  --problem_path                          ""
% 3.78/0.99  --include_path                          ""
% 3.78/0.99  --clausifier                            res/vclausify_rel
% 3.78/0.99  --clausifier_options                    ""
% 3.78/0.99  --stdin                                 false
% 3.78/0.99  --stats_out                             all
% 3.78/0.99  
% 3.78/0.99  ------ General Options
% 3.78/0.99  
% 3.78/0.99  --fof                                   false
% 3.78/0.99  --time_out_real                         305.
% 3.78/0.99  --time_out_virtual                      -1.
% 3.78/0.99  --symbol_type_check                     false
% 3.78/0.99  --clausify_out                          false
% 3.78/0.99  --sig_cnt_out                           false
% 3.78/0.99  --trig_cnt_out                          false
% 3.78/0.99  --trig_cnt_out_tolerance                1.
% 3.78/0.99  --trig_cnt_out_sk_spl                   false
% 3.78/0.99  --abstr_cl_out                          false
% 3.78/0.99  
% 3.78/0.99  ------ Global Options
% 3.78/0.99  
% 3.78/0.99  --schedule                              default
% 3.78/0.99  --add_important_lit                     false
% 3.78/0.99  --prop_solver_per_cl                    1000
% 3.78/0.99  --min_unsat_core                        false
% 3.78/0.99  --soft_assumptions                      false
% 3.78/0.99  --soft_lemma_size                       3
% 3.78/0.99  --prop_impl_unit_size                   0
% 3.78/0.99  --prop_impl_unit                        []
% 3.78/0.99  --share_sel_clauses                     true
% 3.78/0.99  --reset_solvers                         false
% 3.78/0.99  --bc_imp_inh                            [conj_cone]
% 3.78/0.99  --conj_cone_tolerance                   3.
% 3.78/0.99  --extra_neg_conj                        none
% 3.78/0.99  --large_theory_mode                     true
% 3.78/0.99  --prolific_symb_bound                   200
% 3.78/0.99  --lt_threshold                          2000
% 3.78/0.99  --clause_weak_htbl                      true
% 3.78/0.99  --gc_record_bc_elim                     false
% 3.78/0.99  
% 3.78/0.99  ------ Preprocessing Options
% 3.78/0.99  
% 3.78/0.99  --preprocessing_flag                    true
% 3.78/0.99  --time_out_prep_mult                    0.1
% 3.78/0.99  --splitting_mode                        input
% 3.78/0.99  --splitting_grd                         true
% 3.78/0.99  --splitting_cvd                         false
% 3.78/0.99  --splitting_cvd_svl                     false
% 3.78/0.99  --splitting_nvd                         32
% 3.78/0.99  --sub_typing                            true
% 3.78/0.99  --prep_gs_sim                           true
% 3.78/0.99  --prep_unflatten                        true
% 3.78/0.99  --prep_res_sim                          true
% 3.78/0.99  --prep_upred                            true
% 3.78/0.99  --prep_sem_filter                       exhaustive
% 3.78/0.99  --prep_sem_filter_out                   false
% 3.78/0.99  --pred_elim                             true
% 3.78/0.99  --res_sim_input                         true
% 3.78/0.99  --eq_ax_congr_red                       true
% 3.78/0.99  --pure_diseq_elim                       true
% 3.78/0.99  --brand_transform                       false
% 3.78/0.99  --non_eq_to_eq                          false
% 3.78/0.99  --prep_def_merge                        true
% 3.78/0.99  --prep_def_merge_prop_impl              false
% 3.78/0.99  --prep_def_merge_mbd                    true
% 3.78/0.99  --prep_def_merge_tr_red                 false
% 3.78/0.99  --prep_def_merge_tr_cl                  false
% 3.78/0.99  --smt_preprocessing                     true
% 3.78/0.99  --smt_ac_axioms                         fast
% 3.78/0.99  --preprocessed_out                      false
% 3.78/0.99  --preprocessed_stats                    false
% 3.78/0.99  
% 3.78/0.99  ------ Abstraction refinement Options
% 3.78/0.99  
% 3.78/0.99  --abstr_ref                             []
% 3.78/0.99  --abstr_ref_prep                        false
% 3.78/0.99  --abstr_ref_until_sat                   false
% 3.78/0.99  --abstr_ref_sig_restrict                funpre
% 3.78/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.78/0.99  --abstr_ref_under                       []
% 3.78/0.99  
% 3.78/0.99  ------ SAT Options
% 3.78/0.99  
% 3.78/0.99  --sat_mode                              false
% 3.78/0.99  --sat_fm_restart_options                ""
% 3.78/0.99  --sat_gr_def                            false
% 3.78/0.99  --sat_epr_types                         true
% 3.78/0.99  --sat_non_cyclic_types                  false
% 3.78/0.99  --sat_finite_models                     false
% 3.78/0.99  --sat_fm_lemmas                         false
% 3.78/0.99  --sat_fm_prep                           false
% 3.78/0.99  --sat_fm_uc_incr                        true
% 3.78/0.99  --sat_out_model                         small
% 3.78/0.99  --sat_out_clauses                       false
% 3.78/0.99  
% 3.78/0.99  ------ QBF Options
% 3.78/0.99  
% 3.78/0.99  --qbf_mode                              false
% 3.78/0.99  --qbf_elim_univ                         false
% 3.78/0.99  --qbf_dom_inst                          none
% 3.78/0.99  --qbf_dom_pre_inst                      false
% 3.78/0.99  --qbf_sk_in                             false
% 3.78/0.99  --qbf_pred_elim                         true
% 3.78/0.99  --qbf_split                             512
% 3.78/0.99  
% 3.78/0.99  ------ BMC1 Options
% 3.78/0.99  
% 3.78/0.99  --bmc1_incremental                      false
% 3.78/0.99  --bmc1_axioms                           reachable_all
% 3.78/0.99  --bmc1_min_bound                        0
% 3.78/0.99  --bmc1_max_bound                        -1
% 3.78/0.99  --bmc1_max_bound_default                -1
% 3.78/0.99  --bmc1_symbol_reachability              true
% 3.78/0.99  --bmc1_property_lemmas                  false
% 3.78/0.99  --bmc1_k_induction                      false
% 3.78/0.99  --bmc1_non_equiv_states                 false
% 3.78/0.99  --bmc1_deadlock                         false
% 3.78/0.99  --bmc1_ucm                              false
% 3.78/0.99  --bmc1_add_unsat_core                   none
% 3.78/0.99  --bmc1_unsat_core_children              false
% 3.78/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.78/0.99  --bmc1_out_stat                         full
% 3.78/0.99  --bmc1_ground_init                      false
% 3.78/0.99  --bmc1_pre_inst_next_state              false
% 3.78/0.99  --bmc1_pre_inst_state                   false
% 3.78/0.99  --bmc1_pre_inst_reach_state             false
% 3.78/0.99  --bmc1_out_unsat_core                   false
% 3.78/0.99  --bmc1_aig_witness_out                  false
% 3.78/0.99  --bmc1_verbose                          false
% 3.78/0.99  --bmc1_dump_clauses_tptp                false
% 3.78/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.78/0.99  --bmc1_dump_file                        -
% 3.78/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.78/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.78/0.99  --bmc1_ucm_extend_mode                  1
% 3.78/0.99  --bmc1_ucm_init_mode                    2
% 3.78/0.99  --bmc1_ucm_cone_mode                    none
% 3.78/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.78/0.99  --bmc1_ucm_relax_model                  4
% 3.78/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.78/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.78/0.99  --bmc1_ucm_layered_model                none
% 3.78/0.99  --bmc1_ucm_max_lemma_size               10
% 3.78/0.99  
% 3.78/0.99  ------ AIG Options
% 3.78/0.99  
% 3.78/0.99  --aig_mode                              false
% 3.78/0.99  
% 3.78/0.99  ------ Instantiation Options
% 3.78/0.99  
% 3.78/0.99  --instantiation_flag                    true
% 3.78/0.99  --inst_sos_flag                         true
% 3.78/0.99  --inst_sos_phase                        true
% 3.78/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.78/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.78/0.99  --inst_lit_sel_side                     none
% 3.78/0.99  --inst_solver_per_active                1400
% 3.78/0.99  --inst_solver_calls_frac                1.
% 3.78/0.99  --inst_passive_queue_type               priority_queues
% 3.78/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.78/0.99  --inst_passive_queues_freq              [25;2]
% 3.78/0.99  --inst_dismatching                      true
% 3.78/0.99  --inst_eager_unprocessed_to_passive     true
% 3.78/0.99  --inst_prop_sim_given                   true
% 3.78/0.99  --inst_prop_sim_new                     false
% 3.78/0.99  --inst_subs_new                         false
% 3.78/0.99  --inst_eq_res_simp                      false
% 3.78/0.99  --inst_subs_given                       false
% 3.78/0.99  --inst_orphan_elimination               true
% 3.78/0.99  --inst_learning_loop_flag               true
% 3.78/0.99  --inst_learning_start                   3000
% 3.78/0.99  --inst_learning_factor                  2
% 3.78/0.99  --inst_start_prop_sim_after_learn       3
% 3.78/0.99  --inst_sel_renew                        solver
% 3.78/0.99  --inst_lit_activity_flag                true
% 3.78/0.99  --inst_restr_to_given                   false
% 3.78/0.99  --inst_activity_threshold               500
% 3.78/0.99  --inst_out_proof                        true
% 3.78/0.99  
% 3.78/0.99  ------ Resolution Options
% 3.78/0.99  
% 3.78/0.99  --resolution_flag                       false
% 3.78/0.99  --res_lit_sel                           adaptive
% 3.78/0.99  --res_lit_sel_side                      none
% 3.78/0.99  --res_ordering                          kbo
% 3.78/0.99  --res_to_prop_solver                    active
% 3.78/0.99  --res_prop_simpl_new                    false
% 3.78/0.99  --res_prop_simpl_given                  true
% 3.78/0.99  --res_passive_queue_type                priority_queues
% 3.78/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.78/0.99  --res_passive_queues_freq               [15;5]
% 3.78/0.99  --res_forward_subs                      full
% 3.78/0.99  --res_backward_subs                     full
% 3.78/0.99  --res_forward_subs_resolution           true
% 3.78/0.99  --res_backward_subs_resolution          true
% 3.78/0.99  --res_orphan_elimination                true
% 3.78/0.99  --res_time_limit                        2.
% 3.78/0.99  --res_out_proof                         true
% 3.78/0.99  
% 3.78/0.99  ------ Superposition Options
% 3.78/0.99  
% 3.78/0.99  --superposition_flag                    true
% 3.78/0.99  --sup_passive_queue_type                priority_queues
% 3.78/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.78/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.78/0.99  --demod_completeness_check              fast
% 3.78/0.99  --demod_use_ground                      true
% 3.78/0.99  --sup_to_prop_solver                    passive
% 3.78/0.99  --sup_prop_simpl_new                    true
% 3.78/0.99  --sup_prop_simpl_given                  true
% 3.78/0.99  --sup_fun_splitting                     true
% 3.78/0.99  --sup_smt_interval                      50000
% 3.78/0.99  
% 3.78/0.99  ------ Superposition Simplification Setup
% 3.78/0.99  
% 3.78/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.78/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.78/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.78/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.78/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.78/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.78/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.78/0.99  --sup_immed_triv                        [TrivRules]
% 3.78/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.78/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.78/0.99  --sup_immed_bw_main                     []
% 3.78/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.78/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.78/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.78/0.99  --sup_input_bw                          []
% 3.78/0.99  
% 3.78/0.99  ------ Combination Options
% 3.78/0.99  
% 3.78/0.99  --comb_res_mult                         3
% 3.78/0.99  --comb_sup_mult                         2
% 3.78/0.99  --comb_inst_mult                        10
% 3.78/0.99  
% 3.78/0.99  ------ Debug Options
% 3.78/0.99  
% 3.78/0.99  --dbg_backtrace                         false
% 3.78/0.99  --dbg_dump_prop_clauses                 false
% 3.78/0.99  --dbg_dump_prop_clauses_file            -
% 3.78/0.99  --dbg_out_stat                          false
% 3.78/0.99  
% 3.78/0.99  
% 3.78/0.99  
% 3.78/0.99  
% 3.78/0.99  ------ Proving...
% 3.78/0.99  
% 3.78/0.99  
% 3.78/0.99  % SZS status Theorem for theBenchmark.p
% 3.78/0.99  
% 3.78/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.78/0.99  
% 3.78/0.99  fof(f13,conjecture,(
% 3.78/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 3.78/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f14,negated_conjecture,(
% 3.78/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 3.78/0.99    inference(negated_conjecture,[],[f13])).
% 3.78/0.99  
% 3.78/0.99  fof(f15,plain,(
% 3.78/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 3.78/0.99    inference(pure_predicate_removal,[],[f14])).
% 3.78/0.99  
% 3.78/0.99  fof(f31,plain,(
% 3.78/0.99    ? [X0,X1,X2] : (? [X3] : ((k2_relset_1(X0,X1,X2) != X1 & r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 3.78/0.99    inference(ennf_transformation,[],[f15])).
% 3.78/0.99  
% 3.78/0.99  fof(f32,plain,(
% 3.78/0.99    ? [X0,X1,X2] : (? [X3] : (k2_relset_1(X0,X1,X2) != X1 & r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 3.78/0.99    inference(flattening,[],[f31])).
% 3.78/0.99  
% 3.78/0.99  fof(f38,plain,(
% 3.78/0.99    ( ! [X2,X0,X1] : (? [X3] : (k2_relset_1(X0,X1,X2) != X1 & r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) => (k2_relset_1(X0,X1,X2) != X1 & r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,sK3,X2),k6_partfun1(X1)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(sK3))) )),
% 3.78/0.99    introduced(choice_axiom,[])).
% 3.78/0.99  
% 3.78/0.99  fof(f37,plain,(
% 3.78/0.99    ? [X0,X1,X2] : (? [X3] : (k2_relset_1(X0,X1,X2) != X1 & r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (? [X3] : (k2_relset_1(sK0,sK1,sK2) != sK1 & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK0,sK0,sK1,X3,sK2),k6_partfun1(sK1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2))),
% 3.78/0.99    introduced(choice_axiom,[])).
% 3.78/0.99  
% 3.78/0.99  fof(f39,plain,(
% 3.78/0.99    (k2_relset_1(sK0,sK1,sK2) != sK1 & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k6_partfun1(sK1)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2)),
% 3.78/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f32,f38,f37])).
% 3.78/0.99  
% 3.78/0.99  fof(f59,plain,(
% 3.78/0.99    v1_funct_1(sK2)),
% 3.78/0.99    inference(cnf_transformation,[],[f39])).
% 3.78/0.99  
% 3.78/0.99  fof(f62,plain,(
% 3.78/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 3.78/0.99    inference(cnf_transformation,[],[f39])).
% 3.78/0.99  
% 3.78/0.99  fof(f12,axiom,(
% 3.78/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 3.78/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f16,plain,(
% 3.78/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_1(X0)))),
% 3.78/0.99    inference(pure_predicate_removal,[],[f12])).
% 3.78/0.99  
% 3.78/0.99  fof(f29,plain,(
% 3.78/0.99    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.78/0.99    inference(ennf_transformation,[],[f16])).
% 3.78/0.99  
% 3.78/0.99  fof(f30,plain,(
% 3.78/0.99    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.78/0.99    inference(flattening,[],[f29])).
% 3.78/0.99  
% 3.78/0.99  fof(f58,plain,(
% 3.78/0.99    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.78/0.99    inference(cnf_transformation,[],[f30])).
% 3.78/0.99  
% 3.78/0.99  fof(f10,axiom,(
% 3.78/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 3.78/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f27,plain,(
% 3.78/0.99    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.78/0.99    inference(ennf_transformation,[],[f10])).
% 3.78/0.99  
% 3.78/0.99  fof(f28,plain,(
% 3.78/0.99    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.78/0.99    inference(flattening,[],[f27])).
% 3.78/0.99  
% 3.78/0.99  fof(f55,plain,(
% 3.78/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.78/0.99    inference(cnf_transformation,[],[f28])).
% 3.78/0.99  
% 3.78/0.99  fof(f61,plain,(
% 3.78/0.99    v1_funct_1(sK3)),
% 3.78/0.99    inference(cnf_transformation,[],[f39])).
% 3.78/0.99  
% 3.78/0.99  fof(f60,plain,(
% 3.78/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.78/0.99    inference(cnf_transformation,[],[f39])).
% 3.78/0.99  
% 3.78/0.99  fof(f7,axiom,(
% 3.78/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.78/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f23,plain,(
% 3.78/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.78/0.99    inference(ennf_transformation,[],[f7])).
% 3.78/0.99  
% 3.78/0.99  fof(f24,plain,(
% 3.78/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.78/0.99    inference(flattening,[],[f23])).
% 3.78/0.99  
% 3.78/0.99  fof(f36,plain,(
% 3.78/0.99    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.78/0.99    inference(nnf_transformation,[],[f24])).
% 3.78/0.99  
% 3.78/0.99  fof(f50,plain,(
% 3.78/0.99    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.78/0.99    inference(cnf_transformation,[],[f36])).
% 3.78/0.99  
% 3.78/0.99  fof(f63,plain,(
% 3.78/0.99    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k6_partfun1(sK1))),
% 3.78/0.99    inference(cnf_transformation,[],[f39])).
% 3.78/0.99  
% 3.78/0.99  fof(f9,axiom,(
% 3.78/0.99    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 3.78/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f17,plain,(
% 3.78/0.99    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.78/0.99    inference(pure_predicate_removal,[],[f9])).
% 3.78/0.99  
% 3.78/0.99  fof(f54,plain,(
% 3.78/0.99    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.78/0.99    inference(cnf_transformation,[],[f17])).
% 3.78/0.99  
% 3.78/0.99  fof(f8,axiom,(
% 3.78/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 3.78/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f25,plain,(
% 3.78/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.78/0.99    inference(ennf_transformation,[],[f8])).
% 3.78/0.99  
% 3.78/0.99  fof(f26,plain,(
% 3.78/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.78/0.99    inference(flattening,[],[f25])).
% 3.78/0.99  
% 3.78/0.99  fof(f53,plain,(
% 3.78/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.78/0.99    inference(cnf_transformation,[],[f26])).
% 3.78/0.99  
% 3.78/0.99  fof(f4,axiom,(
% 3.78/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.78/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f20,plain,(
% 3.78/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.78/0.99    inference(ennf_transformation,[],[f4])).
% 3.78/0.99  
% 3.78/0.99  fof(f47,plain,(
% 3.78/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.78/0.99    inference(cnf_transformation,[],[f20])).
% 3.78/0.99  
% 3.78/0.99  fof(f2,axiom,(
% 3.78/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.78/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f19,plain,(
% 3.78/0.99    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.78/0.99    inference(ennf_transformation,[],[f2])).
% 3.78/0.99  
% 3.78/0.99  fof(f35,plain,(
% 3.78/0.99    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.78/0.99    inference(nnf_transformation,[],[f19])).
% 3.78/0.99  
% 3.78/0.99  fof(f43,plain,(
% 3.78/0.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.78/0.99    inference(cnf_transformation,[],[f35])).
% 3.78/0.99  
% 3.78/0.99  fof(f5,axiom,(
% 3.78/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.78/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f18,plain,(
% 3.78/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.78/0.99    inference(pure_predicate_removal,[],[f5])).
% 3.78/0.99  
% 3.78/0.99  fof(f21,plain,(
% 3.78/0.99    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.78/0.99    inference(ennf_transformation,[],[f18])).
% 3.78/0.99  
% 3.78/0.99  fof(f48,plain,(
% 3.78/0.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.78/0.99    inference(cnf_transformation,[],[f21])).
% 3.78/0.99  
% 3.78/0.99  fof(f3,axiom,(
% 3.78/0.99    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.78/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f46,plain,(
% 3.78/0.99    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 3.78/0.99    inference(cnf_transformation,[],[f3])).
% 3.78/0.99  
% 3.78/0.99  fof(f11,axiom,(
% 3.78/0.99    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.78/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f56,plain,(
% 3.78/0.99    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.78/0.99    inference(cnf_transformation,[],[f11])).
% 3.78/0.99  
% 3.78/0.99  fof(f65,plain,(
% 3.78/0.99    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 3.78/0.99    inference(definition_unfolding,[],[f46,f56])).
% 3.78/0.99  
% 3.78/0.99  fof(f6,axiom,(
% 3.78/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.78/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f22,plain,(
% 3.78/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.78/0.99    inference(ennf_transformation,[],[f6])).
% 3.78/0.99  
% 3.78/0.99  fof(f49,plain,(
% 3.78/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.78/0.99    inference(cnf_transformation,[],[f22])).
% 3.78/0.99  
% 3.78/0.99  fof(f1,axiom,(
% 3.78/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.78/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f33,plain,(
% 3.78/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.78/0.99    inference(nnf_transformation,[],[f1])).
% 3.78/0.99  
% 3.78/0.99  fof(f34,plain,(
% 3.78/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.78/0.99    inference(flattening,[],[f33])).
% 3.78/0.99  
% 3.78/0.99  fof(f42,plain,(
% 3.78/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.78/0.99    inference(cnf_transformation,[],[f34])).
% 3.78/0.99  
% 3.78/0.99  fof(f64,plain,(
% 3.78/0.99    k2_relset_1(sK0,sK1,sK2) != sK1),
% 3.78/0.99    inference(cnf_transformation,[],[f39])).
% 3.78/0.99  
% 3.78/0.99  cnf(c_23,negated_conjecture,
% 3.78/0.99      ( v1_funct_1(sK2) ),
% 3.78/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_682,plain,
% 3.78/0.99      ( v1_funct_1(sK2) = iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_20,negated_conjecture,
% 3.78/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 3.78/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_685,plain,
% 3.78/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_16,plain,
% 3.78/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 3.78/0.99      | ~ v1_funct_1(X0)
% 3.78/0.99      | ~ v1_relat_1(X0) ),
% 3.78/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_686,plain,
% 3.78/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 3.78/0.99      | v1_funct_1(X0) != iProver_top
% 3.78/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_15,plain,
% 3.78/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.78/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.78/0.99      | ~ v1_funct_1(X0)
% 3.78/0.99      | ~ v1_funct_1(X3)
% 3.78/0.99      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.78/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_687,plain,
% 3.78/0.99      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 3.78/0.99      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 3.78/0.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.78/0.99      | v1_funct_1(X5) != iProver_top
% 3.78/0.99      | v1_funct_1(X4) != iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1602,plain,
% 3.78/0.99      ( k1_partfun1(X0,X1,k1_relat_1(X2),k2_relat_1(X2),X3,X2) = k5_relat_1(X3,X2)
% 3.78/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.78/0.99      | v1_funct_1(X2) != iProver_top
% 3.78/0.99      | v1_funct_1(X3) != iProver_top
% 3.78/0.99      | v1_relat_1(X2) != iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_686,c_687]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_4423,plain,
% 3.78/0.99      ( k1_partfun1(sK1,sK0,k1_relat_1(X0),k2_relat_1(X0),sK3,X0) = k5_relat_1(sK3,X0)
% 3.78/0.99      | v1_funct_1(X0) != iProver_top
% 3.78/0.99      | v1_funct_1(sK3) != iProver_top
% 3.78/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_685,c_1602]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_21,negated_conjecture,
% 3.78/0.99      ( v1_funct_1(sK3) ),
% 3.78/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_26,plain,
% 3.78/0.99      ( v1_funct_1(sK3) = iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_4780,plain,
% 3.78/0.99      ( v1_funct_1(X0) != iProver_top
% 3.78/0.99      | k1_partfun1(sK1,sK0,k1_relat_1(X0),k2_relat_1(X0),sK3,X0) = k5_relat_1(sK3,X0)
% 3.78/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.78/0.99      inference(global_propositional_subsumption,
% 3.78/0.99                [status(thm)],
% 3.78/0.99                [c_4423,c_26]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_4781,plain,
% 3.78/0.99      ( k1_partfun1(sK1,sK0,k1_relat_1(X0),k2_relat_1(X0),sK3,X0) = k5_relat_1(sK3,X0)
% 3.78/0.99      | v1_funct_1(X0) != iProver_top
% 3.78/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.78/0.99      inference(renaming,[status(thm)],[c_4780]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_4788,plain,
% 3.78/0.99      ( k1_partfun1(sK1,sK0,k1_relat_1(sK2),k2_relat_1(sK2),sK3,sK2) = k5_relat_1(sK3,sK2)
% 3.78/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_682,c_4781]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_22,negated_conjecture,
% 3.78/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.78/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_683,plain,
% 3.78/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1604,plain,
% 3.78/0.99      ( k1_partfun1(X0,X1,sK0,sK1,X2,sK2) = k5_relat_1(X2,sK2)
% 3.78/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.78/0.99      | v1_funct_1(X2) != iProver_top
% 3.78/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_683,c_687]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_24,plain,
% 3.78/0.99      ( v1_funct_1(sK2) = iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1807,plain,
% 3.78/0.99      ( v1_funct_1(X2) != iProver_top
% 3.78/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.78/0.99      | k1_partfun1(X0,X1,sK0,sK1,X2,sK2) = k5_relat_1(X2,sK2) ),
% 3.78/0.99      inference(global_propositional_subsumption,
% 3.78/0.99                [status(thm)],
% 3.78/0.99                [c_1604,c_24]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1808,plain,
% 3.78/0.99      ( k1_partfun1(X0,X1,sK0,sK1,X2,sK2) = k5_relat_1(X2,sK2)
% 3.78/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.78/0.99      | v1_funct_1(X2) != iProver_top ),
% 3.78/0.99      inference(renaming,[status(thm)],[c_1807]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1815,plain,
% 3.78/0.99      ( k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) = k5_relat_1(sK3,sK2)
% 3.78/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_685,c_1808]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_11,plain,
% 3.78/0.99      ( ~ r2_relset_1(X0,X1,X2,X3)
% 3.78/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.78/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.78/0.99      | X3 = X2 ),
% 3.78/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_19,negated_conjecture,
% 3.78/0.99      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k6_partfun1(sK1)) ),
% 3.78/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_272,plain,
% 3.78/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.78/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.78/0.99      | X3 = X0
% 3.78/0.99      | k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) != X0
% 3.78/0.99      | k6_partfun1(sK1) != X3
% 3.78/0.99      | sK1 != X2
% 3.78/0.99      | sK1 != X1 ),
% 3.78/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_19]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_273,plain,
% 3.78/0.99      ( ~ m1_subset_1(k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.78/0.99      | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.78/0.99      | k6_partfun1(sK1) = k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) ),
% 3.78/0.99      inference(unflattening,[status(thm)],[c_272]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_14,plain,
% 3.78/0.99      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.78/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_37,plain,
% 3.78/0.99      ( m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_14]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_275,plain,
% 3.78/0.99      ( ~ m1_subset_1(k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.78/0.99      | k6_partfun1(sK1) = k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) ),
% 3.78/0.99      inference(global_propositional_subsumption,
% 3.78/0.99                [status(thm)],
% 3.78/0.99                [c_273,c_37]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_680,plain,
% 3.78/0.99      ( k6_partfun1(sK1) = k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2)
% 3.78/0.99      | m1_subset_1(k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_275]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_12,plain,
% 3.78/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.78/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.78/0.99      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.78/0.99      | ~ v1_funct_1(X0)
% 3.78/0.99      | ~ v1_funct_1(X3) ),
% 3.78/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_719,plain,
% 3.78/0.99      ( m1_subset_1(k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.78/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.78/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.78/0.99      | ~ v1_funct_1(sK3)
% 3.78/0.99      | ~ v1_funct_1(sK2) ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_12]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_853,plain,
% 3.78/0.99      ( k6_partfun1(sK1) = k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) ),
% 3.78/0.99      inference(global_propositional_subsumption,
% 3.78/0.99                [status(thm)],
% 3.78/0.99                [c_680,c_23,c_22,c_21,c_20,c_37,c_273,c_719]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1817,plain,
% 3.78/0.99      ( k5_relat_1(sK3,sK2) = k6_partfun1(sK1)
% 3.78/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.78/0.99      inference(light_normalisation,[status(thm)],[c_1815,c_853]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_2026,plain,
% 3.78/0.99      ( k5_relat_1(sK3,sK2) = k6_partfun1(sK1) ),
% 3.78/0.99      inference(global_propositional_subsumption,
% 3.78/0.99                [status(thm)],
% 3.78/0.99                [c_1817,c_26]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_4794,plain,
% 3.78/0.99      ( k1_partfun1(sK1,sK0,k1_relat_1(sK2),k2_relat_1(sK2),sK3,sK2) = k6_partfun1(sK1)
% 3.78/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.78/0.99      inference(light_normalisation,[status(thm)],[c_4788,c_2026]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_7,plain,
% 3.78/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.78/0.99      | v1_relat_1(X0) ),
% 3.78/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_692,plain,
% 3.78/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.78/0.99      | v1_relat_1(X0) = iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1026,plain,
% 3.78/0.99      ( v1_relat_1(sK2) = iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_683,c_692]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_5099,plain,
% 3.78/0.99      ( k1_partfun1(sK1,sK0,k1_relat_1(sK2),k2_relat_1(sK2),sK3,sK2) = k6_partfun1(sK1) ),
% 3.78/0.99      inference(global_propositional_subsumption,
% 3.78/0.99                [status(thm)],
% 3.78/0.99                [c_4794,c_1026]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_690,plain,
% 3.78/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.78/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 3.78/0.99      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 3.78/0.99      | v1_funct_1(X0) != iProver_top
% 3.78/0.99      | v1_funct_1(X3) != iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_4,plain,
% 3.78/0.99      ( ~ v5_relat_1(X0,X1)
% 3.78/0.99      | r1_tarski(k2_relat_1(X0),X1)
% 3.78/0.99      | ~ v1_relat_1(X0) ),
% 3.78/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_8,plain,
% 3.78/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.78/0.99      | v5_relat_1(X0,X2) ),
% 3.78/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_232,plain,
% 3.78/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.78/0.99      | r1_tarski(k2_relat_1(X3),X4)
% 3.78/0.99      | ~ v1_relat_1(X3)
% 3.78/0.99      | X0 != X3
% 3.78/0.99      | X2 != X4 ),
% 3.78/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_8]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_233,plain,
% 3.78/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.78/0.99      | r1_tarski(k2_relat_1(X0),X2)
% 3.78/0.99      | ~ v1_relat_1(X0) ),
% 3.78/0.99      inference(unflattening,[status(thm)],[c_232]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_237,plain,
% 3.78/0.99      ( r1_tarski(k2_relat_1(X0),X2)
% 3.78/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.78/0.99      inference(global_propositional_subsumption,
% 3.78/0.99                [status(thm)],
% 3.78/0.99                [c_233,c_7]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_238,plain,
% 3.78/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.78/0.99      | r1_tarski(k2_relat_1(X0),X2) ),
% 3.78/0.99      inference(renaming,[status(thm)],[c_237]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_681,plain,
% 3.78/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.78/0.99      | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_238]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_2096,plain,
% 3.78/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.78/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 3.78/0.99      | r1_tarski(k2_relat_1(k1_partfun1(X4,X5,X1,X2,X3,X0)),X2) = iProver_top
% 3.78/0.99      | v1_funct_1(X0) != iProver_top
% 3.78/0.99      | v1_funct_1(X3) != iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_690,c_681]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_10939,plain,
% 3.78/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.78/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 3.78/0.99      | r1_tarski(k2_relat_1(k6_partfun1(sK1)),k2_relat_1(sK2)) = iProver_top
% 3.78/0.99      | v1_funct_1(sK3) != iProver_top
% 3.78/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_5099,c_2096]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_5,plain,
% 3.78/0.99      ( k2_relat_1(k6_partfun1(X0)) = X0 ),
% 3.78/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_10968,plain,
% 3.78/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.78/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 3.78/0.99      | r1_tarski(sK1,k2_relat_1(sK2)) = iProver_top
% 3.78/0.99      | v1_funct_1(sK3) != iProver_top
% 3.78/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.78/0.99      inference(demodulation,[status(thm)],[c_10939,c_5]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_2968,plain,
% 3.78/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
% 3.78/0.99      | ~ v1_funct_1(sK2)
% 3.78/0.99      | ~ v1_relat_1(sK2) ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_16]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_2969,plain,
% 3.78/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top
% 3.78/0.99      | v1_funct_1(sK2) != iProver_top
% 3.78/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_2968]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_789,plain,
% 3.78/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
% 3.78/0.99      | r1_tarski(k2_relat_1(sK2),sK1) ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_238]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_891,plain,
% 3.78/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.78/0.99      | r1_tarski(k2_relat_1(sK2),sK1) ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_789]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_892,plain,
% 3.78/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.78/0.99      | r1_tarski(k2_relat_1(sK2),sK1) = iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_891]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_9,plain,
% 3.78/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.78/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.78/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_823,plain,
% 3.78/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.78/0.99      | k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_0,plain,
% 3.78/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.78/0.99      inference(cnf_transformation,[],[f42]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_741,plain,
% 3.78/0.99      ( ~ r1_tarski(k2_relat_1(sK2),sK1)
% 3.78/0.99      | ~ r1_tarski(sK1,k2_relat_1(sK2))
% 3.78/0.99      | sK1 = k2_relat_1(sK2) ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_742,plain,
% 3.78/0.99      ( sK1 = k2_relat_1(sK2)
% 3.78/0.99      | r1_tarski(k2_relat_1(sK2),sK1) != iProver_top
% 3.78/0.99      | r1_tarski(sK1,k2_relat_1(sK2)) != iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_741]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_413,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_718,plain,
% 3.78/0.99      ( k2_relset_1(sK0,sK1,sK2) != X0
% 3.78/0.99      | k2_relset_1(sK0,sK1,sK2) = sK1
% 3.78/0.99      | sK1 != X0 ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_413]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_733,plain,
% 3.78/0.99      ( k2_relset_1(sK0,sK1,sK2) != k2_relat_1(sK2)
% 3.78/0.99      | k2_relset_1(sK0,sK1,sK2) = sK1
% 3.78/0.99      | sK1 != k2_relat_1(sK2) ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_718]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_18,negated_conjecture,
% 3.78/0.99      ( k2_relset_1(sK0,sK1,sK2) != sK1 ),
% 3.78/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_27,plain,
% 3.78/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_25,plain,
% 3.78/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(contradiction,plain,
% 3.78/0.99      ( $false ),
% 3.78/0.99      inference(minisat,
% 3.78/0.99                [status(thm)],
% 3.78/0.99                [c_10968,c_2969,c_1026,c_892,c_823,c_742,c_733,c_18,c_27,
% 3.78/0.99                 c_26,c_25,c_22,c_24]) ).
% 3.78/0.99  
% 3.78/0.99  
% 3.78/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.78/0.99  
% 3.78/0.99  ------                               Statistics
% 3.78/0.99  
% 3.78/0.99  ------ General
% 3.78/0.99  
% 3.78/0.99  abstr_ref_over_cycles:                  0
% 3.78/0.99  abstr_ref_under_cycles:                 0
% 3.78/0.99  gc_basic_clause_elim:                   0
% 3.78/0.99  forced_gc_time:                         0
% 3.78/0.99  parsing_time:                           0.009
% 3.78/0.99  unif_index_cands_time:                  0.
% 3.78/0.99  unif_index_add_time:                    0.
% 3.78/0.99  orderings_time:                         0.
% 3.78/0.99  out_proof_time:                         0.01
% 3.78/0.99  total_time:                             0.369
% 3.78/0.99  num_of_symbols:                         49
% 3.78/0.99  num_of_terms:                           8792
% 3.78/0.99  
% 3.78/0.99  ------ Preprocessing
% 3.78/0.99  
% 3.78/0.99  num_of_splits:                          0
% 3.78/0.99  num_of_split_atoms:                     0
% 3.78/0.99  num_of_reused_defs:                     0
% 3.78/0.99  num_eq_ax_congr_red:                    14
% 3.78/0.99  num_of_sem_filtered_clauses:            1
% 3.78/0.99  num_of_subtypes:                        0
% 3.78/0.99  monotx_restored_types:                  0
% 3.78/0.99  sat_num_of_epr_types:                   0
% 3.78/0.99  sat_num_of_non_cyclic_types:            0
% 3.78/0.99  sat_guarded_non_collapsed_types:        0
% 3.78/0.99  num_pure_diseq_elim:                    0
% 3.78/0.99  simp_replaced_by:                       0
% 3.78/0.99  res_preprocessed:                       101
% 3.78/0.99  prep_upred:                             0
% 3.78/0.99  prep_unflattend:                        10
% 3.78/0.99  smt_new_axioms:                         0
% 3.78/0.99  pred_elim_cands:                        4
% 3.78/0.99  pred_elim:                              2
% 3.78/0.99  pred_elim_cl:                           4
% 3.78/0.99  pred_elim_cycles:                       5
% 3.78/0.99  merged_defs:                            0
% 3.78/0.99  merged_defs_ncl:                        0
% 3.78/0.99  bin_hyper_res:                          0
% 3.78/0.99  prep_cycles:                            4
% 3.78/0.99  pred_elim_time:                         0.002
% 3.78/0.99  splitting_time:                         0.
% 3.78/0.99  sem_filter_time:                        0.
% 3.78/0.99  monotx_time:                            0.
% 3.78/0.99  subtype_inf_time:                       0.
% 3.78/0.99  
% 3.78/0.99  ------ Problem properties
% 3.78/0.99  
% 3.78/0.99  clauses:                                18
% 3.78/0.99  conjectures:                            5
% 3.78/0.99  epr:                                    4
% 3.78/0.99  horn:                                   18
% 3.78/0.99  ground:                                 6
% 3.78/0.99  unary:                                  9
% 3.78/0.99  binary:                                 4
% 3.78/0.99  lits:                                   38
% 3.78/0.99  lits_eq:                                7
% 3.78/0.99  fd_pure:                                0
% 3.78/0.99  fd_pseudo:                              0
% 3.78/0.99  fd_cond:                                0
% 3.78/0.99  fd_pseudo_cond:                         1
% 3.78/0.99  ac_symbols:                             0
% 3.78/0.99  
% 3.78/0.99  ------ Propositional Solver
% 3.78/0.99  
% 3.78/0.99  prop_solver_calls:                      34
% 3.78/0.99  prop_fast_solver_calls:                 986
% 3.78/0.99  smt_solver_calls:                       0
% 3.78/0.99  smt_fast_solver_calls:                  0
% 3.78/0.99  prop_num_of_clauses:                    4494
% 3.78/0.99  prop_preprocess_simplified:             8489
% 3.78/0.99  prop_fo_subsumed:                       129
% 3.78/0.99  prop_solver_time:                       0.
% 3.78/0.99  smt_solver_time:                        0.
% 3.78/0.99  smt_fast_solver_time:                   0.
% 3.78/0.99  prop_fast_solver_time:                  0.
% 3.78/0.99  prop_unsat_core_time:                   0.
% 3.78/0.99  
% 3.78/0.99  ------ QBF
% 3.78/0.99  
% 3.78/0.99  qbf_q_res:                              0
% 3.78/0.99  qbf_num_tautologies:                    0
% 3.78/0.99  qbf_prep_cycles:                        0
% 3.78/0.99  
% 3.78/0.99  ------ BMC1
% 3.78/0.99  
% 3.78/0.99  bmc1_current_bound:                     -1
% 3.78/0.99  bmc1_last_solved_bound:                 -1
% 3.78/0.99  bmc1_unsat_core_size:                   -1
% 3.78/0.99  bmc1_unsat_core_parents_size:           -1
% 3.78/0.99  bmc1_merge_next_fun:                    0
% 3.78/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.78/0.99  
% 3.78/0.99  ------ Instantiation
% 3.78/0.99  
% 3.78/0.99  inst_num_of_clauses:                    1586
% 3.78/0.99  inst_num_in_passive:                    526
% 3.78/0.99  inst_num_in_active:                     716
% 3.78/0.99  inst_num_in_unprocessed:                344
% 3.78/0.99  inst_num_of_loops:                      760
% 3.78/0.99  inst_num_of_learning_restarts:          0
% 3.78/0.99  inst_num_moves_active_passive:          39
% 3.78/0.99  inst_lit_activity:                      0
% 3.78/0.99  inst_lit_activity_moves:                0
% 3.78/0.99  inst_num_tautologies:                   0
% 3.78/0.99  inst_num_prop_implied:                  0
% 3.78/0.99  inst_num_existing_simplified:           0
% 3.78/0.99  inst_num_eq_res_simplified:             0
% 3.78/0.99  inst_num_child_elim:                    0
% 3.78/0.99  inst_num_of_dismatching_blockings:      870
% 3.78/0.99  inst_num_of_non_proper_insts:           2727
% 3.78/0.99  inst_num_of_duplicates:                 0
% 3.78/0.99  inst_inst_num_from_inst_to_res:         0
% 3.78/0.99  inst_dismatching_checking_time:         0.
% 3.78/0.99  
% 3.78/0.99  ------ Resolution
% 3.78/0.99  
% 3.78/0.99  res_num_of_clauses:                     0
% 3.78/0.99  res_num_in_passive:                     0
% 3.78/0.99  res_num_in_active:                      0
% 3.78/0.99  res_num_of_loops:                       105
% 3.78/0.99  res_forward_subset_subsumed:            361
% 3.78/0.99  res_backward_subset_subsumed:           0
% 3.78/0.99  res_forward_subsumed:                   0
% 3.78/0.99  res_backward_subsumed:                  0
% 3.78/0.99  res_forward_subsumption_resolution:     0
% 3.78/0.99  res_backward_subsumption_resolution:    0
% 3.78/0.99  res_clause_to_clause_subsumption:       1050
% 3.78/0.99  res_orphan_elimination:                 0
% 3.78/0.99  res_tautology_del:                      555
% 3.78/0.99  res_num_eq_res_simplified:              0
% 3.78/0.99  res_num_sel_changes:                    0
% 3.78/0.99  res_moves_from_active_to_pass:          0
% 3.78/0.99  
% 3.78/0.99  ------ Superposition
% 3.78/0.99  
% 3.78/0.99  sup_time_total:                         0.
% 3.78/0.99  sup_time_generating:                    0.
% 3.78/0.99  sup_time_sim_full:                      0.
% 3.78/0.99  sup_time_sim_immed:                     0.
% 3.78/0.99  
% 3.78/0.99  sup_num_of_clauses:                     471
% 3.78/0.99  sup_num_in_active:                      141
% 3.78/0.99  sup_num_in_passive:                     330
% 3.78/0.99  sup_num_of_loops:                       150
% 3.78/0.99  sup_fw_superposition:                   340
% 3.78/0.99  sup_bw_superposition:                   205
% 3.78/0.99  sup_immediate_simplified:               139
% 3.78/0.99  sup_given_eliminated:                   0
% 3.78/0.99  comparisons_done:                       0
% 3.78/0.99  comparisons_avoided:                    0
% 3.78/0.99  
% 3.78/0.99  ------ Simplifications
% 3.78/0.99  
% 3.78/0.99  
% 3.78/0.99  sim_fw_subset_subsumed:                 24
% 3.78/0.99  sim_bw_subset_subsumed:                 14
% 3.78/0.99  sim_fw_subsumed:                        11
% 3.78/0.99  sim_bw_subsumed:                        2
% 3.78/0.99  sim_fw_subsumption_res:                 0
% 3.78/0.99  sim_bw_subsumption_res:                 0
% 3.78/0.99  sim_tautology_del:                      1
% 3.78/0.99  sim_eq_tautology_del:                   28
% 3.78/0.99  sim_eq_res_simp:                        0
% 3.78/0.99  sim_fw_demodulated:                     14
% 3.78/0.99  sim_bw_demodulated:                     1
% 3.78/0.99  sim_light_normalised:                   96
% 3.78/0.99  sim_joinable_taut:                      0
% 3.78/0.99  sim_joinable_simp:                      0
% 3.78/0.99  sim_ac_normalised:                      0
% 3.78/0.99  sim_smt_subsumption:                    0
% 3.78/0.99  
%------------------------------------------------------------------------------
