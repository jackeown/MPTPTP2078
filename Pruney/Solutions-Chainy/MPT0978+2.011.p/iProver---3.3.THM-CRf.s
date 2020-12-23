%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:01:35 EST 2020

% Result     : Theorem 3.19s
% Output     : CNFRefutation 3.19s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 300 expanded)
%              Number of clauses        :   68 (  88 expanded)
%              Number of leaves         :   18 (  70 expanded)
%              Depth                    :   18
%              Number of atoms          :  375 (1407 expanded)
%              Number of equality atoms :  134 ( 306 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
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

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f17,plain,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_1(X3) )
           => ( r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
             => k2_relset_1(X0,X1,X2) = X1 ) ) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f32,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_relset_1(X0,X1,X2) != X1
          & r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

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

fof(f63,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f40])).

fof(f61,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f40])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f30])).

fof(f58,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f60,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f62,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f28])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f64,plain,(
    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f40])).

fof(f12,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f14,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f68,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f57,f59])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f26])).

fof(f54,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f23])).

fof(f52,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f6,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f66,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f50,f59])).

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

fof(f43,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f2,axiom,(
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
    inference(ennf_transformation,[],[f2])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f51,plain,(
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

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f65,plain,(
    k2_relset_1(sK0,sK1,sK2) != sK1 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_698,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_696,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_699,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3826,plain,
    ( k1_partfun1(X0,X1,sK0,sK1,X2,sK2) = k5_relat_1(X2,sK2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_696,c_699])).

cnf(c_23,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_24,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_4733,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK0,sK1,X2,sK2) = k5_relat_1(X2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3826,c_24])).

cnf(c_4734,plain,
    ( k1_partfun1(X0,X1,sK0,sK1,X2,sK2) = k5_relat_1(X2,sK2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_4733])).

cnf(c_4744,plain,
    ( k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) = k5_relat_1(sK3,sK2)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_698,c_4734])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_916,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(X1,X2,X3,X4,X0,sK2) = k5_relat_1(X0,sK2) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1064,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(X0,X1,X2,X3,sK3,sK2) = k5_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_916])).

cnf(c_1531,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(sK1,sK0,X0,X1,sK3,sK2) = k5_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_1064])).

cnf(c_2174,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) = k5_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_1531])).

cnf(c_4775,plain,
    ( k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) = k5_relat_1(sK3,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4744,c_23,c_22,c_21,c_20,c_2174])).

cnf(c_15,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_19,negated_conjecture,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_257,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) != X0
    | k6_partfun1(sK1) != X3
    | sK1 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_19])).

cnf(c_258,plain,
    ( ~ m1_subset_1(k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k6_partfun1(sK1) = k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) ),
    inference(unflattening,[status(thm)],[c_257])).

cnf(c_16,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_33,plain,
    ( m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_260,plain,
    ( ~ m1_subset_1(k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k6_partfun1(sK1) = k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_258,c_33])).

cnf(c_693,plain,
    ( k6_partfun1(sK1) = k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2)
    | m1_subset_1(k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_260])).

cnf(c_4778,plain,
    ( k5_relat_1(sK3,sK2) = k6_partfun1(sK1)
    | m1_subset_1(k5_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4775,c_693])).

cnf(c_25,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_27,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | k4_relset_1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_701,plain,
    ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2367,plain,
    ( k4_relset_1(X0,X1,sK0,sK1,X2,sK2) = k5_relat_1(X2,sK2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_696,c_701])).

cnf(c_2905,plain,
    ( k4_relset_1(sK1,sK0,sK0,sK1,sK3,sK2) = k5_relat_1(sK3,sK2) ),
    inference(superposition,[status(thm)],[c_698,c_2367])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_703,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3186,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2905,c_703])).

cnf(c_4790,plain,
    ( k5_relat_1(sK3,sK2) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4778,c_25,c_27,c_3186])).

cnf(c_7,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_704,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4799,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1(sK1)),k2_relat_1(sK2)) = iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4790,c_704])).

cnf(c_8,plain,
    ( k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_4800,plain,
    ( r1_tarski(sK1,k2_relat_1(sK2)) = iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4799,c_8])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1622,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1)
    | ~ r1_tarski(sK1,k2_relat_1(sK2))
    | sK1 = k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1623,plain,
    ( sK1 = k2_relat_1(sK2)
    | r1_tarski(k2_relat_1(sK2),sK1) != iProver_top
    | r1_tarski(sK1,k2_relat_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1622])).

cnf(c_6,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1518,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1519,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1518])).

cnf(c_1515,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1516,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1515])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_822,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1178,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_822])).

cnf(c_1179,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1178])).

cnf(c_1175,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_822])).

cnf(c_1176,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1175])).

cnf(c_10,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_5,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_236,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_10,c_5])).

cnf(c_694,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_236])).

cnf(c_1125,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_696,c_694])).

cnf(c_388,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_845,plain,
    ( k2_relset_1(sK0,sK1,sK2) != X0
    | k2_relset_1(sK0,sK1,sK2) = sK1
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_388])).

cnf(c_983,plain,
    ( k2_relset_1(sK0,sK1,sK2) != k2_relat_1(sK2)
    | k2_relset_1(sK0,sK1,sK2) = sK1
    | sK1 != k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_845])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_858,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_18,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) != sK1 ),
    inference(cnf_transformation,[],[f65])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4800,c_1623,c_1519,c_1516,c_1179,c_1176,c_1125,c_983,c_858,c_18,c_27,c_25,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:26:00 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.19/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.19/1.00  
% 3.19/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.19/1.00  
% 3.19/1.00  ------  iProver source info
% 3.19/1.00  
% 3.19/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.19/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.19/1.00  git: non_committed_changes: false
% 3.19/1.00  git: last_make_outside_of_git: false
% 3.19/1.00  
% 3.19/1.00  ------ 
% 3.19/1.00  
% 3.19/1.00  ------ Input Options
% 3.19/1.00  
% 3.19/1.00  --out_options                           all
% 3.19/1.00  --tptp_safe_out                         true
% 3.19/1.00  --problem_path                          ""
% 3.19/1.00  --include_path                          ""
% 3.19/1.00  --clausifier                            res/vclausify_rel
% 3.19/1.00  --clausifier_options                    --mode clausify
% 3.19/1.00  --stdin                                 false
% 3.19/1.00  --stats_out                             all
% 3.19/1.00  
% 3.19/1.00  ------ General Options
% 3.19/1.00  
% 3.19/1.00  --fof                                   false
% 3.19/1.00  --time_out_real                         305.
% 3.19/1.00  --time_out_virtual                      -1.
% 3.19/1.00  --symbol_type_check                     false
% 3.19/1.00  --clausify_out                          false
% 3.19/1.00  --sig_cnt_out                           false
% 3.19/1.00  --trig_cnt_out                          false
% 3.19/1.00  --trig_cnt_out_tolerance                1.
% 3.19/1.00  --trig_cnt_out_sk_spl                   false
% 3.19/1.00  --abstr_cl_out                          false
% 3.19/1.00  
% 3.19/1.00  ------ Global Options
% 3.19/1.00  
% 3.19/1.00  --schedule                              default
% 3.19/1.00  --add_important_lit                     false
% 3.19/1.00  --prop_solver_per_cl                    1000
% 3.19/1.00  --min_unsat_core                        false
% 3.19/1.00  --soft_assumptions                      false
% 3.19/1.00  --soft_lemma_size                       3
% 3.19/1.00  --prop_impl_unit_size                   0
% 3.19/1.00  --prop_impl_unit                        []
% 3.19/1.00  --share_sel_clauses                     true
% 3.19/1.00  --reset_solvers                         false
% 3.19/1.00  --bc_imp_inh                            [conj_cone]
% 3.19/1.00  --conj_cone_tolerance                   3.
% 3.19/1.00  --extra_neg_conj                        none
% 3.19/1.00  --large_theory_mode                     true
% 3.19/1.00  --prolific_symb_bound                   200
% 3.19/1.00  --lt_threshold                          2000
% 3.19/1.00  --clause_weak_htbl                      true
% 3.19/1.00  --gc_record_bc_elim                     false
% 3.19/1.00  
% 3.19/1.00  ------ Preprocessing Options
% 3.19/1.00  
% 3.19/1.00  --preprocessing_flag                    true
% 3.19/1.00  --time_out_prep_mult                    0.1
% 3.19/1.00  --splitting_mode                        input
% 3.19/1.00  --splitting_grd                         true
% 3.19/1.00  --splitting_cvd                         false
% 3.19/1.00  --splitting_cvd_svl                     false
% 3.19/1.00  --splitting_nvd                         32
% 3.19/1.00  --sub_typing                            true
% 3.19/1.00  --prep_gs_sim                           true
% 3.19/1.00  --prep_unflatten                        true
% 3.19/1.00  --prep_res_sim                          true
% 3.19/1.00  --prep_upred                            true
% 3.19/1.00  --prep_sem_filter                       exhaustive
% 3.19/1.00  --prep_sem_filter_out                   false
% 3.19/1.00  --pred_elim                             true
% 3.19/1.00  --res_sim_input                         true
% 3.19/1.00  --eq_ax_congr_red                       true
% 3.19/1.00  --pure_diseq_elim                       true
% 3.19/1.00  --brand_transform                       false
% 3.19/1.00  --non_eq_to_eq                          false
% 3.19/1.00  --prep_def_merge                        true
% 3.19/1.00  --prep_def_merge_prop_impl              false
% 3.19/1.00  --prep_def_merge_mbd                    true
% 3.19/1.00  --prep_def_merge_tr_red                 false
% 3.19/1.00  --prep_def_merge_tr_cl                  false
% 3.19/1.00  --smt_preprocessing                     true
% 3.19/1.00  --smt_ac_axioms                         fast
% 3.19/1.00  --preprocessed_out                      false
% 3.19/1.00  --preprocessed_stats                    false
% 3.19/1.00  
% 3.19/1.00  ------ Abstraction refinement Options
% 3.19/1.00  
% 3.19/1.00  --abstr_ref                             []
% 3.19/1.00  --abstr_ref_prep                        false
% 3.19/1.00  --abstr_ref_until_sat                   false
% 3.19/1.00  --abstr_ref_sig_restrict                funpre
% 3.19/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.19/1.00  --abstr_ref_under                       []
% 3.19/1.00  
% 3.19/1.00  ------ SAT Options
% 3.19/1.00  
% 3.19/1.00  --sat_mode                              false
% 3.19/1.00  --sat_fm_restart_options                ""
% 3.19/1.00  --sat_gr_def                            false
% 3.19/1.00  --sat_epr_types                         true
% 3.19/1.00  --sat_non_cyclic_types                  false
% 3.19/1.00  --sat_finite_models                     false
% 3.19/1.00  --sat_fm_lemmas                         false
% 3.19/1.00  --sat_fm_prep                           false
% 3.19/1.00  --sat_fm_uc_incr                        true
% 3.19/1.00  --sat_out_model                         small
% 3.19/1.00  --sat_out_clauses                       false
% 3.19/1.00  
% 3.19/1.00  ------ QBF Options
% 3.19/1.00  
% 3.19/1.00  --qbf_mode                              false
% 3.19/1.00  --qbf_elim_univ                         false
% 3.19/1.00  --qbf_dom_inst                          none
% 3.19/1.00  --qbf_dom_pre_inst                      false
% 3.19/1.00  --qbf_sk_in                             false
% 3.19/1.00  --qbf_pred_elim                         true
% 3.19/1.00  --qbf_split                             512
% 3.19/1.00  
% 3.19/1.00  ------ BMC1 Options
% 3.19/1.00  
% 3.19/1.00  --bmc1_incremental                      false
% 3.19/1.00  --bmc1_axioms                           reachable_all
% 3.19/1.00  --bmc1_min_bound                        0
% 3.19/1.00  --bmc1_max_bound                        -1
% 3.19/1.00  --bmc1_max_bound_default                -1
% 3.19/1.00  --bmc1_symbol_reachability              true
% 3.19/1.00  --bmc1_property_lemmas                  false
% 3.19/1.00  --bmc1_k_induction                      false
% 3.19/1.00  --bmc1_non_equiv_states                 false
% 3.19/1.00  --bmc1_deadlock                         false
% 3.19/1.00  --bmc1_ucm                              false
% 3.19/1.00  --bmc1_add_unsat_core                   none
% 3.19/1.00  --bmc1_unsat_core_children              false
% 3.19/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.19/1.00  --bmc1_out_stat                         full
% 3.19/1.00  --bmc1_ground_init                      false
% 3.19/1.00  --bmc1_pre_inst_next_state              false
% 3.19/1.00  --bmc1_pre_inst_state                   false
% 3.19/1.00  --bmc1_pre_inst_reach_state             false
% 3.19/1.00  --bmc1_out_unsat_core                   false
% 3.19/1.00  --bmc1_aig_witness_out                  false
% 3.19/1.00  --bmc1_verbose                          false
% 3.19/1.00  --bmc1_dump_clauses_tptp                false
% 3.19/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.19/1.00  --bmc1_dump_file                        -
% 3.19/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.19/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.19/1.00  --bmc1_ucm_extend_mode                  1
% 3.19/1.00  --bmc1_ucm_init_mode                    2
% 3.19/1.00  --bmc1_ucm_cone_mode                    none
% 3.19/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.19/1.00  --bmc1_ucm_relax_model                  4
% 3.19/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.19/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.19/1.00  --bmc1_ucm_layered_model                none
% 3.19/1.00  --bmc1_ucm_max_lemma_size               10
% 3.19/1.00  
% 3.19/1.00  ------ AIG Options
% 3.19/1.00  
% 3.19/1.00  --aig_mode                              false
% 3.19/1.00  
% 3.19/1.00  ------ Instantiation Options
% 3.19/1.00  
% 3.19/1.00  --instantiation_flag                    true
% 3.19/1.00  --inst_sos_flag                         false
% 3.19/1.00  --inst_sos_phase                        true
% 3.19/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.19/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.19/1.00  --inst_lit_sel_side                     num_symb
% 3.19/1.00  --inst_solver_per_active                1400
% 3.19/1.00  --inst_solver_calls_frac                1.
% 3.19/1.00  --inst_passive_queue_type               priority_queues
% 3.19/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.19/1.00  --inst_passive_queues_freq              [25;2]
% 3.19/1.00  --inst_dismatching                      true
% 3.19/1.00  --inst_eager_unprocessed_to_passive     true
% 3.19/1.00  --inst_prop_sim_given                   true
% 3.19/1.00  --inst_prop_sim_new                     false
% 3.19/1.00  --inst_subs_new                         false
% 3.19/1.00  --inst_eq_res_simp                      false
% 3.19/1.00  --inst_subs_given                       false
% 3.19/1.00  --inst_orphan_elimination               true
% 3.19/1.00  --inst_learning_loop_flag               true
% 3.19/1.00  --inst_learning_start                   3000
% 3.19/1.00  --inst_learning_factor                  2
% 3.19/1.00  --inst_start_prop_sim_after_learn       3
% 3.19/1.00  --inst_sel_renew                        solver
% 3.19/1.00  --inst_lit_activity_flag                true
% 3.19/1.00  --inst_restr_to_given                   false
% 3.19/1.00  --inst_activity_threshold               500
% 3.19/1.00  --inst_out_proof                        true
% 3.19/1.00  
% 3.19/1.00  ------ Resolution Options
% 3.19/1.00  
% 3.19/1.00  --resolution_flag                       true
% 3.19/1.00  --res_lit_sel                           adaptive
% 3.19/1.00  --res_lit_sel_side                      none
% 3.19/1.00  --res_ordering                          kbo
% 3.19/1.00  --res_to_prop_solver                    active
% 3.19/1.00  --res_prop_simpl_new                    false
% 3.19/1.00  --res_prop_simpl_given                  true
% 3.19/1.00  --res_passive_queue_type                priority_queues
% 3.19/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.19/1.00  --res_passive_queues_freq               [15;5]
% 3.19/1.00  --res_forward_subs                      full
% 3.19/1.00  --res_backward_subs                     full
% 3.19/1.00  --res_forward_subs_resolution           true
% 3.19/1.00  --res_backward_subs_resolution          true
% 3.19/1.00  --res_orphan_elimination                true
% 3.19/1.00  --res_time_limit                        2.
% 3.19/1.00  --res_out_proof                         true
% 3.19/1.00  
% 3.19/1.00  ------ Superposition Options
% 3.19/1.00  
% 3.19/1.00  --superposition_flag                    true
% 3.19/1.00  --sup_passive_queue_type                priority_queues
% 3.19/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.19/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.19/1.00  --demod_completeness_check              fast
% 3.19/1.00  --demod_use_ground                      true
% 3.19/1.00  --sup_to_prop_solver                    passive
% 3.19/1.00  --sup_prop_simpl_new                    true
% 3.19/1.00  --sup_prop_simpl_given                  true
% 3.19/1.00  --sup_fun_splitting                     false
% 3.19/1.00  --sup_smt_interval                      50000
% 3.19/1.00  
% 3.19/1.00  ------ Superposition Simplification Setup
% 3.19/1.00  
% 3.19/1.00  --sup_indices_passive                   []
% 3.19/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.19/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.19/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.19/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.19/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.19/1.00  --sup_full_bw                           [BwDemod]
% 3.19/1.00  --sup_immed_triv                        [TrivRules]
% 3.19/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.19/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.19/1.00  --sup_immed_bw_main                     []
% 3.19/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.19/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.19/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.19/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.19/1.00  
% 3.19/1.00  ------ Combination Options
% 3.19/1.00  
% 3.19/1.00  --comb_res_mult                         3
% 3.19/1.00  --comb_sup_mult                         2
% 3.19/1.00  --comb_inst_mult                        10
% 3.19/1.00  
% 3.19/1.00  ------ Debug Options
% 3.19/1.00  
% 3.19/1.00  --dbg_backtrace                         false
% 3.19/1.00  --dbg_dump_prop_clauses                 false
% 3.19/1.00  --dbg_dump_prop_clauses_file            -
% 3.19/1.00  --dbg_out_stat                          false
% 3.19/1.00  ------ Parsing...
% 3.19/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.19/1.00  
% 3.19/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.19/1.00  
% 3.19/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.19/1.00  
% 3.19/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.19/1.00  ------ Proving...
% 3.19/1.00  ------ Problem Properties 
% 3.19/1.00  
% 3.19/1.00  
% 3.19/1.00  clauses                                 19
% 3.19/1.00  conjectures                             5
% 3.19/1.00  EPR                                     4
% 3.19/1.00  Horn                                    19
% 3.19/1.00  unary                                   10
% 3.19/1.00  binary                                  2
% 3.19/1.00  lits                                    37
% 3.19/1.00  lits eq                                 8
% 3.19/1.00  fd_pure                                 0
% 3.19/1.00  fd_pseudo                               0
% 3.19/1.00  fd_cond                                 0
% 3.19/1.00  fd_pseudo_cond                          1
% 3.19/1.00  AC symbols                              0
% 3.19/1.00  
% 3.19/1.00  ------ Schedule dynamic 5 is on 
% 3.19/1.00  
% 3.19/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.19/1.00  
% 3.19/1.00  
% 3.19/1.00  ------ 
% 3.19/1.00  Current options:
% 3.19/1.00  ------ 
% 3.19/1.00  
% 3.19/1.00  ------ Input Options
% 3.19/1.00  
% 3.19/1.00  --out_options                           all
% 3.19/1.00  --tptp_safe_out                         true
% 3.19/1.00  --problem_path                          ""
% 3.19/1.00  --include_path                          ""
% 3.19/1.00  --clausifier                            res/vclausify_rel
% 3.19/1.00  --clausifier_options                    --mode clausify
% 3.19/1.00  --stdin                                 false
% 3.19/1.00  --stats_out                             all
% 3.19/1.00  
% 3.19/1.00  ------ General Options
% 3.19/1.00  
% 3.19/1.00  --fof                                   false
% 3.19/1.00  --time_out_real                         305.
% 3.19/1.00  --time_out_virtual                      -1.
% 3.19/1.00  --symbol_type_check                     false
% 3.19/1.00  --clausify_out                          false
% 3.19/1.00  --sig_cnt_out                           false
% 3.19/1.00  --trig_cnt_out                          false
% 3.19/1.00  --trig_cnt_out_tolerance                1.
% 3.19/1.00  --trig_cnt_out_sk_spl                   false
% 3.19/1.00  --abstr_cl_out                          false
% 3.19/1.00  
% 3.19/1.00  ------ Global Options
% 3.19/1.00  
% 3.19/1.00  --schedule                              default
% 3.19/1.00  --add_important_lit                     false
% 3.19/1.00  --prop_solver_per_cl                    1000
% 3.19/1.00  --min_unsat_core                        false
% 3.19/1.00  --soft_assumptions                      false
% 3.19/1.00  --soft_lemma_size                       3
% 3.19/1.00  --prop_impl_unit_size                   0
% 3.19/1.00  --prop_impl_unit                        []
% 3.19/1.00  --share_sel_clauses                     true
% 3.19/1.00  --reset_solvers                         false
% 3.19/1.00  --bc_imp_inh                            [conj_cone]
% 3.19/1.00  --conj_cone_tolerance                   3.
% 3.19/1.00  --extra_neg_conj                        none
% 3.19/1.00  --large_theory_mode                     true
% 3.19/1.00  --prolific_symb_bound                   200
% 3.19/1.00  --lt_threshold                          2000
% 3.19/1.00  --clause_weak_htbl                      true
% 3.19/1.00  --gc_record_bc_elim                     false
% 3.19/1.00  
% 3.19/1.00  ------ Preprocessing Options
% 3.19/1.00  
% 3.19/1.00  --preprocessing_flag                    true
% 3.19/1.00  --time_out_prep_mult                    0.1
% 3.19/1.00  --splitting_mode                        input
% 3.19/1.00  --splitting_grd                         true
% 3.19/1.00  --splitting_cvd                         false
% 3.19/1.00  --splitting_cvd_svl                     false
% 3.19/1.00  --splitting_nvd                         32
% 3.19/1.00  --sub_typing                            true
% 3.19/1.00  --prep_gs_sim                           true
% 3.19/1.00  --prep_unflatten                        true
% 3.19/1.00  --prep_res_sim                          true
% 3.19/1.00  --prep_upred                            true
% 3.19/1.00  --prep_sem_filter                       exhaustive
% 3.19/1.00  --prep_sem_filter_out                   false
% 3.19/1.00  --pred_elim                             true
% 3.19/1.00  --res_sim_input                         true
% 3.19/1.00  --eq_ax_congr_red                       true
% 3.19/1.00  --pure_diseq_elim                       true
% 3.19/1.00  --brand_transform                       false
% 3.19/1.00  --non_eq_to_eq                          false
% 3.19/1.00  --prep_def_merge                        true
% 3.19/1.00  --prep_def_merge_prop_impl              false
% 3.19/1.00  --prep_def_merge_mbd                    true
% 3.19/1.00  --prep_def_merge_tr_red                 false
% 3.19/1.00  --prep_def_merge_tr_cl                  false
% 3.19/1.00  --smt_preprocessing                     true
% 3.19/1.00  --smt_ac_axioms                         fast
% 3.19/1.00  --preprocessed_out                      false
% 3.19/1.00  --preprocessed_stats                    false
% 3.19/1.00  
% 3.19/1.00  ------ Abstraction refinement Options
% 3.19/1.00  
% 3.19/1.00  --abstr_ref                             []
% 3.19/1.00  --abstr_ref_prep                        false
% 3.19/1.00  --abstr_ref_until_sat                   false
% 3.19/1.00  --abstr_ref_sig_restrict                funpre
% 3.19/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.19/1.00  --abstr_ref_under                       []
% 3.19/1.00  
% 3.19/1.00  ------ SAT Options
% 3.19/1.00  
% 3.19/1.00  --sat_mode                              false
% 3.19/1.00  --sat_fm_restart_options                ""
% 3.19/1.01  --sat_gr_def                            false
% 3.19/1.01  --sat_epr_types                         true
% 3.19/1.01  --sat_non_cyclic_types                  false
% 3.19/1.01  --sat_finite_models                     false
% 3.19/1.01  --sat_fm_lemmas                         false
% 3.19/1.01  --sat_fm_prep                           false
% 3.19/1.01  --sat_fm_uc_incr                        true
% 3.19/1.01  --sat_out_model                         small
% 3.19/1.01  --sat_out_clauses                       false
% 3.19/1.01  
% 3.19/1.01  ------ QBF Options
% 3.19/1.01  
% 3.19/1.01  --qbf_mode                              false
% 3.19/1.01  --qbf_elim_univ                         false
% 3.19/1.01  --qbf_dom_inst                          none
% 3.19/1.01  --qbf_dom_pre_inst                      false
% 3.19/1.01  --qbf_sk_in                             false
% 3.19/1.01  --qbf_pred_elim                         true
% 3.19/1.01  --qbf_split                             512
% 3.19/1.01  
% 3.19/1.01  ------ BMC1 Options
% 3.19/1.01  
% 3.19/1.01  --bmc1_incremental                      false
% 3.19/1.01  --bmc1_axioms                           reachable_all
% 3.19/1.01  --bmc1_min_bound                        0
% 3.19/1.01  --bmc1_max_bound                        -1
% 3.19/1.01  --bmc1_max_bound_default                -1
% 3.19/1.01  --bmc1_symbol_reachability              true
% 3.19/1.01  --bmc1_property_lemmas                  false
% 3.19/1.01  --bmc1_k_induction                      false
% 3.19/1.01  --bmc1_non_equiv_states                 false
% 3.19/1.01  --bmc1_deadlock                         false
% 3.19/1.01  --bmc1_ucm                              false
% 3.19/1.01  --bmc1_add_unsat_core                   none
% 3.19/1.01  --bmc1_unsat_core_children              false
% 3.19/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.19/1.01  --bmc1_out_stat                         full
% 3.19/1.01  --bmc1_ground_init                      false
% 3.19/1.01  --bmc1_pre_inst_next_state              false
% 3.19/1.01  --bmc1_pre_inst_state                   false
% 3.19/1.01  --bmc1_pre_inst_reach_state             false
% 3.19/1.01  --bmc1_out_unsat_core                   false
% 3.19/1.01  --bmc1_aig_witness_out                  false
% 3.19/1.01  --bmc1_verbose                          false
% 3.19/1.01  --bmc1_dump_clauses_tptp                false
% 3.19/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.19/1.01  --bmc1_dump_file                        -
% 3.19/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.19/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.19/1.01  --bmc1_ucm_extend_mode                  1
% 3.19/1.01  --bmc1_ucm_init_mode                    2
% 3.19/1.01  --bmc1_ucm_cone_mode                    none
% 3.19/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.19/1.01  --bmc1_ucm_relax_model                  4
% 3.19/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.19/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.19/1.01  --bmc1_ucm_layered_model                none
% 3.19/1.01  --bmc1_ucm_max_lemma_size               10
% 3.19/1.01  
% 3.19/1.01  ------ AIG Options
% 3.19/1.01  
% 3.19/1.01  --aig_mode                              false
% 3.19/1.01  
% 3.19/1.01  ------ Instantiation Options
% 3.19/1.01  
% 3.19/1.01  --instantiation_flag                    true
% 3.19/1.01  --inst_sos_flag                         false
% 3.19/1.01  --inst_sos_phase                        true
% 3.19/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.19/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.19/1.01  --inst_lit_sel_side                     none
% 3.19/1.01  --inst_solver_per_active                1400
% 3.19/1.01  --inst_solver_calls_frac                1.
% 3.19/1.01  --inst_passive_queue_type               priority_queues
% 3.19/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.19/1.01  --inst_passive_queues_freq              [25;2]
% 3.19/1.01  --inst_dismatching                      true
% 3.19/1.01  --inst_eager_unprocessed_to_passive     true
% 3.19/1.01  --inst_prop_sim_given                   true
% 3.19/1.01  --inst_prop_sim_new                     false
% 3.19/1.01  --inst_subs_new                         false
% 3.19/1.01  --inst_eq_res_simp                      false
% 3.19/1.01  --inst_subs_given                       false
% 3.19/1.01  --inst_orphan_elimination               true
% 3.19/1.01  --inst_learning_loop_flag               true
% 3.19/1.01  --inst_learning_start                   3000
% 3.19/1.01  --inst_learning_factor                  2
% 3.19/1.01  --inst_start_prop_sim_after_learn       3
% 3.19/1.01  --inst_sel_renew                        solver
% 3.19/1.01  --inst_lit_activity_flag                true
% 3.19/1.01  --inst_restr_to_given                   false
% 3.19/1.01  --inst_activity_threshold               500
% 3.19/1.01  --inst_out_proof                        true
% 3.19/1.01  
% 3.19/1.01  ------ Resolution Options
% 3.19/1.01  
% 3.19/1.01  --resolution_flag                       false
% 3.19/1.01  --res_lit_sel                           adaptive
% 3.19/1.01  --res_lit_sel_side                      none
% 3.19/1.01  --res_ordering                          kbo
% 3.19/1.01  --res_to_prop_solver                    active
% 3.19/1.01  --res_prop_simpl_new                    false
% 3.19/1.01  --res_prop_simpl_given                  true
% 3.19/1.01  --res_passive_queue_type                priority_queues
% 3.19/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.19/1.01  --res_passive_queues_freq               [15;5]
% 3.19/1.01  --res_forward_subs                      full
% 3.19/1.01  --res_backward_subs                     full
% 3.19/1.01  --res_forward_subs_resolution           true
% 3.19/1.01  --res_backward_subs_resolution          true
% 3.19/1.01  --res_orphan_elimination                true
% 3.19/1.01  --res_time_limit                        2.
% 3.19/1.01  --res_out_proof                         true
% 3.19/1.01  
% 3.19/1.01  ------ Superposition Options
% 3.19/1.01  
% 3.19/1.01  --superposition_flag                    true
% 3.19/1.01  --sup_passive_queue_type                priority_queues
% 3.19/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.19/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.19/1.01  --demod_completeness_check              fast
% 3.19/1.01  --demod_use_ground                      true
% 3.19/1.01  --sup_to_prop_solver                    passive
% 3.19/1.01  --sup_prop_simpl_new                    true
% 3.19/1.01  --sup_prop_simpl_given                  true
% 3.19/1.01  --sup_fun_splitting                     false
% 3.19/1.01  --sup_smt_interval                      50000
% 3.19/1.01  
% 3.19/1.01  ------ Superposition Simplification Setup
% 3.19/1.01  
% 3.19/1.01  --sup_indices_passive                   []
% 3.19/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.19/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.19/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.19/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.19/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.19/1.01  --sup_full_bw                           [BwDemod]
% 3.19/1.01  --sup_immed_triv                        [TrivRules]
% 3.19/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.19/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.19/1.01  --sup_immed_bw_main                     []
% 3.19/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.19/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.19/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.19/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.19/1.01  
% 3.19/1.01  ------ Combination Options
% 3.19/1.01  
% 3.19/1.01  --comb_res_mult                         3
% 3.19/1.01  --comb_sup_mult                         2
% 3.19/1.01  --comb_inst_mult                        10
% 3.19/1.01  
% 3.19/1.01  ------ Debug Options
% 3.19/1.01  
% 3.19/1.01  --dbg_backtrace                         false
% 3.19/1.01  --dbg_dump_prop_clauses                 false
% 3.19/1.01  --dbg_dump_prop_clauses_file            -
% 3.19/1.01  --dbg_out_stat                          false
% 3.19/1.01  
% 3.19/1.01  
% 3.19/1.01  
% 3.19/1.01  
% 3.19/1.01  ------ Proving...
% 3.19/1.01  
% 3.19/1.01  
% 3.19/1.01  % SZS status Theorem for theBenchmark.p
% 3.19/1.01  
% 3.19/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.19/1.01  
% 3.19/1.01  fof(f15,conjecture,(
% 3.19/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 3.19/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/1.01  
% 3.19/1.01  fof(f16,negated_conjecture,(
% 3.19/1.01    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 3.19/1.01    inference(negated_conjecture,[],[f15])).
% 3.19/1.01  
% 3.19/1.01  fof(f17,plain,(
% 3.19/1.01    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 3.19/1.01    inference(pure_predicate_removal,[],[f16])).
% 3.19/1.01  
% 3.19/1.01  fof(f32,plain,(
% 3.19/1.01    ? [X0,X1,X2] : (? [X3] : ((k2_relset_1(X0,X1,X2) != X1 & r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 3.19/1.01    inference(ennf_transformation,[],[f17])).
% 3.19/1.01  
% 3.19/1.01  fof(f33,plain,(
% 3.19/1.01    ? [X0,X1,X2] : (? [X3] : (k2_relset_1(X0,X1,X2) != X1 & r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 3.19/1.01    inference(flattening,[],[f32])).
% 3.19/1.01  
% 3.19/1.01  fof(f39,plain,(
% 3.19/1.01    ( ! [X2,X0,X1] : (? [X3] : (k2_relset_1(X0,X1,X2) != X1 & r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) => (k2_relset_1(X0,X1,X2) != X1 & r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,sK3,X2),k6_partfun1(X1)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(sK3))) )),
% 3.19/1.01    introduced(choice_axiom,[])).
% 3.19/1.01  
% 3.19/1.01  fof(f38,plain,(
% 3.19/1.01    ? [X0,X1,X2] : (? [X3] : (k2_relset_1(X0,X1,X2) != X1 & r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (? [X3] : (k2_relset_1(sK0,sK1,sK2) != sK1 & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK0,sK0,sK1,X3,sK2),k6_partfun1(sK1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2))),
% 3.19/1.01    introduced(choice_axiom,[])).
% 3.19/1.01  
% 3.19/1.01  fof(f40,plain,(
% 3.19/1.01    (k2_relset_1(sK0,sK1,sK2) != sK1 & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k6_partfun1(sK1)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2)),
% 3.19/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f33,f39,f38])).
% 3.19/1.01  
% 3.19/1.01  fof(f63,plain,(
% 3.19/1.01    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 3.19/1.01    inference(cnf_transformation,[],[f40])).
% 3.19/1.01  
% 3.19/1.01  fof(f61,plain,(
% 3.19/1.01    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.19/1.01    inference(cnf_transformation,[],[f40])).
% 3.19/1.01  
% 3.19/1.01  fof(f13,axiom,(
% 3.19/1.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.19/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/1.01  
% 3.19/1.01  fof(f30,plain,(
% 3.19/1.01    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.19/1.01    inference(ennf_transformation,[],[f13])).
% 3.19/1.01  
% 3.19/1.01  fof(f31,plain,(
% 3.19/1.01    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.19/1.01    inference(flattening,[],[f30])).
% 3.19/1.01  
% 3.19/1.01  fof(f58,plain,(
% 3.19/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.19/1.01    inference(cnf_transformation,[],[f31])).
% 3.19/1.01  
% 3.19/1.01  fof(f60,plain,(
% 3.19/1.01    v1_funct_1(sK2)),
% 3.19/1.01    inference(cnf_transformation,[],[f40])).
% 3.19/1.01  
% 3.19/1.01  fof(f62,plain,(
% 3.19/1.01    v1_funct_1(sK3)),
% 3.19/1.01    inference(cnf_transformation,[],[f40])).
% 3.19/1.01  
% 3.19/1.01  fof(f11,axiom,(
% 3.19/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.19/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/1.01  
% 3.19/1.01  fof(f28,plain,(
% 3.19/1.01    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.19/1.01    inference(ennf_transformation,[],[f11])).
% 3.19/1.01  
% 3.19/1.01  fof(f29,plain,(
% 3.19/1.01    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.19/1.01    inference(flattening,[],[f28])).
% 3.19/1.01  
% 3.19/1.01  fof(f37,plain,(
% 3.19/1.01    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.19/1.01    inference(nnf_transformation,[],[f29])).
% 3.19/1.01  
% 3.19/1.01  fof(f55,plain,(
% 3.19/1.01    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.19/1.01    inference(cnf_transformation,[],[f37])).
% 3.19/1.01  
% 3.19/1.01  fof(f64,plain,(
% 3.19/1.01    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k6_partfun1(sK1))),
% 3.19/1.01    inference(cnf_transformation,[],[f40])).
% 3.19/1.01  
% 3.19/1.01  fof(f12,axiom,(
% 3.19/1.01    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.19/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/1.01  
% 3.19/1.01  fof(f57,plain,(
% 3.19/1.01    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.19/1.01    inference(cnf_transformation,[],[f12])).
% 3.19/1.01  
% 3.19/1.01  fof(f14,axiom,(
% 3.19/1.01    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.19/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/1.01  
% 3.19/1.01  fof(f59,plain,(
% 3.19/1.01    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.19/1.01    inference(cnf_transformation,[],[f14])).
% 3.19/1.01  
% 3.19/1.01  fof(f68,plain,(
% 3.19/1.01    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.19/1.01    inference(definition_unfolding,[],[f57,f59])).
% 3.19/1.01  
% 3.19/1.01  fof(f10,axiom,(
% 3.19/1.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5))),
% 3.19/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/1.01  
% 3.19/1.01  fof(f26,plain,(
% 3.19/1.01    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.19/1.01    inference(ennf_transformation,[],[f10])).
% 3.19/1.01  
% 3.19/1.01  fof(f27,plain,(
% 3.19/1.01    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.19/1.01    inference(flattening,[],[f26])).
% 3.19/1.01  
% 3.19/1.01  fof(f54,plain,(
% 3.19/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.19/1.01    inference(cnf_transformation,[],[f27])).
% 3.19/1.01  
% 3.19/1.01  fof(f8,axiom,(
% 3.19/1.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))))),
% 3.19/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/1.01  
% 3.19/1.01  fof(f23,plain,(
% 3.19/1.01    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.19/1.01    inference(ennf_transformation,[],[f8])).
% 3.19/1.01  
% 3.19/1.01  fof(f24,plain,(
% 3.19/1.01    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.19/1.01    inference(flattening,[],[f23])).
% 3.19/1.01  
% 3.19/1.01  fof(f52,plain,(
% 3.19/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.19/1.01    inference(cnf_transformation,[],[f24])).
% 3.19/1.01  
% 3.19/1.01  fof(f5,axiom,(
% 3.19/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 3.19/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/1.01  
% 3.19/1.01  fof(f21,plain,(
% 3.19/1.01    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.19/1.01    inference(ennf_transformation,[],[f5])).
% 3.19/1.01  
% 3.19/1.01  fof(f48,plain,(
% 3.19/1.01    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.19/1.01    inference(cnf_transformation,[],[f21])).
% 3.19/1.01  
% 3.19/1.01  fof(f6,axiom,(
% 3.19/1.01    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.19/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/1.01  
% 3.19/1.01  fof(f50,plain,(
% 3.19/1.01    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 3.19/1.01    inference(cnf_transformation,[],[f6])).
% 3.19/1.01  
% 3.19/1.01  fof(f66,plain,(
% 3.19/1.01    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 3.19/1.01    inference(definition_unfolding,[],[f50,f59])).
% 3.19/1.01  
% 3.19/1.01  fof(f1,axiom,(
% 3.19/1.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.19/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/1.01  
% 3.19/1.01  fof(f34,plain,(
% 3.19/1.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.19/1.01    inference(nnf_transformation,[],[f1])).
% 3.19/1.01  
% 3.19/1.01  fof(f35,plain,(
% 3.19/1.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.19/1.01    inference(flattening,[],[f34])).
% 3.19/1.01  
% 3.19/1.01  fof(f43,plain,(
% 3.19/1.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.19/1.01    inference(cnf_transformation,[],[f35])).
% 3.19/1.01  
% 3.19/1.01  fof(f4,axiom,(
% 3.19/1.01    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.19/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/1.01  
% 3.19/1.01  fof(f47,plain,(
% 3.19/1.01    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.19/1.01    inference(cnf_transformation,[],[f4])).
% 3.19/1.01  
% 3.19/1.01  fof(f2,axiom,(
% 3.19/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.19/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/1.01  
% 3.19/1.01  fof(f19,plain,(
% 3.19/1.01    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.19/1.01    inference(ennf_transformation,[],[f2])).
% 3.19/1.01  
% 3.19/1.01  fof(f44,plain,(
% 3.19/1.01    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.19/1.01    inference(cnf_transformation,[],[f19])).
% 3.19/1.01  
% 3.19/1.01  fof(f7,axiom,(
% 3.19/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.19/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/1.01  
% 3.19/1.01  fof(f18,plain,(
% 3.19/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.19/1.01    inference(pure_predicate_removal,[],[f7])).
% 3.19/1.01  
% 3.19/1.01  fof(f22,plain,(
% 3.19/1.01    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.19/1.01    inference(ennf_transformation,[],[f18])).
% 3.19/1.01  
% 3.19/1.01  fof(f51,plain,(
% 3.19/1.01    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.19/1.01    inference(cnf_transformation,[],[f22])).
% 3.19/1.01  
% 3.19/1.01  fof(f3,axiom,(
% 3.19/1.01    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.19/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/1.01  
% 3.19/1.01  fof(f20,plain,(
% 3.19/1.01    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.19/1.01    inference(ennf_transformation,[],[f3])).
% 3.19/1.01  
% 3.19/1.01  fof(f36,plain,(
% 3.19/1.01    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.19/1.01    inference(nnf_transformation,[],[f20])).
% 3.19/1.01  
% 3.19/1.01  fof(f45,plain,(
% 3.19/1.01    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.19/1.01    inference(cnf_transformation,[],[f36])).
% 3.19/1.01  
% 3.19/1.01  fof(f9,axiom,(
% 3.19/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.19/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/1.01  
% 3.19/1.01  fof(f25,plain,(
% 3.19/1.01    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.19/1.01    inference(ennf_transformation,[],[f9])).
% 3.19/1.01  
% 3.19/1.01  fof(f53,plain,(
% 3.19/1.01    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.19/1.01    inference(cnf_transformation,[],[f25])).
% 3.19/1.01  
% 3.19/1.01  fof(f65,plain,(
% 3.19/1.01    k2_relset_1(sK0,sK1,sK2) != sK1),
% 3.19/1.01    inference(cnf_transformation,[],[f40])).
% 3.19/1.01  
% 3.19/1.01  cnf(c_20,negated_conjecture,
% 3.19/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 3.19/1.01      inference(cnf_transformation,[],[f63]) ).
% 3.19/1.01  
% 3.19/1.01  cnf(c_698,plain,
% 3.19/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.19/1.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.19/1.01  
% 3.19/1.01  cnf(c_22,negated_conjecture,
% 3.19/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.19/1.01      inference(cnf_transformation,[],[f61]) ).
% 3.19/1.01  
% 3.19/1.01  cnf(c_696,plain,
% 3.19/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.19/1.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.19/1.01  
% 3.19/1.01  cnf(c_17,plain,
% 3.19/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.19/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.19/1.01      | ~ v1_funct_1(X0)
% 3.19/1.01      | ~ v1_funct_1(X3)
% 3.19/1.01      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.19/1.01      inference(cnf_transformation,[],[f58]) ).
% 3.19/1.01  
% 3.19/1.01  cnf(c_699,plain,
% 3.19/1.01      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 3.19/1.01      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 3.19/1.01      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.19/1.01      | v1_funct_1(X5) != iProver_top
% 3.19/1.01      | v1_funct_1(X4) != iProver_top ),
% 3.19/1.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.19/1.01  
% 3.19/1.01  cnf(c_3826,plain,
% 3.19/1.01      ( k1_partfun1(X0,X1,sK0,sK1,X2,sK2) = k5_relat_1(X2,sK2)
% 3.19/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.19/1.01      | v1_funct_1(X2) != iProver_top
% 3.19/1.01      | v1_funct_1(sK2) != iProver_top ),
% 3.19/1.01      inference(superposition,[status(thm)],[c_696,c_699]) ).
% 3.19/1.01  
% 3.19/1.01  cnf(c_23,negated_conjecture,
% 3.19/1.01      ( v1_funct_1(sK2) ),
% 3.19/1.01      inference(cnf_transformation,[],[f60]) ).
% 3.19/1.01  
% 3.19/1.01  cnf(c_24,plain,
% 3.19/1.01      ( v1_funct_1(sK2) = iProver_top ),
% 3.19/1.01      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.19/1.01  
% 3.19/1.01  cnf(c_4733,plain,
% 3.19/1.01      ( v1_funct_1(X2) != iProver_top
% 3.19/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.19/1.01      | k1_partfun1(X0,X1,sK0,sK1,X2,sK2) = k5_relat_1(X2,sK2) ),
% 3.19/1.01      inference(global_propositional_subsumption,
% 3.19/1.01                [status(thm)],
% 3.19/1.01                [c_3826,c_24]) ).
% 3.19/1.01  
% 3.19/1.01  cnf(c_4734,plain,
% 3.19/1.01      ( k1_partfun1(X0,X1,sK0,sK1,X2,sK2) = k5_relat_1(X2,sK2)
% 3.19/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.19/1.01      | v1_funct_1(X2) != iProver_top ),
% 3.19/1.01      inference(renaming,[status(thm)],[c_4733]) ).
% 3.19/1.01  
% 3.19/1.01  cnf(c_4744,plain,
% 3.19/1.01      ( k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) = k5_relat_1(sK3,sK2)
% 3.19/1.01      | v1_funct_1(sK3) != iProver_top ),
% 3.19/1.01      inference(superposition,[status(thm)],[c_698,c_4734]) ).
% 3.19/1.01  
% 3.19/1.01  cnf(c_21,negated_conjecture,
% 3.19/1.01      ( v1_funct_1(sK3) ),
% 3.19/1.01      inference(cnf_transformation,[],[f62]) ).
% 3.19/1.01  
% 3.19/1.01  cnf(c_916,plain,
% 3.19/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.19/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 3.19/1.01      | ~ v1_funct_1(X0)
% 3.19/1.01      | ~ v1_funct_1(sK2)
% 3.19/1.01      | k1_partfun1(X1,X2,X3,X4,X0,sK2) = k5_relat_1(X0,sK2) ),
% 3.19/1.01      inference(instantiation,[status(thm)],[c_17]) ).
% 3.19/1.01  
% 3.19/1.01  cnf(c_1064,plain,
% 3.19/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.19/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.19/1.01      | ~ v1_funct_1(sK3)
% 3.19/1.01      | ~ v1_funct_1(sK2)
% 3.19/1.01      | k1_partfun1(X0,X1,X2,X3,sK3,sK2) = k5_relat_1(sK3,sK2) ),
% 3.19/1.01      inference(instantiation,[status(thm)],[c_916]) ).
% 3.19/1.01  
% 3.19/1.01  cnf(c_1531,plain,
% 3.19/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.19/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.19/1.01      | ~ v1_funct_1(sK3)
% 3.19/1.01      | ~ v1_funct_1(sK2)
% 3.19/1.01      | k1_partfun1(sK1,sK0,X0,X1,sK3,sK2) = k5_relat_1(sK3,sK2) ),
% 3.19/1.01      inference(instantiation,[status(thm)],[c_1064]) ).
% 3.19/1.01  
% 3.19/1.01  cnf(c_2174,plain,
% 3.19/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.19/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.19/1.01      | ~ v1_funct_1(sK3)
% 3.19/1.01      | ~ v1_funct_1(sK2)
% 3.19/1.01      | k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) = k5_relat_1(sK3,sK2) ),
% 3.19/1.01      inference(instantiation,[status(thm)],[c_1531]) ).
% 3.19/1.01  
% 3.19/1.01  cnf(c_4775,plain,
% 3.19/1.01      ( k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) = k5_relat_1(sK3,sK2) ),
% 3.19/1.01      inference(global_propositional_subsumption,
% 3.19/1.01                [status(thm)],
% 3.19/1.01                [c_4744,c_23,c_22,c_21,c_20,c_2174]) ).
% 3.19/1.01  
% 3.19/1.01  cnf(c_15,plain,
% 3.19/1.01      ( ~ r2_relset_1(X0,X1,X2,X3)
% 3.19/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.19/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.19/1.01      | X3 = X2 ),
% 3.19/1.01      inference(cnf_transformation,[],[f55]) ).
% 3.19/1.01  
% 3.19/1.01  cnf(c_19,negated_conjecture,
% 3.19/1.01      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k6_partfun1(sK1)) ),
% 3.19/1.01      inference(cnf_transformation,[],[f64]) ).
% 3.19/1.01  
% 3.19/1.01  cnf(c_257,plain,
% 3.19/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.19/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.19/1.01      | X3 = X0
% 3.19/1.01      | k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) != X0
% 3.19/1.01      | k6_partfun1(sK1) != X3
% 3.19/1.01      | sK1 != X2
% 3.19/1.01      | sK1 != X1 ),
% 3.19/1.01      inference(resolution_lifted,[status(thm)],[c_15,c_19]) ).
% 3.19/1.01  
% 3.19/1.01  cnf(c_258,plain,
% 3.19/1.01      ( ~ m1_subset_1(k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.19/1.01      | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.19/1.01      | k6_partfun1(sK1) = k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) ),
% 3.19/1.01      inference(unflattening,[status(thm)],[c_257]) ).
% 3.19/1.01  
% 3.19/1.01  cnf(c_16,plain,
% 3.19/1.01      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.19/1.01      inference(cnf_transformation,[],[f68]) ).
% 3.19/1.01  
% 3.19/1.01  cnf(c_33,plain,
% 3.19/1.01      ( m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 3.19/1.01      inference(instantiation,[status(thm)],[c_16]) ).
% 3.19/1.01  
% 3.19/1.01  cnf(c_260,plain,
% 3.19/1.01      ( ~ m1_subset_1(k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.19/1.01      | k6_partfun1(sK1) = k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) ),
% 3.19/1.01      inference(global_propositional_subsumption,
% 3.19/1.01                [status(thm)],
% 3.19/1.01                [c_258,c_33]) ).
% 3.19/1.01  
% 3.19/1.01  cnf(c_693,plain,
% 3.19/1.01      ( k6_partfun1(sK1) = k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2)
% 3.19/1.01      | m1_subset_1(k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
% 3.19/1.01      inference(predicate_to_equality,[status(thm)],[c_260]) ).
% 3.19/1.01  
% 3.19/1.01  cnf(c_4778,plain,
% 3.19/1.01      ( k5_relat_1(sK3,sK2) = k6_partfun1(sK1)
% 3.19/1.01      | m1_subset_1(k5_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
% 3.19/1.01      inference(demodulation,[status(thm)],[c_4775,c_693]) ).
% 3.19/1.01  
% 3.19/1.01  cnf(c_25,plain,
% 3.19/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.19/1.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.19/1.01  
% 3.19/1.01  cnf(c_27,plain,
% 3.19/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.19/1.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.19/1.01  
% 3.19/1.01  cnf(c_13,plain,
% 3.19/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.19/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.19/1.01      | k4_relset_1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.19/1.01      inference(cnf_transformation,[],[f54]) ).
% 3.19/1.01  
% 3.19/1.01  cnf(c_701,plain,
% 3.19/1.01      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 3.19/1.01      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 3.19/1.01      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.19/1.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.19/1.01  
% 3.19/1.01  cnf(c_2367,plain,
% 3.19/1.01      ( k4_relset_1(X0,X1,sK0,sK1,X2,sK2) = k5_relat_1(X2,sK2)
% 3.19/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.19/1.01      inference(superposition,[status(thm)],[c_696,c_701]) ).
% 3.19/1.01  
% 3.19/1.01  cnf(c_2905,plain,
% 3.19/1.01      ( k4_relset_1(sK1,sK0,sK0,sK1,sK3,sK2) = k5_relat_1(sK3,sK2) ),
% 3.19/1.01      inference(superposition,[status(thm)],[c_698,c_2367]) ).
% 3.19/1.01  
% 3.19/1.01  cnf(c_11,plain,
% 3.19/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.19/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.19/1.01      | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) ),
% 3.19/1.01      inference(cnf_transformation,[],[f52]) ).
% 3.19/1.01  
% 3.19/1.01  cnf(c_703,plain,
% 3.19/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.19/1.01      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 3.19/1.01      | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top ),
% 3.19/1.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.19/1.01  
% 3.19/1.01  cnf(c_3186,plain,
% 3.19/1.01      ( m1_subset_1(k5_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
% 3.19/1.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.19/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 3.19/1.01      inference(superposition,[status(thm)],[c_2905,c_703]) ).
% 3.19/1.01  
% 3.19/1.01  cnf(c_4790,plain,
% 3.19/1.01      ( k5_relat_1(sK3,sK2) = k6_partfun1(sK1) ),
% 3.19/1.01      inference(global_propositional_subsumption,
% 3.19/1.01                [status(thm)],
% 3.19/1.01                [c_4778,c_25,c_27,c_3186]) ).
% 3.19/1.01  
% 3.19/1.01  cnf(c_7,plain,
% 3.19/1.01      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
% 3.19/1.01      | ~ v1_relat_1(X0)
% 3.19/1.01      | ~ v1_relat_1(X1) ),
% 3.19/1.01      inference(cnf_transformation,[],[f48]) ).
% 3.19/1.01  
% 3.19/1.01  cnf(c_704,plain,
% 3.19/1.01      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
% 3.19/1.01      | v1_relat_1(X0) != iProver_top
% 3.19/1.01      | v1_relat_1(X1) != iProver_top ),
% 3.19/1.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.19/1.01  
% 3.19/1.01  cnf(c_4799,plain,
% 3.19/1.01      ( r1_tarski(k2_relat_1(k6_partfun1(sK1)),k2_relat_1(sK2)) = iProver_top
% 3.19/1.01      | v1_relat_1(sK3) != iProver_top
% 3.19/1.01      | v1_relat_1(sK2) != iProver_top ),
% 3.19/1.01      inference(superposition,[status(thm)],[c_4790,c_704]) ).
% 3.19/1.01  
% 3.19/1.01  cnf(c_8,plain,
% 3.19/1.01      ( k2_relat_1(k6_partfun1(X0)) = X0 ),
% 3.19/1.01      inference(cnf_transformation,[],[f66]) ).
% 3.19/1.01  
% 3.19/1.01  cnf(c_4800,plain,
% 3.19/1.01      ( r1_tarski(sK1,k2_relat_1(sK2)) = iProver_top
% 3.19/1.01      | v1_relat_1(sK3) != iProver_top
% 3.19/1.01      | v1_relat_1(sK2) != iProver_top ),
% 3.19/1.01      inference(demodulation,[status(thm)],[c_4799,c_8]) ).
% 3.19/1.01  
% 3.19/1.01  cnf(c_0,plain,
% 3.19/1.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.19/1.01      inference(cnf_transformation,[],[f43]) ).
% 3.19/1.01  
% 3.19/1.01  cnf(c_1622,plain,
% 3.19/1.01      ( ~ r1_tarski(k2_relat_1(sK2),sK1)
% 3.19/1.01      | ~ r1_tarski(sK1,k2_relat_1(sK2))
% 3.19/1.01      | sK1 = k2_relat_1(sK2) ),
% 3.19/1.01      inference(instantiation,[status(thm)],[c_0]) ).
% 3.19/1.01  
% 3.19/1.01  cnf(c_1623,plain,
% 3.19/1.01      ( sK1 = k2_relat_1(sK2)
% 3.19/1.01      | r1_tarski(k2_relat_1(sK2),sK1) != iProver_top
% 3.19/1.01      | r1_tarski(sK1,k2_relat_1(sK2)) != iProver_top ),
% 3.19/1.01      inference(predicate_to_equality,[status(thm)],[c_1622]) ).
% 3.19/1.01  
% 3.19/1.01  cnf(c_6,plain,
% 3.19/1.01      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.19/1.01      inference(cnf_transformation,[],[f47]) ).
% 3.19/1.01  
% 3.19/1.01  cnf(c_1518,plain,
% 3.19/1.01      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 3.19/1.01      inference(instantiation,[status(thm)],[c_6]) ).
% 3.19/1.01  
% 3.19/1.01  cnf(c_1519,plain,
% 3.19/1.01      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 3.19/1.01      inference(predicate_to_equality,[status(thm)],[c_1518]) ).
% 3.19/1.01  
% 3.19/1.01  cnf(c_1515,plain,
% 3.19/1.01      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
% 3.19/1.01      inference(instantiation,[status(thm)],[c_6]) ).
% 3.19/1.01  
% 3.19/1.01  cnf(c_1516,plain,
% 3.19/1.01      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
% 3.19/1.01      inference(predicate_to_equality,[status(thm)],[c_1515]) ).
% 3.19/1.01  
% 3.19/1.01  cnf(c_3,plain,
% 3.19/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.19/1.01      | ~ v1_relat_1(X1)
% 3.19/1.01      | v1_relat_1(X0) ),
% 3.19/1.01      inference(cnf_transformation,[],[f44]) ).
% 3.19/1.01  
% 3.19/1.01  cnf(c_822,plain,
% 3.19/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.19/1.01      | v1_relat_1(X0)
% 3.19/1.01      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 3.19/1.01      inference(instantiation,[status(thm)],[c_3]) ).
% 3.19/1.01  
% 3.19/1.01  cnf(c_1178,plain,
% 3.19/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.19/1.01      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
% 3.19/1.01      | v1_relat_1(sK2) ),
% 3.19/1.01      inference(instantiation,[status(thm)],[c_822]) ).
% 3.19/1.01  
% 3.19/1.01  cnf(c_1179,plain,
% 3.19/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.19/1.01      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 3.19/1.01      | v1_relat_1(sK2) = iProver_top ),
% 3.19/1.01      inference(predicate_to_equality,[status(thm)],[c_1178]) ).
% 3.19/1.01  
% 3.19/1.01  cnf(c_1175,plain,
% 3.19/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.19/1.01      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
% 3.19/1.01      | v1_relat_1(sK3) ),
% 3.19/1.01      inference(instantiation,[status(thm)],[c_822]) ).
% 3.19/1.01  
% 3.19/1.01  cnf(c_1176,plain,
% 3.19/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.19/1.01      | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 3.19/1.01      | v1_relat_1(sK3) = iProver_top ),
% 3.19/1.01      inference(predicate_to_equality,[status(thm)],[c_1175]) ).
% 3.19/1.01  
% 3.19/1.01  cnf(c_10,plain,
% 3.19/1.01      ( v5_relat_1(X0,X1)
% 3.19/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.19/1.01      inference(cnf_transformation,[],[f51]) ).
% 3.19/1.01  
% 3.19/1.01  cnf(c_5,plain,
% 3.19/1.01      ( ~ v5_relat_1(X0,X1)
% 3.19/1.01      | r1_tarski(k2_relat_1(X0),X1)
% 3.19/1.01      | ~ v1_relat_1(X0) ),
% 3.19/1.01      inference(cnf_transformation,[],[f45]) ).
% 3.19/1.01  
% 3.19/1.01  cnf(c_236,plain,
% 3.19/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.19/1.01      | r1_tarski(k2_relat_1(X0),X2)
% 3.19/1.01      | ~ v1_relat_1(X0) ),
% 3.19/1.01      inference(resolution,[status(thm)],[c_10,c_5]) ).
% 3.19/1.01  
% 3.19/1.01  cnf(c_694,plain,
% 3.19/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.19/1.01      | r1_tarski(k2_relat_1(X0),X2) = iProver_top
% 3.19/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.19/1.01      inference(predicate_to_equality,[status(thm)],[c_236]) ).
% 3.19/1.01  
% 3.19/1.01  cnf(c_1125,plain,
% 3.19/1.01      ( r1_tarski(k2_relat_1(sK2),sK1) = iProver_top
% 3.19/1.01      | v1_relat_1(sK2) != iProver_top ),
% 3.19/1.01      inference(superposition,[status(thm)],[c_696,c_694]) ).
% 3.19/1.01  
% 3.19/1.01  cnf(c_388,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.19/1.01  
% 3.19/1.01  cnf(c_845,plain,
% 3.19/1.01      ( k2_relset_1(sK0,sK1,sK2) != X0
% 3.19/1.01      | k2_relset_1(sK0,sK1,sK2) = sK1
% 3.19/1.01      | sK1 != X0 ),
% 3.19/1.01      inference(instantiation,[status(thm)],[c_388]) ).
% 3.19/1.01  
% 3.19/1.01  cnf(c_983,plain,
% 3.19/1.01      ( k2_relset_1(sK0,sK1,sK2) != k2_relat_1(sK2)
% 3.19/1.01      | k2_relset_1(sK0,sK1,sK2) = sK1
% 3.19/1.01      | sK1 != k2_relat_1(sK2) ),
% 3.19/1.01      inference(instantiation,[status(thm)],[c_845]) ).
% 3.19/1.01  
% 3.19/1.01  cnf(c_12,plain,
% 3.19/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.19/1.01      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.19/1.01      inference(cnf_transformation,[],[f53]) ).
% 3.19/1.01  
% 3.19/1.01  cnf(c_858,plain,
% 3.19/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.19/1.01      | k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 3.19/1.01      inference(instantiation,[status(thm)],[c_12]) ).
% 3.19/1.01  
% 3.19/1.01  cnf(c_18,negated_conjecture,
% 3.19/1.01      ( k2_relset_1(sK0,sK1,sK2) != sK1 ),
% 3.19/1.01      inference(cnf_transformation,[],[f65]) ).
% 3.19/1.01  
% 3.19/1.01  cnf(contradiction,plain,
% 3.19/1.01      ( $false ),
% 3.19/1.01      inference(minisat,
% 3.19/1.01                [status(thm)],
% 3.19/1.01                [c_4800,c_1623,c_1519,c_1516,c_1179,c_1176,c_1125,c_983,
% 3.19/1.01                 c_858,c_18,c_27,c_25,c_22]) ).
% 3.19/1.01  
% 3.19/1.01  
% 3.19/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.19/1.01  
% 3.19/1.01  ------                               Statistics
% 3.19/1.01  
% 3.19/1.01  ------ General
% 3.19/1.01  
% 3.19/1.01  abstr_ref_over_cycles:                  0
% 3.19/1.01  abstr_ref_under_cycles:                 0
% 3.19/1.01  gc_basic_clause_elim:                   0
% 3.19/1.01  forced_gc_time:                         0
% 3.19/1.01  parsing_time:                           0.009
% 3.19/1.01  unif_index_cands_time:                  0.
% 3.19/1.01  unif_index_add_time:                    0.
% 3.19/1.01  orderings_time:                         0.
% 3.19/1.01  out_proof_time:                         0.008
% 3.19/1.01  total_time:                             0.18
% 3.19/1.01  num_of_symbols:                         50
% 3.19/1.01  num_of_terms:                           5860
% 3.19/1.01  
% 3.19/1.01  ------ Preprocessing
% 3.19/1.01  
% 3.19/1.01  num_of_splits:                          0
% 3.19/1.01  num_of_split_atoms:                     0
% 3.19/1.01  num_of_reused_defs:                     0
% 3.19/1.01  num_eq_ax_congr_red:                    26
% 3.19/1.01  num_of_sem_filtered_clauses:            1
% 3.19/1.01  num_of_subtypes:                        0
% 3.19/1.01  monotx_restored_types:                  0
% 3.19/1.01  sat_num_of_epr_types:                   0
% 3.19/1.01  sat_num_of_non_cyclic_types:            0
% 3.19/1.01  sat_guarded_non_collapsed_types:        0
% 3.19/1.01  num_pure_diseq_elim:                    0
% 3.19/1.01  simp_replaced_by:                       0
% 3.19/1.01  res_preprocessed:                       107
% 3.19/1.01  prep_upred:                             0
% 3.19/1.01  prep_unflattend:                        8
% 3.19/1.01  smt_new_axioms:                         0
% 3.19/1.01  pred_elim_cands:                        4
% 3.19/1.01  pred_elim:                              2
% 3.19/1.01  pred_elim_cl:                           4
% 3.19/1.01  pred_elim_cycles:                       4
% 3.19/1.01  merged_defs:                            0
% 3.19/1.01  merged_defs_ncl:                        0
% 3.19/1.01  bin_hyper_res:                          0
% 3.19/1.01  prep_cycles:                            4
% 3.19/1.01  pred_elim_time:                         0.001
% 3.19/1.01  splitting_time:                         0.
% 3.19/1.01  sem_filter_time:                        0.
% 3.19/1.01  monotx_time:                            0.001
% 3.19/1.01  subtype_inf_time:                       0.
% 3.19/1.01  
% 3.19/1.01  ------ Problem properties
% 3.19/1.01  
% 3.19/1.01  clauses:                                19
% 3.19/1.01  conjectures:                            5
% 3.19/1.01  epr:                                    4
% 3.19/1.01  horn:                                   19
% 3.19/1.01  ground:                                 6
% 3.19/1.01  unary:                                  10
% 3.19/1.01  binary:                                 2
% 3.19/1.01  lits:                                   37
% 3.19/1.01  lits_eq:                                8
% 3.19/1.01  fd_pure:                                0
% 3.19/1.01  fd_pseudo:                              0
% 3.19/1.01  fd_cond:                                0
% 3.19/1.01  fd_pseudo_cond:                         1
% 3.19/1.01  ac_symbols:                             0
% 3.19/1.01  
% 3.19/1.01  ------ Propositional Solver
% 3.19/1.01  
% 3.19/1.01  prop_solver_calls:                      28
% 3.19/1.01  prop_fast_solver_calls:                 590
% 3.19/1.01  smt_solver_calls:                       0
% 3.19/1.01  smt_fast_solver_calls:                  0
% 3.19/1.01  prop_num_of_clauses:                    2454
% 3.19/1.01  prop_preprocess_simplified:             6336
% 3.19/1.01  prop_fo_subsumed:                       13
% 3.19/1.01  prop_solver_time:                       0.
% 3.19/1.01  smt_solver_time:                        0.
% 3.19/1.01  smt_fast_solver_time:                   0.
% 3.19/1.01  prop_fast_solver_time:                  0.
% 3.19/1.01  prop_unsat_core_time:                   0.
% 3.19/1.01  
% 3.19/1.01  ------ QBF
% 3.19/1.01  
% 3.19/1.01  qbf_q_res:                              0
% 3.19/1.01  qbf_num_tautologies:                    0
% 3.19/1.01  qbf_prep_cycles:                        0
% 3.19/1.01  
% 3.19/1.01  ------ BMC1
% 3.19/1.01  
% 3.19/1.01  bmc1_current_bound:                     -1
% 3.19/1.01  bmc1_last_solved_bound:                 -1
% 3.19/1.01  bmc1_unsat_core_size:                   -1
% 3.19/1.01  bmc1_unsat_core_parents_size:           -1
% 3.19/1.01  bmc1_merge_next_fun:                    0
% 3.19/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.19/1.01  
% 3.19/1.01  ------ Instantiation
% 3.19/1.01  
% 3.19/1.01  inst_num_of_clauses:                    807
% 3.19/1.01  inst_num_in_passive:                    381
% 3.19/1.01  inst_num_in_active:                     210
% 3.19/1.01  inst_num_in_unprocessed:                216
% 3.19/1.01  inst_num_of_loops:                      230
% 3.19/1.01  inst_num_of_learning_restarts:          0
% 3.19/1.01  inst_num_moves_active_passive:          19
% 3.19/1.01  inst_lit_activity:                      0
% 3.19/1.01  inst_lit_activity_moves:                1
% 3.19/1.01  inst_num_tautologies:                   0
% 3.19/1.01  inst_num_prop_implied:                  0
% 3.19/1.01  inst_num_existing_simplified:           0
% 3.19/1.01  inst_num_eq_res_simplified:             0
% 3.19/1.01  inst_num_child_elim:                    0
% 3.19/1.01  inst_num_of_dismatching_blockings:      18
% 3.19/1.01  inst_num_of_non_proper_insts:           390
% 3.19/1.01  inst_num_of_duplicates:                 0
% 3.19/1.01  inst_inst_num_from_inst_to_res:         0
% 3.19/1.01  inst_dismatching_checking_time:         0.
% 3.19/1.01  
% 3.19/1.01  ------ Resolution
% 3.19/1.01  
% 3.19/1.01  res_num_of_clauses:                     0
% 3.19/1.01  res_num_in_passive:                     0
% 3.19/1.01  res_num_in_active:                      0
% 3.19/1.01  res_num_of_loops:                       111
% 3.19/1.01  res_forward_subset_subsumed:            12
% 3.19/1.01  res_backward_subset_subsumed:           0
% 3.19/1.01  res_forward_subsumed:                   0
% 3.19/1.01  res_backward_subsumed:                  0
% 3.19/1.01  res_forward_subsumption_resolution:     0
% 3.19/1.01  res_backward_subsumption_resolution:    0
% 3.19/1.01  res_clause_to_clause_subsumption:       133
% 3.19/1.01  res_orphan_elimination:                 0
% 3.19/1.01  res_tautology_del:                      12
% 3.19/1.01  res_num_eq_res_simplified:              0
% 3.19/1.01  res_num_sel_changes:                    0
% 3.19/1.01  res_moves_from_active_to_pass:          0
% 3.19/1.01  
% 3.19/1.01  ------ Superposition
% 3.19/1.01  
% 3.19/1.01  sup_time_total:                         0.
% 3.19/1.01  sup_time_generating:                    0.
% 3.19/1.01  sup_time_sim_full:                      0.
% 3.19/1.01  sup_time_sim_immed:                     0.
% 3.19/1.01  
% 3.19/1.01  sup_num_of_clauses:                     66
% 3.19/1.01  sup_num_in_active:                      42
% 3.19/1.01  sup_num_in_passive:                     24
% 3.19/1.01  sup_num_of_loops:                       45
% 3.19/1.01  sup_fw_superposition:                   37
% 3.19/1.01  sup_bw_superposition:                   12
% 3.19/1.01  sup_immediate_simplified:               3
% 3.19/1.01  sup_given_eliminated:                   0
% 3.19/1.01  comparisons_done:                       0
% 3.19/1.01  comparisons_avoided:                    0
% 3.19/1.01  
% 3.19/1.01  ------ Simplifications
% 3.19/1.01  
% 3.19/1.01  
% 3.19/1.01  sim_fw_subset_subsumed:                 0
% 3.19/1.01  sim_bw_subset_subsumed:                 0
% 3.19/1.01  sim_fw_subsumed:                        1
% 3.19/1.01  sim_bw_subsumed:                        0
% 3.19/1.01  sim_fw_subsumption_res:                 1
% 3.19/1.01  sim_bw_subsumption_res:                 0
% 3.19/1.01  sim_tautology_del:                      0
% 3.19/1.01  sim_eq_tautology_del:                   1
% 3.19/1.01  sim_eq_res_simp:                        0
% 3.19/1.01  sim_fw_demodulated:                     1
% 3.19/1.01  sim_bw_demodulated:                     4
% 3.19/1.01  sim_light_normalised:                   2
% 3.19/1.01  sim_joinable_taut:                      0
% 3.19/1.01  sim_joinable_simp:                      0
% 3.19/1.01  sim_ac_normalised:                      0
% 3.19/1.01  sim_smt_subsumption:                    0
% 3.19/1.01  
%------------------------------------------------------------------------------
