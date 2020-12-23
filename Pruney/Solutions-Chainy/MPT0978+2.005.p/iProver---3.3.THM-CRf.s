%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:01:33 EST 2020

% Result     : Theorem 3.73s
% Output     : CNFRefutation 3.73s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 284 expanded)
%              Number of clauses        :   65 (  82 expanded)
%              Number of leaves         :   17 (  66 expanded)
%              Depth                    :   18
%              Number of atoms          :  365 (1332 expanded)
%              Number of equality atoms :  129 ( 290 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f31,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_relset_1(X0,X1,X2) != X1
          & r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

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

fof(f61,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f39])).

fof(f59,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f39])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f29])).

fof(f56,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f58,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f60,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f27])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f62,plain,(
    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f39])).

fof(f11,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f13,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f66,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f55,f57])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f25])).

fof(f52,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f22])).

fof(f50,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f4,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f64,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f47,f57])).

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

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f63,plain,(
    k2_relset_1(sK0,sK1,sK2) != sK1 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_662,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_660,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_663,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4036,plain,
    ( k1_partfun1(X0,X1,sK0,sK1,X2,sK2) = k5_relat_1(X2,sK2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_660,c_663])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_23,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_5111,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK0,sK1,X2,sK2) = k5_relat_1(X2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4036,c_23])).

cnf(c_5112,plain,
    ( k1_partfun1(X0,X1,sK0,sK1,X2,sK2) = k5_relat_1(X2,sK2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_5111])).

cnf(c_5122,plain,
    ( k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) = k5_relat_1(sK3,sK2)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_662,c_5112])).

cnf(c_20,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_877,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(X1,X2,X3,X4,X0,sK2) = k5_relat_1(X0,sK2) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1029,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(X0,X1,X2,X3,sK3,sK2) = k5_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_877])).

cnf(c_1574,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(sK1,sK0,X0,X1,sK3,sK2) = k5_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_1029])).

cnf(c_2012,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) = k5_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_1574])).

cnf(c_5165,plain,
    ( k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) = k5_relat_1(sK3,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5122,c_22,c_21,c_20,c_19,c_2012])).

cnf(c_14,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_18,negated_conjecture,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_251,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) != X0
    | k6_partfun1(sK1) != X3
    | sK1 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_18])).

cnf(c_252,plain,
    ( ~ m1_subset_1(k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k6_partfun1(sK1) = k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) ),
    inference(unflattening,[status(thm)],[c_251])).

cnf(c_15,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_32,plain,
    ( m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_254,plain,
    ( ~ m1_subset_1(k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k6_partfun1(sK1) = k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_252,c_32])).

cnf(c_657,plain,
    ( k6_partfun1(sK1) = k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2)
    | m1_subset_1(k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_254])).

cnf(c_5168,plain,
    ( k5_relat_1(sK3,sK2) = k6_partfun1(sK1)
    | m1_subset_1(k5_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5165,c_657])).

cnf(c_24,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_26,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | k4_relset_1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_665,plain,
    ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3263,plain,
    ( k4_relset_1(X0,X1,sK0,sK1,X2,sK2) = k5_relat_1(X2,sK2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_660,c_665])).

cnf(c_4575,plain,
    ( k4_relset_1(sK1,sK0,sK0,sK1,sK3,sK2) = k5_relat_1(sK3,sK2) ),
    inference(superposition,[status(thm)],[c_662,c_3263])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_667,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4602,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4575,c_667])).

cnf(c_10352,plain,
    ( k5_relat_1(sK3,sK2) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5168,c_24,c_26,c_4602])).

cnf(c_5,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_669,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_10386,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1(sK1)),k2_relat_1(sK2)) = iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_10352,c_669])).

cnf(c_6,plain,
    ( k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_10390,plain,
    ( r1_tarski(sK1,k2_relat_1(sK2)) = iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10386,c_6])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1696,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1)
    | ~ r1_tarski(sK1,k2_relat_1(sK2))
    | sK1 = k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1697,plain,
    ( sK1 = k2_relat_1(sK2)
    | r1_tarski(k2_relat_1(sK2),sK1) != iProver_top
    | r1_tarski(sK1,k2_relat_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1696])).

cnf(c_377,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_811,plain,
    ( k2_relset_1(sK0,sK1,sK2) != X0
    | k2_relset_1(sK0,sK1,sK2) = sK1
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_377])).

cnf(c_950,plain,
    ( k2_relset_1(sK0,sK1,sK2) != k2_relat_1(sK2)
    | k2_relset_1(sK0,sK1,sK2) = sK1
    | sK1 != k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_811])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_820,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_4,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v5_relat_1(X0,X2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_228,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X3),X4)
    | ~ v1_relat_1(X3)
    | X0 != X3
    | X2 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_9])).

cnf(c_229,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_228])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_233,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_229,c_8])).

cnf(c_234,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_233])).

cnf(c_805,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(instantiation,[status(thm)],[c_234])).

cnf(c_806,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | r1_tarski(k2_relat_1(sK2),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_805])).

cnf(c_784,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_785,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_784])).

cnf(c_781,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_782,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_781])).

cnf(c_17,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) != sK1 ),
    inference(cnf_transformation,[],[f63])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10390,c_1697,c_950,c_820,c_806,c_785,c_782,c_17,c_26,c_24,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:44:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.73/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.73/0.98  
% 3.73/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.73/0.98  
% 3.73/0.98  ------  iProver source info
% 3.73/0.98  
% 3.73/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.73/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.73/0.98  git: non_committed_changes: false
% 3.73/0.98  git: last_make_outside_of_git: false
% 3.73/0.98  
% 3.73/0.98  ------ 
% 3.73/0.98  
% 3.73/0.98  ------ Input Options
% 3.73/0.98  
% 3.73/0.98  --out_options                           all
% 3.73/0.98  --tptp_safe_out                         true
% 3.73/0.98  --problem_path                          ""
% 3.73/0.98  --include_path                          ""
% 3.73/0.98  --clausifier                            res/vclausify_rel
% 3.73/0.98  --clausifier_options                    --mode clausify
% 3.73/0.98  --stdin                                 false
% 3.73/0.98  --stats_out                             all
% 3.73/0.98  
% 3.73/0.98  ------ General Options
% 3.73/0.98  
% 3.73/0.98  --fof                                   false
% 3.73/0.98  --time_out_real                         305.
% 3.73/0.98  --time_out_virtual                      -1.
% 3.73/0.98  --symbol_type_check                     false
% 3.73/0.98  --clausify_out                          false
% 3.73/0.98  --sig_cnt_out                           false
% 3.73/0.98  --trig_cnt_out                          false
% 3.73/0.98  --trig_cnt_out_tolerance                1.
% 3.73/0.98  --trig_cnt_out_sk_spl                   false
% 3.73/0.98  --abstr_cl_out                          false
% 3.73/0.98  
% 3.73/0.98  ------ Global Options
% 3.73/0.98  
% 3.73/0.98  --schedule                              default
% 3.73/0.98  --add_important_lit                     false
% 3.73/0.98  --prop_solver_per_cl                    1000
% 3.73/0.98  --min_unsat_core                        false
% 3.73/0.98  --soft_assumptions                      false
% 3.73/0.98  --soft_lemma_size                       3
% 3.73/0.98  --prop_impl_unit_size                   0
% 3.73/0.98  --prop_impl_unit                        []
% 3.73/0.98  --share_sel_clauses                     true
% 3.73/0.98  --reset_solvers                         false
% 3.73/0.98  --bc_imp_inh                            [conj_cone]
% 3.73/0.98  --conj_cone_tolerance                   3.
% 3.73/0.98  --extra_neg_conj                        none
% 3.73/0.98  --large_theory_mode                     true
% 3.73/0.98  --prolific_symb_bound                   200
% 3.73/0.98  --lt_threshold                          2000
% 3.73/0.98  --clause_weak_htbl                      true
% 3.73/0.98  --gc_record_bc_elim                     false
% 3.73/0.98  
% 3.73/0.98  ------ Preprocessing Options
% 3.73/0.98  
% 3.73/0.98  --preprocessing_flag                    true
% 3.73/0.98  --time_out_prep_mult                    0.1
% 3.73/0.98  --splitting_mode                        input
% 3.73/0.98  --splitting_grd                         true
% 3.73/0.98  --splitting_cvd                         false
% 3.73/0.98  --splitting_cvd_svl                     false
% 3.73/0.98  --splitting_nvd                         32
% 3.73/0.98  --sub_typing                            true
% 3.73/0.98  --prep_gs_sim                           true
% 3.73/0.98  --prep_unflatten                        true
% 3.73/0.98  --prep_res_sim                          true
% 3.73/0.98  --prep_upred                            true
% 3.73/0.98  --prep_sem_filter                       exhaustive
% 3.73/0.98  --prep_sem_filter_out                   false
% 3.73/0.98  --pred_elim                             true
% 3.73/0.98  --res_sim_input                         true
% 3.73/0.98  --eq_ax_congr_red                       true
% 3.73/0.98  --pure_diseq_elim                       true
% 3.73/0.98  --brand_transform                       false
% 3.73/0.98  --non_eq_to_eq                          false
% 3.73/0.98  --prep_def_merge                        true
% 3.73/0.98  --prep_def_merge_prop_impl              false
% 3.73/0.98  --prep_def_merge_mbd                    true
% 3.73/0.98  --prep_def_merge_tr_red                 false
% 3.73/0.98  --prep_def_merge_tr_cl                  false
% 3.73/0.98  --smt_preprocessing                     true
% 3.73/0.98  --smt_ac_axioms                         fast
% 3.73/0.98  --preprocessed_out                      false
% 3.73/0.98  --preprocessed_stats                    false
% 3.73/0.98  
% 3.73/0.98  ------ Abstraction refinement Options
% 3.73/0.98  
% 3.73/0.98  --abstr_ref                             []
% 3.73/0.98  --abstr_ref_prep                        false
% 3.73/0.98  --abstr_ref_until_sat                   false
% 3.73/0.98  --abstr_ref_sig_restrict                funpre
% 3.73/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.73/0.98  --abstr_ref_under                       []
% 3.73/0.98  
% 3.73/0.98  ------ SAT Options
% 3.73/0.98  
% 3.73/0.98  --sat_mode                              false
% 3.73/0.98  --sat_fm_restart_options                ""
% 3.73/0.98  --sat_gr_def                            false
% 3.73/0.98  --sat_epr_types                         true
% 3.73/0.98  --sat_non_cyclic_types                  false
% 3.73/0.98  --sat_finite_models                     false
% 3.73/0.98  --sat_fm_lemmas                         false
% 3.73/0.98  --sat_fm_prep                           false
% 3.73/0.98  --sat_fm_uc_incr                        true
% 3.73/0.98  --sat_out_model                         small
% 3.73/0.98  --sat_out_clauses                       false
% 3.73/0.98  
% 3.73/0.98  ------ QBF Options
% 3.73/0.98  
% 3.73/0.98  --qbf_mode                              false
% 3.73/0.98  --qbf_elim_univ                         false
% 3.73/0.98  --qbf_dom_inst                          none
% 3.73/0.98  --qbf_dom_pre_inst                      false
% 3.73/0.98  --qbf_sk_in                             false
% 3.73/0.98  --qbf_pred_elim                         true
% 3.73/0.98  --qbf_split                             512
% 3.73/0.98  
% 3.73/0.98  ------ BMC1 Options
% 3.73/0.98  
% 3.73/0.98  --bmc1_incremental                      false
% 3.73/0.98  --bmc1_axioms                           reachable_all
% 3.73/0.98  --bmc1_min_bound                        0
% 3.73/0.98  --bmc1_max_bound                        -1
% 3.73/0.98  --bmc1_max_bound_default                -1
% 3.73/0.98  --bmc1_symbol_reachability              true
% 3.73/0.98  --bmc1_property_lemmas                  false
% 3.73/0.98  --bmc1_k_induction                      false
% 3.73/0.98  --bmc1_non_equiv_states                 false
% 3.73/0.98  --bmc1_deadlock                         false
% 3.73/0.98  --bmc1_ucm                              false
% 3.73/0.98  --bmc1_add_unsat_core                   none
% 3.73/0.98  --bmc1_unsat_core_children              false
% 3.73/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.73/0.98  --bmc1_out_stat                         full
% 3.73/0.98  --bmc1_ground_init                      false
% 3.73/0.98  --bmc1_pre_inst_next_state              false
% 3.73/0.98  --bmc1_pre_inst_state                   false
% 3.73/0.98  --bmc1_pre_inst_reach_state             false
% 3.73/0.98  --bmc1_out_unsat_core                   false
% 3.73/0.98  --bmc1_aig_witness_out                  false
% 3.73/0.98  --bmc1_verbose                          false
% 3.73/0.98  --bmc1_dump_clauses_tptp                false
% 3.73/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.73/0.98  --bmc1_dump_file                        -
% 3.73/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.73/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.73/0.98  --bmc1_ucm_extend_mode                  1
% 3.73/0.98  --bmc1_ucm_init_mode                    2
% 3.73/0.98  --bmc1_ucm_cone_mode                    none
% 3.73/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.73/0.98  --bmc1_ucm_relax_model                  4
% 3.73/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.73/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.73/0.98  --bmc1_ucm_layered_model                none
% 3.73/0.98  --bmc1_ucm_max_lemma_size               10
% 3.73/0.98  
% 3.73/0.98  ------ AIG Options
% 3.73/0.98  
% 3.73/0.98  --aig_mode                              false
% 3.73/0.98  
% 3.73/0.98  ------ Instantiation Options
% 3.73/0.98  
% 3.73/0.98  --instantiation_flag                    true
% 3.73/0.98  --inst_sos_flag                         false
% 3.73/0.98  --inst_sos_phase                        true
% 3.73/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.73/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.73/0.98  --inst_lit_sel_side                     num_symb
% 3.73/0.98  --inst_solver_per_active                1400
% 3.73/0.98  --inst_solver_calls_frac                1.
% 3.73/0.98  --inst_passive_queue_type               priority_queues
% 3.73/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.73/0.98  --inst_passive_queues_freq              [25;2]
% 3.73/0.98  --inst_dismatching                      true
% 3.73/0.98  --inst_eager_unprocessed_to_passive     true
% 3.73/0.98  --inst_prop_sim_given                   true
% 3.73/0.98  --inst_prop_sim_new                     false
% 3.73/0.98  --inst_subs_new                         false
% 3.73/0.98  --inst_eq_res_simp                      false
% 3.73/0.98  --inst_subs_given                       false
% 3.73/0.98  --inst_orphan_elimination               true
% 3.73/0.98  --inst_learning_loop_flag               true
% 3.73/0.98  --inst_learning_start                   3000
% 3.73/0.98  --inst_learning_factor                  2
% 3.73/0.98  --inst_start_prop_sim_after_learn       3
% 3.73/0.98  --inst_sel_renew                        solver
% 3.73/0.98  --inst_lit_activity_flag                true
% 3.73/0.98  --inst_restr_to_given                   false
% 3.73/0.98  --inst_activity_threshold               500
% 3.73/0.98  --inst_out_proof                        true
% 3.73/0.98  
% 3.73/0.98  ------ Resolution Options
% 3.73/0.98  
% 3.73/0.98  --resolution_flag                       true
% 3.73/0.98  --res_lit_sel                           adaptive
% 3.73/0.98  --res_lit_sel_side                      none
% 3.73/0.98  --res_ordering                          kbo
% 3.73/0.98  --res_to_prop_solver                    active
% 3.73/0.98  --res_prop_simpl_new                    false
% 3.73/0.98  --res_prop_simpl_given                  true
% 3.73/0.98  --res_passive_queue_type                priority_queues
% 3.73/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.73/0.98  --res_passive_queues_freq               [15;5]
% 3.73/0.98  --res_forward_subs                      full
% 3.73/0.98  --res_backward_subs                     full
% 3.73/0.98  --res_forward_subs_resolution           true
% 3.73/0.98  --res_backward_subs_resolution          true
% 3.73/0.98  --res_orphan_elimination                true
% 3.73/0.98  --res_time_limit                        2.
% 3.73/0.98  --res_out_proof                         true
% 3.73/0.98  
% 3.73/0.98  ------ Superposition Options
% 3.73/0.98  
% 3.73/0.98  --superposition_flag                    true
% 3.73/0.98  --sup_passive_queue_type                priority_queues
% 3.73/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.73/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.73/0.98  --demod_completeness_check              fast
% 3.73/0.98  --demod_use_ground                      true
% 3.73/0.98  --sup_to_prop_solver                    passive
% 3.73/0.98  --sup_prop_simpl_new                    true
% 3.73/0.98  --sup_prop_simpl_given                  true
% 3.73/0.98  --sup_fun_splitting                     false
% 3.73/0.98  --sup_smt_interval                      50000
% 3.73/0.98  
% 3.73/0.98  ------ Superposition Simplification Setup
% 3.73/0.98  
% 3.73/0.98  --sup_indices_passive                   []
% 3.73/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.73/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.73/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.73/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.73/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.73/0.98  --sup_full_bw                           [BwDemod]
% 3.73/0.98  --sup_immed_triv                        [TrivRules]
% 3.73/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.73/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.73/0.98  --sup_immed_bw_main                     []
% 3.73/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.73/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.73/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.73/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.73/0.98  
% 3.73/0.98  ------ Combination Options
% 3.73/0.98  
% 3.73/0.98  --comb_res_mult                         3
% 3.73/0.98  --comb_sup_mult                         2
% 3.73/0.98  --comb_inst_mult                        10
% 3.73/0.98  
% 3.73/0.98  ------ Debug Options
% 3.73/0.98  
% 3.73/0.98  --dbg_backtrace                         false
% 3.73/0.98  --dbg_dump_prop_clauses                 false
% 3.73/0.98  --dbg_dump_prop_clauses_file            -
% 3.73/0.98  --dbg_out_stat                          false
% 3.73/0.98  ------ Parsing...
% 3.73/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.73/0.98  
% 3.73/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.73/0.98  
% 3.73/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.73/0.98  
% 3.73/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.73/0.98  ------ Proving...
% 3.73/0.98  ------ Problem Properties 
% 3.73/0.98  
% 3.73/0.98  
% 3.73/0.98  clauses                                 18
% 3.73/0.98  conjectures                             5
% 3.73/0.98  EPR                                     4
% 3.73/0.98  Horn                                    18
% 3.73/0.98  unary                                   9
% 3.73/0.98  binary                                  4
% 3.73/0.98  lits                                    34
% 3.73/0.98  lits eq                                 8
% 3.73/0.98  fd_pure                                 0
% 3.73/0.98  fd_pseudo                               0
% 3.73/0.98  fd_cond                                 0
% 3.73/0.98  fd_pseudo_cond                          1
% 3.73/0.98  AC symbols                              0
% 3.73/0.98  
% 3.73/0.98  ------ Schedule dynamic 5 is on 
% 3.73/0.98  
% 3.73/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.73/0.98  
% 3.73/0.98  
% 3.73/0.98  ------ 
% 3.73/0.98  Current options:
% 3.73/0.98  ------ 
% 3.73/0.98  
% 3.73/0.98  ------ Input Options
% 3.73/0.98  
% 3.73/0.98  --out_options                           all
% 3.73/0.98  --tptp_safe_out                         true
% 3.73/0.98  --problem_path                          ""
% 3.73/0.98  --include_path                          ""
% 3.73/0.98  --clausifier                            res/vclausify_rel
% 3.73/0.98  --clausifier_options                    --mode clausify
% 3.73/0.98  --stdin                                 false
% 3.73/0.98  --stats_out                             all
% 3.73/0.98  
% 3.73/0.98  ------ General Options
% 3.73/0.98  
% 3.73/0.98  --fof                                   false
% 3.73/0.98  --time_out_real                         305.
% 3.73/0.98  --time_out_virtual                      -1.
% 3.73/0.98  --symbol_type_check                     false
% 3.73/0.98  --clausify_out                          false
% 3.73/0.98  --sig_cnt_out                           false
% 3.73/0.98  --trig_cnt_out                          false
% 3.73/0.98  --trig_cnt_out_tolerance                1.
% 3.73/0.98  --trig_cnt_out_sk_spl                   false
% 3.73/0.98  --abstr_cl_out                          false
% 3.73/0.98  
% 3.73/0.98  ------ Global Options
% 3.73/0.98  
% 3.73/0.98  --schedule                              default
% 3.73/0.98  --add_important_lit                     false
% 3.73/0.98  --prop_solver_per_cl                    1000
% 3.73/0.98  --min_unsat_core                        false
% 3.73/0.98  --soft_assumptions                      false
% 3.73/0.98  --soft_lemma_size                       3
% 3.73/0.98  --prop_impl_unit_size                   0
% 3.73/0.98  --prop_impl_unit                        []
% 3.73/0.98  --share_sel_clauses                     true
% 3.73/0.98  --reset_solvers                         false
% 3.73/0.98  --bc_imp_inh                            [conj_cone]
% 3.73/0.98  --conj_cone_tolerance                   3.
% 3.73/0.98  --extra_neg_conj                        none
% 3.73/0.98  --large_theory_mode                     true
% 3.73/0.98  --prolific_symb_bound                   200
% 3.73/0.98  --lt_threshold                          2000
% 3.73/0.98  --clause_weak_htbl                      true
% 3.73/0.98  --gc_record_bc_elim                     false
% 3.73/0.98  
% 3.73/0.98  ------ Preprocessing Options
% 3.73/0.98  
% 3.73/0.98  --preprocessing_flag                    true
% 3.73/0.98  --time_out_prep_mult                    0.1
% 3.73/0.98  --splitting_mode                        input
% 3.73/0.98  --splitting_grd                         true
% 3.73/0.98  --splitting_cvd                         false
% 3.73/0.98  --splitting_cvd_svl                     false
% 3.73/0.98  --splitting_nvd                         32
% 3.73/0.98  --sub_typing                            true
% 3.73/0.98  --prep_gs_sim                           true
% 3.73/0.98  --prep_unflatten                        true
% 3.73/0.98  --prep_res_sim                          true
% 3.73/0.98  --prep_upred                            true
% 3.73/0.98  --prep_sem_filter                       exhaustive
% 3.73/0.98  --prep_sem_filter_out                   false
% 3.73/0.98  --pred_elim                             true
% 3.73/0.98  --res_sim_input                         true
% 3.73/0.98  --eq_ax_congr_red                       true
% 3.73/0.98  --pure_diseq_elim                       true
% 3.73/0.98  --brand_transform                       false
% 3.73/0.98  --non_eq_to_eq                          false
% 3.73/0.98  --prep_def_merge                        true
% 3.73/0.98  --prep_def_merge_prop_impl              false
% 3.73/0.98  --prep_def_merge_mbd                    true
% 3.73/0.98  --prep_def_merge_tr_red                 false
% 3.73/0.98  --prep_def_merge_tr_cl                  false
% 3.73/0.98  --smt_preprocessing                     true
% 3.73/0.98  --smt_ac_axioms                         fast
% 3.73/0.98  --preprocessed_out                      false
% 3.73/0.98  --preprocessed_stats                    false
% 3.73/0.98  
% 3.73/0.98  ------ Abstraction refinement Options
% 3.73/0.98  
% 3.73/0.98  --abstr_ref                             []
% 3.73/0.98  --abstr_ref_prep                        false
% 3.73/0.98  --abstr_ref_until_sat                   false
% 3.73/0.98  --abstr_ref_sig_restrict                funpre
% 3.73/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.73/0.98  --abstr_ref_under                       []
% 3.73/0.98  
% 3.73/0.98  ------ SAT Options
% 3.73/0.98  
% 3.73/0.98  --sat_mode                              false
% 3.73/0.98  --sat_fm_restart_options                ""
% 3.73/0.98  --sat_gr_def                            false
% 3.73/0.98  --sat_epr_types                         true
% 3.73/0.98  --sat_non_cyclic_types                  false
% 3.73/0.98  --sat_finite_models                     false
% 3.73/0.98  --sat_fm_lemmas                         false
% 3.73/0.98  --sat_fm_prep                           false
% 3.73/0.98  --sat_fm_uc_incr                        true
% 3.73/0.98  --sat_out_model                         small
% 3.73/0.98  --sat_out_clauses                       false
% 3.73/0.98  
% 3.73/0.98  ------ QBF Options
% 3.73/0.98  
% 3.73/0.98  --qbf_mode                              false
% 3.73/0.98  --qbf_elim_univ                         false
% 3.73/0.98  --qbf_dom_inst                          none
% 3.73/0.98  --qbf_dom_pre_inst                      false
% 3.73/0.98  --qbf_sk_in                             false
% 3.73/0.98  --qbf_pred_elim                         true
% 3.73/0.98  --qbf_split                             512
% 3.73/0.98  
% 3.73/0.98  ------ BMC1 Options
% 3.73/0.98  
% 3.73/0.98  --bmc1_incremental                      false
% 3.73/0.98  --bmc1_axioms                           reachable_all
% 3.73/0.98  --bmc1_min_bound                        0
% 3.73/0.98  --bmc1_max_bound                        -1
% 3.73/0.98  --bmc1_max_bound_default                -1
% 3.73/0.98  --bmc1_symbol_reachability              true
% 3.73/0.98  --bmc1_property_lemmas                  false
% 3.73/0.98  --bmc1_k_induction                      false
% 3.73/0.98  --bmc1_non_equiv_states                 false
% 3.73/0.98  --bmc1_deadlock                         false
% 3.73/0.98  --bmc1_ucm                              false
% 3.73/0.98  --bmc1_add_unsat_core                   none
% 3.73/0.98  --bmc1_unsat_core_children              false
% 3.73/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.73/0.98  --bmc1_out_stat                         full
% 3.73/0.98  --bmc1_ground_init                      false
% 3.73/0.98  --bmc1_pre_inst_next_state              false
% 3.73/0.98  --bmc1_pre_inst_state                   false
% 3.73/0.98  --bmc1_pre_inst_reach_state             false
% 3.73/0.98  --bmc1_out_unsat_core                   false
% 3.73/0.98  --bmc1_aig_witness_out                  false
% 3.73/0.98  --bmc1_verbose                          false
% 3.73/0.98  --bmc1_dump_clauses_tptp                false
% 3.73/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.73/0.98  --bmc1_dump_file                        -
% 3.73/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.73/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.73/0.98  --bmc1_ucm_extend_mode                  1
% 3.73/0.98  --bmc1_ucm_init_mode                    2
% 3.73/0.98  --bmc1_ucm_cone_mode                    none
% 3.73/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.73/0.98  --bmc1_ucm_relax_model                  4
% 3.73/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.73/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.73/0.98  --bmc1_ucm_layered_model                none
% 3.73/0.98  --bmc1_ucm_max_lemma_size               10
% 3.73/0.98  
% 3.73/0.98  ------ AIG Options
% 3.73/0.98  
% 3.73/0.98  --aig_mode                              false
% 3.73/0.98  
% 3.73/0.98  ------ Instantiation Options
% 3.73/0.98  
% 3.73/0.98  --instantiation_flag                    true
% 3.73/0.98  --inst_sos_flag                         false
% 3.73/0.98  --inst_sos_phase                        true
% 3.73/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.73/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.73/0.98  --inst_lit_sel_side                     none
% 3.73/0.98  --inst_solver_per_active                1400
% 3.73/0.98  --inst_solver_calls_frac                1.
% 3.73/0.98  --inst_passive_queue_type               priority_queues
% 3.73/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.73/0.98  --inst_passive_queues_freq              [25;2]
% 3.73/0.98  --inst_dismatching                      true
% 3.73/0.98  --inst_eager_unprocessed_to_passive     true
% 3.73/0.98  --inst_prop_sim_given                   true
% 3.73/0.98  --inst_prop_sim_new                     false
% 3.73/0.98  --inst_subs_new                         false
% 3.73/0.98  --inst_eq_res_simp                      false
% 3.73/0.98  --inst_subs_given                       false
% 3.73/0.98  --inst_orphan_elimination               true
% 3.73/0.98  --inst_learning_loop_flag               true
% 3.73/0.98  --inst_learning_start                   3000
% 3.73/0.98  --inst_learning_factor                  2
% 3.73/0.98  --inst_start_prop_sim_after_learn       3
% 3.73/0.98  --inst_sel_renew                        solver
% 3.73/0.98  --inst_lit_activity_flag                true
% 3.73/0.98  --inst_restr_to_given                   false
% 3.73/0.98  --inst_activity_threshold               500
% 3.73/0.98  --inst_out_proof                        true
% 3.73/0.98  
% 3.73/0.98  ------ Resolution Options
% 3.73/0.98  
% 3.73/0.98  --resolution_flag                       false
% 3.73/0.98  --res_lit_sel                           adaptive
% 3.73/0.98  --res_lit_sel_side                      none
% 3.73/0.98  --res_ordering                          kbo
% 3.73/0.98  --res_to_prop_solver                    active
% 3.73/0.98  --res_prop_simpl_new                    false
% 3.73/0.98  --res_prop_simpl_given                  true
% 3.73/0.98  --res_passive_queue_type                priority_queues
% 3.73/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.73/0.98  --res_passive_queues_freq               [15;5]
% 3.73/0.98  --res_forward_subs                      full
% 3.73/0.98  --res_backward_subs                     full
% 3.73/0.98  --res_forward_subs_resolution           true
% 3.73/0.98  --res_backward_subs_resolution          true
% 3.73/0.98  --res_orphan_elimination                true
% 3.73/0.98  --res_time_limit                        2.
% 3.73/0.98  --res_out_proof                         true
% 3.73/0.98  
% 3.73/0.98  ------ Superposition Options
% 3.73/0.98  
% 3.73/0.98  --superposition_flag                    true
% 3.73/0.98  --sup_passive_queue_type                priority_queues
% 3.73/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.73/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.73/0.98  --demod_completeness_check              fast
% 3.73/0.98  --demod_use_ground                      true
% 3.73/0.98  --sup_to_prop_solver                    passive
% 3.73/0.98  --sup_prop_simpl_new                    true
% 3.73/0.98  --sup_prop_simpl_given                  true
% 3.73/0.98  --sup_fun_splitting                     false
% 3.73/0.98  --sup_smt_interval                      50000
% 3.73/0.98  
% 3.73/0.98  ------ Superposition Simplification Setup
% 3.73/0.98  
% 3.73/0.98  --sup_indices_passive                   []
% 3.73/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.73/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.73/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.73/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.73/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.73/0.98  --sup_full_bw                           [BwDemod]
% 3.73/0.98  --sup_immed_triv                        [TrivRules]
% 3.73/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.73/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.73/0.98  --sup_immed_bw_main                     []
% 3.73/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.73/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.73/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.73/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.73/0.98  
% 3.73/0.98  ------ Combination Options
% 3.73/0.98  
% 3.73/0.98  --comb_res_mult                         3
% 3.73/0.98  --comb_sup_mult                         2
% 3.73/0.98  --comb_inst_mult                        10
% 3.73/0.98  
% 3.73/0.98  ------ Debug Options
% 3.73/0.98  
% 3.73/0.98  --dbg_backtrace                         false
% 3.73/0.98  --dbg_dump_prop_clauses                 false
% 3.73/0.98  --dbg_dump_prop_clauses_file            -
% 3.73/0.98  --dbg_out_stat                          false
% 3.73/0.98  
% 3.73/0.98  
% 3.73/0.98  
% 3.73/0.98  
% 3.73/0.98  ------ Proving...
% 3.73/0.98  
% 3.73/0.98  
% 3.73/0.98  % SZS status Theorem for theBenchmark.p
% 3.73/0.98  
% 3.73/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.73/0.98  
% 3.73/0.98  fof(f14,conjecture,(
% 3.73/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 3.73/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/0.98  
% 3.73/0.98  fof(f15,negated_conjecture,(
% 3.73/0.98    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 3.73/0.98    inference(negated_conjecture,[],[f14])).
% 3.73/0.98  
% 3.73/0.98  fof(f16,plain,(
% 3.73/0.98    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 3.73/0.98    inference(pure_predicate_removal,[],[f15])).
% 3.73/0.98  
% 3.73/0.98  fof(f31,plain,(
% 3.73/0.98    ? [X0,X1,X2] : (? [X3] : ((k2_relset_1(X0,X1,X2) != X1 & r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 3.73/0.98    inference(ennf_transformation,[],[f16])).
% 3.73/0.98  
% 3.73/0.98  fof(f32,plain,(
% 3.73/0.98    ? [X0,X1,X2] : (? [X3] : (k2_relset_1(X0,X1,X2) != X1 & r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 3.73/0.98    inference(flattening,[],[f31])).
% 3.73/0.98  
% 3.73/0.98  fof(f38,plain,(
% 3.73/0.98    ( ! [X2,X0,X1] : (? [X3] : (k2_relset_1(X0,X1,X2) != X1 & r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) => (k2_relset_1(X0,X1,X2) != X1 & r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,sK3,X2),k6_partfun1(X1)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(sK3))) )),
% 3.73/0.98    introduced(choice_axiom,[])).
% 3.73/0.98  
% 3.73/0.98  fof(f37,plain,(
% 3.73/0.98    ? [X0,X1,X2] : (? [X3] : (k2_relset_1(X0,X1,X2) != X1 & r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (? [X3] : (k2_relset_1(sK0,sK1,sK2) != sK1 & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK0,sK0,sK1,X3,sK2),k6_partfun1(sK1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2))),
% 3.73/0.98    introduced(choice_axiom,[])).
% 3.73/0.98  
% 3.73/0.98  fof(f39,plain,(
% 3.73/0.98    (k2_relset_1(sK0,sK1,sK2) != sK1 & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k6_partfun1(sK1)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2)),
% 3.73/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f32,f38,f37])).
% 3.73/0.98  
% 3.73/0.98  fof(f61,plain,(
% 3.73/0.98    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 3.73/0.98    inference(cnf_transformation,[],[f39])).
% 3.73/0.98  
% 3.73/0.98  fof(f59,plain,(
% 3.73/0.98    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.73/0.98    inference(cnf_transformation,[],[f39])).
% 3.73/0.98  
% 3.73/0.98  fof(f12,axiom,(
% 3.73/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.73/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/0.98  
% 3.73/0.98  fof(f29,plain,(
% 3.73/0.98    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.73/0.98    inference(ennf_transformation,[],[f12])).
% 3.73/0.98  
% 3.73/0.98  fof(f30,plain,(
% 3.73/0.98    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.73/0.98    inference(flattening,[],[f29])).
% 3.73/0.98  
% 3.73/0.98  fof(f56,plain,(
% 3.73/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.73/0.98    inference(cnf_transformation,[],[f30])).
% 3.73/0.98  
% 3.73/0.98  fof(f58,plain,(
% 3.73/0.98    v1_funct_1(sK2)),
% 3.73/0.98    inference(cnf_transformation,[],[f39])).
% 3.73/0.98  
% 3.73/0.98  fof(f60,plain,(
% 3.73/0.98    v1_funct_1(sK3)),
% 3.73/0.98    inference(cnf_transformation,[],[f39])).
% 3.73/0.98  
% 3.73/0.98  fof(f10,axiom,(
% 3.73/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.73/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/0.98  
% 3.73/0.98  fof(f27,plain,(
% 3.73/0.98    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.73/0.98    inference(ennf_transformation,[],[f10])).
% 3.73/0.98  
% 3.73/0.98  fof(f28,plain,(
% 3.73/0.98    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.73/0.98    inference(flattening,[],[f27])).
% 3.73/0.98  
% 3.73/0.98  fof(f36,plain,(
% 3.73/0.98    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.73/0.98    inference(nnf_transformation,[],[f28])).
% 3.73/0.98  
% 3.73/0.98  fof(f53,plain,(
% 3.73/0.98    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.73/0.98    inference(cnf_transformation,[],[f36])).
% 3.73/0.98  
% 3.73/0.98  fof(f62,plain,(
% 3.73/0.98    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k6_partfun1(sK1))),
% 3.73/0.98    inference(cnf_transformation,[],[f39])).
% 3.73/0.98  
% 3.73/0.98  fof(f11,axiom,(
% 3.73/0.98    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.73/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/0.98  
% 3.73/0.98  fof(f55,plain,(
% 3.73/0.98    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.73/0.98    inference(cnf_transformation,[],[f11])).
% 3.73/0.98  
% 3.73/0.98  fof(f13,axiom,(
% 3.73/0.98    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.73/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/0.98  
% 3.73/0.98  fof(f57,plain,(
% 3.73/0.98    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.73/0.98    inference(cnf_transformation,[],[f13])).
% 3.73/0.98  
% 3.73/0.98  fof(f66,plain,(
% 3.73/0.98    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.73/0.98    inference(definition_unfolding,[],[f55,f57])).
% 3.73/0.98  
% 3.73/0.98  fof(f9,axiom,(
% 3.73/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5))),
% 3.73/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/0.98  
% 3.73/0.98  fof(f25,plain,(
% 3.73/0.98    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.73/0.98    inference(ennf_transformation,[],[f9])).
% 3.73/0.98  
% 3.73/0.98  fof(f26,plain,(
% 3.73/0.98    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.73/0.98    inference(flattening,[],[f25])).
% 3.73/0.98  
% 3.73/0.98  fof(f52,plain,(
% 3.73/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.73/0.98    inference(cnf_transformation,[],[f26])).
% 3.73/0.98  
% 3.73/0.98  fof(f7,axiom,(
% 3.73/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))))),
% 3.73/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/0.98  
% 3.73/0.98  fof(f22,plain,(
% 3.73/0.98    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.73/0.98    inference(ennf_transformation,[],[f7])).
% 3.73/0.98  
% 3.73/0.98  fof(f23,plain,(
% 3.73/0.98    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.73/0.98    inference(flattening,[],[f22])).
% 3.73/0.98  
% 3.73/0.98  fof(f50,plain,(
% 3.73/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.73/0.98    inference(cnf_transformation,[],[f23])).
% 3.73/0.98  
% 3.73/0.98  fof(f3,axiom,(
% 3.73/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 3.73/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/0.98  
% 3.73/0.98  fof(f19,plain,(
% 3.73/0.98    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.73/0.98    inference(ennf_transformation,[],[f3])).
% 3.73/0.98  
% 3.73/0.98  fof(f45,plain,(
% 3.73/0.98    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.73/0.98    inference(cnf_transformation,[],[f19])).
% 3.73/0.98  
% 3.73/0.98  fof(f4,axiom,(
% 3.73/0.98    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.73/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/0.98  
% 3.73/0.98  fof(f47,plain,(
% 3.73/0.98    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 3.73/0.98    inference(cnf_transformation,[],[f4])).
% 3.73/0.98  
% 3.73/0.98  fof(f64,plain,(
% 3.73/0.98    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 3.73/0.98    inference(definition_unfolding,[],[f47,f57])).
% 3.73/0.98  
% 3.73/0.98  fof(f1,axiom,(
% 3.73/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.73/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/0.98  
% 3.73/0.98  fof(f33,plain,(
% 3.73/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.73/0.98    inference(nnf_transformation,[],[f1])).
% 3.73/0.98  
% 3.73/0.98  fof(f34,plain,(
% 3.73/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.73/0.98    inference(flattening,[],[f33])).
% 3.73/0.98  
% 3.73/0.98  fof(f42,plain,(
% 3.73/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.73/0.98    inference(cnf_transformation,[],[f34])).
% 3.73/0.98  
% 3.73/0.98  fof(f8,axiom,(
% 3.73/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.73/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/0.98  
% 3.73/0.98  fof(f24,plain,(
% 3.73/0.98    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.73/0.98    inference(ennf_transformation,[],[f8])).
% 3.73/0.98  
% 3.73/0.98  fof(f51,plain,(
% 3.73/0.98    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.73/0.98    inference(cnf_transformation,[],[f24])).
% 3.73/0.98  
% 3.73/0.98  fof(f2,axiom,(
% 3.73/0.98    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.73/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/0.98  
% 3.73/0.98  fof(f18,plain,(
% 3.73/0.98    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.73/0.98    inference(ennf_transformation,[],[f2])).
% 3.73/0.98  
% 3.73/0.98  fof(f35,plain,(
% 3.73/0.98    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.73/0.98    inference(nnf_transformation,[],[f18])).
% 3.73/0.98  
% 3.73/0.98  fof(f43,plain,(
% 3.73/0.98    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.73/0.98    inference(cnf_transformation,[],[f35])).
% 3.73/0.98  
% 3.73/0.98  fof(f6,axiom,(
% 3.73/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.73/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/0.98  
% 3.73/0.98  fof(f17,plain,(
% 3.73/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.73/0.98    inference(pure_predicate_removal,[],[f6])).
% 3.73/0.98  
% 3.73/0.98  fof(f21,plain,(
% 3.73/0.98    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.73/0.98    inference(ennf_transformation,[],[f17])).
% 3.73/0.98  
% 3.73/0.98  fof(f49,plain,(
% 3.73/0.98    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.73/0.98    inference(cnf_transformation,[],[f21])).
% 3.73/0.98  
% 3.73/0.98  fof(f5,axiom,(
% 3.73/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.73/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/0.98  
% 3.73/0.98  fof(f20,plain,(
% 3.73/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.73/0.98    inference(ennf_transformation,[],[f5])).
% 3.73/0.98  
% 3.73/0.98  fof(f48,plain,(
% 3.73/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.73/0.98    inference(cnf_transformation,[],[f20])).
% 3.73/0.98  
% 3.73/0.98  fof(f63,plain,(
% 3.73/0.98    k2_relset_1(sK0,sK1,sK2) != sK1),
% 3.73/0.98    inference(cnf_transformation,[],[f39])).
% 3.73/0.98  
% 3.73/0.98  cnf(c_19,negated_conjecture,
% 3.73/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 3.73/0.98      inference(cnf_transformation,[],[f61]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_662,plain,
% 3.73/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_21,negated_conjecture,
% 3.73/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.73/0.98      inference(cnf_transformation,[],[f59]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_660,plain,
% 3.73/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_16,plain,
% 3.73/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.73/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.73/0.98      | ~ v1_funct_1(X0)
% 3.73/0.98      | ~ v1_funct_1(X3)
% 3.73/0.98      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.73/0.98      inference(cnf_transformation,[],[f56]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_663,plain,
% 3.73/0.98      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 3.73/0.98      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 3.73/0.98      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.73/0.98      | v1_funct_1(X5) != iProver_top
% 3.73/0.98      | v1_funct_1(X4) != iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_4036,plain,
% 3.73/0.98      ( k1_partfun1(X0,X1,sK0,sK1,X2,sK2) = k5_relat_1(X2,sK2)
% 3.73/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.73/0.98      | v1_funct_1(X2) != iProver_top
% 3.73/0.98      | v1_funct_1(sK2) != iProver_top ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_660,c_663]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_22,negated_conjecture,
% 3.73/0.98      ( v1_funct_1(sK2) ),
% 3.73/0.98      inference(cnf_transformation,[],[f58]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_23,plain,
% 3.73/0.98      ( v1_funct_1(sK2) = iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_5111,plain,
% 3.73/0.98      ( v1_funct_1(X2) != iProver_top
% 3.73/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.73/0.98      | k1_partfun1(X0,X1,sK0,sK1,X2,sK2) = k5_relat_1(X2,sK2) ),
% 3.73/0.98      inference(global_propositional_subsumption,
% 3.73/0.98                [status(thm)],
% 3.73/0.98                [c_4036,c_23]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_5112,plain,
% 3.73/0.98      ( k1_partfun1(X0,X1,sK0,sK1,X2,sK2) = k5_relat_1(X2,sK2)
% 3.73/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.73/0.98      | v1_funct_1(X2) != iProver_top ),
% 3.73/0.98      inference(renaming,[status(thm)],[c_5111]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_5122,plain,
% 3.73/0.98      ( k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) = k5_relat_1(sK3,sK2)
% 3.73/0.98      | v1_funct_1(sK3) != iProver_top ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_662,c_5112]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_20,negated_conjecture,
% 3.73/0.98      ( v1_funct_1(sK3) ),
% 3.73/0.98      inference(cnf_transformation,[],[f60]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_877,plain,
% 3.73/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.73/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 3.73/0.98      | ~ v1_funct_1(X0)
% 3.73/0.98      | ~ v1_funct_1(sK2)
% 3.73/0.98      | k1_partfun1(X1,X2,X3,X4,X0,sK2) = k5_relat_1(X0,sK2) ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_16]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1029,plain,
% 3.73/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.73/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.73/0.98      | ~ v1_funct_1(sK3)
% 3.73/0.98      | ~ v1_funct_1(sK2)
% 3.73/0.98      | k1_partfun1(X0,X1,X2,X3,sK3,sK2) = k5_relat_1(sK3,sK2) ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_877]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1574,plain,
% 3.73/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.73/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.73/0.98      | ~ v1_funct_1(sK3)
% 3.73/0.98      | ~ v1_funct_1(sK2)
% 3.73/0.98      | k1_partfun1(sK1,sK0,X0,X1,sK3,sK2) = k5_relat_1(sK3,sK2) ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_1029]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_2012,plain,
% 3.73/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.73/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.73/0.98      | ~ v1_funct_1(sK3)
% 3.73/0.98      | ~ v1_funct_1(sK2)
% 3.73/0.98      | k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) = k5_relat_1(sK3,sK2) ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_1574]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_5165,plain,
% 3.73/0.98      ( k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) = k5_relat_1(sK3,sK2) ),
% 3.73/0.98      inference(global_propositional_subsumption,
% 3.73/0.98                [status(thm)],
% 3.73/0.98                [c_5122,c_22,c_21,c_20,c_19,c_2012]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_14,plain,
% 3.73/0.98      ( ~ r2_relset_1(X0,X1,X2,X3)
% 3.73/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.73/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.73/0.98      | X3 = X2 ),
% 3.73/0.98      inference(cnf_transformation,[],[f53]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_18,negated_conjecture,
% 3.73/0.98      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k6_partfun1(sK1)) ),
% 3.73/0.98      inference(cnf_transformation,[],[f62]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_251,plain,
% 3.73/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.73/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.73/0.98      | X3 = X0
% 3.73/0.98      | k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) != X0
% 3.73/0.98      | k6_partfun1(sK1) != X3
% 3.73/0.98      | sK1 != X2
% 3.73/0.98      | sK1 != X1 ),
% 3.73/0.98      inference(resolution_lifted,[status(thm)],[c_14,c_18]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_252,plain,
% 3.73/0.98      ( ~ m1_subset_1(k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.73/0.98      | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.73/0.98      | k6_partfun1(sK1) = k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) ),
% 3.73/0.98      inference(unflattening,[status(thm)],[c_251]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_15,plain,
% 3.73/0.98      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.73/0.98      inference(cnf_transformation,[],[f66]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_32,plain,
% 3.73/0.98      ( m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_15]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_254,plain,
% 3.73/0.98      ( ~ m1_subset_1(k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.73/0.98      | k6_partfun1(sK1) = k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) ),
% 3.73/0.98      inference(global_propositional_subsumption,
% 3.73/0.98                [status(thm)],
% 3.73/0.98                [c_252,c_32]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_657,plain,
% 3.73/0.98      ( k6_partfun1(sK1) = k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2)
% 3.73/0.98      | m1_subset_1(k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_254]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_5168,plain,
% 3.73/0.98      ( k5_relat_1(sK3,sK2) = k6_partfun1(sK1)
% 3.73/0.98      | m1_subset_1(k5_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
% 3.73/0.98      inference(demodulation,[status(thm)],[c_5165,c_657]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_24,plain,
% 3.73/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_26,plain,
% 3.73/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_12,plain,
% 3.73/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.73/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.73/0.98      | k4_relset_1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.73/0.98      inference(cnf_transformation,[],[f52]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_665,plain,
% 3.73/0.98      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 3.73/0.98      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 3.73/0.98      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_3263,plain,
% 3.73/0.98      ( k4_relset_1(X0,X1,sK0,sK1,X2,sK2) = k5_relat_1(X2,sK2)
% 3.73/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_660,c_665]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_4575,plain,
% 3.73/0.98      ( k4_relset_1(sK1,sK0,sK0,sK1,sK3,sK2) = k5_relat_1(sK3,sK2) ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_662,c_3263]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_10,plain,
% 3.73/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.73/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.73/0.98      | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) ),
% 3.73/0.98      inference(cnf_transformation,[],[f50]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_667,plain,
% 3.73/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.73/0.98      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 3.73/0.98      | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_4602,plain,
% 3.73/0.98      ( m1_subset_1(k5_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
% 3.73/0.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.73/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_4575,c_667]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_10352,plain,
% 3.73/0.98      ( k5_relat_1(sK3,sK2) = k6_partfun1(sK1) ),
% 3.73/0.98      inference(global_propositional_subsumption,
% 3.73/0.98                [status(thm)],
% 3.73/0.98                [c_5168,c_24,c_26,c_4602]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_5,plain,
% 3.73/0.98      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
% 3.73/0.98      | ~ v1_relat_1(X1)
% 3.73/0.98      | ~ v1_relat_1(X0) ),
% 3.73/0.98      inference(cnf_transformation,[],[f45]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_669,plain,
% 3.73/0.98      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
% 3.73/0.98      | v1_relat_1(X0) != iProver_top
% 3.73/0.98      | v1_relat_1(X1) != iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_10386,plain,
% 3.73/0.98      ( r1_tarski(k2_relat_1(k6_partfun1(sK1)),k2_relat_1(sK2)) = iProver_top
% 3.73/0.98      | v1_relat_1(sK3) != iProver_top
% 3.73/0.98      | v1_relat_1(sK2) != iProver_top ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_10352,c_669]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_6,plain,
% 3.73/0.98      ( k2_relat_1(k6_partfun1(X0)) = X0 ),
% 3.73/0.98      inference(cnf_transformation,[],[f64]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_10390,plain,
% 3.73/0.98      ( r1_tarski(sK1,k2_relat_1(sK2)) = iProver_top
% 3.73/0.98      | v1_relat_1(sK3) != iProver_top
% 3.73/0.98      | v1_relat_1(sK2) != iProver_top ),
% 3.73/0.98      inference(demodulation,[status(thm)],[c_10386,c_6]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_0,plain,
% 3.73/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.73/0.98      inference(cnf_transformation,[],[f42]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1696,plain,
% 3.73/0.98      ( ~ r1_tarski(k2_relat_1(sK2),sK1)
% 3.73/0.98      | ~ r1_tarski(sK1,k2_relat_1(sK2))
% 3.73/0.98      | sK1 = k2_relat_1(sK2) ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_0]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1697,plain,
% 3.73/0.98      ( sK1 = k2_relat_1(sK2)
% 3.73/0.98      | r1_tarski(k2_relat_1(sK2),sK1) != iProver_top
% 3.73/0.98      | r1_tarski(sK1,k2_relat_1(sK2)) != iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_1696]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_377,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_811,plain,
% 3.73/0.98      ( k2_relset_1(sK0,sK1,sK2) != X0
% 3.73/0.98      | k2_relset_1(sK0,sK1,sK2) = sK1
% 3.73/0.98      | sK1 != X0 ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_377]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_950,plain,
% 3.73/0.98      ( k2_relset_1(sK0,sK1,sK2) != k2_relat_1(sK2)
% 3.73/0.98      | k2_relset_1(sK0,sK1,sK2) = sK1
% 3.73/0.98      | sK1 != k2_relat_1(sK2) ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_811]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_11,plain,
% 3.73/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.73/0.98      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.73/0.98      inference(cnf_transformation,[],[f51]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_820,plain,
% 3.73/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.73/0.98      | k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_11]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_4,plain,
% 3.73/0.98      ( ~ v5_relat_1(X0,X1)
% 3.73/0.98      | r1_tarski(k2_relat_1(X0),X1)
% 3.73/0.98      | ~ v1_relat_1(X0) ),
% 3.73/0.98      inference(cnf_transformation,[],[f43]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_9,plain,
% 3.73/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.73/0.98      | v5_relat_1(X0,X2) ),
% 3.73/0.98      inference(cnf_transformation,[],[f49]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_228,plain,
% 3.73/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.73/0.98      | r1_tarski(k2_relat_1(X3),X4)
% 3.73/0.98      | ~ v1_relat_1(X3)
% 3.73/0.98      | X0 != X3
% 3.73/0.98      | X2 != X4 ),
% 3.73/0.98      inference(resolution_lifted,[status(thm)],[c_4,c_9]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_229,plain,
% 3.73/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.73/0.98      | r1_tarski(k2_relat_1(X0),X2)
% 3.73/0.98      | ~ v1_relat_1(X0) ),
% 3.73/0.98      inference(unflattening,[status(thm)],[c_228]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_8,plain,
% 3.73/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.73/0.98      | v1_relat_1(X0) ),
% 3.73/0.98      inference(cnf_transformation,[],[f48]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_233,plain,
% 3.73/0.98      ( r1_tarski(k2_relat_1(X0),X2)
% 3.73/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.73/0.98      inference(global_propositional_subsumption,
% 3.73/0.98                [status(thm)],
% 3.73/0.98                [c_229,c_8]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_234,plain,
% 3.73/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.73/0.98      | r1_tarski(k2_relat_1(X0),X2) ),
% 3.73/0.98      inference(renaming,[status(thm)],[c_233]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_805,plain,
% 3.73/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.73/0.98      | r1_tarski(k2_relat_1(sK2),sK1) ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_234]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_806,plain,
% 3.73/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.73/0.98      | r1_tarski(k2_relat_1(sK2),sK1) = iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_805]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_784,plain,
% 3.73/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.73/0.98      | v1_relat_1(sK2) ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_8]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_785,plain,
% 3.73/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.73/0.98      | v1_relat_1(sK2) = iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_784]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_781,plain,
% 3.73/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.73/0.98      | v1_relat_1(sK3) ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_8]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_782,plain,
% 3.73/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.73/0.98      | v1_relat_1(sK3) = iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_781]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_17,negated_conjecture,
% 3.73/0.98      ( k2_relset_1(sK0,sK1,sK2) != sK1 ),
% 3.73/0.98      inference(cnf_transformation,[],[f63]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(contradiction,plain,
% 3.73/0.98      ( $false ),
% 3.73/0.98      inference(minisat,
% 3.73/0.98                [status(thm)],
% 3.73/0.98                [c_10390,c_1697,c_950,c_820,c_806,c_785,c_782,c_17,c_26,
% 3.73/0.98                 c_24,c_21]) ).
% 3.73/0.98  
% 3.73/0.98  
% 3.73/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.73/0.98  
% 3.73/0.98  ------                               Statistics
% 3.73/0.98  
% 3.73/0.98  ------ General
% 3.73/0.98  
% 3.73/0.98  abstr_ref_over_cycles:                  0
% 3.73/0.98  abstr_ref_under_cycles:                 0
% 3.73/0.98  gc_basic_clause_elim:                   0
% 3.73/0.98  forced_gc_time:                         0
% 3.73/0.98  parsing_time:                           0.009
% 3.73/0.98  unif_index_cands_time:                  0.
% 3.73/0.98  unif_index_add_time:                    0.
% 3.73/0.98  orderings_time:                         0.
% 3.73/0.98  out_proof_time:                         0.012
% 3.73/0.98  total_time:                             0.341
% 3.73/0.98  num_of_symbols:                         50
% 3.73/0.98  num_of_terms:                           12708
% 3.73/0.98  
% 3.73/0.98  ------ Preprocessing
% 3.73/0.98  
% 3.73/0.98  num_of_splits:                          0
% 3.73/0.98  num_of_split_atoms:                     0
% 3.73/0.98  num_of_reused_defs:                     0
% 3.73/0.98  num_eq_ax_congr_red:                    29
% 3.73/0.98  num_of_sem_filtered_clauses:            1
% 3.73/0.98  num_of_subtypes:                        0
% 3.73/0.98  monotx_restored_types:                  0
% 3.73/0.98  sat_num_of_epr_types:                   0
% 3.73/0.98  sat_num_of_non_cyclic_types:            0
% 3.73/0.98  sat_guarded_non_collapsed_types:        0
% 3.73/0.98  num_pure_diseq_elim:                    0
% 3.73/0.98  simp_replaced_by:                       0
% 3.73/0.98  res_preprocessed:                       101
% 3.73/0.98  prep_upred:                             0
% 3.73/0.98  prep_unflattend:                        10
% 3.73/0.98  smt_new_axioms:                         0
% 3.73/0.98  pred_elim_cands:                        4
% 3.73/0.98  pred_elim:                              2
% 3.73/0.98  pred_elim_cl:                           4
% 3.73/0.98  pred_elim_cycles:                       4
% 3.73/0.98  merged_defs:                            0
% 3.73/0.98  merged_defs_ncl:                        0
% 3.73/0.98  bin_hyper_res:                          0
% 3.73/0.98  prep_cycles:                            4
% 3.73/0.98  pred_elim_time:                         0.002
% 3.73/0.98  splitting_time:                         0.
% 3.73/0.98  sem_filter_time:                        0.
% 3.73/0.98  monotx_time:                            0.
% 3.73/0.98  subtype_inf_time:                       0.
% 3.73/0.98  
% 3.73/0.98  ------ Problem properties
% 3.73/0.98  
% 3.73/0.98  clauses:                                18
% 3.73/0.98  conjectures:                            5
% 3.73/0.98  epr:                                    4
% 3.73/0.98  horn:                                   18
% 3.73/0.98  ground:                                 6
% 3.73/0.98  unary:                                  9
% 3.73/0.98  binary:                                 4
% 3.73/0.98  lits:                                   34
% 3.73/0.98  lits_eq:                                8
% 3.73/0.98  fd_pure:                                0
% 3.73/0.98  fd_pseudo:                              0
% 3.73/0.98  fd_cond:                                0
% 3.73/0.98  fd_pseudo_cond:                         1
% 3.73/0.98  ac_symbols:                             0
% 3.73/0.98  
% 3.73/0.98  ------ Propositional Solver
% 3.73/0.98  
% 3.73/0.98  prop_solver_calls:                      29
% 3.73/0.98  prop_fast_solver_calls:                 712
% 3.73/0.98  smt_solver_calls:                       0
% 3.73/0.98  smt_fast_solver_calls:                  0
% 3.73/0.98  prop_num_of_clauses:                    4505
% 3.73/0.98  prop_preprocess_simplified:             9000
% 3.73/0.98  prop_fo_subsumed:                       23
% 3.73/0.98  prop_solver_time:                       0.
% 3.73/0.98  smt_solver_time:                        0.
% 3.73/0.98  smt_fast_solver_time:                   0.
% 3.73/0.98  prop_fast_solver_time:                  0.
% 3.73/0.98  prop_unsat_core_time:                   0.
% 3.73/0.98  
% 3.73/0.98  ------ QBF
% 3.73/0.98  
% 3.73/0.98  qbf_q_res:                              0
% 3.73/0.98  qbf_num_tautologies:                    0
% 3.73/0.98  qbf_prep_cycles:                        0
% 3.73/0.98  
% 3.73/0.98  ------ BMC1
% 3.73/0.98  
% 3.73/0.98  bmc1_current_bound:                     -1
% 3.73/0.98  bmc1_last_solved_bound:                 -1
% 3.73/0.98  bmc1_unsat_core_size:                   -1
% 3.73/0.98  bmc1_unsat_core_parents_size:           -1
% 3.73/0.98  bmc1_merge_next_fun:                    0
% 3.73/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.73/0.98  
% 3.73/0.98  ------ Instantiation
% 3.73/0.98  
% 3.73/0.98  inst_num_of_clauses:                    1167
% 3.73/0.98  inst_num_in_passive:                    461
% 3.73/0.98  inst_num_in_active:                     638
% 3.73/0.98  inst_num_in_unprocessed:                68
% 3.73/0.98  inst_num_of_loops:                      660
% 3.73/0.98  inst_num_of_learning_restarts:          0
% 3.73/0.98  inst_num_moves_active_passive:          21
% 3.73/0.98  inst_lit_activity:                      0
% 3.73/0.98  inst_lit_activity_moves:                1
% 3.73/0.98  inst_num_tautologies:                   0
% 3.73/0.98  inst_num_prop_implied:                  0
% 3.73/0.98  inst_num_existing_simplified:           0
% 3.73/0.98  inst_num_eq_res_simplified:             0
% 3.73/0.98  inst_num_child_elim:                    0
% 3.73/0.98  inst_num_of_dismatching_blockings:      221
% 3.73/0.98  inst_num_of_non_proper_insts:           753
% 3.73/0.98  inst_num_of_duplicates:                 0
% 3.73/0.98  inst_inst_num_from_inst_to_res:         0
% 3.73/0.98  inst_dismatching_checking_time:         0.
% 3.73/0.98  
% 3.73/0.98  ------ Resolution
% 3.73/0.98  
% 3.73/0.98  res_num_of_clauses:                     0
% 3.73/0.98  res_num_in_passive:                     0
% 3.73/0.98  res_num_in_active:                      0
% 3.73/0.98  res_num_of_loops:                       105
% 3.73/0.98  res_forward_subset_subsumed:            41
% 3.73/0.98  res_backward_subset_subsumed:           0
% 3.73/0.98  res_forward_subsumed:                   0
% 3.73/0.98  res_backward_subsumed:                  0
% 3.73/0.98  res_forward_subsumption_resolution:     0
% 3.73/0.98  res_backward_subsumption_resolution:    0
% 3.73/0.98  res_clause_to_clause_subsumption:       1115
% 3.73/0.98  res_orphan_elimination:                 0
% 3.73/0.98  res_tautology_del:                      35
% 3.73/0.98  res_num_eq_res_simplified:              0
% 3.73/0.98  res_num_sel_changes:                    0
% 3.73/0.98  res_moves_from_active_to_pass:          0
% 3.73/0.98  
% 3.73/0.98  ------ Superposition
% 3.73/0.98  
% 3.73/0.98  sup_time_total:                         0.
% 3.73/0.98  sup_time_generating:                    0.
% 3.73/0.98  sup_time_sim_full:                      0.
% 3.73/0.98  sup_time_sim_immed:                     0.
% 3.73/0.98  
% 3.73/0.98  sup_num_of_clauses:                     475
% 3.73/0.98  sup_num_in_active:                      116
% 3.73/0.98  sup_num_in_passive:                     359
% 3.73/0.98  sup_num_of_loops:                       130
% 3.73/0.98  sup_fw_superposition:                   256
% 3.73/0.98  sup_bw_superposition:                   242
% 3.73/0.98  sup_immediate_simplified:               143
% 3.73/0.98  sup_given_eliminated:                   0
% 3.73/0.98  comparisons_done:                       0
% 3.73/0.98  comparisons_avoided:                    0
% 3.73/0.98  
% 3.73/0.98  ------ Simplifications
% 3.73/0.98  
% 3.73/0.98  
% 3.73/0.98  sim_fw_subset_subsumed:                 1
% 3.73/0.98  sim_bw_subset_subsumed:                 0
% 3.73/0.98  sim_fw_subsumed:                        11
% 3.73/0.98  sim_bw_subsumed:                        0
% 3.73/0.98  sim_fw_subsumption_res:                 1
% 3.73/0.98  sim_bw_subsumption_res:                 0
% 3.73/0.98  sim_tautology_del:                      0
% 3.73/0.98  sim_eq_tautology_del:                   4
% 3.73/0.98  sim_eq_res_simp:                        0
% 3.73/0.98  sim_fw_demodulated:                     16
% 3.73/0.98  sim_bw_demodulated:                     17
% 3.73/0.98  sim_light_normalised:                   116
% 3.73/0.98  sim_joinable_taut:                      0
% 3.73/0.98  sim_joinable_simp:                      0
% 3.73/0.98  sim_ac_normalised:                      0
% 3.73/0.98  sim_smt_subsumption:                    0
% 3.73/0.98  
%------------------------------------------------------------------------------
