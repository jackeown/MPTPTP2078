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
% DateTime   : Thu Dec  3 12:01:34 EST 2020

% Result     : Theorem 3.60s
% Output     : CNFRefutation 3.60s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 273 expanded)
%              Number of clauses        :   59 (  78 expanded)
%              Number of leaves         :   17 (  63 expanded)
%              Depth                    :   17
%              Number of atoms          :  348 (1268 expanded)
%              Number of equality atoms :  111 ( 268 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f17,plain,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_1(X3) )
           => ( r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
             => k2_relset_1(X0,X1,X2) = X1 ) ) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f34,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_relset_1(X0,X1,X2) != X1
          & r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f35,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_relset_1(X0,X1,X2) != X1
          & r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f34])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f35,f39,f38])).

fof(f61,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f40])).

fof(f59,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f40])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f32])).

fof(f56,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f58,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f9,axiom,(
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
    inference(ennf_transformation,[],[f9])).

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

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f62,plain,(
    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f40])).

fof(f11,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f55,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f60,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f30])).

fof(f54,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f5,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f13,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f64,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f47,f57])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( r2_xboole_0(X1,X0)
        & r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f63,plain,(
    k2_relset_1(sK0,sK1,sK2) != sK1 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_646,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_644,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_647,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1530,plain,
    ( k1_partfun1(X0,X1,sK0,sK1,X2,sK2) = k5_relat_1(X2,sK2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_644,c_647])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_22,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1792,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK0,sK1,X2,sK2) = k5_relat_1(X2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1530,c_22])).

cnf(c_1793,plain,
    ( k1_partfun1(X0,X1,sK0,sK1,X2,sK2) = k5_relat_1(X2,sK2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_1792])).

cnf(c_1799,plain,
    ( k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) = k5_relat_1(sK3,sK2)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_646,c_1793])).

cnf(c_11,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_17,negated_conjecture,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_266,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) != X0
    | k6_partfun1(sK1) != X3
    | sK1 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_17])).

cnf(c_267,plain,
    ( ~ m1_subset_1(k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k6_partfun1(sK1) = k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) ),
    inference(unflattening,[status(thm)],[c_266])).

cnf(c_14,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_31,plain,
    ( m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_269,plain,
    ( ~ m1_subset_1(k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k6_partfun1(sK1) = k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_267,c_31])).

cnf(c_640,plain,
    ( k6_partfun1(sK1) = k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2)
    | m1_subset_1(k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_269])).

cnf(c_19,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_677,plain,
    ( m1_subset_1(k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_807,plain,
    ( k6_partfun1(sK1) = k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_640,c_21,c_20,c_19,c_18,c_31,c_267,c_677])).

cnf(c_1801,plain,
    ( k5_relat_1(sK3,sK2) = k6_partfun1(sK1)
    | v1_funct_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1799,c_807])).

cnf(c_24,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1921,plain,
    ( k5_relat_1(sK3,sK2) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1801,c_24])).

cnf(c_4,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_653,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1923,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1(sK1)),k2_relat_1(sK2)) = iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1921,c_653])).

cnf(c_5,plain,
    ( k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1924,plain,
    ( r1_tarski(sK1,k2_relat_1(sK2)) = iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1923,c_5])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_652,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1000,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_644,c_652])).

cnf(c_999,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_646,c_652])).

cnf(c_3,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v5_relat_1(X0,X2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_243,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X3),X4)
    | ~ v1_relat_1(X3)
    | X0 != X3
    | X2 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_8])).

cnf(c_244,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_243])).

cnf(c_248,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_244,c_7])).

cnf(c_249,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_248])).

cnf(c_748,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(instantiation,[status(thm)],[c_249])).

cnf(c_843,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(instantiation,[status(thm)],[c_748])).

cnf(c_844,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | r1_tarski(k2_relat_1(sK2),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_843])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_775,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_xboole_0(X0,X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_223,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X3)
    | X3 != X0
    | X2 != X1
    | X1 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_1])).

cnf(c_224,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(unflattening,[status(thm)],[c_223])).

cnf(c_699,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1)
    | ~ r1_tarski(sK1,k2_relat_1(sK2))
    | sK1 = k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_224])).

cnf(c_700,plain,
    ( sK1 = k2_relat_1(sK2)
    | r1_tarski(k2_relat_1(sK2),sK1) != iProver_top
    | r1_tarski(sK1,k2_relat_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_699])).

cnf(c_386,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_676,plain,
    ( k2_relset_1(sK0,sK1,sK2) != X0
    | k2_relset_1(sK0,sK1,sK2) = sK1
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_386])).

cnf(c_691,plain,
    ( k2_relset_1(sK0,sK1,sK2) != k2_relat_1(sK2)
    | k2_relset_1(sK0,sK1,sK2) = sK1
    | sK1 != k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_676])).

cnf(c_16,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) != sK1 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_23,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1924,c_1000,c_999,c_844,c_775,c_700,c_691,c_16,c_23,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:43:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.60/1.08  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.60/1.08  
% 3.60/1.08  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.60/1.08  
% 3.60/1.08  ------  iProver source info
% 3.60/1.08  
% 3.60/1.08  git: date: 2020-06-30 10:37:57 +0100
% 3.60/1.08  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.60/1.08  git: non_committed_changes: false
% 3.60/1.08  git: last_make_outside_of_git: false
% 3.60/1.08  
% 3.60/1.08  ------ 
% 3.60/1.08  
% 3.60/1.08  ------ Input Options
% 3.60/1.08  
% 3.60/1.08  --out_options                           all
% 3.60/1.08  --tptp_safe_out                         true
% 3.60/1.08  --problem_path                          ""
% 3.60/1.08  --include_path                          ""
% 3.60/1.08  --clausifier                            res/vclausify_rel
% 3.60/1.08  --clausifier_options                    ""
% 3.60/1.08  --stdin                                 false
% 3.60/1.08  --stats_out                             all
% 3.60/1.08  
% 3.60/1.08  ------ General Options
% 3.60/1.08  
% 3.60/1.08  --fof                                   false
% 3.60/1.08  --time_out_real                         305.
% 3.60/1.08  --time_out_virtual                      -1.
% 3.60/1.08  --symbol_type_check                     false
% 3.60/1.08  --clausify_out                          false
% 3.60/1.08  --sig_cnt_out                           false
% 3.60/1.08  --trig_cnt_out                          false
% 3.60/1.08  --trig_cnt_out_tolerance                1.
% 3.60/1.08  --trig_cnt_out_sk_spl                   false
% 3.60/1.08  --abstr_cl_out                          false
% 3.60/1.08  
% 3.60/1.08  ------ Global Options
% 3.60/1.08  
% 3.60/1.08  --schedule                              default
% 3.60/1.08  --add_important_lit                     false
% 3.60/1.08  --prop_solver_per_cl                    1000
% 3.60/1.08  --min_unsat_core                        false
% 3.60/1.08  --soft_assumptions                      false
% 3.60/1.08  --soft_lemma_size                       3
% 3.60/1.08  --prop_impl_unit_size                   0
% 3.60/1.08  --prop_impl_unit                        []
% 3.60/1.08  --share_sel_clauses                     true
% 3.60/1.08  --reset_solvers                         false
% 3.60/1.08  --bc_imp_inh                            [conj_cone]
% 3.60/1.08  --conj_cone_tolerance                   3.
% 3.60/1.08  --extra_neg_conj                        none
% 3.60/1.08  --large_theory_mode                     true
% 3.60/1.08  --prolific_symb_bound                   200
% 3.60/1.08  --lt_threshold                          2000
% 3.60/1.08  --clause_weak_htbl                      true
% 3.60/1.08  --gc_record_bc_elim                     false
% 3.60/1.08  
% 3.60/1.08  ------ Preprocessing Options
% 3.60/1.08  
% 3.60/1.08  --preprocessing_flag                    true
% 3.60/1.08  --time_out_prep_mult                    0.1
% 3.60/1.08  --splitting_mode                        input
% 3.60/1.08  --splitting_grd                         true
% 3.60/1.08  --splitting_cvd                         false
% 3.60/1.08  --splitting_cvd_svl                     false
% 3.60/1.08  --splitting_nvd                         32
% 3.60/1.08  --sub_typing                            true
% 3.60/1.08  --prep_gs_sim                           true
% 3.60/1.08  --prep_unflatten                        true
% 3.60/1.08  --prep_res_sim                          true
% 3.60/1.08  --prep_upred                            true
% 3.60/1.08  --prep_sem_filter                       exhaustive
% 3.60/1.08  --prep_sem_filter_out                   false
% 3.60/1.08  --pred_elim                             true
% 3.60/1.08  --res_sim_input                         true
% 3.60/1.08  --eq_ax_congr_red                       true
% 3.60/1.08  --pure_diseq_elim                       true
% 3.60/1.08  --brand_transform                       false
% 3.60/1.08  --non_eq_to_eq                          false
% 3.60/1.08  --prep_def_merge                        true
% 3.60/1.08  --prep_def_merge_prop_impl              false
% 3.60/1.08  --prep_def_merge_mbd                    true
% 3.60/1.08  --prep_def_merge_tr_red                 false
% 3.60/1.08  --prep_def_merge_tr_cl                  false
% 3.60/1.08  --smt_preprocessing                     true
% 3.60/1.08  --smt_ac_axioms                         fast
% 3.60/1.08  --preprocessed_out                      false
% 3.60/1.08  --preprocessed_stats                    false
% 3.60/1.08  
% 3.60/1.08  ------ Abstraction refinement Options
% 3.60/1.08  
% 3.60/1.08  --abstr_ref                             []
% 3.60/1.08  --abstr_ref_prep                        false
% 3.60/1.08  --abstr_ref_until_sat                   false
% 3.60/1.08  --abstr_ref_sig_restrict                funpre
% 3.60/1.08  --abstr_ref_af_restrict_to_split_sk     false
% 3.60/1.08  --abstr_ref_under                       []
% 3.60/1.08  
% 3.60/1.08  ------ SAT Options
% 3.60/1.08  
% 3.60/1.08  --sat_mode                              false
% 3.60/1.08  --sat_fm_restart_options                ""
% 3.60/1.08  --sat_gr_def                            false
% 3.60/1.08  --sat_epr_types                         true
% 3.60/1.08  --sat_non_cyclic_types                  false
% 3.60/1.08  --sat_finite_models                     false
% 3.60/1.08  --sat_fm_lemmas                         false
% 3.60/1.08  --sat_fm_prep                           false
% 3.60/1.08  --sat_fm_uc_incr                        true
% 3.60/1.08  --sat_out_model                         small
% 3.60/1.08  --sat_out_clauses                       false
% 3.60/1.08  
% 3.60/1.08  ------ QBF Options
% 3.60/1.08  
% 3.60/1.08  --qbf_mode                              false
% 3.60/1.08  --qbf_elim_univ                         false
% 3.60/1.08  --qbf_dom_inst                          none
% 3.60/1.08  --qbf_dom_pre_inst                      false
% 3.60/1.08  --qbf_sk_in                             false
% 3.60/1.08  --qbf_pred_elim                         true
% 3.60/1.08  --qbf_split                             512
% 3.60/1.08  
% 3.60/1.08  ------ BMC1 Options
% 3.60/1.08  
% 3.60/1.08  --bmc1_incremental                      false
% 3.60/1.08  --bmc1_axioms                           reachable_all
% 3.60/1.08  --bmc1_min_bound                        0
% 3.60/1.08  --bmc1_max_bound                        -1
% 3.60/1.08  --bmc1_max_bound_default                -1
% 3.60/1.08  --bmc1_symbol_reachability              true
% 3.60/1.08  --bmc1_property_lemmas                  false
% 3.60/1.08  --bmc1_k_induction                      false
% 3.60/1.08  --bmc1_non_equiv_states                 false
% 3.60/1.08  --bmc1_deadlock                         false
% 3.60/1.08  --bmc1_ucm                              false
% 3.60/1.08  --bmc1_add_unsat_core                   none
% 3.60/1.08  --bmc1_unsat_core_children              false
% 3.60/1.08  --bmc1_unsat_core_extrapolate_axioms    false
% 3.60/1.08  --bmc1_out_stat                         full
% 3.60/1.08  --bmc1_ground_init                      false
% 3.60/1.08  --bmc1_pre_inst_next_state              false
% 3.60/1.08  --bmc1_pre_inst_state                   false
% 3.60/1.08  --bmc1_pre_inst_reach_state             false
% 3.60/1.08  --bmc1_out_unsat_core                   false
% 3.60/1.08  --bmc1_aig_witness_out                  false
% 3.60/1.08  --bmc1_verbose                          false
% 3.60/1.08  --bmc1_dump_clauses_tptp                false
% 3.60/1.08  --bmc1_dump_unsat_core_tptp             false
% 3.60/1.08  --bmc1_dump_file                        -
% 3.60/1.08  --bmc1_ucm_expand_uc_limit              128
% 3.60/1.08  --bmc1_ucm_n_expand_iterations          6
% 3.60/1.08  --bmc1_ucm_extend_mode                  1
% 3.60/1.08  --bmc1_ucm_init_mode                    2
% 3.60/1.08  --bmc1_ucm_cone_mode                    none
% 3.60/1.08  --bmc1_ucm_reduced_relation_type        0
% 3.60/1.08  --bmc1_ucm_relax_model                  4
% 3.60/1.08  --bmc1_ucm_full_tr_after_sat            true
% 3.60/1.08  --bmc1_ucm_expand_neg_assumptions       false
% 3.60/1.08  --bmc1_ucm_layered_model                none
% 3.60/1.08  --bmc1_ucm_max_lemma_size               10
% 3.60/1.08  
% 3.60/1.08  ------ AIG Options
% 3.60/1.08  
% 3.60/1.08  --aig_mode                              false
% 3.60/1.08  
% 3.60/1.08  ------ Instantiation Options
% 3.60/1.08  
% 3.60/1.08  --instantiation_flag                    true
% 3.60/1.08  --inst_sos_flag                         true
% 3.60/1.08  --inst_sos_phase                        true
% 3.60/1.08  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.60/1.08  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.60/1.08  --inst_lit_sel_side                     num_symb
% 3.60/1.08  --inst_solver_per_active                1400
% 3.60/1.08  --inst_solver_calls_frac                1.
% 3.60/1.08  --inst_passive_queue_type               priority_queues
% 3.60/1.08  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.60/1.08  --inst_passive_queues_freq              [25;2]
% 3.60/1.08  --inst_dismatching                      true
% 3.60/1.08  --inst_eager_unprocessed_to_passive     true
% 3.60/1.08  --inst_prop_sim_given                   true
% 3.60/1.08  --inst_prop_sim_new                     false
% 3.60/1.08  --inst_subs_new                         false
% 3.60/1.08  --inst_eq_res_simp                      false
% 3.60/1.08  --inst_subs_given                       false
% 3.60/1.08  --inst_orphan_elimination               true
% 3.60/1.08  --inst_learning_loop_flag               true
% 3.60/1.08  --inst_learning_start                   3000
% 3.60/1.08  --inst_learning_factor                  2
% 3.60/1.08  --inst_start_prop_sim_after_learn       3
% 3.60/1.08  --inst_sel_renew                        solver
% 3.60/1.08  --inst_lit_activity_flag                true
% 3.60/1.08  --inst_restr_to_given                   false
% 3.60/1.08  --inst_activity_threshold               500
% 3.60/1.08  --inst_out_proof                        true
% 3.60/1.08  
% 3.60/1.08  ------ Resolution Options
% 3.60/1.08  
% 3.60/1.08  --resolution_flag                       true
% 3.60/1.08  --res_lit_sel                           adaptive
% 3.60/1.08  --res_lit_sel_side                      none
% 3.60/1.08  --res_ordering                          kbo
% 3.60/1.08  --res_to_prop_solver                    active
% 3.60/1.08  --res_prop_simpl_new                    false
% 3.60/1.08  --res_prop_simpl_given                  true
% 3.60/1.08  --res_passive_queue_type                priority_queues
% 3.60/1.08  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.60/1.08  --res_passive_queues_freq               [15;5]
% 3.60/1.08  --res_forward_subs                      full
% 3.60/1.08  --res_backward_subs                     full
% 3.60/1.08  --res_forward_subs_resolution           true
% 3.60/1.08  --res_backward_subs_resolution          true
% 3.60/1.08  --res_orphan_elimination                true
% 3.60/1.08  --res_time_limit                        2.
% 3.60/1.08  --res_out_proof                         true
% 3.60/1.08  
% 3.60/1.08  ------ Superposition Options
% 3.60/1.08  
% 3.60/1.08  --superposition_flag                    true
% 3.60/1.08  --sup_passive_queue_type                priority_queues
% 3.60/1.08  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.60/1.08  --sup_passive_queues_freq               [8;1;4]
% 3.60/1.08  --demod_completeness_check              fast
% 3.60/1.08  --demod_use_ground                      true
% 3.60/1.08  --sup_to_prop_solver                    passive
% 3.60/1.08  --sup_prop_simpl_new                    true
% 3.60/1.08  --sup_prop_simpl_given                  true
% 3.60/1.08  --sup_fun_splitting                     true
% 3.60/1.08  --sup_smt_interval                      50000
% 3.60/1.08  
% 3.60/1.08  ------ Superposition Simplification Setup
% 3.60/1.08  
% 3.60/1.08  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.60/1.08  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.60/1.08  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.60/1.08  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.60/1.08  --sup_full_triv                         [TrivRules;PropSubs]
% 3.60/1.08  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.60/1.08  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.60/1.08  --sup_immed_triv                        [TrivRules]
% 3.60/1.08  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.60/1.08  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.60/1.08  --sup_immed_bw_main                     []
% 3.60/1.08  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.60/1.08  --sup_input_triv                        [Unflattening;TrivRules]
% 3.60/1.08  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.60/1.08  --sup_input_bw                          []
% 3.60/1.08  
% 3.60/1.08  ------ Combination Options
% 3.60/1.08  
% 3.60/1.08  --comb_res_mult                         3
% 3.60/1.08  --comb_sup_mult                         2
% 3.60/1.08  --comb_inst_mult                        10
% 3.60/1.08  
% 3.60/1.08  ------ Debug Options
% 3.60/1.08  
% 3.60/1.08  --dbg_backtrace                         false
% 3.60/1.08  --dbg_dump_prop_clauses                 false
% 3.60/1.08  --dbg_dump_prop_clauses_file            -
% 3.60/1.08  --dbg_out_stat                          false
% 3.60/1.08  ------ Parsing...
% 3.60/1.08  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.60/1.08  
% 3.60/1.08  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.60/1.08  
% 3.60/1.08  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.60/1.08  
% 3.60/1.08  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.60/1.08  ------ Proving...
% 3.60/1.08  ------ Problem Properties 
% 3.60/1.08  
% 3.60/1.08  
% 3.60/1.08  clauses                                 17
% 3.60/1.08  conjectures                             5
% 3.60/1.08  EPR                                     3
% 3.60/1.08  Horn                                    17
% 3.60/1.08  unary                                   8
% 3.60/1.08  binary                                  4
% 3.60/1.08  lits                                    37
% 3.60/1.08  lits eq                                 7
% 3.60/1.08  fd_pure                                 0
% 3.60/1.08  fd_pseudo                               0
% 3.60/1.08  fd_cond                                 0
% 3.60/1.08  fd_pseudo_cond                          1
% 3.60/1.08  AC symbols                              0
% 3.60/1.08  
% 3.60/1.08  ------ Schedule dynamic 5 is on 
% 3.60/1.08  
% 3.60/1.08  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.60/1.08  
% 3.60/1.08  
% 3.60/1.08  ------ 
% 3.60/1.08  Current options:
% 3.60/1.08  ------ 
% 3.60/1.08  
% 3.60/1.08  ------ Input Options
% 3.60/1.08  
% 3.60/1.08  --out_options                           all
% 3.60/1.08  --tptp_safe_out                         true
% 3.60/1.08  --problem_path                          ""
% 3.60/1.08  --include_path                          ""
% 3.60/1.08  --clausifier                            res/vclausify_rel
% 3.60/1.08  --clausifier_options                    ""
% 3.60/1.08  --stdin                                 false
% 3.60/1.08  --stats_out                             all
% 3.60/1.08  
% 3.60/1.08  ------ General Options
% 3.60/1.08  
% 3.60/1.08  --fof                                   false
% 3.60/1.08  --time_out_real                         305.
% 3.60/1.08  --time_out_virtual                      -1.
% 3.60/1.08  --symbol_type_check                     false
% 3.60/1.08  --clausify_out                          false
% 3.60/1.08  --sig_cnt_out                           false
% 3.60/1.08  --trig_cnt_out                          false
% 3.60/1.08  --trig_cnt_out_tolerance                1.
% 3.60/1.08  --trig_cnt_out_sk_spl                   false
% 3.60/1.08  --abstr_cl_out                          false
% 3.60/1.08  
% 3.60/1.08  ------ Global Options
% 3.60/1.08  
% 3.60/1.08  --schedule                              default
% 3.60/1.08  --add_important_lit                     false
% 3.60/1.08  --prop_solver_per_cl                    1000
% 3.60/1.08  --min_unsat_core                        false
% 3.60/1.08  --soft_assumptions                      false
% 3.60/1.08  --soft_lemma_size                       3
% 3.60/1.08  --prop_impl_unit_size                   0
% 3.60/1.08  --prop_impl_unit                        []
% 3.60/1.08  --share_sel_clauses                     true
% 3.60/1.08  --reset_solvers                         false
% 3.60/1.08  --bc_imp_inh                            [conj_cone]
% 3.60/1.08  --conj_cone_tolerance                   3.
% 3.60/1.08  --extra_neg_conj                        none
% 3.60/1.08  --large_theory_mode                     true
% 3.60/1.08  --prolific_symb_bound                   200
% 3.60/1.08  --lt_threshold                          2000
% 3.60/1.08  --clause_weak_htbl                      true
% 3.60/1.08  --gc_record_bc_elim                     false
% 3.60/1.08  
% 3.60/1.08  ------ Preprocessing Options
% 3.60/1.08  
% 3.60/1.08  --preprocessing_flag                    true
% 3.60/1.08  --time_out_prep_mult                    0.1
% 3.60/1.08  --splitting_mode                        input
% 3.60/1.08  --splitting_grd                         true
% 3.60/1.08  --splitting_cvd                         false
% 3.60/1.08  --splitting_cvd_svl                     false
% 3.60/1.08  --splitting_nvd                         32
% 3.60/1.08  --sub_typing                            true
% 3.60/1.08  --prep_gs_sim                           true
% 3.60/1.08  --prep_unflatten                        true
% 3.60/1.08  --prep_res_sim                          true
% 3.60/1.08  --prep_upred                            true
% 3.60/1.08  --prep_sem_filter                       exhaustive
% 3.60/1.08  --prep_sem_filter_out                   false
% 3.60/1.08  --pred_elim                             true
% 3.60/1.08  --res_sim_input                         true
% 3.60/1.08  --eq_ax_congr_red                       true
% 3.60/1.08  --pure_diseq_elim                       true
% 3.60/1.08  --brand_transform                       false
% 3.60/1.08  --non_eq_to_eq                          false
% 3.60/1.08  --prep_def_merge                        true
% 3.60/1.08  --prep_def_merge_prop_impl              false
% 3.60/1.08  --prep_def_merge_mbd                    true
% 3.60/1.08  --prep_def_merge_tr_red                 false
% 3.60/1.08  --prep_def_merge_tr_cl                  false
% 3.60/1.08  --smt_preprocessing                     true
% 3.60/1.08  --smt_ac_axioms                         fast
% 3.60/1.08  --preprocessed_out                      false
% 3.60/1.08  --preprocessed_stats                    false
% 3.60/1.08  
% 3.60/1.08  ------ Abstraction refinement Options
% 3.60/1.08  
% 3.60/1.08  --abstr_ref                             []
% 3.60/1.08  --abstr_ref_prep                        false
% 3.60/1.08  --abstr_ref_until_sat                   false
% 3.60/1.08  --abstr_ref_sig_restrict                funpre
% 3.60/1.08  --abstr_ref_af_restrict_to_split_sk     false
% 3.60/1.08  --abstr_ref_under                       []
% 3.60/1.08  
% 3.60/1.08  ------ SAT Options
% 3.60/1.08  
% 3.60/1.08  --sat_mode                              false
% 3.60/1.08  --sat_fm_restart_options                ""
% 3.60/1.08  --sat_gr_def                            false
% 3.60/1.08  --sat_epr_types                         true
% 3.60/1.08  --sat_non_cyclic_types                  false
% 3.60/1.08  --sat_finite_models                     false
% 3.60/1.08  --sat_fm_lemmas                         false
% 3.60/1.08  --sat_fm_prep                           false
% 3.60/1.08  --sat_fm_uc_incr                        true
% 3.60/1.08  --sat_out_model                         small
% 3.60/1.08  --sat_out_clauses                       false
% 3.60/1.08  
% 3.60/1.08  ------ QBF Options
% 3.60/1.08  
% 3.60/1.08  --qbf_mode                              false
% 3.60/1.08  --qbf_elim_univ                         false
% 3.60/1.08  --qbf_dom_inst                          none
% 3.60/1.08  --qbf_dom_pre_inst                      false
% 3.60/1.08  --qbf_sk_in                             false
% 3.60/1.08  --qbf_pred_elim                         true
% 3.60/1.08  --qbf_split                             512
% 3.60/1.08  
% 3.60/1.08  ------ BMC1 Options
% 3.60/1.08  
% 3.60/1.08  --bmc1_incremental                      false
% 3.60/1.08  --bmc1_axioms                           reachable_all
% 3.60/1.08  --bmc1_min_bound                        0
% 3.60/1.08  --bmc1_max_bound                        -1
% 3.60/1.08  --bmc1_max_bound_default                -1
% 3.60/1.08  --bmc1_symbol_reachability              true
% 3.60/1.08  --bmc1_property_lemmas                  false
% 3.60/1.08  --bmc1_k_induction                      false
% 3.60/1.08  --bmc1_non_equiv_states                 false
% 3.60/1.08  --bmc1_deadlock                         false
% 3.60/1.08  --bmc1_ucm                              false
% 3.60/1.08  --bmc1_add_unsat_core                   none
% 3.60/1.08  --bmc1_unsat_core_children              false
% 3.60/1.08  --bmc1_unsat_core_extrapolate_axioms    false
% 3.60/1.08  --bmc1_out_stat                         full
% 3.60/1.08  --bmc1_ground_init                      false
% 3.60/1.08  --bmc1_pre_inst_next_state              false
% 3.60/1.08  --bmc1_pre_inst_state                   false
% 3.60/1.08  --bmc1_pre_inst_reach_state             false
% 3.60/1.08  --bmc1_out_unsat_core                   false
% 3.60/1.08  --bmc1_aig_witness_out                  false
% 3.60/1.08  --bmc1_verbose                          false
% 3.60/1.08  --bmc1_dump_clauses_tptp                false
% 3.60/1.08  --bmc1_dump_unsat_core_tptp             false
% 3.60/1.08  --bmc1_dump_file                        -
% 3.60/1.08  --bmc1_ucm_expand_uc_limit              128
% 3.60/1.08  --bmc1_ucm_n_expand_iterations          6
% 3.60/1.08  --bmc1_ucm_extend_mode                  1
% 3.60/1.08  --bmc1_ucm_init_mode                    2
% 3.60/1.08  --bmc1_ucm_cone_mode                    none
% 3.60/1.08  --bmc1_ucm_reduced_relation_type        0
% 3.60/1.08  --bmc1_ucm_relax_model                  4
% 3.60/1.08  --bmc1_ucm_full_tr_after_sat            true
% 3.60/1.08  --bmc1_ucm_expand_neg_assumptions       false
% 3.60/1.08  --bmc1_ucm_layered_model                none
% 3.60/1.08  --bmc1_ucm_max_lemma_size               10
% 3.60/1.08  
% 3.60/1.08  ------ AIG Options
% 3.60/1.08  
% 3.60/1.08  --aig_mode                              false
% 3.60/1.08  
% 3.60/1.08  ------ Instantiation Options
% 3.60/1.08  
% 3.60/1.08  --instantiation_flag                    true
% 3.60/1.08  --inst_sos_flag                         true
% 3.60/1.08  --inst_sos_phase                        true
% 3.60/1.08  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.60/1.08  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.60/1.08  --inst_lit_sel_side                     none
% 3.60/1.08  --inst_solver_per_active                1400
% 3.60/1.08  --inst_solver_calls_frac                1.
% 3.60/1.08  --inst_passive_queue_type               priority_queues
% 3.60/1.08  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.60/1.08  --inst_passive_queues_freq              [25;2]
% 3.60/1.08  --inst_dismatching                      true
% 3.60/1.08  --inst_eager_unprocessed_to_passive     true
% 3.60/1.08  --inst_prop_sim_given                   true
% 3.60/1.08  --inst_prop_sim_new                     false
% 3.60/1.08  --inst_subs_new                         false
% 3.60/1.08  --inst_eq_res_simp                      false
% 3.60/1.08  --inst_subs_given                       false
% 3.60/1.08  --inst_orphan_elimination               true
% 3.60/1.08  --inst_learning_loop_flag               true
% 3.60/1.08  --inst_learning_start                   3000
% 3.60/1.08  --inst_learning_factor                  2
% 3.60/1.08  --inst_start_prop_sim_after_learn       3
% 3.60/1.08  --inst_sel_renew                        solver
% 3.60/1.08  --inst_lit_activity_flag                true
% 3.60/1.08  --inst_restr_to_given                   false
% 3.60/1.08  --inst_activity_threshold               500
% 3.60/1.08  --inst_out_proof                        true
% 3.60/1.08  
% 3.60/1.08  ------ Resolution Options
% 3.60/1.08  
% 3.60/1.08  --resolution_flag                       false
% 3.60/1.08  --res_lit_sel                           adaptive
% 3.60/1.08  --res_lit_sel_side                      none
% 3.60/1.08  --res_ordering                          kbo
% 3.60/1.08  --res_to_prop_solver                    active
% 3.60/1.08  --res_prop_simpl_new                    false
% 3.60/1.08  --res_prop_simpl_given                  true
% 3.60/1.08  --res_passive_queue_type                priority_queues
% 3.60/1.08  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.60/1.08  --res_passive_queues_freq               [15;5]
% 3.60/1.08  --res_forward_subs                      full
% 3.60/1.08  --res_backward_subs                     full
% 3.60/1.08  --res_forward_subs_resolution           true
% 3.60/1.08  --res_backward_subs_resolution          true
% 3.60/1.08  --res_orphan_elimination                true
% 3.60/1.08  --res_time_limit                        2.
% 3.60/1.08  --res_out_proof                         true
% 3.60/1.08  
% 3.60/1.08  ------ Superposition Options
% 3.60/1.08  
% 3.60/1.08  --superposition_flag                    true
% 3.60/1.08  --sup_passive_queue_type                priority_queues
% 3.60/1.08  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.60/1.08  --sup_passive_queues_freq               [8;1;4]
% 3.60/1.08  --demod_completeness_check              fast
% 3.60/1.08  --demod_use_ground                      true
% 3.60/1.08  --sup_to_prop_solver                    passive
% 3.60/1.08  --sup_prop_simpl_new                    true
% 3.60/1.08  --sup_prop_simpl_given                  true
% 3.60/1.08  --sup_fun_splitting                     true
% 3.60/1.08  --sup_smt_interval                      50000
% 3.60/1.08  
% 3.60/1.08  ------ Superposition Simplification Setup
% 3.60/1.08  
% 3.60/1.08  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.60/1.08  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.60/1.08  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.60/1.08  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.60/1.08  --sup_full_triv                         [TrivRules;PropSubs]
% 3.60/1.08  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.60/1.08  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.60/1.08  --sup_immed_triv                        [TrivRules]
% 3.60/1.08  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.60/1.08  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.60/1.08  --sup_immed_bw_main                     []
% 3.60/1.08  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.60/1.08  --sup_input_triv                        [Unflattening;TrivRules]
% 3.60/1.08  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.60/1.08  --sup_input_bw                          []
% 3.60/1.08  
% 3.60/1.08  ------ Combination Options
% 3.60/1.08  
% 3.60/1.08  --comb_res_mult                         3
% 3.60/1.08  --comb_sup_mult                         2
% 3.60/1.08  --comb_inst_mult                        10
% 3.60/1.08  
% 3.60/1.08  ------ Debug Options
% 3.60/1.08  
% 3.60/1.08  --dbg_backtrace                         false
% 3.60/1.08  --dbg_dump_prop_clauses                 false
% 3.60/1.08  --dbg_dump_prop_clauses_file            -
% 3.60/1.08  --dbg_out_stat                          false
% 3.60/1.08  
% 3.60/1.08  
% 3.60/1.08  
% 3.60/1.08  
% 3.60/1.08  ------ Proving...
% 3.60/1.08  
% 3.60/1.08  
% 3.60/1.08  % SZS status Theorem for theBenchmark.p
% 3.60/1.08  
% 3.60/1.08  % SZS output start CNFRefutation for theBenchmark.p
% 3.60/1.08  
% 3.60/1.08  fof(f14,conjecture,(
% 3.60/1.08    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 3.60/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.60/1.08  
% 3.60/1.08  fof(f15,negated_conjecture,(
% 3.60/1.08    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 3.60/1.08    inference(negated_conjecture,[],[f14])).
% 3.60/1.08  
% 3.60/1.08  fof(f17,plain,(
% 3.60/1.08    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 3.60/1.08    inference(pure_predicate_removal,[],[f15])).
% 3.60/1.08  
% 3.60/1.08  fof(f34,plain,(
% 3.60/1.08    ? [X0,X1,X2] : (? [X3] : ((k2_relset_1(X0,X1,X2) != X1 & r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 3.60/1.08    inference(ennf_transformation,[],[f17])).
% 3.60/1.08  
% 3.60/1.08  fof(f35,plain,(
% 3.60/1.08    ? [X0,X1,X2] : (? [X3] : (k2_relset_1(X0,X1,X2) != X1 & r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 3.60/1.08    inference(flattening,[],[f34])).
% 3.60/1.08  
% 3.60/1.08  fof(f39,plain,(
% 3.60/1.08    ( ! [X2,X0,X1] : (? [X3] : (k2_relset_1(X0,X1,X2) != X1 & r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) => (k2_relset_1(X0,X1,X2) != X1 & r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,sK3,X2),k6_partfun1(X1)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(sK3))) )),
% 3.60/1.08    introduced(choice_axiom,[])).
% 3.60/1.08  
% 3.60/1.08  fof(f38,plain,(
% 3.60/1.08    ? [X0,X1,X2] : (? [X3] : (k2_relset_1(X0,X1,X2) != X1 & r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (? [X3] : (k2_relset_1(sK0,sK1,sK2) != sK1 & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK0,sK0,sK1,X3,sK2),k6_partfun1(sK1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2))),
% 3.60/1.08    introduced(choice_axiom,[])).
% 3.60/1.08  
% 3.60/1.08  fof(f40,plain,(
% 3.60/1.08    (k2_relset_1(sK0,sK1,sK2) != sK1 & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k6_partfun1(sK1)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2)),
% 3.60/1.08    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f35,f39,f38])).
% 3.60/1.08  
% 3.60/1.08  fof(f61,plain,(
% 3.60/1.08    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 3.60/1.08    inference(cnf_transformation,[],[f40])).
% 3.60/1.08  
% 3.60/1.08  fof(f59,plain,(
% 3.60/1.08    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.60/1.08    inference(cnf_transformation,[],[f40])).
% 3.60/1.08  
% 3.60/1.08  fof(f12,axiom,(
% 3.60/1.08    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.60/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.60/1.08  
% 3.60/1.08  fof(f32,plain,(
% 3.60/1.08    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.60/1.08    inference(ennf_transformation,[],[f12])).
% 3.60/1.08  
% 3.60/1.08  fof(f33,plain,(
% 3.60/1.08    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.60/1.08    inference(flattening,[],[f32])).
% 3.60/1.08  
% 3.60/1.08  fof(f56,plain,(
% 3.60/1.08    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.60/1.08    inference(cnf_transformation,[],[f33])).
% 3.60/1.08  
% 3.60/1.08  fof(f58,plain,(
% 3.60/1.08    v1_funct_1(sK2)),
% 3.60/1.08    inference(cnf_transformation,[],[f40])).
% 3.60/1.08  
% 3.60/1.08  fof(f9,axiom,(
% 3.60/1.08    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.60/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.60/1.08  
% 3.60/1.08  fof(f28,plain,(
% 3.60/1.08    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.60/1.08    inference(ennf_transformation,[],[f9])).
% 3.60/1.08  
% 3.60/1.08  fof(f29,plain,(
% 3.60/1.08    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.60/1.08    inference(flattening,[],[f28])).
% 3.60/1.08  
% 3.60/1.08  fof(f37,plain,(
% 3.60/1.08    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.60/1.08    inference(nnf_transformation,[],[f29])).
% 3.60/1.08  
% 3.60/1.08  fof(f51,plain,(
% 3.60/1.08    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.60/1.08    inference(cnf_transformation,[],[f37])).
% 3.60/1.08  
% 3.60/1.08  fof(f62,plain,(
% 3.60/1.08    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k6_partfun1(sK1))),
% 3.60/1.08    inference(cnf_transformation,[],[f40])).
% 3.60/1.08  
% 3.60/1.08  fof(f11,axiom,(
% 3.60/1.08    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 3.60/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.60/1.08  
% 3.60/1.08  fof(f18,plain,(
% 3.60/1.08    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.60/1.08    inference(pure_predicate_removal,[],[f11])).
% 3.60/1.08  
% 3.60/1.08  fof(f55,plain,(
% 3.60/1.08    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.60/1.08    inference(cnf_transformation,[],[f18])).
% 3.60/1.08  
% 3.60/1.08  fof(f60,plain,(
% 3.60/1.08    v1_funct_1(sK3)),
% 3.60/1.08    inference(cnf_transformation,[],[f40])).
% 3.60/1.08  
% 3.60/1.08  fof(f10,axiom,(
% 3.60/1.08    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 3.60/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.60/1.08  
% 3.60/1.08  fof(f30,plain,(
% 3.60/1.08    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.60/1.08    inference(ennf_transformation,[],[f10])).
% 3.60/1.08  
% 3.60/1.08  fof(f31,plain,(
% 3.60/1.08    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.60/1.08    inference(flattening,[],[f30])).
% 3.60/1.08  
% 3.60/1.08  fof(f54,plain,(
% 3.60/1.08    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.60/1.08    inference(cnf_transformation,[],[f31])).
% 3.60/1.08  
% 3.60/1.08  fof(f4,axiom,(
% 3.60/1.08    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 3.60/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.60/1.08  
% 3.60/1.08  fof(f24,plain,(
% 3.60/1.08    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.60/1.08    inference(ennf_transformation,[],[f4])).
% 3.60/1.08  
% 3.60/1.08  fof(f45,plain,(
% 3.60/1.08    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.60/1.08    inference(cnf_transformation,[],[f24])).
% 3.60/1.08  
% 3.60/1.08  fof(f5,axiom,(
% 3.60/1.08    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.60/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.60/1.08  
% 3.60/1.08  fof(f47,plain,(
% 3.60/1.08    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 3.60/1.08    inference(cnf_transformation,[],[f5])).
% 3.60/1.08  
% 3.60/1.08  fof(f13,axiom,(
% 3.60/1.08    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.60/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.60/1.08  
% 3.60/1.08  fof(f57,plain,(
% 3.60/1.08    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.60/1.08    inference(cnf_transformation,[],[f13])).
% 3.60/1.08  
% 3.60/1.08  fof(f64,plain,(
% 3.60/1.08    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 3.60/1.08    inference(definition_unfolding,[],[f47,f57])).
% 3.60/1.08  
% 3.60/1.08  fof(f6,axiom,(
% 3.60/1.08    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.60/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.60/1.08  
% 3.60/1.08  fof(f25,plain,(
% 3.60/1.08    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.60/1.08    inference(ennf_transformation,[],[f6])).
% 3.60/1.08  
% 3.60/1.08  fof(f48,plain,(
% 3.60/1.08    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.60/1.08    inference(cnf_transformation,[],[f25])).
% 3.60/1.08  
% 3.60/1.08  fof(f3,axiom,(
% 3.60/1.08    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.60/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.60/1.08  
% 3.60/1.08  fof(f23,plain,(
% 3.60/1.08    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.60/1.08    inference(ennf_transformation,[],[f3])).
% 3.60/1.08  
% 3.60/1.08  fof(f36,plain,(
% 3.60/1.08    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.60/1.08    inference(nnf_transformation,[],[f23])).
% 3.60/1.08  
% 3.60/1.08  fof(f43,plain,(
% 3.60/1.08    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.60/1.08    inference(cnf_transformation,[],[f36])).
% 3.60/1.08  
% 3.60/1.08  fof(f7,axiom,(
% 3.60/1.08    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.60/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.60/1.08  
% 3.60/1.08  fof(f19,plain,(
% 3.60/1.08    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.60/1.08    inference(pure_predicate_removal,[],[f7])).
% 3.60/1.08  
% 3.60/1.08  fof(f26,plain,(
% 3.60/1.08    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.60/1.08    inference(ennf_transformation,[],[f19])).
% 3.60/1.08  
% 3.60/1.08  fof(f49,plain,(
% 3.60/1.08    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.60/1.08    inference(cnf_transformation,[],[f26])).
% 3.60/1.08  
% 3.60/1.08  fof(f8,axiom,(
% 3.60/1.08    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.60/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.60/1.08  
% 3.60/1.08  fof(f27,plain,(
% 3.60/1.08    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.60/1.08    inference(ennf_transformation,[],[f8])).
% 3.60/1.08  
% 3.60/1.08  fof(f50,plain,(
% 3.60/1.08    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.60/1.08    inference(cnf_transformation,[],[f27])).
% 3.60/1.08  
% 3.60/1.08  fof(f1,axiom,(
% 3.60/1.08    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 3.60/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.60/1.08  
% 3.60/1.08  fof(f16,plain,(
% 3.60/1.08    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) => r2_xboole_0(X0,X1))),
% 3.60/1.08    inference(unused_predicate_definition_removal,[],[f1])).
% 3.60/1.08  
% 3.60/1.08  fof(f20,plain,(
% 3.60/1.08    ! [X0,X1] : (r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1)))),
% 3.60/1.08    inference(ennf_transformation,[],[f16])).
% 3.60/1.08  
% 3.60/1.08  fof(f21,plain,(
% 3.60/1.08    ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1))),
% 3.60/1.08    inference(flattening,[],[f20])).
% 3.60/1.08  
% 3.60/1.08  fof(f41,plain,(
% 3.60/1.08    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 3.60/1.08    inference(cnf_transformation,[],[f21])).
% 3.60/1.08  
% 3.60/1.08  fof(f2,axiom,(
% 3.60/1.08    ! [X0,X1] : ~(r2_xboole_0(X1,X0) & r1_tarski(X0,X1))),
% 3.60/1.08    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.60/1.08  
% 3.60/1.08  fof(f22,plain,(
% 3.60/1.08    ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r1_tarski(X0,X1))),
% 3.60/1.08    inference(ennf_transformation,[],[f2])).
% 3.60/1.08  
% 3.60/1.08  fof(f42,plain,(
% 3.60/1.08    ( ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.60/1.08    inference(cnf_transformation,[],[f22])).
% 3.60/1.08  
% 3.60/1.08  fof(f63,plain,(
% 3.60/1.08    k2_relset_1(sK0,sK1,sK2) != sK1),
% 3.60/1.08    inference(cnf_transformation,[],[f40])).
% 3.60/1.08  
% 3.60/1.08  cnf(c_18,negated_conjecture,
% 3.60/1.08      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 3.60/1.08      inference(cnf_transformation,[],[f61]) ).
% 3.60/1.08  
% 3.60/1.08  cnf(c_646,plain,
% 3.60/1.08      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.60/1.08      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.60/1.08  
% 3.60/1.08  cnf(c_20,negated_conjecture,
% 3.60/1.08      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.60/1.08      inference(cnf_transformation,[],[f59]) ).
% 3.60/1.08  
% 3.60/1.08  cnf(c_644,plain,
% 3.60/1.08      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.60/1.08      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.60/1.08  
% 3.60/1.08  cnf(c_15,plain,
% 3.60/1.08      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.60/1.08      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.60/1.08      | ~ v1_funct_1(X0)
% 3.60/1.08      | ~ v1_funct_1(X3)
% 3.60/1.08      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.60/1.08      inference(cnf_transformation,[],[f56]) ).
% 3.60/1.08  
% 3.60/1.08  cnf(c_647,plain,
% 3.60/1.08      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 3.60/1.08      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 3.60/1.08      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.60/1.08      | v1_funct_1(X5) != iProver_top
% 3.60/1.08      | v1_funct_1(X4) != iProver_top ),
% 3.60/1.08      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.60/1.08  
% 3.60/1.08  cnf(c_1530,plain,
% 3.60/1.08      ( k1_partfun1(X0,X1,sK0,sK1,X2,sK2) = k5_relat_1(X2,sK2)
% 3.60/1.08      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.60/1.08      | v1_funct_1(X2) != iProver_top
% 3.60/1.08      | v1_funct_1(sK2) != iProver_top ),
% 3.60/1.08      inference(superposition,[status(thm)],[c_644,c_647]) ).
% 3.60/1.08  
% 3.60/1.08  cnf(c_21,negated_conjecture,
% 3.60/1.08      ( v1_funct_1(sK2) ),
% 3.60/1.08      inference(cnf_transformation,[],[f58]) ).
% 3.60/1.08  
% 3.60/1.08  cnf(c_22,plain,
% 3.60/1.08      ( v1_funct_1(sK2) = iProver_top ),
% 3.60/1.08      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.60/1.08  
% 3.60/1.08  cnf(c_1792,plain,
% 3.60/1.08      ( v1_funct_1(X2) != iProver_top
% 3.60/1.08      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.60/1.08      | k1_partfun1(X0,X1,sK0,sK1,X2,sK2) = k5_relat_1(X2,sK2) ),
% 3.60/1.08      inference(global_propositional_subsumption,
% 3.60/1.08                [status(thm)],
% 3.60/1.08                [c_1530,c_22]) ).
% 3.60/1.08  
% 3.60/1.08  cnf(c_1793,plain,
% 3.60/1.08      ( k1_partfun1(X0,X1,sK0,sK1,X2,sK2) = k5_relat_1(X2,sK2)
% 3.60/1.08      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.60/1.08      | v1_funct_1(X2) != iProver_top ),
% 3.60/1.08      inference(renaming,[status(thm)],[c_1792]) ).
% 3.60/1.08  
% 3.60/1.08  cnf(c_1799,plain,
% 3.60/1.08      ( k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) = k5_relat_1(sK3,sK2)
% 3.60/1.08      | v1_funct_1(sK3) != iProver_top ),
% 3.60/1.08      inference(superposition,[status(thm)],[c_646,c_1793]) ).
% 3.60/1.08  
% 3.60/1.08  cnf(c_11,plain,
% 3.60/1.08      ( ~ r2_relset_1(X0,X1,X2,X3)
% 3.60/1.08      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.60/1.08      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.60/1.08      | X3 = X2 ),
% 3.60/1.08      inference(cnf_transformation,[],[f51]) ).
% 3.60/1.08  
% 3.60/1.08  cnf(c_17,negated_conjecture,
% 3.60/1.08      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k6_partfun1(sK1)) ),
% 3.60/1.08      inference(cnf_transformation,[],[f62]) ).
% 3.60/1.08  
% 3.60/1.08  cnf(c_266,plain,
% 3.60/1.08      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.60/1.08      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.60/1.08      | X3 = X0
% 3.60/1.08      | k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) != X0
% 3.60/1.08      | k6_partfun1(sK1) != X3
% 3.60/1.08      | sK1 != X2
% 3.60/1.08      | sK1 != X1 ),
% 3.60/1.08      inference(resolution_lifted,[status(thm)],[c_11,c_17]) ).
% 3.60/1.08  
% 3.60/1.08  cnf(c_267,plain,
% 3.60/1.08      ( ~ m1_subset_1(k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.60/1.08      | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.60/1.08      | k6_partfun1(sK1) = k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) ),
% 3.60/1.08      inference(unflattening,[status(thm)],[c_266]) ).
% 3.60/1.08  
% 3.60/1.08  cnf(c_14,plain,
% 3.60/1.08      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.60/1.08      inference(cnf_transformation,[],[f55]) ).
% 3.60/1.08  
% 3.60/1.08  cnf(c_31,plain,
% 3.60/1.08      ( m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 3.60/1.08      inference(instantiation,[status(thm)],[c_14]) ).
% 3.60/1.08  
% 3.60/1.08  cnf(c_269,plain,
% 3.60/1.08      ( ~ m1_subset_1(k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.60/1.08      | k6_partfun1(sK1) = k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) ),
% 3.60/1.08      inference(global_propositional_subsumption,
% 3.60/1.08                [status(thm)],
% 3.60/1.08                [c_267,c_31]) ).
% 3.60/1.08  
% 3.60/1.08  cnf(c_640,plain,
% 3.60/1.08      ( k6_partfun1(sK1) = k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2)
% 3.60/1.08      | m1_subset_1(k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
% 3.60/1.08      inference(predicate_to_equality,[status(thm)],[c_269]) ).
% 3.60/1.08  
% 3.60/1.08  cnf(c_19,negated_conjecture,
% 3.60/1.08      ( v1_funct_1(sK3) ),
% 3.60/1.08      inference(cnf_transformation,[],[f60]) ).
% 3.60/1.08  
% 3.60/1.08  cnf(c_12,plain,
% 3.60/1.08      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.60/1.08      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.60/1.08      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.60/1.08      | ~ v1_funct_1(X0)
% 3.60/1.08      | ~ v1_funct_1(X3) ),
% 3.60/1.08      inference(cnf_transformation,[],[f54]) ).
% 3.60/1.08  
% 3.60/1.08  cnf(c_677,plain,
% 3.60/1.08      ( m1_subset_1(k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.60/1.08      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.60/1.08      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.60/1.08      | ~ v1_funct_1(sK3)
% 3.60/1.08      | ~ v1_funct_1(sK2) ),
% 3.60/1.08      inference(instantiation,[status(thm)],[c_12]) ).
% 3.60/1.08  
% 3.60/1.08  cnf(c_807,plain,
% 3.60/1.08      ( k6_partfun1(sK1) = k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) ),
% 3.60/1.08      inference(global_propositional_subsumption,
% 3.60/1.08                [status(thm)],
% 3.60/1.08                [c_640,c_21,c_20,c_19,c_18,c_31,c_267,c_677]) ).
% 3.60/1.08  
% 3.60/1.08  cnf(c_1801,plain,
% 3.60/1.08      ( k5_relat_1(sK3,sK2) = k6_partfun1(sK1)
% 3.60/1.08      | v1_funct_1(sK3) != iProver_top ),
% 3.60/1.08      inference(light_normalisation,[status(thm)],[c_1799,c_807]) ).
% 3.60/1.08  
% 3.60/1.08  cnf(c_24,plain,
% 3.60/1.08      ( v1_funct_1(sK3) = iProver_top ),
% 3.60/1.08      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.60/1.08  
% 3.60/1.08  cnf(c_1921,plain,
% 3.60/1.08      ( k5_relat_1(sK3,sK2) = k6_partfun1(sK1) ),
% 3.60/1.08      inference(global_propositional_subsumption,
% 3.60/1.08                [status(thm)],
% 3.60/1.08                [c_1801,c_24]) ).
% 3.60/1.08  
% 3.60/1.08  cnf(c_4,plain,
% 3.60/1.08      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
% 3.60/1.08      | ~ v1_relat_1(X1)
% 3.60/1.08      | ~ v1_relat_1(X0) ),
% 3.60/1.08      inference(cnf_transformation,[],[f45]) ).
% 3.60/1.08  
% 3.60/1.08  cnf(c_653,plain,
% 3.60/1.08      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
% 3.60/1.08      | v1_relat_1(X0) != iProver_top
% 3.60/1.08      | v1_relat_1(X1) != iProver_top ),
% 3.60/1.08      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.60/1.08  
% 3.60/1.08  cnf(c_1923,plain,
% 3.60/1.08      ( r1_tarski(k2_relat_1(k6_partfun1(sK1)),k2_relat_1(sK2)) = iProver_top
% 3.60/1.08      | v1_relat_1(sK3) != iProver_top
% 3.60/1.09      | v1_relat_1(sK2) != iProver_top ),
% 3.60/1.09      inference(superposition,[status(thm)],[c_1921,c_653]) ).
% 3.60/1.09  
% 3.60/1.09  cnf(c_5,plain,
% 3.60/1.09      ( k2_relat_1(k6_partfun1(X0)) = X0 ),
% 3.60/1.09      inference(cnf_transformation,[],[f64]) ).
% 3.60/1.09  
% 3.60/1.09  cnf(c_1924,plain,
% 3.60/1.09      ( r1_tarski(sK1,k2_relat_1(sK2)) = iProver_top
% 3.60/1.09      | v1_relat_1(sK3) != iProver_top
% 3.60/1.09      | v1_relat_1(sK2) != iProver_top ),
% 3.60/1.09      inference(demodulation,[status(thm)],[c_1923,c_5]) ).
% 3.60/1.09  
% 3.60/1.09  cnf(c_7,plain,
% 3.60/1.09      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.60/1.09      | v1_relat_1(X0) ),
% 3.60/1.09      inference(cnf_transformation,[],[f48]) ).
% 3.60/1.09  
% 3.60/1.09  cnf(c_652,plain,
% 3.60/1.09      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.60/1.09      | v1_relat_1(X0) = iProver_top ),
% 3.60/1.09      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.60/1.09  
% 3.60/1.09  cnf(c_1000,plain,
% 3.60/1.09      ( v1_relat_1(sK2) = iProver_top ),
% 3.60/1.09      inference(superposition,[status(thm)],[c_644,c_652]) ).
% 3.60/1.09  
% 3.60/1.09  cnf(c_999,plain,
% 3.60/1.09      ( v1_relat_1(sK3) = iProver_top ),
% 3.60/1.09      inference(superposition,[status(thm)],[c_646,c_652]) ).
% 3.60/1.09  
% 3.60/1.09  cnf(c_3,plain,
% 3.60/1.09      ( ~ v5_relat_1(X0,X1)
% 3.60/1.09      | r1_tarski(k2_relat_1(X0),X1)
% 3.60/1.09      | ~ v1_relat_1(X0) ),
% 3.60/1.09      inference(cnf_transformation,[],[f43]) ).
% 3.60/1.09  
% 3.60/1.09  cnf(c_8,plain,
% 3.60/1.09      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.60/1.09      | v5_relat_1(X0,X2) ),
% 3.60/1.09      inference(cnf_transformation,[],[f49]) ).
% 3.60/1.09  
% 3.60/1.09  cnf(c_243,plain,
% 3.60/1.09      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.60/1.09      | r1_tarski(k2_relat_1(X3),X4)
% 3.60/1.09      | ~ v1_relat_1(X3)
% 3.60/1.09      | X0 != X3
% 3.60/1.09      | X2 != X4 ),
% 3.60/1.09      inference(resolution_lifted,[status(thm)],[c_3,c_8]) ).
% 3.60/1.09  
% 3.60/1.09  cnf(c_244,plain,
% 3.60/1.09      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.60/1.09      | r1_tarski(k2_relat_1(X0),X2)
% 3.60/1.09      | ~ v1_relat_1(X0) ),
% 3.60/1.09      inference(unflattening,[status(thm)],[c_243]) ).
% 3.60/1.09  
% 3.60/1.09  cnf(c_248,plain,
% 3.60/1.09      ( r1_tarski(k2_relat_1(X0),X2)
% 3.60/1.09      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.60/1.09      inference(global_propositional_subsumption,
% 3.60/1.09                [status(thm)],
% 3.60/1.09                [c_244,c_7]) ).
% 3.60/1.09  
% 3.60/1.09  cnf(c_249,plain,
% 3.60/1.09      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.60/1.09      | r1_tarski(k2_relat_1(X0),X2) ),
% 3.60/1.09      inference(renaming,[status(thm)],[c_248]) ).
% 3.60/1.09  
% 3.60/1.09  cnf(c_748,plain,
% 3.60/1.09      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
% 3.60/1.09      | r1_tarski(k2_relat_1(sK2),sK1) ),
% 3.60/1.09      inference(instantiation,[status(thm)],[c_249]) ).
% 3.60/1.09  
% 3.60/1.09  cnf(c_843,plain,
% 3.60/1.09      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.60/1.09      | r1_tarski(k2_relat_1(sK2),sK1) ),
% 3.60/1.09      inference(instantiation,[status(thm)],[c_748]) ).
% 3.60/1.09  
% 3.60/1.09  cnf(c_844,plain,
% 3.60/1.09      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.60/1.09      | r1_tarski(k2_relat_1(sK2),sK1) = iProver_top ),
% 3.60/1.09      inference(predicate_to_equality,[status(thm)],[c_843]) ).
% 3.60/1.09  
% 3.60/1.09  cnf(c_9,plain,
% 3.60/1.09      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.60/1.09      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.60/1.09      inference(cnf_transformation,[],[f50]) ).
% 3.60/1.09  
% 3.60/1.09  cnf(c_775,plain,
% 3.60/1.09      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.60/1.09      | k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 3.60/1.09      inference(instantiation,[status(thm)],[c_9]) ).
% 3.60/1.09  
% 3.60/1.09  cnf(c_0,plain,
% 3.60/1.09      ( ~ r1_tarski(X0,X1) | r2_xboole_0(X0,X1) | X1 = X0 ),
% 3.60/1.09      inference(cnf_transformation,[],[f41]) ).
% 3.60/1.09  
% 3.60/1.09  cnf(c_1,plain,
% 3.60/1.09      ( ~ r1_tarski(X0,X1) | ~ r2_xboole_0(X1,X0) ),
% 3.60/1.09      inference(cnf_transformation,[],[f42]) ).
% 3.60/1.09  
% 3.60/1.09  cnf(c_223,plain,
% 3.60/1.09      ( ~ r1_tarski(X0,X1)
% 3.60/1.09      | ~ r1_tarski(X2,X3)
% 3.60/1.09      | X3 != X0
% 3.60/1.09      | X2 != X1
% 3.60/1.09      | X1 = X0 ),
% 3.60/1.09      inference(resolution_lifted,[status(thm)],[c_0,c_1]) ).
% 3.60/1.09  
% 3.60/1.09  cnf(c_224,plain,
% 3.60/1.09      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.60/1.09      inference(unflattening,[status(thm)],[c_223]) ).
% 3.60/1.09  
% 3.60/1.09  cnf(c_699,plain,
% 3.60/1.09      ( ~ r1_tarski(k2_relat_1(sK2),sK1)
% 3.60/1.09      | ~ r1_tarski(sK1,k2_relat_1(sK2))
% 3.60/1.09      | sK1 = k2_relat_1(sK2) ),
% 3.60/1.09      inference(instantiation,[status(thm)],[c_224]) ).
% 3.60/1.09  
% 3.60/1.09  cnf(c_700,plain,
% 3.60/1.09      ( sK1 = k2_relat_1(sK2)
% 3.60/1.09      | r1_tarski(k2_relat_1(sK2),sK1) != iProver_top
% 3.60/1.09      | r1_tarski(sK1,k2_relat_1(sK2)) != iProver_top ),
% 3.60/1.09      inference(predicate_to_equality,[status(thm)],[c_699]) ).
% 3.60/1.09  
% 3.60/1.09  cnf(c_386,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.60/1.09  
% 3.60/1.09  cnf(c_676,plain,
% 3.60/1.09      ( k2_relset_1(sK0,sK1,sK2) != X0
% 3.60/1.09      | k2_relset_1(sK0,sK1,sK2) = sK1
% 3.60/1.09      | sK1 != X0 ),
% 3.60/1.09      inference(instantiation,[status(thm)],[c_386]) ).
% 3.60/1.09  
% 3.60/1.09  cnf(c_691,plain,
% 3.60/1.09      ( k2_relset_1(sK0,sK1,sK2) != k2_relat_1(sK2)
% 3.60/1.09      | k2_relset_1(sK0,sK1,sK2) = sK1
% 3.60/1.09      | sK1 != k2_relat_1(sK2) ),
% 3.60/1.09      inference(instantiation,[status(thm)],[c_676]) ).
% 3.60/1.09  
% 3.60/1.09  cnf(c_16,negated_conjecture,
% 3.60/1.09      ( k2_relset_1(sK0,sK1,sK2) != sK1 ),
% 3.60/1.09      inference(cnf_transformation,[],[f63]) ).
% 3.60/1.09  
% 3.60/1.09  cnf(c_23,plain,
% 3.60/1.09      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.60/1.09      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.60/1.09  
% 3.60/1.09  cnf(contradiction,plain,
% 3.60/1.09      ( $false ),
% 3.60/1.09      inference(minisat,
% 3.60/1.09                [status(thm)],
% 3.60/1.09                [c_1924,c_1000,c_999,c_844,c_775,c_700,c_691,c_16,c_23,
% 3.60/1.09                 c_20]) ).
% 3.60/1.09  
% 3.60/1.09  
% 3.60/1.09  % SZS output end CNFRefutation for theBenchmark.p
% 3.60/1.09  
% 3.60/1.09  ------                               Statistics
% 3.60/1.09  
% 3.60/1.09  ------ General
% 3.60/1.09  
% 3.60/1.09  abstr_ref_over_cycles:                  0
% 3.60/1.09  abstr_ref_under_cycles:                 0
% 3.60/1.09  gc_basic_clause_elim:                   0
% 3.60/1.09  forced_gc_time:                         0
% 3.60/1.09  parsing_time:                           0.032
% 3.60/1.09  unif_index_cands_time:                  0.
% 3.60/1.09  unif_index_add_time:                    0.
% 3.60/1.09  orderings_time:                         0.
% 3.60/1.09  out_proof_time:                         0.012
% 3.60/1.09  total_time:                             0.175
% 3.60/1.09  num_of_symbols:                         50
% 3.60/1.09  num_of_terms:                           2176
% 3.60/1.09  
% 3.60/1.09  ------ Preprocessing
% 3.60/1.09  
% 3.60/1.09  num_of_splits:                          0
% 3.60/1.09  num_of_split_atoms:                     0
% 3.60/1.09  num_of_reused_defs:                     0
% 3.60/1.09  num_eq_ax_congr_red:                    13
% 3.60/1.09  num_of_sem_filtered_clauses:            1
% 3.60/1.09  num_of_subtypes:                        0
% 3.60/1.09  monotx_restored_types:                  0
% 3.60/1.09  sat_num_of_epr_types:                   0
% 3.60/1.09  sat_num_of_non_cyclic_types:            0
% 3.60/1.09  sat_guarded_non_collapsed_types:        0
% 3.60/1.09  num_pure_diseq_elim:                    0
% 3.60/1.09  simp_replaced_by:                       0
% 3.60/1.09  res_preprocessed:                       98
% 3.60/1.09  prep_upred:                             0
% 3.60/1.09  prep_unflattend:                        12
% 3.60/1.09  smt_new_axioms:                         0
% 3.60/1.09  pred_elim_cands:                        4
% 3.60/1.09  pred_elim:                              3
% 3.60/1.09  pred_elim_cl:                           5
% 3.60/1.09  pred_elim_cycles:                       5
% 3.60/1.09  merged_defs:                            0
% 3.60/1.09  merged_defs_ncl:                        0
% 3.60/1.09  bin_hyper_res:                          0
% 3.60/1.09  prep_cycles:                            4
% 3.60/1.09  pred_elim_time:                         0.003
% 3.60/1.09  splitting_time:                         0.
% 3.60/1.09  sem_filter_time:                        0.
% 3.60/1.09  monotx_time:                            0.011
% 3.60/1.09  subtype_inf_time:                       0.
% 3.60/1.09  
% 3.60/1.09  ------ Problem properties
% 3.60/1.09  
% 3.60/1.09  clauses:                                17
% 3.60/1.09  conjectures:                            5
% 3.60/1.09  epr:                                    3
% 3.60/1.09  horn:                                   17
% 3.60/1.09  ground:                                 6
% 3.60/1.09  unary:                                  8
% 3.60/1.09  binary:                                 4
% 3.60/1.09  lits:                                   37
% 3.60/1.09  lits_eq:                                7
% 3.60/1.09  fd_pure:                                0
% 3.60/1.09  fd_pseudo:                              0
% 3.60/1.09  fd_cond:                                0
% 3.60/1.09  fd_pseudo_cond:                         1
% 3.60/1.09  ac_symbols:                             0
% 3.60/1.09  
% 3.60/1.09  ------ Propositional Solver
% 3.60/1.09  
% 3.60/1.09  prop_solver_calls:                      30
% 3.60/1.09  prop_fast_solver_calls:                 554
% 3.60/1.09  smt_solver_calls:                       0
% 3.60/1.09  smt_fast_solver_calls:                  0
% 3.60/1.09  prop_num_of_clauses:                    861
% 3.60/1.09  prop_preprocess_simplified:             3137
% 3.60/1.09  prop_fo_subsumed:                       9
% 3.60/1.09  prop_solver_time:                       0.
% 3.60/1.09  smt_solver_time:                        0.
% 3.60/1.09  smt_fast_solver_time:                   0.
% 3.60/1.09  prop_fast_solver_time:                  0.
% 3.60/1.09  prop_unsat_core_time:                   0.
% 3.60/1.09  
% 3.60/1.09  ------ QBF
% 3.60/1.09  
% 3.60/1.09  qbf_q_res:                              0
% 3.60/1.09  qbf_num_tautologies:                    0
% 3.60/1.09  qbf_prep_cycles:                        0
% 3.60/1.09  
% 3.60/1.09  ------ BMC1
% 3.60/1.09  
% 3.60/1.09  bmc1_current_bound:                     -1
% 3.60/1.09  bmc1_last_solved_bound:                 -1
% 3.60/1.09  bmc1_unsat_core_size:                   -1
% 3.60/1.09  bmc1_unsat_core_parents_size:           -1
% 3.60/1.09  bmc1_merge_next_fun:                    0
% 3.60/1.09  bmc1_unsat_core_clauses_time:           0.
% 3.60/1.09  
% 3.60/1.09  ------ Instantiation
% 3.60/1.09  
% 3.60/1.09  inst_num_of_clauses:                    300
% 3.60/1.09  inst_num_in_passive:                    9
% 3.60/1.09  inst_num_in_active:                     143
% 3.60/1.09  inst_num_in_unprocessed:                148
% 3.60/1.09  inst_num_of_loops:                      160
% 3.60/1.09  inst_num_of_learning_restarts:          0
% 3.60/1.09  inst_num_moves_active_passive:          13
% 3.60/1.09  inst_lit_activity:                      0
% 3.60/1.09  inst_lit_activity_moves:                0
% 3.60/1.09  inst_num_tautologies:                   0
% 3.60/1.09  inst_num_prop_implied:                  0
% 3.60/1.09  inst_num_existing_simplified:           0
% 3.60/1.09  inst_num_eq_res_simplified:             0
% 3.60/1.09  inst_num_child_elim:                    0
% 3.60/1.09  inst_num_of_dismatching_blockings:      52
% 3.60/1.09  inst_num_of_non_proper_insts:           338
% 3.60/1.09  inst_num_of_duplicates:                 0
% 3.60/1.09  inst_inst_num_from_inst_to_res:         0
% 3.60/1.09  inst_dismatching_checking_time:         0.
% 3.60/1.09  
% 3.60/1.09  ------ Resolution
% 3.60/1.09  
% 3.60/1.09  res_num_of_clauses:                     0
% 3.60/1.09  res_num_in_passive:                     0
% 3.60/1.09  res_num_in_active:                      0
% 3.60/1.09  res_num_of_loops:                       102
% 3.60/1.09  res_forward_subset_subsumed:            37
% 3.60/1.09  res_backward_subset_subsumed:           0
% 3.60/1.09  res_forward_subsumed:                   0
% 3.60/1.09  res_backward_subsumed:                  0
% 3.60/1.09  res_forward_subsumption_resolution:     0
% 3.60/1.09  res_backward_subsumption_resolution:    0
% 3.60/1.09  res_clause_to_clause_subsumption:       58
% 3.60/1.09  res_orphan_elimination:                 0
% 3.60/1.09  res_tautology_del:                      34
% 3.60/1.09  res_num_eq_res_simplified:              0
% 3.60/1.09  res_num_sel_changes:                    0
% 3.60/1.09  res_moves_from_active_to_pass:          0
% 3.60/1.09  
% 3.60/1.09  ------ Superposition
% 3.60/1.09  
% 3.60/1.09  sup_time_total:                         0.
% 3.60/1.09  sup_time_generating:                    0.
% 3.60/1.09  sup_time_sim_full:                      0.
% 3.60/1.09  sup_time_sim_immed:                     0.
% 3.60/1.09  
% 3.60/1.09  sup_num_of_clauses:                     41
% 3.60/1.09  sup_num_in_active:                      31
% 3.60/1.09  sup_num_in_passive:                     10
% 3.60/1.09  sup_num_of_loops:                       31
% 3.60/1.09  sup_fw_superposition:                   19
% 3.60/1.09  sup_bw_superposition:                   5
% 3.60/1.09  sup_immediate_simplified:               4
% 3.60/1.09  sup_given_eliminated:                   0
% 3.60/1.09  comparisons_done:                       0
% 3.60/1.09  comparisons_avoided:                    0
% 3.60/1.09  
% 3.60/1.09  ------ Simplifications
% 3.60/1.09  
% 3.60/1.09  
% 3.60/1.09  sim_fw_subset_subsumed:                 0
% 3.60/1.09  sim_bw_subset_subsumed:                 0
% 3.60/1.09  sim_fw_subsumed:                        0
% 3.60/1.09  sim_bw_subsumed:                        0
% 3.60/1.09  sim_fw_subsumption_res:                 0
% 3.60/1.09  sim_bw_subsumption_res:                 0
% 3.60/1.09  sim_tautology_del:                      0
% 3.60/1.09  sim_eq_tautology_del:                   0
% 3.60/1.09  sim_eq_res_simp:                        0
% 3.60/1.09  sim_fw_demodulated:                     1
% 3.60/1.09  sim_bw_demodulated:                     1
% 3.60/1.09  sim_light_normalised:                   3
% 3.60/1.09  sim_joinable_taut:                      0
% 3.60/1.09  sim_joinable_simp:                      0
% 3.60/1.09  sim_ac_normalised:                      0
% 3.60/1.09  sim_smt_subsumption:                    0
% 3.60/1.09  
%------------------------------------------------------------------------------
