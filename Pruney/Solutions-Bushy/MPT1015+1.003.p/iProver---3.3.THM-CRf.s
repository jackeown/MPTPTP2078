%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1015+1.003 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:40 EST 2020

% Result     : Theorem 7.34s
% Output     : CNFRefutation 7.34s
% Verified   : 
% Statistics : Number of formulae       :  183 ( 589 expanded)
%              Number of clauses        :  116 ( 196 expanded)
%              Number of leaves         :   20 ( 143 expanded)
%              Depth                    :   21
%              Number of atoms          :  626 (3782 expanded)
%              Number of equality atoms :  253 ( 370 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
         => ( ( v2_funct_1(X1)
              & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) )
           => r2_relset_1(X0,X0,X2,k6_partfun1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X2,X0,X0)
              & v1_funct_1(X2) )
           => ( ( v2_funct_1(X1)
                & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) )
             => r2_relset_1(X0,X0,X2,k6_partfun1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f35,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k6_partfun1(X0))
          & v2_funct_1(X1)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f36,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k6_partfun1(X0))
          & v2_funct_1(X1)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k6_partfun1(X0))
          & v2_funct_1(X1)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
     => ( ~ r2_relset_1(X0,X0,sK2,k6_partfun1(X0))
        & v2_funct_1(X1)
        & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,sK2,X1),X1)
        & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(sK2,X0,X0)
        & v1_funct_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r2_relset_1(X0,X0,X2,k6_partfun1(X0))
            & v2_funct_1(X1)
            & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ? [X2] :
          ( ~ r2_relset_1(sK0,sK0,X2,k6_partfun1(sK0))
          & v2_funct_1(sK1)
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,X2,sK1),sK1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
          & v1_funct_2(X2,sK0,sK0)
          & v1_funct_1(X2) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0))
    & v2_funct_1(sK1)
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK2,sK0,sK0)
    & v1_funct_1(sK2)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f36,f39,f38])).

fof(f61,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f40])).

fof(f58,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f40])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f22])).

fof(f46,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f56,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f59,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f20,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f19])).

fof(f43,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f26])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f62,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f11])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( ( k5_relat_1(X2,X1) = X1
              & v2_funct_1(X1)
              & r1_tarski(k2_relat_1(X2),X0)
              & k1_relat_1(X2) = X0
              & k1_relat_1(X1) = X0 )
           => k6_relat_1(X0) = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k6_relat_1(X0) = X2
          | k5_relat_1(X2,X1) != X1
          | ~ v2_funct_1(X1)
          | ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X0
          | k1_relat_1(X1) != X0
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k6_relat_1(X0) = X2
          | k5_relat_1(X2,X1) != X1
          | ~ v2_funct_1(X1)
          | ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X0
          | k1_relat_1(X1) != X0
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k6_relat_1(X0) = X2
      | k5_relat_1(X2,X1) != X1
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(k2_relat_1(X2),X0)
      | k1_relat_1(X2) != X0
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f68,plain,(
    ! [X2,X1] :
      ( k6_relat_1(k1_relat_1(X2)) = X2
      | k5_relat_1(X2,X1) != X1
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(k2_relat_1(X2),k1_relat_1(X2))
      | k1_relat_1(X1) != k1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f54])).

fof(f63,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f57,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f60,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f67,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f51])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
       => r2_relset_1(X0,X1,X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X3,X2)
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X3,X2)
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f28])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X2)
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f4,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f45,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f8,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f65,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f45,f49])).

fof(f64,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f40])).

fof(f66,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k6_relat_1(sK0)) ),
    inference(definition_unfolding,[],[f64,f49])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_479,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_896,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_479])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_477,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_898,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_477])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_487,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ m1_subset_1(X1_47,k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49)))
    | ~ v1_funct_1(X0_47)
    | ~ v1_funct_1(X1_47)
    | k1_partfun1(X2_49,X3_49,X0_49,X1_49,X1_47,X0_47) = k5_relat_1(X1_47,X0_47) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_888,plain,
    ( k1_partfun1(X0_49,X1_49,X2_49,X3_49,X0_47,X1_47) = k5_relat_1(X0_47,X1_47)
    | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | m1_subset_1(X1_47,k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49))) != iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | v1_funct_1(X1_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_487])).

cnf(c_2982,plain,
    ( k1_partfun1(X0_49,X1_49,sK0,sK0,X0_47,sK1) = k5_relat_1(X0_47,sK1)
    | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_898,c_888])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_23,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3630,plain,
    ( v1_funct_1(X0_47) != iProver_top
    | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | k1_partfun1(X0_49,X1_49,sK0,sK0,X0_47,sK1) = k5_relat_1(X0_47,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2982,c_23])).

cnf(c_3631,plain,
    ( k1_partfun1(X0_49,X1_49,sK0,sK0,X0_47,sK1) = k5_relat_1(X0_47,sK1)
    | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_funct_1(X0_47) != iProver_top ),
    inference(renaming,[status(thm)],[c_3630])).

cnf(c_3637,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) = k5_relat_1(sK2,sK1)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_896,c_3631])).

cnf(c_19,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_26,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3684,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) = k5_relat_1(sK2,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3637,c_26])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_491,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ m1_subset_1(X1_47,k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49)))
    | m1_subset_1(k1_partfun1(X2_49,X3_49,X0_49,X1_49,X1_47,X0_47),k1_zfmisc_1(k2_zfmisc_1(X2_49,X1_49)))
    | ~ v1_funct_1(X0_47)
    | ~ v1_funct_1(X1_47) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_884,plain,
    ( m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | m1_subset_1(X1_47,k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49))) != iProver_top
    | m1_subset_1(k1_partfun1(X0_49,X1_49,X2_49,X3_49,X0_47,X1_47),k1_zfmisc_1(k2_zfmisc_1(X0_49,X3_49))) = iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | v1_funct_1(X1_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_491])).

cnf(c_3690,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3684,c_884])).

cnf(c_25,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_28,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_23494,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3690,c_23,c_25,c_26,c_28])).

cnf(c_9,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_483,plain,
    ( ~ r2_relset_1(X0_49,X1_49,X0_47,X1_47)
    | ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ m1_subset_1(X1_47,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | X1_47 = X0_47 ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_892,plain,
    ( X0_47 = X1_47
    | r2_relset_1(X0_49,X1_49,X1_47,X0_47) != iProver_top
    | m1_subset_1(X1_47,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_483])).

cnf(c_2076,plain,
    ( sK1 = X0_47
    | r2_relset_1(sK0,sK0,X0_47,sK1) != iProver_top
    | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_898,c_892])).

cnf(c_23514,plain,
    ( k5_relat_1(sK2,sK1) = sK1
    | r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK1),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_23494,c_2076])).

cnf(c_16,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1708,plain,
    ( ~ r2_relset_1(X0_49,X1_49,k1_partfun1(sK0,X2_49,X3_49,sK0,X0_47,X1_47),X2_47)
    | ~ m1_subset_1(X2_47,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ m1_subset_1(k1_partfun1(sK0,X2_49,X3_49,sK0,X0_47,X1_47),k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | X2_47 = k1_partfun1(sK0,X2_49,X3_49,sK0,X0_47,X1_47) ),
    inference(instantiation,[status(thm)],[c_483])).

cnf(c_2210,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1)
    | ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_1708])).

cnf(c_2940,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_491])).

cnf(c_497,plain,
    ( X0_47 != X1_47
    | X2_47 != X1_47
    | X2_47 = X0_47 ),
    theory(equality)).

cnf(c_1212,plain,
    ( X0_47 != X1_47
    | k5_relat_1(X2_47,sK1) != X1_47
    | k5_relat_1(X2_47,sK1) = X0_47 ),
    inference(instantiation,[status(thm)],[c_497])).

cnf(c_2506,plain,
    ( X0_47 != k1_partfun1(X0_49,X1_49,X2_49,X3_49,X1_47,X2_47)
    | k5_relat_1(X1_47,sK1) = X0_47
    | k5_relat_1(X1_47,sK1) != k1_partfun1(X0_49,X1_49,X2_49,X3_49,X1_47,X2_47) ),
    inference(instantiation,[status(thm)],[c_1212])).

cnf(c_3480,plain,
    ( k5_relat_1(sK2,sK1) != k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1)
    | k5_relat_1(sK2,sK1) = sK1
    | sK1 != k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_2506])).

cnf(c_1457,plain,
    ( X0_47 != k5_relat_1(X1_47,sK1)
    | k5_relat_1(X1_47,sK1) = X0_47
    | k5_relat_1(X1_47,sK1) != k5_relat_1(X1_47,sK1) ),
    inference(instantiation,[status(thm)],[c_1212])).

cnf(c_1777,plain,
    ( k1_partfun1(X0_49,X1_49,X2_49,X3_49,X0_47,sK1) != k5_relat_1(X0_47,sK1)
    | k5_relat_1(X0_47,sK1) = k1_partfun1(X0_49,X1_49,X2_49,X3_49,X0_47,sK1)
    | k5_relat_1(X0_47,sK1) != k5_relat_1(X0_47,sK1) ),
    inference(instantiation,[status(thm)],[c_1457])).

cnf(c_2406,plain,
    ( k1_partfun1(sK0,X0_49,X1_49,sK0,X0_47,sK1) != k5_relat_1(X0_47,sK1)
    | k5_relat_1(X0_47,sK1) = k1_partfun1(sK0,X0_49,X1_49,sK0,X0_47,sK1)
    | k5_relat_1(X0_47,sK1) != k5_relat_1(X0_47,sK1) ),
    inference(instantiation,[status(thm)],[c_1777])).

cnf(c_5526,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) != k5_relat_1(sK2,sK1)
    | k5_relat_1(sK2,sK1) = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1)
    | k5_relat_1(sK2,sK1) != k5_relat_1(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_2406])).

cnf(c_494,plain,
    ( X0_47 = X0_47 ),
    theory(equality)).

cnf(c_1209,plain,
    ( k5_relat_1(X0_47,sK1) = k5_relat_1(X0_47,sK1) ),
    inference(instantiation,[status(thm)],[c_494])).

cnf(c_7328,plain,
    ( k5_relat_1(sK2,sK1) = k5_relat_1(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_1209])).

cnf(c_23630,plain,
    ( k5_relat_1(sK2,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_23514,c_22,c_20,c_19,c_26,c_17,c_16,c_2210,c_2940,c_3480,c_3637,c_5526,c_7328])).

cnf(c_11,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_12,plain,
    ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X0))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(X0,X1) != X1
    | k1_relat_1(X1) != k1_relat_1(X0)
    | k6_relat_1(k1_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_15,negated_conjecture,
    ( v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_270,plain,
    ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(X0,X1) != X1
    | k1_relat_1(X1) != k1_relat_1(X0)
    | k6_relat_1(k1_relat_1(X0)) = X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_15])).

cnf(c_271,plain,
    ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK1)
    | k5_relat_1(X0,sK1) != sK1
    | k1_relat_1(sK1) != k1_relat_1(X0)
    | k6_relat_1(k1_relat_1(X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_270])).

cnf(c_275,plain,
    ( ~ v1_funct_1(X0)
    | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK1)
    | k5_relat_1(X0,sK1) != sK1
    | k1_relat_1(sK1) != k1_relat_1(X0)
    | k6_relat_1(k1_relat_1(X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_271,c_22])).

cnf(c_276,plain,
    ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK1)
    | k5_relat_1(X0,sK1) != sK1
    | k1_relat_1(sK1) != k1_relat_1(X0)
    | k6_relat_1(k1_relat_1(X0)) = X0 ),
    inference(renaming,[status(thm)],[c_275])).

cnf(c_311,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(sK1)
    | k5_relat_1(X2,sK1) != sK1
    | k2_relat_1(X2) != X0
    | k1_relat_1(X2) != X1
    | k1_relat_1(X2) != k1_relat_1(sK1)
    | k6_relat_1(k1_relat_1(X2)) = X2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_276])).

cnf(c_312,plain,
    ( ~ m1_subset_1(k2_relat_1(X0),k1_zfmisc_1(k1_relat_1(X0)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK1)
    | k5_relat_1(X0,sK1) != sK1
    | k1_relat_1(X0) != k1_relat_1(sK1)
    | k6_relat_1(k1_relat_1(X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_311])).

cnf(c_473,plain,
    ( ~ m1_subset_1(k2_relat_1(X0_47),k1_zfmisc_1(k1_relat_1(X0_47)))
    | ~ v1_funct_1(X0_47)
    | ~ v1_relat_1(X0_47)
    | ~ v1_relat_1(sK1)
    | k1_relat_1(X0_47) != k1_relat_1(sK1)
    | k5_relat_1(X0_47,sK1) != sK1
    | k6_relat_1(k1_relat_1(X0_47)) = X0_47 ),
    inference(subtyping,[status(esa)],[c_312])).

cnf(c_900,plain,
    ( k1_relat_1(X0_47) != k1_relat_1(sK1)
    | k5_relat_1(X0_47,sK1) != sK1
    | k6_relat_1(k1_relat_1(X0_47)) = X0_47
    | m1_subset_1(k2_relat_1(X0_47),k1_zfmisc_1(k1_relat_1(X0_47))) != iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | v1_relat_1(X0_47) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_473])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_492,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | v1_relat_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_525,plain,
    ( m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_relat_1(X0_47) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_492])).

cnf(c_527,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_relat_1(sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_525])).

cnf(c_558,plain,
    ( k1_relat_1(X0_47) != k1_relat_1(sK1)
    | k5_relat_1(X0_47,sK1) != sK1
    | k6_relat_1(k1_relat_1(X0_47)) = X0_47
    | m1_subset_1(k2_relat_1(X0_47),k1_zfmisc_1(k1_relat_1(X0_47))) != iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | v1_relat_1(X0_47) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_473])).

cnf(c_3967,plain,
    ( v1_relat_1(X0_47) != iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | m1_subset_1(k2_relat_1(X0_47),k1_zfmisc_1(k1_relat_1(X0_47))) != iProver_top
    | k6_relat_1(k1_relat_1(X0_47)) = X0_47
    | k5_relat_1(X0_47,sK1) != sK1
    | k1_relat_1(X0_47) != k1_relat_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_900,c_25,c_527,c_558])).

cnf(c_3968,plain,
    ( k1_relat_1(X0_47) != k1_relat_1(sK1)
    | k5_relat_1(X0_47,sK1) != sK1
    | k6_relat_1(k1_relat_1(X0_47)) = X0_47
    | m1_subset_1(k2_relat_1(X0_47),k1_zfmisc_1(k1_relat_1(X0_47))) != iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | v1_relat_1(X0_47) != iProver_top ),
    inference(renaming,[status(thm)],[c_3967])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_486,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | k1_relset_1(X0_49,X1_49,X0_47) = k1_relat_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_889,plain,
    ( k1_relset_1(X0_49,X1_49,X0_47) = k1_relat_1(X0_47)
    | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_486])).

cnf(c_1366,plain,
    ( k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_898,c_889])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(X1,X1,X0) = X1 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_21,negated_conjecture,
    ( v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_260,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(X1,X1,X0) = X1
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_21])).

cnf(c_261,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | k1_relset_1(sK0,sK0,sK1) = sK0 ),
    inference(unflattening,[status(thm)],[c_260])).

cnf(c_263,plain,
    ( k1_relset_1(sK0,sK0,sK1) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_261,c_22,c_20])).

cnf(c_474,plain,
    ( k1_relset_1(sK0,sK0,sK1) = sK0 ),
    inference(subtyping,[status(esa)],[c_263])).

cnf(c_1371,plain,
    ( k1_relat_1(sK1) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_1366,c_474])).

cnf(c_3971,plain,
    ( k1_relat_1(X0_47) != sK0
    | k5_relat_1(X0_47,sK1) != sK1
    | k6_relat_1(k1_relat_1(X0_47)) = X0_47
    | m1_subset_1(k2_relat_1(X0_47),k1_zfmisc_1(k1_relat_1(X0_47))) != iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | v1_relat_1(X0_47) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3968,c_1371])).

cnf(c_23643,plain,
    ( k1_relat_1(sK2) != sK0
    | k6_relat_1(k1_relat_1(sK2)) = sK2
    | m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(k1_relat_1(sK2))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_23630,c_3971])).

cnf(c_1365,plain,
    ( k1_relset_1(sK0,sK0,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_896,c_889])).

cnf(c_18,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_252,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(X1,X1,X0) = X1
    | sK2 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_18])).

cnf(c_253,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | k1_relset_1(sK0,sK0,sK2) = sK0 ),
    inference(unflattening,[status(thm)],[c_252])).

cnf(c_255,plain,
    ( k1_relset_1(sK0,sK0,sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_253,c_19,c_17])).

cnf(c_475,plain,
    ( k1_relset_1(sK0,sK0,sK2) = sK0 ),
    inference(subtyping,[status(esa)],[c_255])).

cnf(c_1374,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_1365,c_475])).

cnf(c_23644,plain,
    ( sK0 != sK0
    | k6_relat_1(sK0) = sK2
    | m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_23643,c_1374])).

cnf(c_23645,plain,
    ( k6_relat_1(sK0) = sK2
    | m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_23644])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_485,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | k2_relset_1(X0_49,X1_49,X0_47) = k2_relat_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_890,plain,
    ( k2_relset_1(X0_49,X1_49,X0_47) = k2_relat_1(X0_47)
    | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_485])).

cnf(c_1380,plain,
    ( k2_relset_1(sK0,sK0,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_896,c_890])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_489,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | m1_subset_1(k2_relset_1(X0_49,X1_49,X0_47),k1_zfmisc_1(X1_49)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_886,plain,
    ( m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | m1_subset_1(k2_relset_1(X0_49,X1_49,X0_47),k1_zfmisc_1(X1_49)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_489])).

cnf(c_2031,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK0)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1380,c_886])).

cnf(c_509,plain,
    ( ~ r2_relset_1(X0_49,X1_49,X0_47,X1_47)
    | r2_relset_1(X2_49,X3_49,X2_47,X3_47)
    | X2_49 != X0_49
    | X3_49 != X1_49
    | X2_47 != X0_47
    | X3_47 != X1_47 ),
    theory(equality)).

cnf(c_1153,plain,
    ( ~ r2_relset_1(X0_49,X1_49,X0_47,X1_47)
    | r2_relset_1(sK0,sK0,k6_relat_1(sK0),sK2)
    | sK0 != X0_49
    | sK0 != X1_49
    | k6_relat_1(sK0) != X0_47
    | sK2 != X1_47 ),
    inference(instantiation,[status(thm)],[c_509])).

cnf(c_1357,plain,
    ( ~ r2_relset_1(X0_49,X1_49,X0_47,sK2)
    | r2_relset_1(sK0,sK0,k6_relat_1(sK0),sK2)
    | sK0 != X0_49
    | sK0 != X1_49
    | k6_relat_1(sK0) != X0_47
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1153])).

cnf(c_1688,plain,
    ( ~ r2_relset_1(X0_49,X1_49,sK2,sK2)
    | r2_relset_1(sK0,sK0,k6_relat_1(sK0),sK2)
    | sK0 != X0_49
    | sK0 != X1_49
    | k6_relat_1(sK0) != sK2
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1357])).

cnf(c_1691,plain,
    ( r2_relset_1(sK0,sK0,k6_relat_1(sK0),sK2)
    | ~ r2_relset_1(sK0,sK0,sK2,sK2)
    | sK0 != sK0
    | k6_relat_1(sK0) != sK2
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1688])).

cnf(c_8,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_484,plain,
    ( r2_relset_1(X0_49,X1_49,X0_47,X0_47)
    | ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_891,plain,
    ( r2_relset_1(X0_49,X1_49,X0_47,X0_47) = iProver_top
    | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_484])).

cnf(c_1468,plain,
    ( r2_relset_1(sK0,sK0,sK2,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_896,c_891])).

cnf(c_1477,plain,
    ( r2_relset_1(sK0,sK0,sK2,sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1468])).

cnf(c_1199,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_494])).

cnf(c_1139,plain,
    ( v1_relat_1(sK2) ),
    inference(resolution,[status(thm)],[c_492,c_479])).

cnf(c_1140,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1139])).

cnf(c_10,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | r2_relset_1(X0,X1,X3,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_482,plain,
    ( ~ r2_relset_1(X0_49,X1_49,X0_47,X1_47)
    | r2_relset_1(X0_49,X1_49,X1_47,X0_47)
    | ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ m1_subset_1(X1_47,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1112,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_relat_1(sK0),sK2)
    | r2_relset_1(sK0,sK0,sK2,k6_relat_1(sK0))
    | ~ m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_482])).

cnf(c_496,plain,
    ( X0_49 = X0_49 ),
    theory(equality)).

cnf(c_524,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_496])).

cnf(c_4,plain,
    ( m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_58,plain,
    ( m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_14,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK0,sK2,k6_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f66])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_23645,c_2031,c_1691,c_1477,c_1199,c_1140,c_1112,c_524,c_58,c_14,c_28,c_17,c_26])).


%------------------------------------------------------------------------------
