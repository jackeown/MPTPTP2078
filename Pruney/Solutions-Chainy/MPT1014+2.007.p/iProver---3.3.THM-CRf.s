%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:06:47 EST 2020

% Result     : Theorem 3.30s
% Output     : CNFRefutation 3.30s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 373 expanded)
%              Number of clauses        :   90 ( 123 expanded)
%              Number of leaves         :   17 (  92 expanded)
%              Depth                    :   19
%              Number of atoms          :  459 (2363 expanded)
%              Number of equality atoms :  205 ( 439 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
         => ( ( k2_relset_1(X0,X0,X1) = X0
              & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1) )
           => r2_relset_1(X0,X0,X2,k6_partfun1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X2,X0,X0)
              & v1_funct_1(X2) )
           => ( ( k2_relset_1(X0,X0,X1) = X0
                & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1) )
             => r2_relset_1(X0,X0,X2,k6_partfun1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f28,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k6_partfun1(X0))
          & k2_relset_1(X0,X0,X1) = X0
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f29,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k6_partfun1(X0))
          & k2_relset_1(X0,X0,X1) = X0
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k6_partfun1(X0))
          & k2_relset_1(X0,X0,X1) = X0
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
     => ( ~ r2_relset_1(X0,X0,sK2,k6_partfun1(X0))
        & k2_relset_1(X0,X0,X1) = X0
        & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,sK2),X1)
        & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(sK2,X0,X0)
        & v1_funct_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r2_relset_1(X0,X0,X2,k6_partfun1(X0))
            & k2_relset_1(X0,X0,X1) = X0
            & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ? [X2] :
          ( ~ r2_relset_1(sK0,sK0,X2,k6_partfun1(sK0))
          & k2_relset_1(sK0,sK0,sK1) = sK0
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),sK1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
          & v1_funct_2(X2,sK0,sK0)
          & v1_funct_1(X2) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0))
    & k2_relset_1(sK0,sK0,sK1) = sK0
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK2,sK0,sK0)
    & v1_funct_1(sK2)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f32,f31])).

fof(f47,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f33])).

fof(f50,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f33])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f24])).

fof(f42,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f48,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f45,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f22])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f51,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f20])).

fof(f39,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f17,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f16])).

fof(f36,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f52,plain,(
    k2_relset_1(sK0,sK0,sK1) = sK0 ),
    inference(cnf_transformation,[],[f33])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X0,X1) = X0
              & k2_relat_1(X0) = k1_relat_1(X1) )
           => k6_relat_1(k1_relat_1(X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_relat_1(k1_relat_1(X1)) = X1
          | k5_relat_1(X0,X1) != X0
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_relat_1(k1_relat_1(X1)) = X1
          | k5_relat_1(X0,X1) != X0
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k6_relat_1(k1_relat_1(X1)) = X1
      | k5_relat_1(X0,X1) != X0
      | k2_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f9,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k6_partfun1(k1_relat_1(X1)) = X1
      | k5_relat_1(X0,X1) != X0
      | k2_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f34,f43])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f49,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f41])).

fof(f53,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_385,plain,
    ( ~ m1_subset_1(X0_46,X0_48)
    | m1_subset_1(X1_46,X1_48)
    | X1_48 != X0_48
    | X1_46 != X0_46 ),
    theory(equality)).

cnf(c_836,plain,
    ( m1_subset_1(X0_46,X0_48)
    | ~ m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | X0_48 != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | X0_46 != X1_46 ),
    inference(instantiation,[status(thm)],[c_385])).

cnf(c_997,plain,
    ( m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
    | ~ m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | X0_46 != X1_46 ),
    inference(instantiation,[status(thm)],[c_836])).

cnf(c_3569,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | k6_partfun1(sK0) != X0_46 ),
    inference(instantiation,[status(thm)],[c_997])).

cnf(c_4629,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | k6_partfun1(sK0) != sK2 ),
    inference(instantiation,[status(thm)],[c_3569])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_363,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_643,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_363])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_365,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_641,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_365])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_367,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
    | ~ m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(X2_47,X3_47)))
    | ~ v1_funct_1(X0_46)
    | ~ v1_funct_1(X1_46)
    | k1_partfun1(X2_47,X3_47,X0_47,X1_47,X1_46,X0_46) = k5_relat_1(X1_46,X0_46) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_640,plain,
    ( k1_partfun1(X0_47,X1_47,X2_47,X3_47,X0_46,X1_46) = k5_relat_1(X0_46,X1_46)
    | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
    | m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(X2_47,X3_47))) != iProver_top
    | v1_funct_1(X0_46) != iProver_top
    | v1_funct_1(X1_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_367])).

cnf(c_1352,plain,
    ( k1_partfun1(X0_47,X1_47,sK0,sK0,X0_46,sK2) = k5_relat_1(X0_46,sK2)
    | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
    | v1_funct_1(X0_46) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_641,c_640])).

cnf(c_15,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_22,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1696,plain,
    ( v1_funct_1(X0_46) != iProver_top
    | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
    | k1_partfun1(X0_47,X1_47,sK0,sK0,X0_46,sK2) = k5_relat_1(X0_46,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1352,c_22])).

cnf(c_1697,plain,
    ( k1_partfun1(X0_47,X1_47,sK0,sK0,X0_46,sK2) = k5_relat_1(X0_46,sK2)
    | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
    | v1_funct_1(X0_46) != iProver_top ),
    inference(renaming,[status(thm)],[c_1696])).

cnf(c_1706,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2)
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_643,c_1697])).

cnf(c_18,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_987,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_367])).

cnf(c_1806,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1706,c_18,c_16,c_15,c_13,c_987])).

cnf(c_7,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_12,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),sK1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_229,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) != X0
    | sK1 != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_12])).

cnf(c_230,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) ),
    inference(unflattening,[status(thm)],[c_229])).

cnf(c_232,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_230,c_16])).

cnf(c_358,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) ),
    inference(subtyping,[status(esa)],[c_232])).

cnf(c_646,plain,
    ( sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2)
    | m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_358])).

cnf(c_1809,plain,
    ( k5_relat_1(sK1,sK2) = sK1
    | m1_subset_1(k5_relat_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1806,c_646])).

cnf(c_21,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_24,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | k4_relset_1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_368,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
    | ~ m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(X2_47,X3_47)))
    | k4_relset_1(X2_47,X3_47,X0_47,X1_47,X1_46,X0_46) = k5_relat_1(X1_46,X0_46) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_639,plain,
    ( k4_relset_1(X0_47,X1_47,X2_47,X3_47,X0_46,X1_46) = k5_relat_1(X0_46,X1_46)
    | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
    | m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(X2_47,X3_47))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_368])).

cnf(c_1320,plain,
    ( k4_relset_1(X0_47,X1_47,sK0,sK0,X0_46,sK2) = k5_relat_1(X0_46,sK2)
    | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top ),
    inference(superposition,[status(thm)],[c_641,c_639])).

cnf(c_1447,plain,
    ( k4_relset_1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_643,c_1320])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_371,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
    | ~ m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(X2_47,X3_47)))
    | m1_subset_1(k4_relset_1(X2_47,X3_47,X0_47,X1_47,X1_46,X0_46),k1_zfmisc_1(k2_zfmisc_1(X2_47,X1_47))) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_636,plain,
    ( m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
    | m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(X2_47,X3_47))) != iProver_top
    | m1_subset_1(k4_relset_1(X0_47,X1_47,X2_47,X3_47,X0_46,X1_46),k1_zfmisc_1(k2_zfmisc_1(X0_47,X3_47))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_371])).

cnf(c_1538,plain,
    ( m1_subset_1(k5_relat_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1447,c_636])).

cnf(c_3116,plain,
    ( k5_relat_1(sK1,sK2) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1809,c_21,c_24,c_1538])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_369,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
    | k2_relset_1(X0_47,X1_47,X0_46) = k2_relat_1(X0_46) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_638,plain,
    ( k2_relset_1(X0_47,X1_47,X0_46) = k2_relat_1(X0_46)
    | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_369])).

cnf(c_929,plain,
    ( k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_643,c_638])).

cnf(c_11,negated_conjecture,
    ( k2_relset_1(sK0,sK0,sK1) = sK0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_366,negated_conjecture,
    ( k2_relset_1(sK0,sK0,sK1) = sK0 ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_931,plain,
    ( k2_relat_1(sK1) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_929,c_366])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | k5_relat_1(X1,X0) != X1
    | k2_relat_1(X1) != k1_relat_1(X0)
    | k6_partfun1(k1_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_373,plain,
    ( ~ v1_relat_1(X0_46)
    | ~ v1_relat_1(X1_46)
    | ~ v1_funct_1(X0_46)
    | ~ v1_funct_1(X1_46)
    | k2_relat_1(X1_46) != k1_relat_1(X0_46)
    | k5_relat_1(X1_46,X0_46) != X1_46
    | k6_partfun1(k1_relat_1(X0_46)) = X0_46 ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_634,plain,
    ( k2_relat_1(X0_46) != k1_relat_1(X1_46)
    | k5_relat_1(X0_46,X1_46) != X0_46
    | k6_partfun1(k1_relat_1(X1_46)) = X1_46
    | v1_relat_1(X1_46) != iProver_top
    | v1_relat_1(X0_46) != iProver_top
    | v1_funct_1(X0_46) != iProver_top
    | v1_funct_1(X1_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_373])).

cnf(c_978,plain,
    ( k1_relat_1(X0_46) != sK0
    | k5_relat_1(sK1,X0_46) != sK1
    | k6_partfun1(k1_relat_1(X0_46)) = X0_46
    | v1_relat_1(X0_46) != iProver_top
    | v1_relat_1(sK1) != iProver_top
    | v1_funct_1(X0_46) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_931,c_634])).

cnf(c_19,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_372,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
    | v1_relat_1(X0_46) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_405,plain,
    ( m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
    | v1_relat_1(X0_46) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_372])).

cnf(c_407,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_relat_1(sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_405])).

cnf(c_1176,plain,
    ( v1_funct_1(X0_46) != iProver_top
    | k1_relat_1(X0_46) != sK0
    | k5_relat_1(sK1,X0_46) != sK1
    | k6_partfun1(k1_relat_1(X0_46)) = X0_46
    | v1_relat_1(X0_46) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_978,c_19,c_21,c_407])).

cnf(c_1177,plain,
    ( k1_relat_1(X0_46) != sK0
    | k5_relat_1(sK1,X0_46) != sK1
    | k6_partfun1(k1_relat_1(X0_46)) = X0_46
    | v1_relat_1(X0_46) != iProver_top
    | v1_funct_1(X0_46) != iProver_top ),
    inference(renaming,[status(thm)],[c_1176])).

cnf(c_3132,plain,
    ( k1_relat_1(sK2) != sK0
    | k6_partfun1(k1_relat_1(sK2)) = sK2
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3116,c_1177])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_370,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
    | k1_relset_1(X0_47,X1_47,X0_46) = k1_relat_1(X0_46) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_637,plain,
    ( k1_relset_1(X0_47,X1_47,X0_46) = k1_relat_1(X0_46)
    | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_370])).

cnf(c_917,plain,
    ( k1_relset_1(sK0,sK0,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_641,c_637])).

cnf(c_9,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(X1,X1,X0) = X1 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_14,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_199,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(X1,X1,X0) = X1
    | sK2 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_14])).

cnf(c_200,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | k1_relset_1(sK0,sK0,sK2) = sK0 ),
    inference(unflattening,[status(thm)],[c_199])).

cnf(c_202,plain,
    ( k1_relset_1(sK0,sK0,sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_200,c_15,c_13])).

cnf(c_361,plain,
    ( k1_relset_1(sK0,sK0,sK2) = sK0 ),
    inference(subtyping,[status(esa)],[c_202])).

cnf(c_923,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_917,c_361])).

cnf(c_3133,plain,
    ( sK0 != sK0
    | k6_partfun1(sK0) = sK2
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3132,c_923])).

cnf(c_3134,plain,
    ( k6_partfun1(sK0) = sK2
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3133])).

cnf(c_635,plain,
    ( m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
    | v1_relat_1(X0_46) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_372])).

cnf(c_874,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_641,c_635])).

cnf(c_379,plain,
    ( X0_46 != X1_46
    | X2_46 != X1_46
    | X2_46 = X0_46 ),
    theory(equality)).

cnf(c_753,plain,
    ( k6_partfun1(sK0) != X0_46
    | sK2 != X0_46
    | sK2 = k6_partfun1(sK0) ),
    inference(instantiation,[status(thm)],[c_379])).

cnf(c_820,plain,
    ( k6_partfun1(sK0) != sK2
    | sK2 = k6_partfun1(sK0)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_753])).

cnf(c_377,plain,
    ( X0_48 = X0_48 ),
    theory(equality)).

cnf(c_787,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_377])).

cnf(c_375,plain,
    ( X0_46 = X0_46 ),
    theory(equality)).

cnf(c_779,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_375])).

cnf(c_6,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_10,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_219,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k6_partfun1(sK0) != X0
    | sK2 != X0
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_10])).

cnf(c_220,plain,
    ( ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK2 != k6_partfun1(sK0) ),
    inference(unflattening,[status(thm)],[c_219])).

cnf(c_359,plain,
    ( ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK2 != k6_partfun1(sK0) ),
    inference(subtyping,[status(esa)],[c_220])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4629,c_3134,c_874,c_820,c_787,c_779,c_359,c_13,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:42:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.30/0.96  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.30/0.96  
% 3.30/0.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.30/0.96  
% 3.30/0.96  ------  iProver source info
% 3.30/0.96  
% 3.30/0.96  git: date: 2020-06-30 10:37:57 +0100
% 3.30/0.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.30/0.96  git: non_committed_changes: false
% 3.30/0.96  git: last_make_outside_of_git: false
% 3.30/0.96  
% 3.30/0.96  ------ 
% 3.30/0.96  
% 3.30/0.96  ------ Input Options
% 3.30/0.96  
% 3.30/0.96  --out_options                           all
% 3.30/0.96  --tptp_safe_out                         true
% 3.30/0.96  --problem_path                          ""
% 3.30/0.96  --include_path                          ""
% 3.30/0.96  --clausifier                            res/vclausify_rel
% 3.30/0.96  --clausifier_options                    --mode clausify
% 3.30/0.96  --stdin                                 false
% 3.30/0.96  --stats_out                             all
% 3.30/0.96  
% 3.30/0.96  ------ General Options
% 3.30/0.96  
% 3.30/0.96  --fof                                   false
% 3.30/0.96  --time_out_real                         305.
% 3.30/0.96  --time_out_virtual                      -1.
% 3.30/0.96  --symbol_type_check                     false
% 3.30/0.96  --clausify_out                          false
% 3.30/0.96  --sig_cnt_out                           false
% 3.30/0.96  --trig_cnt_out                          false
% 3.30/0.96  --trig_cnt_out_tolerance                1.
% 3.30/0.96  --trig_cnt_out_sk_spl                   false
% 3.30/0.96  --abstr_cl_out                          false
% 3.30/0.96  
% 3.30/0.96  ------ Global Options
% 3.30/0.96  
% 3.30/0.96  --schedule                              default
% 3.30/0.96  --add_important_lit                     false
% 3.30/0.96  --prop_solver_per_cl                    1000
% 3.30/0.96  --min_unsat_core                        false
% 3.30/0.96  --soft_assumptions                      false
% 3.30/0.96  --soft_lemma_size                       3
% 3.30/0.96  --prop_impl_unit_size                   0
% 3.30/0.96  --prop_impl_unit                        []
% 3.30/0.96  --share_sel_clauses                     true
% 3.30/0.96  --reset_solvers                         false
% 3.30/0.96  --bc_imp_inh                            [conj_cone]
% 3.30/0.96  --conj_cone_tolerance                   3.
% 3.30/0.96  --extra_neg_conj                        none
% 3.30/0.96  --large_theory_mode                     true
% 3.30/0.96  --prolific_symb_bound                   200
% 3.30/0.96  --lt_threshold                          2000
% 3.30/0.96  --clause_weak_htbl                      true
% 3.30/0.96  --gc_record_bc_elim                     false
% 3.30/0.96  
% 3.30/0.96  ------ Preprocessing Options
% 3.30/0.96  
% 3.30/0.96  --preprocessing_flag                    true
% 3.30/0.96  --time_out_prep_mult                    0.1
% 3.30/0.96  --splitting_mode                        input
% 3.30/0.96  --splitting_grd                         true
% 3.30/0.96  --splitting_cvd                         false
% 3.30/0.96  --splitting_cvd_svl                     false
% 3.30/0.96  --splitting_nvd                         32
% 3.30/0.96  --sub_typing                            true
% 3.30/0.96  --prep_gs_sim                           true
% 3.30/0.96  --prep_unflatten                        true
% 3.30/0.96  --prep_res_sim                          true
% 3.30/0.96  --prep_upred                            true
% 3.30/0.96  --prep_sem_filter                       exhaustive
% 3.30/0.96  --prep_sem_filter_out                   false
% 3.30/0.96  --pred_elim                             true
% 3.30/0.96  --res_sim_input                         true
% 3.30/0.96  --eq_ax_congr_red                       true
% 3.30/0.96  --pure_diseq_elim                       true
% 3.30/0.96  --brand_transform                       false
% 3.30/0.96  --non_eq_to_eq                          false
% 3.30/0.96  --prep_def_merge                        true
% 3.30/0.96  --prep_def_merge_prop_impl              false
% 3.30/0.96  --prep_def_merge_mbd                    true
% 3.30/0.96  --prep_def_merge_tr_red                 false
% 3.30/0.96  --prep_def_merge_tr_cl                  false
% 3.30/0.96  --smt_preprocessing                     true
% 3.30/0.96  --smt_ac_axioms                         fast
% 3.30/0.96  --preprocessed_out                      false
% 3.30/0.96  --preprocessed_stats                    false
% 3.30/0.96  
% 3.30/0.96  ------ Abstraction refinement Options
% 3.30/0.96  
% 3.30/0.96  --abstr_ref                             []
% 3.30/0.96  --abstr_ref_prep                        false
% 3.30/0.96  --abstr_ref_until_sat                   false
% 3.30/0.96  --abstr_ref_sig_restrict                funpre
% 3.30/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 3.30/0.96  --abstr_ref_under                       []
% 3.30/0.96  
% 3.30/0.96  ------ SAT Options
% 3.30/0.96  
% 3.30/0.96  --sat_mode                              false
% 3.30/0.96  --sat_fm_restart_options                ""
% 3.30/0.96  --sat_gr_def                            false
% 3.30/0.96  --sat_epr_types                         true
% 3.30/0.96  --sat_non_cyclic_types                  false
% 3.30/0.96  --sat_finite_models                     false
% 3.30/0.96  --sat_fm_lemmas                         false
% 3.30/0.96  --sat_fm_prep                           false
% 3.30/0.96  --sat_fm_uc_incr                        true
% 3.30/0.96  --sat_out_model                         small
% 3.30/0.96  --sat_out_clauses                       false
% 3.30/0.96  
% 3.30/0.96  ------ QBF Options
% 3.30/0.96  
% 3.30/0.96  --qbf_mode                              false
% 3.30/0.96  --qbf_elim_univ                         false
% 3.30/0.96  --qbf_dom_inst                          none
% 3.30/0.96  --qbf_dom_pre_inst                      false
% 3.30/0.96  --qbf_sk_in                             false
% 3.30/0.96  --qbf_pred_elim                         true
% 3.30/0.96  --qbf_split                             512
% 3.30/0.96  
% 3.30/0.96  ------ BMC1 Options
% 3.30/0.96  
% 3.30/0.96  --bmc1_incremental                      false
% 3.30/0.96  --bmc1_axioms                           reachable_all
% 3.30/0.96  --bmc1_min_bound                        0
% 3.30/0.96  --bmc1_max_bound                        -1
% 3.30/0.96  --bmc1_max_bound_default                -1
% 3.30/0.96  --bmc1_symbol_reachability              true
% 3.30/0.96  --bmc1_property_lemmas                  false
% 3.30/0.96  --bmc1_k_induction                      false
% 3.30/0.96  --bmc1_non_equiv_states                 false
% 3.30/0.96  --bmc1_deadlock                         false
% 3.30/0.96  --bmc1_ucm                              false
% 3.30/0.96  --bmc1_add_unsat_core                   none
% 3.30/0.96  --bmc1_unsat_core_children              false
% 3.30/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 3.30/0.96  --bmc1_out_stat                         full
% 3.30/0.96  --bmc1_ground_init                      false
% 3.30/0.96  --bmc1_pre_inst_next_state              false
% 3.30/0.96  --bmc1_pre_inst_state                   false
% 3.30/0.96  --bmc1_pre_inst_reach_state             false
% 3.30/0.96  --bmc1_out_unsat_core                   false
% 3.30/0.96  --bmc1_aig_witness_out                  false
% 3.30/0.96  --bmc1_verbose                          false
% 3.30/0.96  --bmc1_dump_clauses_tptp                false
% 3.30/0.96  --bmc1_dump_unsat_core_tptp             false
% 3.30/0.96  --bmc1_dump_file                        -
% 3.30/0.96  --bmc1_ucm_expand_uc_limit              128
% 3.30/0.96  --bmc1_ucm_n_expand_iterations          6
% 3.30/0.96  --bmc1_ucm_extend_mode                  1
% 3.30/0.96  --bmc1_ucm_init_mode                    2
% 3.30/0.96  --bmc1_ucm_cone_mode                    none
% 3.30/0.96  --bmc1_ucm_reduced_relation_type        0
% 3.30/0.96  --bmc1_ucm_relax_model                  4
% 3.30/0.96  --bmc1_ucm_full_tr_after_sat            true
% 3.30/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 3.30/0.96  --bmc1_ucm_layered_model                none
% 3.30/0.96  --bmc1_ucm_max_lemma_size               10
% 3.30/0.96  
% 3.30/0.96  ------ AIG Options
% 3.30/0.96  
% 3.30/0.96  --aig_mode                              false
% 3.30/0.96  
% 3.30/0.96  ------ Instantiation Options
% 3.30/0.96  
% 3.30/0.96  --instantiation_flag                    true
% 3.30/0.96  --inst_sos_flag                         false
% 3.30/0.96  --inst_sos_phase                        true
% 3.30/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.30/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.30/0.96  --inst_lit_sel_side                     num_symb
% 3.30/0.96  --inst_solver_per_active                1400
% 3.30/0.96  --inst_solver_calls_frac                1.
% 3.30/0.96  --inst_passive_queue_type               priority_queues
% 3.30/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.30/0.96  --inst_passive_queues_freq              [25;2]
% 3.30/0.96  --inst_dismatching                      true
% 3.30/0.96  --inst_eager_unprocessed_to_passive     true
% 3.30/0.96  --inst_prop_sim_given                   true
% 3.30/0.96  --inst_prop_sim_new                     false
% 3.30/0.96  --inst_subs_new                         false
% 3.30/0.96  --inst_eq_res_simp                      false
% 3.30/0.96  --inst_subs_given                       false
% 3.30/0.96  --inst_orphan_elimination               true
% 3.30/0.96  --inst_learning_loop_flag               true
% 3.30/0.96  --inst_learning_start                   3000
% 3.30/0.96  --inst_learning_factor                  2
% 3.30/0.96  --inst_start_prop_sim_after_learn       3
% 3.30/0.96  --inst_sel_renew                        solver
% 3.30/0.96  --inst_lit_activity_flag                true
% 3.30/0.96  --inst_restr_to_given                   false
% 3.30/0.96  --inst_activity_threshold               500
% 3.30/0.96  --inst_out_proof                        true
% 3.30/0.96  
% 3.30/0.96  ------ Resolution Options
% 3.30/0.96  
% 3.30/0.96  --resolution_flag                       true
% 3.30/0.96  --res_lit_sel                           adaptive
% 3.30/0.96  --res_lit_sel_side                      none
% 3.30/0.96  --res_ordering                          kbo
% 3.30/0.96  --res_to_prop_solver                    active
% 3.30/0.96  --res_prop_simpl_new                    false
% 3.30/0.96  --res_prop_simpl_given                  true
% 3.30/0.96  --res_passive_queue_type                priority_queues
% 3.30/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.30/0.96  --res_passive_queues_freq               [15;5]
% 3.30/0.96  --res_forward_subs                      full
% 3.30/0.96  --res_backward_subs                     full
% 3.30/0.96  --res_forward_subs_resolution           true
% 3.30/0.96  --res_backward_subs_resolution          true
% 3.30/0.96  --res_orphan_elimination                true
% 3.30/0.96  --res_time_limit                        2.
% 3.30/0.96  --res_out_proof                         true
% 3.30/0.96  
% 3.30/0.96  ------ Superposition Options
% 3.30/0.96  
% 3.30/0.96  --superposition_flag                    true
% 3.30/0.96  --sup_passive_queue_type                priority_queues
% 3.30/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.30/0.96  --sup_passive_queues_freq               [8;1;4]
% 3.30/0.96  --demod_completeness_check              fast
% 3.30/0.96  --demod_use_ground                      true
% 3.30/0.96  --sup_to_prop_solver                    passive
% 3.30/0.96  --sup_prop_simpl_new                    true
% 3.30/0.96  --sup_prop_simpl_given                  true
% 3.30/0.96  --sup_fun_splitting                     false
% 3.30/0.96  --sup_smt_interval                      50000
% 3.30/0.96  
% 3.30/0.96  ------ Superposition Simplification Setup
% 3.30/0.96  
% 3.30/0.96  --sup_indices_passive                   []
% 3.30/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.30/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.30/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.30/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 3.30/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.30/0.96  --sup_full_bw                           [BwDemod]
% 3.30/0.96  --sup_immed_triv                        [TrivRules]
% 3.30/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.30/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.30/0.96  --sup_immed_bw_main                     []
% 3.30/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.30/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 3.30/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.30/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.30/0.96  
% 3.30/0.96  ------ Combination Options
% 3.30/0.96  
% 3.30/0.96  --comb_res_mult                         3
% 3.30/0.96  --comb_sup_mult                         2
% 3.30/0.96  --comb_inst_mult                        10
% 3.30/0.96  
% 3.30/0.96  ------ Debug Options
% 3.30/0.96  
% 3.30/0.96  --dbg_backtrace                         false
% 3.30/0.96  --dbg_dump_prop_clauses                 false
% 3.30/0.96  --dbg_dump_prop_clauses_file            -
% 3.30/0.96  --dbg_out_stat                          false
% 3.30/0.96  ------ Parsing...
% 3.30/0.96  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.30/0.96  
% 3.30/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.30/0.96  
% 3.30/0.96  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.30/0.96  
% 3.30/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.30/0.96  ------ Proving...
% 3.30/0.96  ------ Problem Properties 
% 3.30/0.96  
% 3.30/0.96  
% 3.30/0.96  clauses                                 17
% 3.30/0.96  conjectures                             5
% 3.30/0.96  EPR                                     2
% 3.30/0.96  Horn                                    17
% 3.30/0.96  unary                                   7
% 3.30/0.96  binary                                  6
% 3.30/0.96  lits                                    37
% 3.30/0.96  lits eq                                 14
% 3.30/0.96  fd_pure                                 0
% 3.30/0.96  fd_pseudo                               0
% 3.30/0.96  fd_cond                                 0
% 3.30/0.96  fd_pseudo_cond                          0
% 3.30/0.96  AC symbols                              0
% 3.30/0.96  
% 3.30/0.96  ------ Schedule dynamic 5 is on 
% 3.30/0.96  
% 3.30/0.96  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.30/0.96  
% 3.30/0.96  
% 3.30/0.96  ------ 
% 3.30/0.96  Current options:
% 3.30/0.96  ------ 
% 3.30/0.96  
% 3.30/0.96  ------ Input Options
% 3.30/0.96  
% 3.30/0.96  --out_options                           all
% 3.30/0.96  --tptp_safe_out                         true
% 3.30/0.96  --problem_path                          ""
% 3.30/0.96  --include_path                          ""
% 3.30/0.96  --clausifier                            res/vclausify_rel
% 3.30/0.96  --clausifier_options                    --mode clausify
% 3.30/0.96  --stdin                                 false
% 3.30/0.96  --stats_out                             all
% 3.30/0.96  
% 3.30/0.96  ------ General Options
% 3.30/0.96  
% 3.30/0.96  --fof                                   false
% 3.30/0.96  --time_out_real                         305.
% 3.30/0.96  --time_out_virtual                      -1.
% 3.30/0.96  --symbol_type_check                     false
% 3.30/0.96  --clausify_out                          false
% 3.30/0.96  --sig_cnt_out                           false
% 3.30/0.96  --trig_cnt_out                          false
% 3.30/0.96  --trig_cnt_out_tolerance                1.
% 3.30/0.96  --trig_cnt_out_sk_spl                   false
% 3.30/0.96  --abstr_cl_out                          false
% 3.30/0.96  
% 3.30/0.96  ------ Global Options
% 3.30/0.96  
% 3.30/0.96  --schedule                              default
% 3.30/0.96  --add_important_lit                     false
% 3.30/0.96  --prop_solver_per_cl                    1000
% 3.30/0.96  --min_unsat_core                        false
% 3.30/0.96  --soft_assumptions                      false
% 3.30/0.96  --soft_lemma_size                       3
% 3.30/0.96  --prop_impl_unit_size                   0
% 3.30/0.96  --prop_impl_unit                        []
% 3.30/0.96  --share_sel_clauses                     true
% 3.30/0.96  --reset_solvers                         false
% 3.30/0.96  --bc_imp_inh                            [conj_cone]
% 3.30/0.96  --conj_cone_tolerance                   3.
% 3.30/0.96  --extra_neg_conj                        none
% 3.30/0.96  --large_theory_mode                     true
% 3.30/0.96  --prolific_symb_bound                   200
% 3.30/0.96  --lt_threshold                          2000
% 3.30/0.96  --clause_weak_htbl                      true
% 3.30/0.96  --gc_record_bc_elim                     false
% 3.30/0.96  
% 3.30/0.96  ------ Preprocessing Options
% 3.30/0.96  
% 3.30/0.96  --preprocessing_flag                    true
% 3.30/0.96  --time_out_prep_mult                    0.1
% 3.30/0.96  --splitting_mode                        input
% 3.30/0.96  --splitting_grd                         true
% 3.30/0.96  --splitting_cvd                         false
% 3.30/0.96  --splitting_cvd_svl                     false
% 3.30/0.96  --splitting_nvd                         32
% 3.30/0.96  --sub_typing                            true
% 3.30/0.96  --prep_gs_sim                           true
% 3.30/0.96  --prep_unflatten                        true
% 3.30/0.96  --prep_res_sim                          true
% 3.30/0.96  --prep_upred                            true
% 3.30/0.96  --prep_sem_filter                       exhaustive
% 3.30/0.96  --prep_sem_filter_out                   false
% 3.30/0.96  --pred_elim                             true
% 3.30/0.96  --res_sim_input                         true
% 3.30/0.96  --eq_ax_congr_red                       true
% 3.30/0.96  --pure_diseq_elim                       true
% 3.30/0.96  --brand_transform                       false
% 3.30/0.96  --non_eq_to_eq                          false
% 3.30/0.96  --prep_def_merge                        true
% 3.30/0.96  --prep_def_merge_prop_impl              false
% 3.30/0.96  --prep_def_merge_mbd                    true
% 3.30/0.96  --prep_def_merge_tr_red                 false
% 3.30/0.96  --prep_def_merge_tr_cl                  false
% 3.30/0.96  --smt_preprocessing                     true
% 3.30/0.96  --smt_ac_axioms                         fast
% 3.30/0.96  --preprocessed_out                      false
% 3.30/0.96  --preprocessed_stats                    false
% 3.30/0.96  
% 3.30/0.96  ------ Abstraction refinement Options
% 3.30/0.96  
% 3.30/0.96  --abstr_ref                             []
% 3.30/0.96  --abstr_ref_prep                        false
% 3.30/0.96  --abstr_ref_until_sat                   false
% 3.30/0.96  --abstr_ref_sig_restrict                funpre
% 3.30/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 3.30/0.96  --abstr_ref_under                       []
% 3.30/0.96  
% 3.30/0.96  ------ SAT Options
% 3.30/0.96  
% 3.30/0.96  --sat_mode                              false
% 3.30/0.96  --sat_fm_restart_options                ""
% 3.30/0.96  --sat_gr_def                            false
% 3.30/0.96  --sat_epr_types                         true
% 3.30/0.96  --sat_non_cyclic_types                  false
% 3.30/0.96  --sat_finite_models                     false
% 3.30/0.96  --sat_fm_lemmas                         false
% 3.30/0.96  --sat_fm_prep                           false
% 3.30/0.96  --sat_fm_uc_incr                        true
% 3.30/0.96  --sat_out_model                         small
% 3.30/0.96  --sat_out_clauses                       false
% 3.30/0.96  
% 3.30/0.96  ------ QBF Options
% 3.30/0.96  
% 3.30/0.96  --qbf_mode                              false
% 3.30/0.96  --qbf_elim_univ                         false
% 3.30/0.96  --qbf_dom_inst                          none
% 3.30/0.96  --qbf_dom_pre_inst                      false
% 3.30/0.96  --qbf_sk_in                             false
% 3.30/0.96  --qbf_pred_elim                         true
% 3.30/0.96  --qbf_split                             512
% 3.30/0.96  
% 3.30/0.96  ------ BMC1 Options
% 3.30/0.96  
% 3.30/0.96  --bmc1_incremental                      false
% 3.30/0.96  --bmc1_axioms                           reachable_all
% 3.30/0.96  --bmc1_min_bound                        0
% 3.30/0.96  --bmc1_max_bound                        -1
% 3.30/0.96  --bmc1_max_bound_default                -1
% 3.30/0.96  --bmc1_symbol_reachability              true
% 3.30/0.96  --bmc1_property_lemmas                  false
% 3.30/0.96  --bmc1_k_induction                      false
% 3.30/0.96  --bmc1_non_equiv_states                 false
% 3.30/0.96  --bmc1_deadlock                         false
% 3.30/0.96  --bmc1_ucm                              false
% 3.30/0.96  --bmc1_add_unsat_core                   none
% 3.30/0.96  --bmc1_unsat_core_children              false
% 3.30/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 3.30/0.96  --bmc1_out_stat                         full
% 3.30/0.96  --bmc1_ground_init                      false
% 3.30/0.96  --bmc1_pre_inst_next_state              false
% 3.30/0.96  --bmc1_pre_inst_state                   false
% 3.30/0.96  --bmc1_pre_inst_reach_state             false
% 3.30/0.96  --bmc1_out_unsat_core                   false
% 3.30/0.96  --bmc1_aig_witness_out                  false
% 3.30/0.96  --bmc1_verbose                          false
% 3.30/0.96  --bmc1_dump_clauses_tptp                false
% 3.30/0.96  --bmc1_dump_unsat_core_tptp             false
% 3.30/0.96  --bmc1_dump_file                        -
% 3.30/0.96  --bmc1_ucm_expand_uc_limit              128
% 3.30/0.96  --bmc1_ucm_n_expand_iterations          6
% 3.30/0.96  --bmc1_ucm_extend_mode                  1
% 3.30/0.96  --bmc1_ucm_init_mode                    2
% 3.30/0.96  --bmc1_ucm_cone_mode                    none
% 3.30/0.96  --bmc1_ucm_reduced_relation_type        0
% 3.30/0.96  --bmc1_ucm_relax_model                  4
% 3.30/0.96  --bmc1_ucm_full_tr_after_sat            true
% 3.30/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 3.30/0.96  --bmc1_ucm_layered_model                none
% 3.30/0.96  --bmc1_ucm_max_lemma_size               10
% 3.30/0.96  
% 3.30/0.96  ------ AIG Options
% 3.30/0.96  
% 3.30/0.96  --aig_mode                              false
% 3.30/0.96  
% 3.30/0.96  ------ Instantiation Options
% 3.30/0.96  
% 3.30/0.96  --instantiation_flag                    true
% 3.30/0.96  --inst_sos_flag                         false
% 3.30/0.96  --inst_sos_phase                        true
% 3.30/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.30/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.30/0.96  --inst_lit_sel_side                     none
% 3.30/0.96  --inst_solver_per_active                1400
% 3.30/0.96  --inst_solver_calls_frac                1.
% 3.30/0.96  --inst_passive_queue_type               priority_queues
% 3.30/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.30/0.96  --inst_passive_queues_freq              [25;2]
% 3.30/0.96  --inst_dismatching                      true
% 3.30/0.96  --inst_eager_unprocessed_to_passive     true
% 3.30/0.96  --inst_prop_sim_given                   true
% 3.30/0.96  --inst_prop_sim_new                     false
% 3.30/0.96  --inst_subs_new                         false
% 3.30/0.96  --inst_eq_res_simp                      false
% 3.30/0.96  --inst_subs_given                       false
% 3.30/0.96  --inst_orphan_elimination               true
% 3.30/0.96  --inst_learning_loop_flag               true
% 3.30/0.96  --inst_learning_start                   3000
% 3.30/0.96  --inst_learning_factor                  2
% 3.30/0.96  --inst_start_prop_sim_after_learn       3
% 3.30/0.96  --inst_sel_renew                        solver
% 3.30/0.96  --inst_lit_activity_flag                true
% 3.30/0.96  --inst_restr_to_given                   false
% 3.30/0.96  --inst_activity_threshold               500
% 3.30/0.96  --inst_out_proof                        true
% 3.30/0.96  
% 3.30/0.96  ------ Resolution Options
% 3.30/0.96  
% 3.30/0.96  --resolution_flag                       false
% 3.30/0.96  --res_lit_sel                           adaptive
% 3.30/0.96  --res_lit_sel_side                      none
% 3.30/0.96  --res_ordering                          kbo
% 3.30/0.96  --res_to_prop_solver                    active
% 3.30/0.96  --res_prop_simpl_new                    false
% 3.30/0.96  --res_prop_simpl_given                  true
% 3.30/0.96  --res_passive_queue_type                priority_queues
% 3.30/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.30/0.96  --res_passive_queues_freq               [15;5]
% 3.30/0.96  --res_forward_subs                      full
% 3.30/0.96  --res_backward_subs                     full
% 3.30/0.96  --res_forward_subs_resolution           true
% 3.30/0.96  --res_backward_subs_resolution          true
% 3.30/0.96  --res_orphan_elimination                true
% 3.30/0.96  --res_time_limit                        2.
% 3.30/0.96  --res_out_proof                         true
% 3.30/0.96  
% 3.30/0.96  ------ Superposition Options
% 3.30/0.96  
% 3.30/0.96  --superposition_flag                    true
% 3.30/0.96  --sup_passive_queue_type                priority_queues
% 3.30/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.30/0.96  --sup_passive_queues_freq               [8;1;4]
% 3.30/0.96  --demod_completeness_check              fast
% 3.30/0.96  --demod_use_ground                      true
% 3.30/0.96  --sup_to_prop_solver                    passive
% 3.30/0.96  --sup_prop_simpl_new                    true
% 3.30/0.96  --sup_prop_simpl_given                  true
% 3.30/0.96  --sup_fun_splitting                     false
% 3.30/0.96  --sup_smt_interval                      50000
% 3.30/0.96  
% 3.30/0.96  ------ Superposition Simplification Setup
% 3.30/0.96  
% 3.30/0.96  --sup_indices_passive                   []
% 3.30/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.30/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.30/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.30/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 3.30/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.30/0.96  --sup_full_bw                           [BwDemod]
% 3.30/0.96  --sup_immed_triv                        [TrivRules]
% 3.30/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.30/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.30/0.96  --sup_immed_bw_main                     []
% 3.30/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.30/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 3.30/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.30/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.30/0.96  
% 3.30/0.96  ------ Combination Options
% 3.30/0.96  
% 3.30/0.96  --comb_res_mult                         3
% 3.30/0.96  --comb_sup_mult                         2
% 3.30/0.96  --comb_inst_mult                        10
% 3.30/0.96  
% 3.30/0.96  ------ Debug Options
% 3.30/0.96  
% 3.30/0.96  --dbg_backtrace                         false
% 3.30/0.96  --dbg_dump_prop_clauses                 false
% 3.30/0.96  --dbg_dump_prop_clauses_file            -
% 3.30/0.96  --dbg_out_stat                          false
% 3.30/0.96  
% 3.30/0.96  
% 3.30/0.96  
% 3.30/0.96  
% 3.30/0.96  ------ Proving...
% 3.30/0.96  
% 3.30/0.96  
% 3.30/0.96  % SZS status Theorem for theBenchmark.p
% 3.30/0.96  
% 3.30/0.96  % SZS output start CNFRefutation for theBenchmark.p
% 3.30/0.96  
% 3.30/0.96  fof(f11,conjecture,(
% 3.30/0.96    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((k2_relset_1(X0,X0,X1) = X0 & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1)) => r2_relset_1(X0,X0,X2,k6_partfun1(X0)))))),
% 3.30/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.30/0.96  
% 3.30/0.96  fof(f12,negated_conjecture,(
% 3.30/0.96    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((k2_relset_1(X0,X0,X1) = X0 & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1)) => r2_relset_1(X0,X0,X2,k6_partfun1(X0)))))),
% 3.30/0.96    inference(negated_conjecture,[],[f11])).
% 3.30/0.96  
% 3.30/0.96  fof(f28,plain,(
% 3.30/0.96    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & (k2_relset_1(X0,X0,X1) = X0 & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 3.30/0.96    inference(ennf_transformation,[],[f12])).
% 3.30/0.96  
% 3.30/0.96  fof(f29,plain,(
% 3.30/0.96    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & k2_relset_1(X0,X0,X1) = X0 & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 3.30/0.96    inference(flattening,[],[f28])).
% 3.30/0.96  
% 3.30/0.96  fof(f32,plain,(
% 3.30/0.96    ( ! [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & k2_relset_1(X0,X0,X1) = X0 & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (~r2_relset_1(X0,X0,sK2,k6_partfun1(X0)) & k2_relset_1(X0,X0,X1) = X0 & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,sK2),X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(sK2,X0,X0) & v1_funct_1(sK2))) )),
% 3.30/0.96    introduced(choice_axiom,[])).
% 3.30/0.96  
% 3.30/0.96  fof(f31,plain,(
% 3.30/0.96    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & k2_relset_1(X0,X0,X1) = X0 & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK0,sK0,X2,k6_partfun1(sK0)) & k2_relset_1(sK0,sK0,sK1) = sK0 & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 3.30/0.96    introduced(choice_axiom,[])).
% 3.30/0.96  
% 3.30/0.96  fof(f33,plain,(
% 3.30/0.96    (~r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0)) & k2_relset_1(sK0,sK0,sK1) = sK0 & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 3.30/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f32,f31])).
% 3.30/0.96  
% 3.30/0.96  fof(f47,plain,(
% 3.30/0.96    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.30/0.96    inference(cnf_transformation,[],[f33])).
% 3.30/0.96  
% 3.30/0.96  fof(f50,plain,(
% 3.30/0.96    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.30/0.96    inference(cnf_transformation,[],[f33])).
% 3.30/0.96  
% 3.30/0.96  fof(f8,axiom,(
% 3.30/0.96    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.30/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.30/0.96  
% 3.30/0.96  fof(f24,plain,(
% 3.30/0.96    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.30/0.96    inference(ennf_transformation,[],[f8])).
% 3.30/0.96  
% 3.30/0.96  fof(f25,plain,(
% 3.30/0.96    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.30/0.96    inference(flattening,[],[f24])).
% 3.30/0.96  
% 3.30/0.96  fof(f42,plain,(
% 3.30/0.96    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.30/0.96    inference(cnf_transformation,[],[f25])).
% 3.30/0.96  
% 3.30/0.96  fof(f48,plain,(
% 3.30/0.96    v1_funct_1(sK2)),
% 3.30/0.96    inference(cnf_transformation,[],[f33])).
% 3.30/0.96  
% 3.30/0.96  fof(f45,plain,(
% 3.30/0.96    v1_funct_1(sK1)),
% 3.30/0.96    inference(cnf_transformation,[],[f33])).
% 3.30/0.96  
% 3.30/0.96  fof(f7,axiom,(
% 3.30/0.96    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.30/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.30/0.96  
% 3.30/0.96  fof(f22,plain,(
% 3.30/0.96    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.30/0.96    inference(ennf_transformation,[],[f7])).
% 3.30/0.96  
% 3.30/0.96  fof(f23,plain,(
% 3.30/0.96    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.30/0.96    inference(flattening,[],[f22])).
% 3.30/0.96  
% 3.30/0.96  fof(f30,plain,(
% 3.30/0.96    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.30/0.96    inference(nnf_transformation,[],[f23])).
% 3.30/0.96  
% 3.30/0.96  fof(f40,plain,(
% 3.30/0.96    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.30/0.96    inference(cnf_transformation,[],[f30])).
% 3.30/0.96  
% 3.30/0.96  fof(f51,plain,(
% 3.30/0.96    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),sK1)),
% 3.30/0.96    inference(cnf_transformation,[],[f33])).
% 3.30/0.96  
% 3.30/0.96  fof(f6,axiom,(
% 3.30/0.96    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5))),
% 3.30/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.30/0.96  
% 3.30/0.96  fof(f20,plain,(
% 3.30/0.96    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.30/0.96    inference(ennf_transformation,[],[f6])).
% 3.30/0.96  
% 3.30/0.96  fof(f21,plain,(
% 3.30/0.96    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.30/0.96    inference(flattening,[],[f20])).
% 3.30/0.96  
% 3.30/0.96  fof(f39,plain,(
% 3.30/0.96    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.30/0.96    inference(cnf_transformation,[],[f21])).
% 3.30/0.96  
% 3.30/0.96  fof(f3,axiom,(
% 3.30/0.96    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))))),
% 3.30/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.30/0.96  
% 3.30/0.96  fof(f16,plain,(
% 3.30/0.96    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.30/0.96    inference(ennf_transformation,[],[f3])).
% 3.30/0.96  
% 3.30/0.96  fof(f17,plain,(
% 3.30/0.96    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.30/0.96    inference(flattening,[],[f16])).
% 3.30/0.96  
% 3.30/0.96  fof(f36,plain,(
% 3.30/0.96    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.30/0.96    inference(cnf_transformation,[],[f17])).
% 3.30/0.96  
% 3.30/0.96  fof(f5,axiom,(
% 3.30/0.96    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.30/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.30/0.96  
% 3.30/0.96  fof(f19,plain,(
% 3.30/0.96    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.30/0.96    inference(ennf_transformation,[],[f5])).
% 3.30/0.96  
% 3.30/0.96  fof(f38,plain,(
% 3.30/0.96    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.30/0.96    inference(cnf_transformation,[],[f19])).
% 3.30/0.96  
% 3.30/0.96  fof(f52,plain,(
% 3.30/0.96    k2_relset_1(sK0,sK0,sK1) = sK0),
% 3.30/0.96    inference(cnf_transformation,[],[f33])).
% 3.30/0.96  
% 3.30/0.96  fof(f1,axiom,(
% 3.30/0.96    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = X0 & k2_relat_1(X0) = k1_relat_1(X1)) => k6_relat_1(k1_relat_1(X1)) = X1)))),
% 3.30/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.30/0.96  
% 3.30/0.96  fof(f13,plain,(
% 3.30/0.96    ! [X0] : (! [X1] : ((k6_relat_1(k1_relat_1(X1)) = X1 | (k5_relat_1(X0,X1) != X0 | k2_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.30/0.96    inference(ennf_transformation,[],[f1])).
% 3.30/0.96  
% 3.30/0.96  fof(f14,plain,(
% 3.30/0.96    ! [X0] : (! [X1] : (k6_relat_1(k1_relat_1(X1)) = X1 | k5_relat_1(X0,X1) != X0 | k2_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.30/0.96    inference(flattening,[],[f13])).
% 3.30/0.96  
% 3.30/0.96  fof(f34,plain,(
% 3.30/0.96    ( ! [X0,X1] : (k6_relat_1(k1_relat_1(X1)) = X1 | k5_relat_1(X0,X1) != X0 | k2_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.30/0.96    inference(cnf_transformation,[],[f14])).
% 3.30/0.96  
% 3.30/0.96  fof(f9,axiom,(
% 3.30/0.96    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.30/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.30/0.96  
% 3.30/0.96  fof(f43,plain,(
% 3.30/0.96    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.30/0.96    inference(cnf_transformation,[],[f9])).
% 3.30/0.96  
% 3.30/0.96  fof(f54,plain,(
% 3.30/0.96    ( ! [X0,X1] : (k6_partfun1(k1_relat_1(X1)) = X1 | k5_relat_1(X0,X1) != X0 | k2_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.30/0.96    inference(definition_unfolding,[],[f34,f43])).
% 3.30/0.96  
% 3.30/0.96  fof(f2,axiom,(
% 3.30/0.96    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.30/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.30/0.96  
% 3.30/0.96  fof(f15,plain,(
% 3.30/0.96    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.30/0.96    inference(ennf_transformation,[],[f2])).
% 3.30/0.96  
% 3.30/0.96  fof(f35,plain,(
% 3.30/0.96    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.30/0.96    inference(cnf_transformation,[],[f15])).
% 3.30/0.96  
% 3.30/0.96  fof(f4,axiom,(
% 3.30/0.96    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.30/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.30/0.96  
% 3.30/0.96  fof(f18,plain,(
% 3.30/0.96    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.30/0.96    inference(ennf_transformation,[],[f4])).
% 3.30/0.96  
% 3.30/0.96  fof(f37,plain,(
% 3.30/0.96    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.30/0.96    inference(cnf_transformation,[],[f18])).
% 3.30/0.96  
% 3.30/0.96  fof(f10,axiom,(
% 3.30/0.96    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 3.30/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.30/0.96  
% 3.30/0.96  fof(f26,plain,(
% 3.30/0.96    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.30/0.96    inference(ennf_transformation,[],[f10])).
% 3.30/0.96  
% 3.30/0.96  fof(f27,plain,(
% 3.30/0.96    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.30/0.96    inference(flattening,[],[f26])).
% 3.30/0.96  
% 3.30/0.96  fof(f44,plain,(
% 3.30/0.96    ( ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.30/0.96    inference(cnf_transformation,[],[f27])).
% 3.30/0.96  
% 3.30/0.96  fof(f49,plain,(
% 3.30/0.96    v1_funct_2(sK2,sK0,sK0)),
% 3.30/0.96    inference(cnf_transformation,[],[f33])).
% 3.30/0.96  
% 3.30/0.96  fof(f41,plain,(
% 3.30/0.96    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.30/0.96    inference(cnf_transformation,[],[f30])).
% 3.30/0.96  
% 3.30/0.96  fof(f55,plain,(
% 3.30/0.96    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.30/0.96    inference(equality_resolution,[],[f41])).
% 3.30/0.96  
% 3.30/0.96  fof(f53,plain,(
% 3.30/0.96    ~r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0))),
% 3.30/0.96    inference(cnf_transformation,[],[f33])).
% 3.30/0.96  
% 3.30/0.96  cnf(c_385,plain,
% 3.30/0.96      ( ~ m1_subset_1(X0_46,X0_48)
% 3.30/0.96      | m1_subset_1(X1_46,X1_48)
% 3.30/0.96      | X1_48 != X0_48
% 3.30/0.96      | X1_46 != X0_46 ),
% 3.30/0.96      theory(equality) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_836,plain,
% 3.30/0.96      ( m1_subset_1(X0_46,X0_48)
% 3.30/0.96      | ~ m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.30/0.96      | X0_48 != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
% 3.30/0.96      | X0_46 != X1_46 ),
% 3.30/0.96      inference(instantiation,[status(thm)],[c_385]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_997,plain,
% 3.30/0.96      ( m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
% 3.30/0.96      | ~ m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.30/0.96      | k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
% 3.30/0.96      | X0_46 != X1_46 ),
% 3.30/0.96      inference(instantiation,[status(thm)],[c_836]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_3569,plain,
% 3.30/0.96      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.30/0.96      | m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.30/0.96      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
% 3.30/0.96      | k6_partfun1(sK0) != X0_46 ),
% 3.30/0.96      inference(instantiation,[status(thm)],[c_997]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_4629,plain,
% 3.30/0.96      ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.30/0.96      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.30/0.96      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
% 3.30/0.96      | k6_partfun1(sK0) != sK2 ),
% 3.30/0.96      inference(instantiation,[status(thm)],[c_3569]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_16,negated_conjecture,
% 3.30/0.96      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.30/0.96      inference(cnf_transformation,[],[f47]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_363,negated_conjecture,
% 3.30/0.96      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.30/0.96      inference(subtyping,[status(esa)],[c_16]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_643,plain,
% 3.30/0.96      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.30/0.96      inference(predicate_to_equality,[status(thm)],[c_363]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_13,negated_conjecture,
% 3.30/0.96      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.30/0.96      inference(cnf_transformation,[],[f50]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_365,negated_conjecture,
% 3.30/0.96      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.30/0.96      inference(subtyping,[status(esa)],[c_13]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_641,plain,
% 3.30/0.96      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.30/0.96      inference(predicate_to_equality,[status(thm)],[c_365]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_8,plain,
% 3.30/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.30/0.96      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.30/0.96      | ~ v1_funct_1(X0)
% 3.30/0.96      | ~ v1_funct_1(X3)
% 3.30/0.96      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.30/0.96      inference(cnf_transformation,[],[f42]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_367,plain,
% 3.30/0.96      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
% 3.30/0.96      | ~ m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(X2_47,X3_47)))
% 3.30/0.96      | ~ v1_funct_1(X0_46)
% 3.30/0.96      | ~ v1_funct_1(X1_46)
% 3.30/0.96      | k1_partfun1(X2_47,X3_47,X0_47,X1_47,X1_46,X0_46) = k5_relat_1(X1_46,X0_46) ),
% 3.30/0.96      inference(subtyping,[status(esa)],[c_8]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_640,plain,
% 3.30/0.96      ( k1_partfun1(X0_47,X1_47,X2_47,X3_47,X0_46,X1_46) = k5_relat_1(X0_46,X1_46)
% 3.30/0.96      | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
% 3.30/0.96      | m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(X2_47,X3_47))) != iProver_top
% 3.30/0.96      | v1_funct_1(X0_46) != iProver_top
% 3.30/0.96      | v1_funct_1(X1_46) != iProver_top ),
% 3.30/0.96      inference(predicate_to_equality,[status(thm)],[c_367]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_1352,plain,
% 3.30/0.96      ( k1_partfun1(X0_47,X1_47,sK0,sK0,X0_46,sK2) = k5_relat_1(X0_46,sK2)
% 3.30/0.96      | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
% 3.30/0.96      | v1_funct_1(X0_46) != iProver_top
% 3.30/0.96      | v1_funct_1(sK2) != iProver_top ),
% 3.30/0.96      inference(superposition,[status(thm)],[c_641,c_640]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_15,negated_conjecture,
% 3.30/0.96      ( v1_funct_1(sK2) ),
% 3.30/0.96      inference(cnf_transformation,[],[f48]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_22,plain,
% 3.30/0.96      ( v1_funct_1(sK2) = iProver_top ),
% 3.30/0.96      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_1696,plain,
% 3.30/0.96      ( v1_funct_1(X0_46) != iProver_top
% 3.30/0.96      | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
% 3.30/0.96      | k1_partfun1(X0_47,X1_47,sK0,sK0,X0_46,sK2) = k5_relat_1(X0_46,sK2) ),
% 3.30/0.96      inference(global_propositional_subsumption,
% 3.30/0.96                [status(thm)],
% 3.30/0.96                [c_1352,c_22]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_1697,plain,
% 3.30/0.96      ( k1_partfun1(X0_47,X1_47,sK0,sK0,X0_46,sK2) = k5_relat_1(X0_46,sK2)
% 3.30/0.96      | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
% 3.30/0.96      | v1_funct_1(X0_46) != iProver_top ),
% 3.30/0.96      inference(renaming,[status(thm)],[c_1696]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_1706,plain,
% 3.30/0.96      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2)
% 3.30/0.96      | v1_funct_1(sK1) != iProver_top ),
% 3.30/0.96      inference(superposition,[status(thm)],[c_643,c_1697]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_18,negated_conjecture,
% 3.30/0.96      ( v1_funct_1(sK1) ),
% 3.30/0.96      inference(cnf_transformation,[],[f45]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_987,plain,
% 3.30/0.96      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.30/0.96      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.30/0.96      | ~ v1_funct_1(sK1)
% 3.30/0.96      | ~ v1_funct_1(sK2)
% 3.30/0.96      | k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2) ),
% 3.30/0.96      inference(instantiation,[status(thm)],[c_367]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_1806,plain,
% 3.30/0.96      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2) ),
% 3.30/0.96      inference(global_propositional_subsumption,
% 3.30/0.96                [status(thm)],
% 3.30/0.96                [c_1706,c_18,c_16,c_15,c_13,c_987]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_7,plain,
% 3.30/0.96      ( ~ r2_relset_1(X0,X1,X2,X3)
% 3.30/0.96      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.30/0.96      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.30/0.96      | X3 = X2 ),
% 3.30/0.96      inference(cnf_transformation,[],[f40]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_12,negated_conjecture,
% 3.30/0.96      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),sK1) ),
% 3.30/0.96      inference(cnf_transformation,[],[f51]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_229,plain,
% 3.30/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.30/0.96      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.30/0.96      | X3 = X0
% 3.30/0.96      | k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) != X0
% 3.30/0.96      | sK1 != X3
% 3.30/0.96      | sK0 != X2
% 3.30/0.96      | sK0 != X1 ),
% 3.30/0.96      inference(resolution_lifted,[status(thm)],[c_7,c_12]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_230,plain,
% 3.30/0.96      ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.30/0.96      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.30/0.96      | sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) ),
% 3.30/0.96      inference(unflattening,[status(thm)],[c_229]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_232,plain,
% 3.30/0.96      ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.30/0.96      | sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) ),
% 3.30/0.96      inference(global_propositional_subsumption,
% 3.30/0.96                [status(thm)],
% 3.30/0.96                [c_230,c_16]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_358,plain,
% 3.30/0.96      ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.30/0.96      | sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) ),
% 3.30/0.96      inference(subtyping,[status(esa)],[c_232]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_646,plain,
% 3.30/0.96      ( sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2)
% 3.30/0.96      | m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.30/0.96      inference(predicate_to_equality,[status(thm)],[c_358]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_1809,plain,
% 3.30/0.96      ( k5_relat_1(sK1,sK2) = sK1
% 3.30/0.96      | m1_subset_1(k5_relat_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.30/0.96      inference(demodulation,[status(thm)],[c_1806,c_646]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_21,plain,
% 3.30/0.96      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.30/0.96      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_24,plain,
% 3.30/0.96      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.30/0.96      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_5,plain,
% 3.30/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.30/0.96      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.30/0.96      | k4_relset_1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.30/0.96      inference(cnf_transformation,[],[f39]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_368,plain,
% 3.30/0.96      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
% 3.30/0.96      | ~ m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(X2_47,X3_47)))
% 3.30/0.96      | k4_relset_1(X2_47,X3_47,X0_47,X1_47,X1_46,X0_46) = k5_relat_1(X1_46,X0_46) ),
% 3.30/0.96      inference(subtyping,[status(esa)],[c_5]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_639,plain,
% 3.30/0.96      ( k4_relset_1(X0_47,X1_47,X2_47,X3_47,X0_46,X1_46) = k5_relat_1(X0_46,X1_46)
% 3.30/0.96      | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
% 3.30/0.96      | m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(X2_47,X3_47))) != iProver_top ),
% 3.30/0.96      inference(predicate_to_equality,[status(thm)],[c_368]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_1320,plain,
% 3.30/0.96      ( k4_relset_1(X0_47,X1_47,sK0,sK0,X0_46,sK2) = k5_relat_1(X0_46,sK2)
% 3.30/0.96      | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top ),
% 3.30/0.96      inference(superposition,[status(thm)],[c_641,c_639]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_1447,plain,
% 3.30/0.96      ( k4_relset_1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2) ),
% 3.30/0.96      inference(superposition,[status(thm)],[c_643,c_1320]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_2,plain,
% 3.30/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.30/0.96      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.30/0.96      | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) ),
% 3.30/0.96      inference(cnf_transformation,[],[f36]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_371,plain,
% 3.30/0.96      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
% 3.30/0.96      | ~ m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(X2_47,X3_47)))
% 3.30/0.96      | m1_subset_1(k4_relset_1(X2_47,X3_47,X0_47,X1_47,X1_46,X0_46),k1_zfmisc_1(k2_zfmisc_1(X2_47,X1_47))) ),
% 3.30/0.96      inference(subtyping,[status(esa)],[c_2]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_636,plain,
% 3.30/0.96      ( m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
% 3.30/0.96      | m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(X2_47,X3_47))) != iProver_top
% 3.30/0.96      | m1_subset_1(k4_relset_1(X0_47,X1_47,X2_47,X3_47,X0_46,X1_46),k1_zfmisc_1(k2_zfmisc_1(X0_47,X3_47))) = iProver_top ),
% 3.30/0.96      inference(predicate_to_equality,[status(thm)],[c_371]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_1538,plain,
% 3.30/0.96      ( m1_subset_1(k5_relat_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 3.30/0.96      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.30/0.96      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.30/0.96      inference(superposition,[status(thm)],[c_1447,c_636]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_3116,plain,
% 3.30/0.96      ( k5_relat_1(sK1,sK2) = sK1 ),
% 3.30/0.96      inference(global_propositional_subsumption,
% 3.30/0.96                [status(thm)],
% 3.30/0.96                [c_1809,c_21,c_24,c_1538]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_4,plain,
% 3.30/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.30/0.96      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.30/0.96      inference(cnf_transformation,[],[f38]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_369,plain,
% 3.30/0.96      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
% 3.30/0.96      | k2_relset_1(X0_47,X1_47,X0_46) = k2_relat_1(X0_46) ),
% 3.30/0.96      inference(subtyping,[status(esa)],[c_4]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_638,plain,
% 3.30/0.96      ( k2_relset_1(X0_47,X1_47,X0_46) = k2_relat_1(X0_46)
% 3.30/0.96      | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top ),
% 3.30/0.96      inference(predicate_to_equality,[status(thm)],[c_369]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_929,plain,
% 3.30/0.96      ( k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) ),
% 3.30/0.96      inference(superposition,[status(thm)],[c_643,c_638]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_11,negated_conjecture,
% 3.30/0.96      ( k2_relset_1(sK0,sK0,sK1) = sK0 ),
% 3.30/0.96      inference(cnf_transformation,[],[f52]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_366,negated_conjecture,
% 3.30/0.96      ( k2_relset_1(sK0,sK0,sK1) = sK0 ),
% 3.30/0.96      inference(subtyping,[status(esa)],[c_11]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_931,plain,
% 3.30/0.96      ( k2_relat_1(sK1) = sK0 ),
% 3.30/0.96      inference(light_normalisation,[status(thm)],[c_929,c_366]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_0,plain,
% 3.30/0.96      ( ~ v1_relat_1(X0)
% 3.30/0.96      | ~ v1_relat_1(X1)
% 3.30/0.96      | ~ v1_funct_1(X0)
% 3.30/0.96      | ~ v1_funct_1(X1)
% 3.30/0.96      | k5_relat_1(X1,X0) != X1
% 3.30/0.96      | k2_relat_1(X1) != k1_relat_1(X0)
% 3.30/0.96      | k6_partfun1(k1_relat_1(X0)) = X0 ),
% 3.30/0.96      inference(cnf_transformation,[],[f54]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_373,plain,
% 3.30/0.96      ( ~ v1_relat_1(X0_46)
% 3.30/0.96      | ~ v1_relat_1(X1_46)
% 3.30/0.96      | ~ v1_funct_1(X0_46)
% 3.30/0.96      | ~ v1_funct_1(X1_46)
% 3.30/0.96      | k2_relat_1(X1_46) != k1_relat_1(X0_46)
% 3.30/0.96      | k5_relat_1(X1_46,X0_46) != X1_46
% 3.30/0.96      | k6_partfun1(k1_relat_1(X0_46)) = X0_46 ),
% 3.30/0.96      inference(subtyping,[status(esa)],[c_0]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_634,plain,
% 3.30/0.96      ( k2_relat_1(X0_46) != k1_relat_1(X1_46)
% 3.30/0.96      | k5_relat_1(X0_46,X1_46) != X0_46
% 3.30/0.96      | k6_partfun1(k1_relat_1(X1_46)) = X1_46
% 3.30/0.96      | v1_relat_1(X1_46) != iProver_top
% 3.30/0.96      | v1_relat_1(X0_46) != iProver_top
% 3.30/0.96      | v1_funct_1(X0_46) != iProver_top
% 3.30/0.96      | v1_funct_1(X1_46) != iProver_top ),
% 3.30/0.96      inference(predicate_to_equality,[status(thm)],[c_373]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_978,plain,
% 3.30/0.96      ( k1_relat_1(X0_46) != sK0
% 3.30/0.96      | k5_relat_1(sK1,X0_46) != sK1
% 3.30/0.96      | k6_partfun1(k1_relat_1(X0_46)) = X0_46
% 3.30/0.96      | v1_relat_1(X0_46) != iProver_top
% 3.30/0.96      | v1_relat_1(sK1) != iProver_top
% 3.30/0.96      | v1_funct_1(X0_46) != iProver_top
% 3.30/0.96      | v1_funct_1(sK1) != iProver_top ),
% 3.30/0.96      inference(superposition,[status(thm)],[c_931,c_634]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_19,plain,
% 3.30/0.96      ( v1_funct_1(sK1) = iProver_top ),
% 3.30/0.96      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_1,plain,
% 3.30/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.30/0.96      | v1_relat_1(X0) ),
% 3.30/0.96      inference(cnf_transformation,[],[f35]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_372,plain,
% 3.30/0.96      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
% 3.30/0.96      | v1_relat_1(X0_46) ),
% 3.30/0.96      inference(subtyping,[status(esa)],[c_1]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_405,plain,
% 3.30/0.96      ( m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
% 3.30/0.96      | v1_relat_1(X0_46) = iProver_top ),
% 3.30/0.96      inference(predicate_to_equality,[status(thm)],[c_372]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_407,plain,
% 3.30/0.96      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.30/0.96      | v1_relat_1(sK1) = iProver_top ),
% 3.30/0.96      inference(instantiation,[status(thm)],[c_405]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_1176,plain,
% 3.30/0.96      ( v1_funct_1(X0_46) != iProver_top
% 3.30/0.96      | k1_relat_1(X0_46) != sK0
% 3.30/0.96      | k5_relat_1(sK1,X0_46) != sK1
% 3.30/0.96      | k6_partfun1(k1_relat_1(X0_46)) = X0_46
% 3.30/0.96      | v1_relat_1(X0_46) != iProver_top ),
% 3.30/0.96      inference(global_propositional_subsumption,
% 3.30/0.96                [status(thm)],
% 3.30/0.96                [c_978,c_19,c_21,c_407]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_1177,plain,
% 3.30/0.96      ( k1_relat_1(X0_46) != sK0
% 3.30/0.96      | k5_relat_1(sK1,X0_46) != sK1
% 3.30/0.96      | k6_partfun1(k1_relat_1(X0_46)) = X0_46
% 3.30/0.96      | v1_relat_1(X0_46) != iProver_top
% 3.30/0.96      | v1_funct_1(X0_46) != iProver_top ),
% 3.30/0.96      inference(renaming,[status(thm)],[c_1176]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_3132,plain,
% 3.30/0.96      ( k1_relat_1(sK2) != sK0
% 3.30/0.96      | k6_partfun1(k1_relat_1(sK2)) = sK2
% 3.30/0.96      | v1_relat_1(sK2) != iProver_top
% 3.30/0.96      | v1_funct_1(sK2) != iProver_top ),
% 3.30/0.96      inference(superposition,[status(thm)],[c_3116,c_1177]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_3,plain,
% 3.30/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.30/0.96      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.30/0.96      inference(cnf_transformation,[],[f37]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_370,plain,
% 3.30/0.96      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
% 3.30/0.96      | k1_relset_1(X0_47,X1_47,X0_46) = k1_relat_1(X0_46) ),
% 3.30/0.96      inference(subtyping,[status(esa)],[c_3]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_637,plain,
% 3.30/0.96      ( k1_relset_1(X0_47,X1_47,X0_46) = k1_relat_1(X0_46)
% 3.30/0.96      | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top ),
% 3.30/0.96      inference(predicate_to_equality,[status(thm)],[c_370]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_917,plain,
% 3.30/0.96      ( k1_relset_1(sK0,sK0,sK2) = k1_relat_1(sK2) ),
% 3.30/0.96      inference(superposition,[status(thm)],[c_641,c_637]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_9,plain,
% 3.30/0.96      ( ~ v1_funct_2(X0,X1,X1)
% 3.30/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.30/0.96      | ~ v1_funct_1(X0)
% 3.30/0.96      | k1_relset_1(X1,X1,X0) = X1 ),
% 3.30/0.96      inference(cnf_transformation,[],[f44]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_14,negated_conjecture,
% 3.30/0.96      ( v1_funct_2(sK2,sK0,sK0) ),
% 3.30/0.96      inference(cnf_transformation,[],[f49]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_199,plain,
% 3.30/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.30/0.96      | ~ v1_funct_1(X0)
% 3.30/0.96      | k1_relset_1(X1,X1,X0) = X1
% 3.30/0.96      | sK2 != X0
% 3.30/0.96      | sK0 != X1 ),
% 3.30/0.96      inference(resolution_lifted,[status(thm)],[c_9,c_14]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_200,plain,
% 3.30/0.96      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.30/0.96      | ~ v1_funct_1(sK2)
% 3.30/0.96      | k1_relset_1(sK0,sK0,sK2) = sK0 ),
% 3.30/0.96      inference(unflattening,[status(thm)],[c_199]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_202,plain,
% 3.30/0.96      ( k1_relset_1(sK0,sK0,sK2) = sK0 ),
% 3.30/0.96      inference(global_propositional_subsumption,
% 3.30/0.96                [status(thm)],
% 3.30/0.96                [c_200,c_15,c_13]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_361,plain,
% 3.30/0.96      ( k1_relset_1(sK0,sK0,sK2) = sK0 ),
% 3.30/0.96      inference(subtyping,[status(esa)],[c_202]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_923,plain,
% 3.30/0.96      ( k1_relat_1(sK2) = sK0 ),
% 3.30/0.96      inference(light_normalisation,[status(thm)],[c_917,c_361]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_3133,plain,
% 3.30/0.96      ( sK0 != sK0
% 3.30/0.96      | k6_partfun1(sK0) = sK2
% 3.30/0.96      | v1_relat_1(sK2) != iProver_top
% 3.30/0.96      | v1_funct_1(sK2) != iProver_top ),
% 3.30/0.96      inference(light_normalisation,[status(thm)],[c_3132,c_923]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_3134,plain,
% 3.30/0.96      ( k6_partfun1(sK0) = sK2
% 3.30/0.96      | v1_relat_1(sK2) != iProver_top
% 3.30/0.96      | v1_funct_1(sK2) != iProver_top ),
% 3.30/0.96      inference(equality_resolution_simp,[status(thm)],[c_3133]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_635,plain,
% 3.30/0.96      ( m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
% 3.30/0.96      | v1_relat_1(X0_46) = iProver_top ),
% 3.30/0.96      inference(predicate_to_equality,[status(thm)],[c_372]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_874,plain,
% 3.30/0.96      ( v1_relat_1(sK2) = iProver_top ),
% 3.30/0.96      inference(superposition,[status(thm)],[c_641,c_635]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_379,plain,
% 3.30/0.96      ( X0_46 != X1_46 | X2_46 != X1_46 | X2_46 = X0_46 ),
% 3.30/0.96      theory(equality) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_753,plain,
% 3.30/0.96      ( k6_partfun1(sK0) != X0_46
% 3.30/0.96      | sK2 != X0_46
% 3.30/0.96      | sK2 = k6_partfun1(sK0) ),
% 3.30/0.96      inference(instantiation,[status(thm)],[c_379]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_820,plain,
% 3.30/0.96      ( k6_partfun1(sK0) != sK2 | sK2 = k6_partfun1(sK0) | sK2 != sK2 ),
% 3.30/0.96      inference(instantiation,[status(thm)],[c_753]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_377,plain,( X0_48 = X0_48 ),theory(equality) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_787,plain,
% 3.30/0.96      ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
% 3.30/0.96      inference(instantiation,[status(thm)],[c_377]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_375,plain,( X0_46 = X0_46 ),theory(equality) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_779,plain,
% 3.30/0.96      ( sK2 = sK2 ),
% 3.30/0.96      inference(instantiation,[status(thm)],[c_375]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_6,plain,
% 3.30/0.96      ( r2_relset_1(X0,X1,X2,X2)
% 3.30/0.96      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.30/0.96      inference(cnf_transformation,[],[f55]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_10,negated_conjecture,
% 3.30/0.96      ( ~ r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0)) ),
% 3.30/0.96      inference(cnf_transformation,[],[f53]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_219,plain,
% 3.30/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.30/0.96      | k6_partfun1(sK0) != X0
% 3.30/0.96      | sK2 != X0
% 3.30/0.96      | sK0 != X2
% 3.30/0.96      | sK0 != X1 ),
% 3.30/0.96      inference(resolution_lifted,[status(thm)],[c_6,c_10]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_220,plain,
% 3.30/0.96      ( ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.30/0.96      | sK2 != k6_partfun1(sK0) ),
% 3.30/0.96      inference(unflattening,[status(thm)],[c_219]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(c_359,plain,
% 3.30/0.96      ( ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.30/0.96      | sK2 != k6_partfun1(sK0) ),
% 3.30/0.96      inference(subtyping,[status(esa)],[c_220]) ).
% 3.30/0.96  
% 3.30/0.96  cnf(contradiction,plain,
% 3.30/0.96      ( $false ),
% 3.30/0.96      inference(minisat,
% 3.30/0.96                [status(thm)],
% 3.30/0.96                [c_4629,c_3134,c_874,c_820,c_787,c_779,c_359,c_13,c_22]) ).
% 3.30/0.96  
% 3.30/0.96  
% 3.30/0.96  % SZS output end CNFRefutation for theBenchmark.p
% 3.30/0.96  
% 3.30/0.96  ------                               Statistics
% 3.30/0.96  
% 3.30/0.96  ------ General
% 3.30/0.96  
% 3.30/0.96  abstr_ref_over_cycles:                  0
% 3.30/0.96  abstr_ref_under_cycles:                 0
% 3.30/0.96  gc_basic_clause_elim:                   0
% 3.30/0.96  forced_gc_time:                         0
% 3.30/0.96  parsing_time:                           0.01
% 3.30/0.96  unif_index_cands_time:                  0.
% 3.30/0.96  unif_index_add_time:                    0.
% 3.30/0.96  orderings_time:                         0.
% 3.30/0.96  out_proof_time:                         0.015
% 3.30/0.96  total_time:                             0.189
% 3.30/0.96  num_of_symbols:                         53
% 3.30/0.96  num_of_terms:                           3516
% 3.30/0.96  
% 3.30/0.96  ------ Preprocessing
% 3.30/0.96  
% 3.30/0.96  num_of_splits:                          0
% 3.30/0.96  num_of_split_atoms:                     0
% 3.30/0.96  num_of_reused_defs:                     0
% 3.30/0.96  num_eq_ax_congr_red:                    36
% 3.30/0.96  num_of_sem_filtered_clauses:            1
% 3.30/0.96  num_of_subtypes:                        4
% 3.30/0.96  monotx_restored_types:                  0
% 3.30/0.96  sat_num_of_epr_types:                   0
% 3.30/0.96  sat_num_of_non_cyclic_types:            0
% 3.30/0.96  sat_guarded_non_collapsed_types:        1
% 3.30/0.96  num_pure_diseq_elim:                    0
% 3.30/0.96  simp_replaced_by:                       0
% 3.30/0.96  res_preprocessed:                       99
% 3.30/0.96  prep_upred:                             0
% 3.30/0.96  prep_unflattend:                        15
% 3.30/0.96  smt_new_axioms:                         0
% 3.30/0.96  pred_elim_cands:                        3
% 3.30/0.96  pred_elim:                              2
% 3.30/0.96  pred_elim_cl:                           2
% 3.30/0.96  pred_elim_cycles:                       4
% 3.30/0.96  merged_defs:                            0
% 3.30/0.96  merged_defs_ncl:                        0
% 3.30/0.96  bin_hyper_res:                          0
% 3.30/0.96  prep_cycles:                            4
% 3.30/0.96  pred_elim_time:                         0.001
% 3.30/0.96  splitting_time:                         0.
% 3.30/0.96  sem_filter_time:                        0.
% 3.30/0.96  monotx_time:                            0.
% 3.30/0.96  subtype_inf_time:                       0.
% 3.30/0.96  
% 3.30/0.96  ------ Problem properties
% 3.30/0.96  
% 3.30/0.96  clauses:                                17
% 3.30/0.96  conjectures:                            5
% 3.30/0.96  epr:                                    2
% 3.30/0.96  horn:                                   17
% 3.30/0.96  ground:                                 10
% 3.30/0.96  unary:                                  7
% 3.30/0.96  binary:                                 6
% 3.30/0.96  lits:                                   37
% 3.30/0.96  lits_eq:                                14
% 3.30/0.96  fd_pure:                                0
% 3.30/0.96  fd_pseudo:                              0
% 3.30/0.96  fd_cond:                                0
% 3.30/0.96  fd_pseudo_cond:                         0
% 3.30/0.96  ac_symbols:                             0
% 3.30/0.96  
% 3.30/0.96  ------ Propositional Solver
% 3.30/0.96  
% 3.30/0.96  prop_solver_calls:                      33
% 3.30/0.96  prop_fast_solver_calls:                 650
% 3.30/0.96  smt_solver_calls:                       0
% 3.30/0.96  smt_fast_solver_calls:                  0
% 3.30/0.96  prop_num_of_clauses:                    1292
% 3.30/0.96  prop_preprocess_simplified:             4178
% 3.30/0.96  prop_fo_subsumed:                       18
% 3.30/0.96  prop_solver_time:                       0.
% 3.30/0.96  smt_solver_time:                        0.
% 3.30/0.96  smt_fast_solver_time:                   0.
% 3.30/0.96  prop_fast_solver_time:                  0.
% 3.30/0.96  prop_unsat_core_time:                   0.
% 3.30/0.96  
% 3.30/0.96  ------ QBF
% 3.30/0.96  
% 3.30/0.96  qbf_q_res:                              0
% 3.30/0.96  qbf_num_tautologies:                    0
% 3.30/0.96  qbf_prep_cycles:                        0
% 3.30/0.96  
% 3.30/0.96  ------ BMC1
% 3.30/0.96  
% 3.30/0.96  bmc1_current_bound:                     -1
% 3.30/0.96  bmc1_last_solved_bound:                 -1
% 3.30/0.96  bmc1_unsat_core_size:                   -1
% 3.30/0.96  bmc1_unsat_core_parents_size:           -1
% 3.30/0.96  bmc1_merge_next_fun:                    0
% 3.30/0.96  bmc1_unsat_core_clauses_time:           0.
% 3.30/0.96  
% 3.30/0.96  ------ Instantiation
% 3.30/0.96  
% 3.30/0.96  inst_num_of_clauses:                    584
% 3.30/0.96  inst_num_in_passive:                    206
% 3.30/0.96  inst_num_in_active:                     345
% 3.30/0.96  inst_num_in_unprocessed:                32
% 3.30/0.96  inst_num_of_loops:                      400
% 3.30/0.96  inst_num_of_learning_restarts:          0
% 3.30/0.96  inst_num_moves_active_passive:          46
% 3.30/0.96  inst_lit_activity:                      0
% 3.30/0.96  inst_lit_activity_moves:                0
% 3.30/0.96  inst_num_tautologies:                   0
% 3.30/0.96  inst_num_prop_implied:                  0
% 3.30/0.96  inst_num_existing_simplified:           0
% 3.30/0.96  inst_num_eq_res_simplified:             0
% 3.30/0.96  inst_num_child_elim:                    0
% 3.30/0.96  inst_num_of_dismatching_blockings:      306
% 3.30/0.96  inst_num_of_non_proper_insts:           772
% 3.30/0.96  inst_num_of_duplicates:                 0
% 3.30/0.96  inst_inst_num_from_inst_to_res:         0
% 3.30/0.96  inst_dismatching_checking_time:         0.
% 3.30/0.96  
% 3.30/0.96  ------ Resolution
% 3.30/0.96  
% 3.30/0.96  res_num_of_clauses:                     0
% 3.30/0.96  res_num_in_passive:                     0
% 3.30/0.96  res_num_in_active:                      0
% 3.30/0.96  res_num_of_loops:                       103
% 3.30/0.96  res_forward_subset_subsumed:            86
% 3.30/0.96  res_backward_subset_subsumed:           0
% 3.30/0.96  res_forward_subsumed:                   0
% 3.30/0.96  res_backward_subsumed:                  0
% 3.30/0.96  res_forward_subsumption_resolution:     0
% 3.30/0.96  res_backward_subsumption_resolution:    0
% 3.30/0.96  res_clause_to_clause_subsumption:       295
% 3.30/0.96  res_orphan_elimination:                 0
% 3.30/0.96  res_tautology_del:                      138
% 3.30/0.96  res_num_eq_res_simplified:              1
% 3.30/0.96  res_num_sel_changes:                    0
% 3.30/0.96  res_moves_from_active_to_pass:          0
% 3.30/0.96  
% 3.30/0.96  ------ Superposition
% 3.30/0.96  
% 3.30/0.96  sup_time_total:                         0.
% 3.30/0.96  sup_time_generating:                    0.
% 3.30/0.96  sup_time_sim_full:                      0.
% 3.30/0.96  sup_time_sim_immed:                     0.
% 3.30/0.96  
% 3.30/0.96  sup_num_of_clauses:                     128
% 3.30/0.96  sup_num_in_active:                      71
% 3.30/0.96  sup_num_in_passive:                     57
% 3.30/0.96  sup_num_of_loops:                       78
% 3.30/0.96  sup_fw_superposition:                   76
% 3.30/0.96  sup_bw_superposition:                   46
% 3.30/0.96  sup_immediate_simplified:               19
% 3.30/0.96  sup_given_eliminated:                   0
% 3.30/0.96  comparisons_done:                       0
% 3.30/0.96  comparisons_avoided:                    0
% 3.30/0.96  
% 3.30/0.96  ------ Simplifications
% 3.30/0.96  
% 3.30/0.96  
% 3.30/0.96  sim_fw_subset_subsumed:                 3
% 3.30/0.96  sim_bw_subset_subsumed:                 0
% 3.30/0.96  sim_fw_subsumed:                        0
% 3.30/0.96  sim_bw_subsumed:                        0
% 3.30/0.96  sim_fw_subsumption_res:                 0
% 3.30/0.96  sim_bw_subsumption_res:                 0
% 3.30/0.96  sim_tautology_del:                      1
% 3.30/0.96  sim_eq_tautology_del:                   1
% 3.30/0.96  sim_eq_res_simp:                        1
% 3.30/0.96  sim_fw_demodulated:                     0
% 3.30/0.96  sim_bw_demodulated:                     7
% 3.30/0.96  sim_light_normalised:                   20
% 3.30/0.96  sim_joinable_taut:                      0
% 3.30/0.96  sim_joinable_simp:                      0
% 3.30/0.96  sim_ac_normalised:                      0
% 3.30/0.96  sim_smt_subsumption:                    0
% 3.30/0.96  
%------------------------------------------------------------------------------
