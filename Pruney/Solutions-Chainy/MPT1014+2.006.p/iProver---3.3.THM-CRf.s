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
% DateTime   : Thu Dec  3 12:06:47 EST 2020

% Result     : Theorem 2.73s
% Output     : CNFRefutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 352 expanded)
%              Number of clauses        :   82 ( 113 expanded)
%              Number of leaves         :   16 (  88 expanded)
%              Depth                    :   18
%              Number of atoms          :  443 (2276 expanded)
%              Number of equality atoms :  185 ( 417 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
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

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f29,plain,(
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

fof(f28,plain,
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

fof(f30,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0))
    & k2_relset_1(sK0,sK0,sK1) = sK0
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK2,sK0,sK0)
    & v1_funct_1(sK2)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f29,f28])).

fof(f44,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f30])).

fof(f47,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f30])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f21])).

fof(f39,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f45,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f17])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f48,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f42,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f6,axiom,(
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
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f19])).

fof(f38,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f49,plain,(
    k2_relset_1(sK0,sK0,sK1) = sK0 ),
    inference(cnf_transformation,[],[f30])).

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

fof(f12,plain,(
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
    inference(flattening,[],[f12])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k6_relat_1(k1_relat_1(X1)) = X1
      | k5_relat_1(X0,X1) != X0
      | k2_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f8,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k6_partfun1(k1_relat_1(X1)) = X1
      | k5_relat_1(X0,X1) != X0
      | k2_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f31,f40])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f46,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f36])).

fof(f50,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_385,plain,
    ( ~ m1_subset_1(X0_45,X0_47)
    | m1_subset_1(X1_45,X1_47)
    | X1_47 != X0_47
    | X1_45 != X0_45 ),
    theory(equality)).

cnf(c_845,plain,
    ( m1_subset_1(X0_45,X0_47)
    | ~ m1_subset_1(X1_45,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | X0_47 != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | X0_45 != X1_45 ),
    inference(instantiation,[status(thm)],[c_385])).

cnf(c_990,plain,
    ( m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)))
    | ~ m1_subset_1(X1_45,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | X0_45 != X1_45 ),
    inference(instantiation,[status(thm)],[c_845])).

cnf(c_3575,plain,
    ( ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | k6_partfun1(sK0) != X0_45 ),
    inference(instantiation,[status(thm)],[c_990])).

cnf(c_4618,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | k6_partfun1(sK0) != sK2 ),
    inference(instantiation,[status(thm)],[c_3575])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_363,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_643,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_363])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f47])).

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
    inference(cnf_transformation,[],[f39])).

cnf(c_367,plain,
    ( ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)))
    | ~ m1_subset_1(X1_45,k1_zfmisc_1(k2_zfmisc_1(X2_46,X3_46)))
    | ~ v1_funct_1(X0_45)
    | ~ v1_funct_1(X1_45)
    | k1_partfun1(X2_46,X3_46,X0_46,X1_46,X1_45,X0_45) = k5_relat_1(X1_45,X0_45) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_640,plain,
    ( k1_partfun1(X0_46,X1_46,X2_46,X3_46,X0_45,X1_45) = k5_relat_1(X0_45,X1_45)
    | m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) != iProver_top
    | m1_subset_1(X1_45,k1_zfmisc_1(k2_zfmisc_1(X2_46,X3_46))) != iProver_top
    | v1_funct_1(X0_45) != iProver_top
    | v1_funct_1(X1_45) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_367])).

cnf(c_1287,plain,
    ( k1_partfun1(X0_46,X1_46,sK0,sK0,X0_45,sK2) = k5_relat_1(X0_45,sK2)
    | m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) != iProver_top
    | v1_funct_1(X0_45) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_641,c_640])).

cnf(c_15,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_22,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1392,plain,
    ( v1_funct_1(X0_45) != iProver_top
    | m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) != iProver_top
    | k1_partfun1(X0_46,X1_46,sK0,sK0,X0_45,sK2) = k5_relat_1(X0_45,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1287,c_22])).

cnf(c_1393,plain,
    ( k1_partfun1(X0_46,X1_46,sK0,sK0,X0_45,sK2) = k5_relat_1(X0_45,sK2)
    | m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) != iProver_top
    | v1_funct_1(X0_45) != iProver_top ),
    inference(renaming,[status(thm)],[c_1392])).

cnf(c_1402,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2)
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_643,c_1393])).

cnf(c_5,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_12,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),sK1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_229,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) != X0
    | sK1 != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_12])).

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

cnf(c_18,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_369,plain,
    ( ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)))
    | ~ m1_subset_1(X1_45,k1_zfmisc_1(k2_zfmisc_1(X2_46,X3_46)))
    | m1_subset_1(k1_partfun1(X2_46,X3_46,X0_46,X1_46,X1_45,X0_45),k1_zfmisc_1(k2_zfmisc_1(X2_46,X1_46)))
    | ~ v1_funct_1(X0_45)
    | ~ v1_funct_1(X1_45) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_778,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_369])).

cnf(c_1116,plain,
    ( sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_646,c_18,c_16,c_15,c_13,c_358,c_778])).

cnf(c_1418,plain,
    ( k5_relat_1(sK1,sK2) = sK1
    | v1_funct_1(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1402,c_1116])).

cnf(c_19,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1760,plain,
    ( k5_relat_1(sK1,sK2) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1418,c_19])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_370,plain,
    ( ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)))
    | k2_relset_1(X0_46,X1_46,X0_45) = k2_relat_1(X0_45) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_637,plain,
    ( k2_relset_1(X0_46,X1_46,X0_45) = k2_relat_1(X0_45)
    | m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_370])).

cnf(c_939,plain,
    ( k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_643,c_637])).

cnf(c_11,negated_conjecture,
    ( k2_relset_1(sK0,sK0,sK1) = sK0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_366,negated_conjecture,
    ( k2_relset_1(sK0,sK0,sK1) = sK0 ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_941,plain,
    ( k2_relat_1(sK1) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_939,c_366])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | k5_relat_1(X1,X0) != X1
    | k2_relat_1(X1) != k1_relat_1(X0)
    | k6_partfun1(k1_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_373,plain,
    ( ~ v1_relat_1(X0_45)
    | ~ v1_relat_1(X1_45)
    | ~ v1_funct_1(X0_45)
    | ~ v1_funct_1(X1_45)
    | k2_relat_1(X1_45) != k1_relat_1(X0_45)
    | k5_relat_1(X1_45,X0_45) != X1_45
    | k6_partfun1(k1_relat_1(X0_45)) = X0_45 ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_634,plain,
    ( k2_relat_1(X0_45) != k1_relat_1(X1_45)
    | k5_relat_1(X0_45,X1_45) != X0_45
    | k6_partfun1(k1_relat_1(X1_45)) = X1_45
    | v1_relat_1(X1_45) != iProver_top
    | v1_relat_1(X0_45) != iProver_top
    | v1_funct_1(X0_45) != iProver_top
    | v1_funct_1(X1_45) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_373])).

cnf(c_984,plain,
    ( k1_relat_1(X0_45) != sK0
    | k5_relat_1(sK1,X0_45) != sK1
    | k6_partfun1(k1_relat_1(X0_45)) = X0_45
    | v1_relat_1(X0_45) != iProver_top
    | v1_relat_1(sK1) != iProver_top
    | v1_funct_1(X0_45) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_941,c_634])).

cnf(c_21,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_372,plain,
    ( ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)))
    | v1_relat_1(X0_45) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_405,plain,
    ( m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) != iProver_top
    | v1_relat_1(X0_45) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_372])).

cnf(c_407,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_relat_1(sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_405])).

cnf(c_1169,plain,
    ( v1_funct_1(X0_45) != iProver_top
    | k1_relat_1(X0_45) != sK0
    | k5_relat_1(sK1,X0_45) != sK1
    | k6_partfun1(k1_relat_1(X0_45)) = X0_45
    | v1_relat_1(X0_45) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_984,c_19,c_21,c_407])).

cnf(c_1170,plain,
    ( k1_relat_1(X0_45) != sK0
    | k5_relat_1(sK1,X0_45) != sK1
    | k6_partfun1(k1_relat_1(X0_45)) = X0_45
    | v1_relat_1(X0_45) != iProver_top
    | v1_funct_1(X0_45) != iProver_top ),
    inference(renaming,[status(thm)],[c_1169])).

cnf(c_1763,plain,
    ( k1_relat_1(sK2) != sK0
    | k6_partfun1(k1_relat_1(sK2)) = sK2
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1760,c_1170])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_371,plain,
    ( ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)))
    | k1_relset_1(X0_46,X1_46,X0_45) = k1_relat_1(X0_45) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_636,plain,
    ( k1_relset_1(X0_46,X1_46,X0_45) = k1_relat_1(X0_45)
    | m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_371])).

cnf(c_927,plain,
    ( k1_relset_1(sK0,sK0,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_641,c_636])).

cnf(c_9,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(X1,X1,X0) = X1 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_14,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f46])).

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

cnf(c_933,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_927,c_361])).

cnf(c_1764,plain,
    ( sK0 != sK0
    | k6_partfun1(sK0) = sK2
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1763,c_933])).

cnf(c_1765,plain,
    ( k6_partfun1(sK0) = sK2
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_1764])).

cnf(c_635,plain,
    ( m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) != iProver_top
    | v1_relat_1(X0_45) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_372])).

cnf(c_876,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_641,c_635])).

cnf(c_379,plain,
    ( X0_45 != X1_45
    | X2_45 != X1_45
    | X2_45 = X0_45 ),
    theory(equality)).

cnf(c_761,plain,
    ( k6_partfun1(sK0) != X0_45
    | sK2 != X0_45
    | sK2 = k6_partfun1(sK0) ),
    inference(instantiation,[status(thm)],[c_379])).

cnf(c_836,plain,
    ( k6_partfun1(sK0) != sK2
    | sK2 = k6_partfun1(sK0)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_761])).

cnf(c_377,plain,
    ( X0_47 = X0_47 ),
    theory(equality)).

cnf(c_798,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_377])).

cnf(c_375,plain,
    ( X0_45 = X0_45 ),
    theory(equality)).

cnf(c_790,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_375])).

cnf(c_4,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_10,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_219,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k6_partfun1(sK0) != X0
    | sK2 != X0
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_10])).

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
    inference(minisat,[status(thm)],[c_4618,c_1765,c_876,c_836,c_798,c_790,c_359,c_13,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:48:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.73/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/0.99  
% 2.73/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.73/0.99  
% 2.73/0.99  ------  iProver source info
% 2.73/0.99  
% 2.73/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.73/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.73/0.99  git: non_committed_changes: false
% 2.73/0.99  git: last_make_outside_of_git: false
% 2.73/0.99  
% 2.73/0.99  ------ 
% 2.73/0.99  
% 2.73/0.99  ------ Input Options
% 2.73/0.99  
% 2.73/0.99  --out_options                           all
% 2.73/0.99  --tptp_safe_out                         true
% 2.73/0.99  --problem_path                          ""
% 2.73/0.99  --include_path                          ""
% 2.73/0.99  --clausifier                            res/vclausify_rel
% 2.73/0.99  --clausifier_options                    --mode clausify
% 2.73/0.99  --stdin                                 false
% 2.73/0.99  --stats_out                             all
% 2.73/0.99  
% 2.73/0.99  ------ General Options
% 2.73/0.99  
% 2.73/0.99  --fof                                   false
% 2.73/0.99  --time_out_real                         305.
% 2.73/0.99  --time_out_virtual                      -1.
% 2.73/0.99  --symbol_type_check                     false
% 2.73/0.99  --clausify_out                          false
% 2.73/0.99  --sig_cnt_out                           false
% 2.73/0.99  --trig_cnt_out                          false
% 2.73/0.99  --trig_cnt_out_tolerance                1.
% 2.73/0.99  --trig_cnt_out_sk_spl                   false
% 2.73/0.99  --abstr_cl_out                          false
% 2.73/0.99  
% 2.73/0.99  ------ Global Options
% 2.73/0.99  
% 2.73/0.99  --schedule                              default
% 2.73/0.99  --add_important_lit                     false
% 2.73/0.99  --prop_solver_per_cl                    1000
% 2.73/0.99  --min_unsat_core                        false
% 2.73/0.99  --soft_assumptions                      false
% 2.73/0.99  --soft_lemma_size                       3
% 2.73/0.99  --prop_impl_unit_size                   0
% 2.73/0.99  --prop_impl_unit                        []
% 2.73/0.99  --share_sel_clauses                     true
% 2.73/0.99  --reset_solvers                         false
% 2.73/0.99  --bc_imp_inh                            [conj_cone]
% 2.73/0.99  --conj_cone_tolerance                   3.
% 2.73/0.99  --extra_neg_conj                        none
% 2.73/0.99  --large_theory_mode                     true
% 2.73/0.99  --prolific_symb_bound                   200
% 2.73/0.99  --lt_threshold                          2000
% 2.73/0.99  --clause_weak_htbl                      true
% 2.73/0.99  --gc_record_bc_elim                     false
% 2.73/0.99  
% 2.73/0.99  ------ Preprocessing Options
% 2.73/0.99  
% 2.73/0.99  --preprocessing_flag                    true
% 2.73/0.99  --time_out_prep_mult                    0.1
% 2.73/0.99  --splitting_mode                        input
% 2.73/0.99  --splitting_grd                         true
% 2.73/0.99  --splitting_cvd                         false
% 2.73/0.99  --splitting_cvd_svl                     false
% 2.73/0.99  --splitting_nvd                         32
% 2.73/0.99  --sub_typing                            true
% 2.73/0.99  --prep_gs_sim                           true
% 2.73/0.99  --prep_unflatten                        true
% 2.73/0.99  --prep_res_sim                          true
% 2.73/0.99  --prep_upred                            true
% 2.73/0.99  --prep_sem_filter                       exhaustive
% 2.73/0.99  --prep_sem_filter_out                   false
% 2.73/0.99  --pred_elim                             true
% 2.73/0.99  --res_sim_input                         true
% 2.73/0.99  --eq_ax_congr_red                       true
% 2.73/0.99  --pure_diseq_elim                       true
% 2.73/0.99  --brand_transform                       false
% 2.73/0.99  --non_eq_to_eq                          false
% 2.73/0.99  --prep_def_merge                        true
% 2.73/0.99  --prep_def_merge_prop_impl              false
% 2.73/0.99  --prep_def_merge_mbd                    true
% 2.73/0.99  --prep_def_merge_tr_red                 false
% 2.73/0.99  --prep_def_merge_tr_cl                  false
% 2.73/0.99  --smt_preprocessing                     true
% 2.73/0.99  --smt_ac_axioms                         fast
% 2.73/0.99  --preprocessed_out                      false
% 2.73/0.99  --preprocessed_stats                    false
% 2.73/0.99  
% 2.73/0.99  ------ Abstraction refinement Options
% 2.73/0.99  
% 2.73/0.99  --abstr_ref                             []
% 2.73/0.99  --abstr_ref_prep                        false
% 2.73/0.99  --abstr_ref_until_sat                   false
% 2.73/0.99  --abstr_ref_sig_restrict                funpre
% 2.73/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.73/0.99  --abstr_ref_under                       []
% 2.73/0.99  
% 2.73/0.99  ------ SAT Options
% 2.73/0.99  
% 2.73/0.99  --sat_mode                              false
% 2.73/0.99  --sat_fm_restart_options                ""
% 2.73/0.99  --sat_gr_def                            false
% 2.73/0.99  --sat_epr_types                         true
% 2.73/0.99  --sat_non_cyclic_types                  false
% 2.73/0.99  --sat_finite_models                     false
% 2.73/0.99  --sat_fm_lemmas                         false
% 2.73/0.99  --sat_fm_prep                           false
% 2.73/0.99  --sat_fm_uc_incr                        true
% 2.73/0.99  --sat_out_model                         small
% 2.73/0.99  --sat_out_clauses                       false
% 2.73/0.99  
% 2.73/0.99  ------ QBF Options
% 2.73/0.99  
% 2.73/0.99  --qbf_mode                              false
% 2.73/0.99  --qbf_elim_univ                         false
% 2.73/0.99  --qbf_dom_inst                          none
% 2.73/0.99  --qbf_dom_pre_inst                      false
% 2.73/0.99  --qbf_sk_in                             false
% 2.73/0.99  --qbf_pred_elim                         true
% 2.73/0.99  --qbf_split                             512
% 2.73/0.99  
% 2.73/0.99  ------ BMC1 Options
% 2.73/0.99  
% 2.73/0.99  --bmc1_incremental                      false
% 2.73/0.99  --bmc1_axioms                           reachable_all
% 2.73/0.99  --bmc1_min_bound                        0
% 2.73/0.99  --bmc1_max_bound                        -1
% 2.73/0.99  --bmc1_max_bound_default                -1
% 2.73/0.99  --bmc1_symbol_reachability              true
% 2.73/0.99  --bmc1_property_lemmas                  false
% 2.73/0.99  --bmc1_k_induction                      false
% 2.73/0.99  --bmc1_non_equiv_states                 false
% 2.73/0.99  --bmc1_deadlock                         false
% 2.73/0.99  --bmc1_ucm                              false
% 2.73/0.99  --bmc1_add_unsat_core                   none
% 2.73/0.99  --bmc1_unsat_core_children              false
% 2.73/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.73/0.99  --bmc1_out_stat                         full
% 2.73/0.99  --bmc1_ground_init                      false
% 2.73/0.99  --bmc1_pre_inst_next_state              false
% 2.73/0.99  --bmc1_pre_inst_state                   false
% 2.73/0.99  --bmc1_pre_inst_reach_state             false
% 2.73/0.99  --bmc1_out_unsat_core                   false
% 2.73/0.99  --bmc1_aig_witness_out                  false
% 2.73/0.99  --bmc1_verbose                          false
% 2.73/0.99  --bmc1_dump_clauses_tptp                false
% 2.73/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.73/0.99  --bmc1_dump_file                        -
% 2.73/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.73/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.73/0.99  --bmc1_ucm_extend_mode                  1
% 2.73/0.99  --bmc1_ucm_init_mode                    2
% 2.73/0.99  --bmc1_ucm_cone_mode                    none
% 2.73/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.73/0.99  --bmc1_ucm_relax_model                  4
% 2.73/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.73/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.73/0.99  --bmc1_ucm_layered_model                none
% 2.73/0.99  --bmc1_ucm_max_lemma_size               10
% 2.73/0.99  
% 2.73/0.99  ------ AIG Options
% 2.73/0.99  
% 2.73/0.99  --aig_mode                              false
% 2.73/0.99  
% 2.73/0.99  ------ Instantiation Options
% 2.73/0.99  
% 2.73/0.99  --instantiation_flag                    true
% 2.73/0.99  --inst_sos_flag                         false
% 2.73/0.99  --inst_sos_phase                        true
% 2.73/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.73/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.73/0.99  --inst_lit_sel_side                     num_symb
% 2.73/0.99  --inst_solver_per_active                1400
% 2.73/0.99  --inst_solver_calls_frac                1.
% 2.73/0.99  --inst_passive_queue_type               priority_queues
% 2.73/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.73/0.99  --inst_passive_queues_freq              [25;2]
% 2.73/0.99  --inst_dismatching                      true
% 2.73/0.99  --inst_eager_unprocessed_to_passive     true
% 2.73/0.99  --inst_prop_sim_given                   true
% 2.73/0.99  --inst_prop_sim_new                     false
% 2.73/0.99  --inst_subs_new                         false
% 2.73/0.99  --inst_eq_res_simp                      false
% 2.73/0.99  --inst_subs_given                       false
% 2.73/0.99  --inst_orphan_elimination               true
% 2.73/0.99  --inst_learning_loop_flag               true
% 2.73/0.99  --inst_learning_start                   3000
% 2.73/0.99  --inst_learning_factor                  2
% 2.73/0.99  --inst_start_prop_sim_after_learn       3
% 2.73/0.99  --inst_sel_renew                        solver
% 2.73/0.99  --inst_lit_activity_flag                true
% 2.73/0.99  --inst_restr_to_given                   false
% 2.73/0.99  --inst_activity_threshold               500
% 2.73/0.99  --inst_out_proof                        true
% 2.73/0.99  
% 2.73/0.99  ------ Resolution Options
% 2.73/0.99  
% 2.73/0.99  --resolution_flag                       true
% 2.73/0.99  --res_lit_sel                           adaptive
% 2.73/0.99  --res_lit_sel_side                      none
% 2.73/0.99  --res_ordering                          kbo
% 2.73/0.99  --res_to_prop_solver                    active
% 2.73/0.99  --res_prop_simpl_new                    false
% 2.73/0.99  --res_prop_simpl_given                  true
% 2.73/0.99  --res_passive_queue_type                priority_queues
% 2.73/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.73/0.99  --res_passive_queues_freq               [15;5]
% 2.73/0.99  --res_forward_subs                      full
% 2.73/0.99  --res_backward_subs                     full
% 2.73/0.99  --res_forward_subs_resolution           true
% 2.73/0.99  --res_backward_subs_resolution          true
% 2.73/0.99  --res_orphan_elimination                true
% 2.73/0.99  --res_time_limit                        2.
% 2.73/0.99  --res_out_proof                         true
% 2.73/0.99  
% 2.73/0.99  ------ Superposition Options
% 2.73/0.99  
% 2.73/0.99  --superposition_flag                    true
% 2.73/0.99  --sup_passive_queue_type                priority_queues
% 2.73/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.73/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.73/0.99  --demod_completeness_check              fast
% 2.73/0.99  --demod_use_ground                      true
% 2.73/0.99  --sup_to_prop_solver                    passive
% 2.73/0.99  --sup_prop_simpl_new                    true
% 2.73/0.99  --sup_prop_simpl_given                  true
% 2.73/0.99  --sup_fun_splitting                     false
% 2.73/0.99  --sup_smt_interval                      50000
% 2.73/0.99  
% 2.73/0.99  ------ Superposition Simplification Setup
% 2.73/0.99  
% 2.73/0.99  --sup_indices_passive                   []
% 2.73/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.73/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/0.99  --sup_full_bw                           [BwDemod]
% 2.73/0.99  --sup_immed_triv                        [TrivRules]
% 2.73/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.73/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/0.99  --sup_immed_bw_main                     []
% 2.73/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.73/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.73/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.73/0.99  
% 2.73/0.99  ------ Combination Options
% 2.73/0.99  
% 2.73/0.99  --comb_res_mult                         3
% 2.73/0.99  --comb_sup_mult                         2
% 2.73/0.99  --comb_inst_mult                        10
% 2.73/0.99  
% 2.73/0.99  ------ Debug Options
% 2.73/0.99  
% 2.73/0.99  --dbg_backtrace                         false
% 2.73/0.99  --dbg_dump_prop_clauses                 false
% 2.73/0.99  --dbg_dump_prop_clauses_file            -
% 2.73/0.99  --dbg_out_stat                          false
% 2.73/0.99  ------ Parsing...
% 2.73/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.73/0.99  
% 2.73/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.73/0.99  
% 2.73/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.73/0.99  
% 2.73/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.73/0.99  ------ Proving...
% 2.73/0.99  ------ Problem Properties 
% 2.73/0.99  
% 2.73/0.99  
% 2.73/0.99  clauses                                 17
% 2.73/0.99  conjectures                             5
% 2.73/0.99  EPR                                     2
% 2.73/0.99  Horn                                    17
% 2.73/0.99  unary                                   7
% 2.73/0.99  binary                                  6
% 2.73/0.99  lits                                    41
% 2.73/0.99  lits eq                                 13
% 2.73/0.99  fd_pure                                 0
% 2.73/0.99  fd_pseudo                               0
% 2.73/0.99  fd_cond                                 0
% 2.73/0.99  fd_pseudo_cond                          0
% 2.73/0.99  AC symbols                              0
% 2.73/0.99  
% 2.73/0.99  ------ Schedule dynamic 5 is on 
% 2.73/0.99  
% 2.73/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.73/0.99  
% 2.73/0.99  
% 2.73/0.99  ------ 
% 2.73/0.99  Current options:
% 2.73/0.99  ------ 
% 2.73/0.99  
% 2.73/0.99  ------ Input Options
% 2.73/0.99  
% 2.73/0.99  --out_options                           all
% 2.73/0.99  --tptp_safe_out                         true
% 2.73/0.99  --problem_path                          ""
% 2.73/0.99  --include_path                          ""
% 2.73/0.99  --clausifier                            res/vclausify_rel
% 2.73/0.99  --clausifier_options                    --mode clausify
% 2.73/0.99  --stdin                                 false
% 2.73/0.99  --stats_out                             all
% 2.73/0.99  
% 2.73/0.99  ------ General Options
% 2.73/0.99  
% 2.73/0.99  --fof                                   false
% 2.73/0.99  --time_out_real                         305.
% 2.73/0.99  --time_out_virtual                      -1.
% 2.73/0.99  --symbol_type_check                     false
% 2.73/0.99  --clausify_out                          false
% 2.73/0.99  --sig_cnt_out                           false
% 2.73/0.99  --trig_cnt_out                          false
% 2.73/0.99  --trig_cnt_out_tolerance                1.
% 2.73/0.99  --trig_cnt_out_sk_spl                   false
% 2.73/0.99  --abstr_cl_out                          false
% 2.73/0.99  
% 2.73/0.99  ------ Global Options
% 2.73/0.99  
% 2.73/0.99  --schedule                              default
% 2.73/0.99  --add_important_lit                     false
% 2.73/0.99  --prop_solver_per_cl                    1000
% 2.73/0.99  --min_unsat_core                        false
% 2.73/0.99  --soft_assumptions                      false
% 2.73/0.99  --soft_lemma_size                       3
% 2.73/0.99  --prop_impl_unit_size                   0
% 2.73/0.99  --prop_impl_unit                        []
% 2.73/0.99  --share_sel_clauses                     true
% 2.73/0.99  --reset_solvers                         false
% 2.73/0.99  --bc_imp_inh                            [conj_cone]
% 2.73/0.99  --conj_cone_tolerance                   3.
% 2.73/0.99  --extra_neg_conj                        none
% 2.73/0.99  --large_theory_mode                     true
% 2.73/0.99  --prolific_symb_bound                   200
% 2.73/0.99  --lt_threshold                          2000
% 2.73/0.99  --clause_weak_htbl                      true
% 2.73/0.99  --gc_record_bc_elim                     false
% 2.73/0.99  
% 2.73/0.99  ------ Preprocessing Options
% 2.73/0.99  
% 2.73/0.99  --preprocessing_flag                    true
% 2.73/0.99  --time_out_prep_mult                    0.1
% 2.73/0.99  --splitting_mode                        input
% 2.73/0.99  --splitting_grd                         true
% 2.73/0.99  --splitting_cvd                         false
% 2.73/0.99  --splitting_cvd_svl                     false
% 2.73/0.99  --splitting_nvd                         32
% 2.73/0.99  --sub_typing                            true
% 2.73/0.99  --prep_gs_sim                           true
% 2.73/0.99  --prep_unflatten                        true
% 2.73/0.99  --prep_res_sim                          true
% 2.73/0.99  --prep_upred                            true
% 2.73/0.99  --prep_sem_filter                       exhaustive
% 2.73/0.99  --prep_sem_filter_out                   false
% 2.73/0.99  --pred_elim                             true
% 2.73/0.99  --res_sim_input                         true
% 2.73/0.99  --eq_ax_congr_red                       true
% 2.73/0.99  --pure_diseq_elim                       true
% 2.73/0.99  --brand_transform                       false
% 2.73/0.99  --non_eq_to_eq                          false
% 2.73/0.99  --prep_def_merge                        true
% 2.73/0.99  --prep_def_merge_prop_impl              false
% 2.73/0.99  --prep_def_merge_mbd                    true
% 2.73/0.99  --prep_def_merge_tr_red                 false
% 2.73/0.99  --prep_def_merge_tr_cl                  false
% 2.73/0.99  --smt_preprocessing                     true
% 2.73/0.99  --smt_ac_axioms                         fast
% 2.73/0.99  --preprocessed_out                      false
% 2.73/0.99  --preprocessed_stats                    false
% 2.73/0.99  
% 2.73/0.99  ------ Abstraction refinement Options
% 2.73/0.99  
% 2.73/0.99  --abstr_ref                             []
% 2.73/0.99  --abstr_ref_prep                        false
% 2.73/0.99  --abstr_ref_until_sat                   false
% 2.73/0.99  --abstr_ref_sig_restrict                funpre
% 2.73/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.73/0.99  --abstr_ref_under                       []
% 2.73/0.99  
% 2.73/0.99  ------ SAT Options
% 2.73/0.99  
% 2.73/0.99  --sat_mode                              false
% 2.73/0.99  --sat_fm_restart_options                ""
% 2.73/0.99  --sat_gr_def                            false
% 2.73/0.99  --sat_epr_types                         true
% 2.73/0.99  --sat_non_cyclic_types                  false
% 2.73/0.99  --sat_finite_models                     false
% 2.73/0.99  --sat_fm_lemmas                         false
% 2.73/0.99  --sat_fm_prep                           false
% 2.73/0.99  --sat_fm_uc_incr                        true
% 2.73/0.99  --sat_out_model                         small
% 2.73/0.99  --sat_out_clauses                       false
% 2.73/0.99  
% 2.73/0.99  ------ QBF Options
% 2.73/0.99  
% 2.73/0.99  --qbf_mode                              false
% 2.73/0.99  --qbf_elim_univ                         false
% 2.73/0.99  --qbf_dom_inst                          none
% 2.73/0.99  --qbf_dom_pre_inst                      false
% 2.73/0.99  --qbf_sk_in                             false
% 2.73/0.99  --qbf_pred_elim                         true
% 2.73/0.99  --qbf_split                             512
% 2.73/0.99  
% 2.73/0.99  ------ BMC1 Options
% 2.73/0.99  
% 2.73/0.99  --bmc1_incremental                      false
% 2.73/0.99  --bmc1_axioms                           reachable_all
% 2.73/0.99  --bmc1_min_bound                        0
% 2.73/0.99  --bmc1_max_bound                        -1
% 2.73/0.99  --bmc1_max_bound_default                -1
% 2.73/0.99  --bmc1_symbol_reachability              true
% 2.73/0.99  --bmc1_property_lemmas                  false
% 2.73/0.99  --bmc1_k_induction                      false
% 2.73/0.99  --bmc1_non_equiv_states                 false
% 2.73/0.99  --bmc1_deadlock                         false
% 2.73/0.99  --bmc1_ucm                              false
% 2.73/0.99  --bmc1_add_unsat_core                   none
% 2.73/0.99  --bmc1_unsat_core_children              false
% 2.73/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.73/0.99  --bmc1_out_stat                         full
% 2.73/0.99  --bmc1_ground_init                      false
% 2.73/0.99  --bmc1_pre_inst_next_state              false
% 2.73/0.99  --bmc1_pre_inst_state                   false
% 2.73/0.99  --bmc1_pre_inst_reach_state             false
% 2.73/0.99  --bmc1_out_unsat_core                   false
% 2.73/0.99  --bmc1_aig_witness_out                  false
% 2.73/0.99  --bmc1_verbose                          false
% 2.73/0.99  --bmc1_dump_clauses_tptp                false
% 2.73/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.73/0.99  --bmc1_dump_file                        -
% 2.73/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.73/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.73/0.99  --bmc1_ucm_extend_mode                  1
% 2.73/0.99  --bmc1_ucm_init_mode                    2
% 2.73/0.99  --bmc1_ucm_cone_mode                    none
% 2.73/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.73/0.99  --bmc1_ucm_relax_model                  4
% 2.73/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.73/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.73/0.99  --bmc1_ucm_layered_model                none
% 2.73/0.99  --bmc1_ucm_max_lemma_size               10
% 2.73/0.99  
% 2.73/0.99  ------ AIG Options
% 2.73/0.99  
% 2.73/0.99  --aig_mode                              false
% 2.73/0.99  
% 2.73/0.99  ------ Instantiation Options
% 2.73/0.99  
% 2.73/0.99  --instantiation_flag                    true
% 2.73/0.99  --inst_sos_flag                         false
% 2.73/0.99  --inst_sos_phase                        true
% 2.73/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.73/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.73/0.99  --inst_lit_sel_side                     none
% 2.73/0.99  --inst_solver_per_active                1400
% 2.73/0.99  --inst_solver_calls_frac                1.
% 2.73/0.99  --inst_passive_queue_type               priority_queues
% 2.73/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.73/0.99  --inst_passive_queues_freq              [25;2]
% 2.73/0.99  --inst_dismatching                      true
% 2.73/0.99  --inst_eager_unprocessed_to_passive     true
% 2.73/0.99  --inst_prop_sim_given                   true
% 2.73/0.99  --inst_prop_sim_new                     false
% 2.73/0.99  --inst_subs_new                         false
% 2.73/0.99  --inst_eq_res_simp                      false
% 2.73/0.99  --inst_subs_given                       false
% 2.73/0.99  --inst_orphan_elimination               true
% 2.73/0.99  --inst_learning_loop_flag               true
% 2.73/0.99  --inst_learning_start                   3000
% 2.73/0.99  --inst_learning_factor                  2
% 2.73/0.99  --inst_start_prop_sim_after_learn       3
% 2.73/0.99  --inst_sel_renew                        solver
% 2.73/0.99  --inst_lit_activity_flag                true
% 2.73/0.99  --inst_restr_to_given                   false
% 2.73/0.99  --inst_activity_threshold               500
% 2.73/0.99  --inst_out_proof                        true
% 2.73/0.99  
% 2.73/0.99  ------ Resolution Options
% 2.73/0.99  
% 2.73/0.99  --resolution_flag                       false
% 2.73/0.99  --res_lit_sel                           adaptive
% 2.73/0.99  --res_lit_sel_side                      none
% 2.73/0.99  --res_ordering                          kbo
% 2.73/0.99  --res_to_prop_solver                    active
% 2.73/0.99  --res_prop_simpl_new                    false
% 2.73/0.99  --res_prop_simpl_given                  true
% 2.73/0.99  --res_passive_queue_type                priority_queues
% 2.73/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.73/0.99  --res_passive_queues_freq               [15;5]
% 2.73/0.99  --res_forward_subs                      full
% 2.73/0.99  --res_backward_subs                     full
% 2.73/0.99  --res_forward_subs_resolution           true
% 2.73/0.99  --res_backward_subs_resolution          true
% 2.73/0.99  --res_orphan_elimination                true
% 2.73/0.99  --res_time_limit                        2.
% 2.73/0.99  --res_out_proof                         true
% 2.73/0.99  
% 2.73/0.99  ------ Superposition Options
% 2.73/0.99  
% 2.73/0.99  --superposition_flag                    true
% 2.73/0.99  --sup_passive_queue_type                priority_queues
% 2.73/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.73/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.73/0.99  --demod_completeness_check              fast
% 2.73/0.99  --demod_use_ground                      true
% 2.73/0.99  --sup_to_prop_solver                    passive
% 2.73/0.99  --sup_prop_simpl_new                    true
% 2.73/0.99  --sup_prop_simpl_given                  true
% 2.73/0.99  --sup_fun_splitting                     false
% 2.73/0.99  --sup_smt_interval                      50000
% 2.73/0.99  
% 2.73/0.99  ------ Superposition Simplification Setup
% 2.73/0.99  
% 2.73/0.99  --sup_indices_passive                   []
% 2.73/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.73/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/0.99  --sup_full_bw                           [BwDemod]
% 2.73/0.99  --sup_immed_triv                        [TrivRules]
% 2.73/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.73/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/0.99  --sup_immed_bw_main                     []
% 2.73/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.73/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.73/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.73/0.99  
% 2.73/0.99  ------ Combination Options
% 2.73/0.99  
% 2.73/0.99  --comb_res_mult                         3
% 2.73/0.99  --comb_sup_mult                         2
% 2.73/0.99  --comb_inst_mult                        10
% 2.73/0.99  
% 2.73/0.99  ------ Debug Options
% 2.73/0.99  
% 2.73/0.99  --dbg_backtrace                         false
% 2.73/0.99  --dbg_dump_prop_clauses                 false
% 2.73/0.99  --dbg_dump_prop_clauses_file            -
% 2.73/0.99  --dbg_out_stat                          false
% 2.73/0.99  
% 2.73/0.99  
% 2.73/0.99  
% 2.73/0.99  
% 2.73/0.99  ------ Proving...
% 2.73/0.99  
% 2.73/0.99  
% 2.73/0.99  % SZS status Theorem for theBenchmark.p
% 2.73/0.99  
% 2.73/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.73/0.99  
% 2.73/0.99  fof(f10,conjecture,(
% 2.73/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((k2_relset_1(X0,X0,X1) = X0 & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1)) => r2_relset_1(X0,X0,X2,k6_partfun1(X0)))))),
% 2.73/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/0.99  
% 2.73/0.99  fof(f11,negated_conjecture,(
% 2.73/0.99    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((k2_relset_1(X0,X0,X1) = X0 & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1)) => r2_relset_1(X0,X0,X2,k6_partfun1(X0)))))),
% 2.73/0.99    inference(negated_conjecture,[],[f10])).
% 2.73/0.99  
% 2.73/0.99  fof(f25,plain,(
% 2.73/0.99    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & (k2_relset_1(X0,X0,X1) = X0 & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 2.73/0.99    inference(ennf_transformation,[],[f11])).
% 2.73/0.99  
% 2.73/0.99  fof(f26,plain,(
% 2.73/0.99    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & k2_relset_1(X0,X0,X1) = X0 & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 2.73/0.99    inference(flattening,[],[f25])).
% 2.73/0.99  
% 2.73/0.99  fof(f29,plain,(
% 2.73/0.99    ( ! [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & k2_relset_1(X0,X0,X1) = X0 & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (~r2_relset_1(X0,X0,sK2,k6_partfun1(X0)) & k2_relset_1(X0,X0,X1) = X0 & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,sK2),X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(sK2,X0,X0) & v1_funct_1(sK2))) )),
% 2.73/0.99    introduced(choice_axiom,[])).
% 2.73/0.99  
% 2.73/0.99  fof(f28,plain,(
% 2.73/0.99    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & k2_relset_1(X0,X0,X1) = X0 & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK0,sK0,X2,k6_partfun1(sK0)) & k2_relset_1(sK0,sK0,sK1) = sK0 & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 2.73/0.99    introduced(choice_axiom,[])).
% 2.73/0.99  
% 2.73/0.99  fof(f30,plain,(
% 2.73/0.99    (~r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0)) & k2_relset_1(sK0,sK0,sK1) = sK0 & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 2.73/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f29,f28])).
% 2.73/0.99  
% 2.73/0.99  fof(f44,plain,(
% 2.73/0.99    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.73/0.99    inference(cnf_transformation,[],[f30])).
% 2.73/0.99  
% 2.73/0.99  fof(f47,plain,(
% 2.73/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.73/0.99    inference(cnf_transformation,[],[f30])).
% 2.73/0.99  
% 2.73/0.99  fof(f7,axiom,(
% 2.73/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 2.73/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/0.99  
% 2.73/0.99  fof(f21,plain,(
% 2.73/0.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.73/0.99    inference(ennf_transformation,[],[f7])).
% 2.73/0.99  
% 2.73/0.99  fof(f22,plain,(
% 2.73/0.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.73/0.99    inference(flattening,[],[f21])).
% 2.73/0.99  
% 2.73/0.99  fof(f39,plain,(
% 2.73/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.73/0.99    inference(cnf_transformation,[],[f22])).
% 2.73/0.99  
% 2.73/0.99  fof(f45,plain,(
% 2.73/0.99    v1_funct_1(sK2)),
% 2.73/0.99    inference(cnf_transformation,[],[f30])).
% 2.73/0.99  
% 2.73/0.99  fof(f5,axiom,(
% 2.73/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.73/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/0.99  
% 2.73/0.99  fof(f17,plain,(
% 2.73/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.73/0.99    inference(ennf_transformation,[],[f5])).
% 2.73/0.99  
% 2.73/0.99  fof(f18,plain,(
% 2.73/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.73/0.99    inference(flattening,[],[f17])).
% 2.73/0.99  
% 2.73/0.99  fof(f27,plain,(
% 2.73/0.99    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.73/0.99    inference(nnf_transformation,[],[f18])).
% 2.73/0.99  
% 2.73/0.99  fof(f35,plain,(
% 2.73/0.99    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.73/0.99    inference(cnf_transformation,[],[f27])).
% 2.73/0.99  
% 2.73/0.99  fof(f48,plain,(
% 2.73/0.99    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),sK1)),
% 2.73/0.99    inference(cnf_transformation,[],[f30])).
% 2.73/0.99  
% 2.73/0.99  fof(f42,plain,(
% 2.73/0.99    v1_funct_1(sK1)),
% 2.73/0.99    inference(cnf_transformation,[],[f30])).
% 2.73/0.99  
% 2.73/0.99  fof(f6,axiom,(
% 2.73/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 2.73/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/0.99  
% 2.73/0.99  fof(f19,plain,(
% 2.73/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.73/0.99    inference(ennf_transformation,[],[f6])).
% 2.73/0.99  
% 2.73/0.99  fof(f20,plain,(
% 2.73/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.73/0.99    inference(flattening,[],[f19])).
% 2.73/0.99  
% 2.73/0.99  fof(f38,plain,(
% 2.73/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.73/0.99    inference(cnf_transformation,[],[f20])).
% 2.73/0.99  
% 2.73/0.99  fof(f4,axiom,(
% 2.73/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.73/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/0.99  
% 2.73/0.99  fof(f16,plain,(
% 2.73/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.73/0.99    inference(ennf_transformation,[],[f4])).
% 2.73/0.99  
% 2.73/0.99  fof(f34,plain,(
% 2.73/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.73/0.99    inference(cnf_transformation,[],[f16])).
% 2.73/0.99  
% 2.73/0.99  fof(f49,plain,(
% 2.73/0.99    k2_relset_1(sK0,sK0,sK1) = sK0),
% 2.73/0.99    inference(cnf_transformation,[],[f30])).
% 2.73/0.99  
% 2.73/0.99  fof(f1,axiom,(
% 2.73/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = X0 & k2_relat_1(X0) = k1_relat_1(X1)) => k6_relat_1(k1_relat_1(X1)) = X1)))),
% 2.73/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/0.99  
% 2.73/0.99  fof(f12,plain,(
% 2.73/0.99    ! [X0] : (! [X1] : ((k6_relat_1(k1_relat_1(X1)) = X1 | (k5_relat_1(X0,X1) != X0 | k2_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.73/0.99    inference(ennf_transformation,[],[f1])).
% 2.73/0.99  
% 2.73/0.99  fof(f13,plain,(
% 2.73/0.99    ! [X0] : (! [X1] : (k6_relat_1(k1_relat_1(X1)) = X1 | k5_relat_1(X0,X1) != X0 | k2_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.73/0.99    inference(flattening,[],[f12])).
% 2.73/0.99  
% 2.73/0.99  fof(f31,plain,(
% 2.73/0.99    ( ! [X0,X1] : (k6_relat_1(k1_relat_1(X1)) = X1 | k5_relat_1(X0,X1) != X0 | k2_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.73/0.99    inference(cnf_transformation,[],[f13])).
% 2.73/0.99  
% 2.73/0.99  fof(f8,axiom,(
% 2.73/0.99    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.73/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/0.99  
% 2.73/0.99  fof(f40,plain,(
% 2.73/0.99    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.73/0.99    inference(cnf_transformation,[],[f8])).
% 2.73/0.99  
% 2.73/0.99  fof(f51,plain,(
% 2.73/0.99    ( ! [X0,X1] : (k6_partfun1(k1_relat_1(X1)) = X1 | k5_relat_1(X0,X1) != X0 | k2_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.73/0.99    inference(definition_unfolding,[],[f31,f40])).
% 2.73/0.99  
% 2.73/0.99  fof(f2,axiom,(
% 2.73/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.73/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/0.99  
% 2.73/0.99  fof(f14,plain,(
% 2.73/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.73/0.99    inference(ennf_transformation,[],[f2])).
% 2.73/0.99  
% 2.73/0.99  fof(f32,plain,(
% 2.73/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.73/0.99    inference(cnf_transformation,[],[f14])).
% 2.73/0.99  
% 2.73/0.99  fof(f3,axiom,(
% 2.73/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.73/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/0.99  
% 2.73/0.99  fof(f15,plain,(
% 2.73/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.73/0.99    inference(ennf_transformation,[],[f3])).
% 2.73/0.99  
% 2.73/0.99  fof(f33,plain,(
% 2.73/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.73/0.99    inference(cnf_transformation,[],[f15])).
% 2.73/0.99  
% 2.73/0.99  fof(f9,axiom,(
% 2.73/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 2.73/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/0.99  
% 2.73/0.99  fof(f23,plain,(
% 2.73/0.99    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 2.73/0.99    inference(ennf_transformation,[],[f9])).
% 2.73/0.99  
% 2.73/0.99  fof(f24,plain,(
% 2.73/0.99    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 2.73/0.99    inference(flattening,[],[f23])).
% 2.73/0.99  
% 2.73/0.99  fof(f41,plain,(
% 2.73/0.99    ( ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 2.73/0.99    inference(cnf_transformation,[],[f24])).
% 2.73/0.99  
% 2.73/0.99  fof(f46,plain,(
% 2.73/0.99    v1_funct_2(sK2,sK0,sK0)),
% 2.73/0.99    inference(cnf_transformation,[],[f30])).
% 2.73/0.99  
% 2.73/0.99  fof(f36,plain,(
% 2.73/0.99    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.73/0.99    inference(cnf_transformation,[],[f27])).
% 2.73/0.99  
% 2.73/0.99  fof(f52,plain,(
% 2.73/0.99    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.73/0.99    inference(equality_resolution,[],[f36])).
% 2.73/0.99  
% 2.73/0.99  fof(f50,plain,(
% 2.73/0.99    ~r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0))),
% 2.73/0.99    inference(cnf_transformation,[],[f30])).
% 2.73/0.99  
% 2.73/0.99  cnf(c_385,plain,
% 2.73/0.99      ( ~ m1_subset_1(X0_45,X0_47)
% 2.73/0.99      | m1_subset_1(X1_45,X1_47)
% 2.73/0.99      | X1_47 != X0_47
% 2.73/0.99      | X1_45 != X0_45 ),
% 2.73/0.99      theory(equality) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_845,plain,
% 2.73/0.99      ( m1_subset_1(X0_45,X0_47)
% 2.73/0.99      | ~ m1_subset_1(X1_45,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.73/0.99      | X0_47 != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
% 2.73/0.99      | X0_45 != X1_45 ),
% 2.73/0.99      inference(instantiation,[status(thm)],[c_385]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_990,plain,
% 2.73/0.99      ( m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)))
% 2.73/0.99      | ~ m1_subset_1(X1_45,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.73/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
% 2.73/0.99      | X0_45 != X1_45 ),
% 2.73/0.99      inference(instantiation,[status(thm)],[c_845]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_3575,plain,
% 2.73/0.99      ( ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.73/0.99      | m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.73/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
% 2.73/0.99      | k6_partfun1(sK0) != X0_45 ),
% 2.73/0.99      inference(instantiation,[status(thm)],[c_990]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_4618,plain,
% 2.73/0.99      ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.73/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.73/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
% 2.73/0.99      | k6_partfun1(sK0) != sK2 ),
% 2.73/0.99      inference(instantiation,[status(thm)],[c_3575]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_16,negated_conjecture,
% 2.73/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 2.73/0.99      inference(cnf_transformation,[],[f44]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_363,negated_conjecture,
% 2.73/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 2.73/0.99      inference(subtyping,[status(esa)],[c_16]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_643,plain,
% 2.73/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 2.73/0.99      inference(predicate_to_equality,[status(thm)],[c_363]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_13,negated_conjecture,
% 2.73/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 2.73/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_365,negated_conjecture,
% 2.73/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 2.73/0.99      inference(subtyping,[status(esa)],[c_13]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_641,plain,
% 2.73/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 2.73/0.99      inference(predicate_to_equality,[status(thm)],[c_365]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_8,plain,
% 2.73/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.73/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 2.73/0.99      | ~ v1_funct_1(X0)
% 2.73/0.99      | ~ v1_funct_1(X3)
% 2.73/0.99      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 2.73/0.99      inference(cnf_transformation,[],[f39]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_367,plain,
% 2.73/0.99      ( ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)))
% 2.73/0.99      | ~ m1_subset_1(X1_45,k1_zfmisc_1(k2_zfmisc_1(X2_46,X3_46)))
% 2.73/0.99      | ~ v1_funct_1(X0_45)
% 2.73/0.99      | ~ v1_funct_1(X1_45)
% 2.73/0.99      | k1_partfun1(X2_46,X3_46,X0_46,X1_46,X1_45,X0_45) = k5_relat_1(X1_45,X0_45) ),
% 2.73/0.99      inference(subtyping,[status(esa)],[c_8]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_640,plain,
% 2.73/0.99      ( k1_partfun1(X0_46,X1_46,X2_46,X3_46,X0_45,X1_45) = k5_relat_1(X0_45,X1_45)
% 2.73/0.99      | m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) != iProver_top
% 2.73/0.99      | m1_subset_1(X1_45,k1_zfmisc_1(k2_zfmisc_1(X2_46,X3_46))) != iProver_top
% 2.73/0.99      | v1_funct_1(X0_45) != iProver_top
% 2.73/0.99      | v1_funct_1(X1_45) != iProver_top ),
% 2.73/0.99      inference(predicate_to_equality,[status(thm)],[c_367]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1287,plain,
% 2.73/0.99      ( k1_partfun1(X0_46,X1_46,sK0,sK0,X0_45,sK2) = k5_relat_1(X0_45,sK2)
% 2.73/0.99      | m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) != iProver_top
% 2.73/0.99      | v1_funct_1(X0_45) != iProver_top
% 2.73/0.99      | v1_funct_1(sK2) != iProver_top ),
% 2.73/0.99      inference(superposition,[status(thm)],[c_641,c_640]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_15,negated_conjecture,
% 2.73/0.99      ( v1_funct_1(sK2) ),
% 2.73/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_22,plain,
% 2.73/0.99      ( v1_funct_1(sK2) = iProver_top ),
% 2.73/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1392,plain,
% 2.73/0.99      ( v1_funct_1(X0_45) != iProver_top
% 2.73/0.99      | m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) != iProver_top
% 2.73/0.99      | k1_partfun1(X0_46,X1_46,sK0,sK0,X0_45,sK2) = k5_relat_1(X0_45,sK2) ),
% 2.73/0.99      inference(global_propositional_subsumption,
% 2.73/0.99                [status(thm)],
% 2.73/0.99                [c_1287,c_22]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1393,plain,
% 2.73/0.99      ( k1_partfun1(X0_46,X1_46,sK0,sK0,X0_45,sK2) = k5_relat_1(X0_45,sK2)
% 2.73/0.99      | m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) != iProver_top
% 2.73/0.99      | v1_funct_1(X0_45) != iProver_top ),
% 2.73/0.99      inference(renaming,[status(thm)],[c_1392]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1402,plain,
% 2.73/0.99      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2)
% 2.73/0.99      | v1_funct_1(sK1) != iProver_top ),
% 2.73/0.99      inference(superposition,[status(thm)],[c_643,c_1393]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_5,plain,
% 2.73/0.99      ( ~ r2_relset_1(X0,X1,X2,X3)
% 2.73/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.73/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.73/0.99      | X3 = X2 ),
% 2.73/0.99      inference(cnf_transformation,[],[f35]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_12,negated_conjecture,
% 2.73/0.99      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),sK1) ),
% 2.73/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_229,plain,
% 2.73/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.73/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.73/0.99      | X3 = X0
% 2.73/0.99      | k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) != X0
% 2.73/0.99      | sK1 != X3
% 2.73/0.99      | sK0 != X2
% 2.73/0.99      | sK0 != X1 ),
% 2.73/0.99      inference(resolution_lifted,[status(thm)],[c_5,c_12]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_230,plain,
% 2.73/0.99      ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.73/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.73/0.99      | sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) ),
% 2.73/0.99      inference(unflattening,[status(thm)],[c_229]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_232,plain,
% 2.73/0.99      ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.73/0.99      | sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) ),
% 2.73/0.99      inference(global_propositional_subsumption,
% 2.73/0.99                [status(thm)],
% 2.73/0.99                [c_230,c_16]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_358,plain,
% 2.73/0.99      ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.73/0.99      | sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) ),
% 2.73/0.99      inference(subtyping,[status(esa)],[c_232]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_646,plain,
% 2.73/0.99      ( sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2)
% 2.73/0.99      | m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 2.73/0.99      inference(predicate_to_equality,[status(thm)],[c_358]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_18,negated_conjecture,
% 2.73/0.99      ( v1_funct_1(sK1) ),
% 2.73/0.99      inference(cnf_transformation,[],[f42]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_6,plain,
% 2.73/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.73/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 2.73/0.99      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 2.73/0.99      | ~ v1_funct_1(X0)
% 2.73/0.99      | ~ v1_funct_1(X3) ),
% 2.73/0.99      inference(cnf_transformation,[],[f38]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_369,plain,
% 2.73/0.99      ( ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)))
% 2.73/0.99      | ~ m1_subset_1(X1_45,k1_zfmisc_1(k2_zfmisc_1(X2_46,X3_46)))
% 2.73/0.99      | m1_subset_1(k1_partfun1(X2_46,X3_46,X0_46,X1_46,X1_45,X0_45),k1_zfmisc_1(k2_zfmisc_1(X2_46,X1_46)))
% 2.73/0.99      | ~ v1_funct_1(X0_45)
% 2.73/0.99      | ~ v1_funct_1(X1_45) ),
% 2.73/0.99      inference(subtyping,[status(esa)],[c_6]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_778,plain,
% 2.73/0.99      ( m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.73/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.73/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.73/0.99      | ~ v1_funct_1(sK1)
% 2.73/0.99      | ~ v1_funct_1(sK2) ),
% 2.73/0.99      inference(instantiation,[status(thm)],[c_369]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1116,plain,
% 2.73/0.99      ( sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) ),
% 2.73/0.99      inference(global_propositional_subsumption,
% 2.73/0.99                [status(thm)],
% 2.73/0.99                [c_646,c_18,c_16,c_15,c_13,c_358,c_778]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1418,plain,
% 2.73/0.99      ( k5_relat_1(sK1,sK2) = sK1 | v1_funct_1(sK1) != iProver_top ),
% 2.73/0.99      inference(light_normalisation,[status(thm)],[c_1402,c_1116]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_19,plain,
% 2.73/0.99      ( v1_funct_1(sK1) = iProver_top ),
% 2.73/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1760,plain,
% 2.73/0.99      ( k5_relat_1(sK1,sK2) = sK1 ),
% 2.73/0.99      inference(global_propositional_subsumption,
% 2.73/0.99                [status(thm)],
% 2.73/0.99                [c_1418,c_19]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_3,plain,
% 2.73/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.73/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.73/0.99      inference(cnf_transformation,[],[f34]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_370,plain,
% 2.73/0.99      ( ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)))
% 2.73/0.99      | k2_relset_1(X0_46,X1_46,X0_45) = k2_relat_1(X0_45) ),
% 2.73/0.99      inference(subtyping,[status(esa)],[c_3]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_637,plain,
% 2.73/0.99      ( k2_relset_1(X0_46,X1_46,X0_45) = k2_relat_1(X0_45)
% 2.73/0.99      | m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) != iProver_top ),
% 2.73/0.99      inference(predicate_to_equality,[status(thm)],[c_370]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_939,plain,
% 2.73/0.99      ( k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) ),
% 2.73/0.99      inference(superposition,[status(thm)],[c_643,c_637]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_11,negated_conjecture,
% 2.73/0.99      ( k2_relset_1(sK0,sK0,sK1) = sK0 ),
% 2.73/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_366,negated_conjecture,
% 2.73/0.99      ( k2_relset_1(sK0,sK0,sK1) = sK0 ),
% 2.73/0.99      inference(subtyping,[status(esa)],[c_11]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_941,plain,
% 2.73/0.99      ( k2_relat_1(sK1) = sK0 ),
% 2.73/0.99      inference(light_normalisation,[status(thm)],[c_939,c_366]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_0,plain,
% 2.73/0.99      ( ~ v1_relat_1(X0)
% 2.73/0.99      | ~ v1_relat_1(X1)
% 2.73/0.99      | ~ v1_funct_1(X0)
% 2.73/0.99      | ~ v1_funct_1(X1)
% 2.73/0.99      | k5_relat_1(X1,X0) != X1
% 2.73/0.99      | k2_relat_1(X1) != k1_relat_1(X0)
% 2.73/0.99      | k6_partfun1(k1_relat_1(X0)) = X0 ),
% 2.73/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_373,plain,
% 2.73/0.99      ( ~ v1_relat_1(X0_45)
% 2.73/0.99      | ~ v1_relat_1(X1_45)
% 2.73/0.99      | ~ v1_funct_1(X0_45)
% 2.73/0.99      | ~ v1_funct_1(X1_45)
% 2.73/0.99      | k2_relat_1(X1_45) != k1_relat_1(X0_45)
% 2.73/0.99      | k5_relat_1(X1_45,X0_45) != X1_45
% 2.73/0.99      | k6_partfun1(k1_relat_1(X0_45)) = X0_45 ),
% 2.73/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_634,plain,
% 2.73/0.99      ( k2_relat_1(X0_45) != k1_relat_1(X1_45)
% 2.73/0.99      | k5_relat_1(X0_45,X1_45) != X0_45
% 2.73/0.99      | k6_partfun1(k1_relat_1(X1_45)) = X1_45
% 2.73/0.99      | v1_relat_1(X1_45) != iProver_top
% 2.73/0.99      | v1_relat_1(X0_45) != iProver_top
% 2.73/0.99      | v1_funct_1(X0_45) != iProver_top
% 2.73/0.99      | v1_funct_1(X1_45) != iProver_top ),
% 2.73/0.99      inference(predicate_to_equality,[status(thm)],[c_373]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_984,plain,
% 2.73/0.99      ( k1_relat_1(X0_45) != sK0
% 2.73/0.99      | k5_relat_1(sK1,X0_45) != sK1
% 2.73/0.99      | k6_partfun1(k1_relat_1(X0_45)) = X0_45
% 2.73/0.99      | v1_relat_1(X0_45) != iProver_top
% 2.73/0.99      | v1_relat_1(sK1) != iProver_top
% 2.73/0.99      | v1_funct_1(X0_45) != iProver_top
% 2.73/0.99      | v1_funct_1(sK1) != iProver_top ),
% 2.73/0.99      inference(superposition,[status(thm)],[c_941,c_634]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_21,plain,
% 2.73/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 2.73/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1,plain,
% 2.73/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.73/0.99      | v1_relat_1(X0) ),
% 2.73/0.99      inference(cnf_transformation,[],[f32]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_372,plain,
% 2.73/0.99      ( ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)))
% 2.73/0.99      | v1_relat_1(X0_45) ),
% 2.73/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_405,plain,
% 2.73/0.99      ( m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) != iProver_top
% 2.73/0.99      | v1_relat_1(X0_45) = iProver_top ),
% 2.73/0.99      inference(predicate_to_equality,[status(thm)],[c_372]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_407,plain,
% 2.73/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 2.73/0.99      | v1_relat_1(sK1) = iProver_top ),
% 2.73/0.99      inference(instantiation,[status(thm)],[c_405]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1169,plain,
% 2.73/0.99      ( v1_funct_1(X0_45) != iProver_top
% 2.73/0.99      | k1_relat_1(X0_45) != sK0
% 2.73/0.99      | k5_relat_1(sK1,X0_45) != sK1
% 2.73/0.99      | k6_partfun1(k1_relat_1(X0_45)) = X0_45
% 2.73/0.99      | v1_relat_1(X0_45) != iProver_top ),
% 2.73/0.99      inference(global_propositional_subsumption,
% 2.73/0.99                [status(thm)],
% 2.73/0.99                [c_984,c_19,c_21,c_407]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1170,plain,
% 2.73/0.99      ( k1_relat_1(X0_45) != sK0
% 2.73/0.99      | k5_relat_1(sK1,X0_45) != sK1
% 2.73/0.99      | k6_partfun1(k1_relat_1(X0_45)) = X0_45
% 2.73/0.99      | v1_relat_1(X0_45) != iProver_top
% 2.73/0.99      | v1_funct_1(X0_45) != iProver_top ),
% 2.73/0.99      inference(renaming,[status(thm)],[c_1169]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1763,plain,
% 2.73/0.99      ( k1_relat_1(sK2) != sK0
% 2.73/0.99      | k6_partfun1(k1_relat_1(sK2)) = sK2
% 2.73/0.99      | v1_relat_1(sK2) != iProver_top
% 2.73/0.99      | v1_funct_1(sK2) != iProver_top ),
% 2.73/0.99      inference(superposition,[status(thm)],[c_1760,c_1170]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_2,plain,
% 2.73/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.73/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.73/0.99      inference(cnf_transformation,[],[f33]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_371,plain,
% 2.73/0.99      ( ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)))
% 2.73/0.99      | k1_relset_1(X0_46,X1_46,X0_45) = k1_relat_1(X0_45) ),
% 2.73/0.99      inference(subtyping,[status(esa)],[c_2]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_636,plain,
% 2.73/0.99      ( k1_relset_1(X0_46,X1_46,X0_45) = k1_relat_1(X0_45)
% 2.73/0.99      | m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) != iProver_top ),
% 2.73/0.99      inference(predicate_to_equality,[status(thm)],[c_371]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_927,plain,
% 2.73/0.99      ( k1_relset_1(sK0,sK0,sK2) = k1_relat_1(sK2) ),
% 2.73/0.99      inference(superposition,[status(thm)],[c_641,c_636]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_9,plain,
% 2.73/0.99      ( ~ v1_funct_2(X0,X1,X1)
% 2.73/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 2.73/0.99      | ~ v1_funct_1(X0)
% 2.73/0.99      | k1_relset_1(X1,X1,X0) = X1 ),
% 2.73/0.99      inference(cnf_transformation,[],[f41]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_14,negated_conjecture,
% 2.73/0.99      ( v1_funct_2(sK2,sK0,sK0) ),
% 2.73/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_199,plain,
% 2.73/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 2.73/0.99      | ~ v1_funct_1(X0)
% 2.73/0.99      | k1_relset_1(X1,X1,X0) = X1
% 2.73/0.99      | sK2 != X0
% 2.73/0.99      | sK0 != X1 ),
% 2.73/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_14]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_200,plain,
% 2.73/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.73/0.99      | ~ v1_funct_1(sK2)
% 2.73/0.99      | k1_relset_1(sK0,sK0,sK2) = sK0 ),
% 2.73/0.99      inference(unflattening,[status(thm)],[c_199]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_202,plain,
% 2.73/0.99      ( k1_relset_1(sK0,sK0,sK2) = sK0 ),
% 2.73/0.99      inference(global_propositional_subsumption,
% 2.73/0.99                [status(thm)],
% 2.73/0.99                [c_200,c_15,c_13]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_361,plain,
% 2.73/0.99      ( k1_relset_1(sK0,sK0,sK2) = sK0 ),
% 2.73/0.99      inference(subtyping,[status(esa)],[c_202]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_933,plain,
% 2.73/0.99      ( k1_relat_1(sK2) = sK0 ),
% 2.73/0.99      inference(light_normalisation,[status(thm)],[c_927,c_361]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1764,plain,
% 2.73/0.99      ( sK0 != sK0
% 2.73/0.99      | k6_partfun1(sK0) = sK2
% 2.73/0.99      | v1_relat_1(sK2) != iProver_top
% 2.73/0.99      | v1_funct_1(sK2) != iProver_top ),
% 2.73/0.99      inference(light_normalisation,[status(thm)],[c_1763,c_933]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1765,plain,
% 2.73/0.99      ( k6_partfun1(sK0) = sK2
% 2.73/0.99      | v1_relat_1(sK2) != iProver_top
% 2.73/0.99      | v1_funct_1(sK2) != iProver_top ),
% 2.73/0.99      inference(equality_resolution_simp,[status(thm)],[c_1764]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_635,plain,
% 2.73/0.99      ( m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) != iProver_top
% 2.73/0.99      | v1_relat_1(X0_45) = iProver_top ),
% 2.73/0.99      inference(predicate_to_equality,[status(thm)],[c_372]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_876,plain,
% 2.73/0.99      ( v1_relat_1(sK2) = iProver_top ),
% 2.73/0.99      inference(superposition,[status(thm)],[c_641,c_635]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_379,plain,
% 2.73/0.99      ( X0_45 != X1_45 | X2_45 != X1_45 | X2_45 = X0_45 ),
% 2.73/0.99      theory(equality) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_761,plain,
% 2.73/0.99      ( k6_partfun1(sK0) != X0_45
% 2.73/0.99      | sK2 != X0_45
% 2.73/0.99      | sK2 = k6_partfun1(sK0) ),
% 2.73/0.99      inference(instantiation,[status(thm)],[c_379]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_836,plain,
% 2.73/0.99      ( k6_partfun1(sK0) != sK2 | sK2 = k6_partfun1(sK0) | sK2 != sK2 ),
% 2.73/0.99      inference(instantiation,[status(thm)],[c_761]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_377,plain,( X0_47 = X0_47 ),theory(equality) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_798,plain,
% 2.73/0.99      ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
% 2.73/0.99      inference(instantiation,[status(thm)],[c_377]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_375,plain,( X0_45 = X0_45 ),theory(equality) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_790,plain,
% 2.73/0.99      ( sK2 = sK2 ),
% 2.73/0.99      inference(instantiation,[status(thm)],[c_375]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_4,plain,
% 2.73/0.99      ( r2_relset_1(X0,X1,X2,X2)
% 2.73/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 2.73/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_10,negated_conjecture,
% 2.73/0.99      ( ~ r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0)) ),
% 2.73/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_219,plain,
% 2.73/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.73/0.99      | k6_partfun1(sK0) != X0
% 2.73/0.99      | sK2 != X0
% 2.73/0.99      | sK0 != X2
% 2.73/0.99      | sK0 != X1 ),
% 2.73/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_10]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_220,plain,
% 2.73/0.99      ( ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.73/0.99      | sK2 != k6_partfun1(sK0) ),
% 2.73/0.99      inference(unflattening,[status(thm)],[c_219]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_359,plain,
% 2.73/0.99      ( ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.73/0.99      | sK2 != k6_partfun1(sK0) ),
% 2.73/0.99      inference(subtyping,[status(esa)],[c_220]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(contradiction,plain,
% 2.73/0.99      ( $false ),
% 2.73/0.99      inference(minisat,
% 2.73/0.99                [status(thm)],
% 2.73/0.99                [c_4618,c_1765,c_876,c_836,c_798,c_790,c_359,c_13,c_22]) ).
% 2.73/0.99  
% 2.73/0.99  
% 2.73/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.73/0.99  
% 2.73/0.99  ------                               Statistics
% 2.73/0.99  
% 2.73/0.99  ------ General
% 2.73/0.99  
% 2.73/0.99  abstr_ref_over_cycles:                  0
% 2.73/0.99  abstr_ref_under_cycles:                 0
% 2.73/0.99  gc_basic_clause_elim:                   0
% 2.73/0.99  forced_gc_time:                         0
% 2.73/0.99  parsing_time:                           0.009
% 2.73/0.99  unif_index_cands_time:                  0.
% 2.73/0.99  unif_index_add_time:                    0.
% 2.73/0.99  orderings_time:                         0.
% 2.73/0.99  out_proof_time:                         0.008
% 2.73/0.99  total_time:                             0.175
% 2.73/0.99  num_of_symbols:                         52
% 2.73/0.99  num_of_terms:                           3313
% 2.73/0.99  
% 2.73/0.99  ------ Preprocessing
% 2.73/0.99  
% 2.73/0.99  num_of_splits:                          0
% 2.73/0.99  num_of_split_atoms:                     0
% 2.73/0.99  num_of_reused_defs:                     0
% 2.73/0.99  num_eq_ax_congr_red:                    18
% 2.73/0.99  num_of_sem_filtered_clauses:            1
% 2.73/0.99  num_of_subtypes:                        4
% 2.73/0.99  monotx_restored_types:                  0
% 2.73/0.99  sat_num_of_epr_types:                   0
% 2.73/0.99  sat_num_of_non_cyclic_types:            0
% 2.73/0.99  sat_guarded_non_collapsed_types:        1
% 2.73/0.99  num_pure_diseq_elim:                    0
% 2.73/0.99  simp_replaced_by:                       0
% 2.73/0.99  res_preprocessed:                       99
% 2.73/0.99  prep_upred:                             0
% 2.73/0.99  prep_unflattend:                        15
% 2.73/0.99  smt_new_axioms:                         0
% 2.73/0.99  pred_elim_cands:                        3
% 2.73/0.99  pred_elim:                              2
% 2.73/0.99  pred_elim_cl:                           2
% 2.73/0.99  pred_elim_cycles:                       4
% 2.73/0.99  merged_defs:                            0
% 2.73/0.99  merged_defs_ncl:                        0
% 2.73/0.99  bin_hyper_res:                          0
% 2.73/0.99  prep_cycles:                            4
% 2.73/0.99  pred_elim_time:                         0.003
% 2.73/0.99  splitting_time:                         0.
% 2.73/0.99  sem_filter_time:                        0.
% 2.73/0.99  monotx_time:                            0.
% 2.73/0.99  subtype_inf_time:                       0.
% 2.73/0.99  
% 2.73/0.99  ------ Problem properties
% 2.73/0.99  
% 2.73/0.99  clauses:                                17
% 2.73/0.99  conjectures:                            5
% 2.73/0.99  epr:                                    2
% 2.73/0.99  horn:                                   17
% 2.73/0.99  ground:                                 10
% 2.73/0.99  unary:                                  7
% 2.73/0.99  binary:                                 6
% 2.73/0.99  lits:                                   41
% 2.73/0.99  lits_eq:                                13
% 2.73/0.99  fd_pure:                                0
% 2.73/0.99  fd_pseudo:                              0
% 2.73/0.99  fd_cond:                                0
% 2.73/0.99  fd_pseudo_cond:                         0
% 2.73/0.99  ac_symbols:                             0
% 2.73/0.99  
% 2.73/0.99  ------ Propositional Solver
% 2.73/0.99  
% 2.73/0.99  prop_solver_calls:                      32
% 2.73/0.99  prop_fast_solver_calls:                 763
% 2.73/0.99  smt_solver_calls:                       0
% 2.73/0.99  smt_fast_solver_calls:                  0
% 2.73/0.99  prop_num_of_clauses:                    1225
% 2.73/0.99  prop_preprocess_simplified:             4000
% 2.73/0.99  prop_fo_subsumed:                       61
% 2.73/0.99  prop_solver_time:                       0.
% 2.73/0.99  smt_solver_time:                        0.
% 2.73/0.99  smt_fast_solver_time:                   0.
% 2.73/0.99  prop_fast_solver_time:                  0.
% 2.73/0.99  prop_unsat_core_time:                   0.
% 2.73/0.99  
% 2.73/0.99  ------ QBF
% 2.73/0.99  
% 2.73/0.99  qbf_q_res:                              0
% 2.73/0.99  qbf_num_tautologies:                    0
% 2.73/0.99  qbf_prep_cycles:                        0
% 2.73/0.99  
% 2.73/0.99  ------ BMC1
% 2.73/0.99  
% 2.73/0.99  bmc1_current_bound:                     -1
% 2.73/0.99  bmc1_last_solved_bound:                 -1
% 2.73/0.99  bmc1_unsat_core_size:                   -1
% 2.73/0.99  bmc1_unsat_core_parents_size:           -1
% 2.73/0.99  bmc1_merge_next_fun:                    0
% 2.73/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.73/0.99  
% 2.73/0.99  ------ Instantiation
% 2.73/0.99  
% 2.73/0.99  inst_num_of_clauses:                    536
% 2.73/0.99  inst_num_in_passive:                    205
% 2.73/0.99  inst_num_in_active:                     330
% 2.73/0.99  inst_num_in_unprocessed:                0
% 2.73/0.99  inst_num_of_loops:                      362
% 2.73/0.99  inst_num_of_learning_restarts:          0
% 2.73/0.99  inst_num_moves_active_passive:          19
% 2.73/0.99  inst_lit_activity:                      0
% 2.73/0.99  inst_lit_activity_moves:                0
% 2.73/0.99  inst_num_tautologies:                   0
% 2.73/0.99  inst_num_prop_implied:                  0
% 2.73/0.99  inst_num_existing_simplified:           0
% 2.73/0.99  inst_num_eq_res_simplified:             0
% 2.73/0.99  inst_num_child_elim:                    0
% 2.73/0.99  inst_num_of_dismatching_blockings:      321
% 2.73/0.99  inst_num_of_non_proper_insts:           832
% 2.73/0.99  inst_num_of_duplicates:                 0
% 2.73/0.99  inst_inst_num_from_inst_to_res:         0
% 2.73/0.99  inst_dismatching_checking_time:         0.
% 2.73/0.99  
% 2.73/0.99  ------ Resolution
% 2.73/0.99  
% 2.73/0.99  res_num_of_clauses:                     0
% 2.73/0.99  res_num_in_passive:                     0
% 2.73/0.99  res_num_in_active:                      0
% 2.73/0.99  res_num_of_loops:                       103
% 2.73/0.99  res_forward_subset_subsumed:            38
% 2.73/0.99  res_backward_subset_subsumed:           2
% 2.73/0.99  res_forward_subsumed:                   0
% 2.73/0.99  res_backward_subsumed:                  0
% 2.73/0.99  res_forward_subsumption_resolution:     0
% 2.73/0.99  res_backward_subsumption_resolution:    0
% 2.73/0.99  res_clause_to_clause_subsumption:       260
% 2.73/0.99  res_orphan_elimination:                 0
% 2.73/0.99  res_tautology_del:                      149
% 2.73/0.99  res_num_eq_res_simplified:              1
% 2.73/0.99  res_num_sel_changes:                    0
% 2.73/0.99  res_moves_from_active_to_pass:          0
% 2.73/0.99  
% 2.73/0.99  ------ Superposition
% 2.73/0.99  
% 2.73/0.99  sup_time_total:                         0.
% 2.73/0.99  sup_time_generating:                    0.
% 2.73/0.99  sup_time_sim_full:                      0.
% 2.73/0.99  sup_time_sim_immed:                     0.
% 2.73/0.99  
% 2.73/0.99  sup_num_of_clauses:                     119
% 2.73/0.99  sup_num_in_active:                      71
% 2.73/0.99  sup_num_in_passive:                     48
% 2.73/0.99  sup_num_of_loops:                       72
% 2.73/0.99  sup_fw_superposition:                   61
% 2.73/0.99  sup_bw_superposition:                   55
% 2.73/0.99  sup_immediate_simplified:               23
% 2.73/0.99  sup_given_eliminated:                   0
% 2.73/0.99  comparisons_done:                       0
% 2.73/0.99  comparisons_avoided:                    0
% 2.73/0.99  
% 2.73/0.99  ------ Simplifications
% 2.73/0.99  
% 2.73/0.99  
% 2.73/0.99  sim_fw_subset_subsumed:                 6
% 2.73/0.99  sim_bw_subset_subsumed:                 0
% 2.73/0.99  sim_fw_subsumed:                        0
% 2.73/0.99  sim_bw_subsumed:                        0
% 2.73/0.99  sim_fw_subsumption_res:                 0
% 2.73/0.99  sim_bw_subsumption_res:                 0
% 2.73/0.99  sim_tautology_del:                      1
% 2.73/0.99  sim_eq_tautology_del:                   5
% 2.73/0.99  sim_eq_res_simp:                        1
% 2.73/0.99  sim_fw_demodulated:                     0
% 2.73/0.99  sim_bw_demodulated:                     1
% 2.73/0.99  sim_light_normalised:                   25
% 2.73/0.99  sim_joinable_taut:                      0
% 2.73/0.99  sim_joinable_simp:                      0
% 2.73/0.99  sim_ac_normalised:                      0
% 2.73/0.99  sim_smt_subsumption:                    0
% 2.73/0.99  
%------------------------------------------------------------------------------
