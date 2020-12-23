%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:06:50 EST 2020

% Result     : Theorem 6.88s
% Output     : CNFRefutation 6.88s
% Verified   : 
% Statistics : Number of formulae       :  175 ( 545 expanded)
%              Number of clauses        :  106 ( 184 expanded)
%              Number of leaves         :   17 ( 126 expanded)
%              Depth                    :   22
%              Number of atoms          :  528 (3122 expanded)
%              Number of equality atoms :  169 ( 236 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
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

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f42,plain,(
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

fof(f41,plain,
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

fof(f43,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0))
    & v2_funct_1(sK1)
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK2,sK0,sK0)
    & v1_funct_1(sK2)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f38,f42,f41])).

fof(f63,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f50,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f65,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f43])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f68,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f43])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f33])).

fof(f60,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f29])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f69,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f66,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f31])).

fof(f59,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f64,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f52,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f13,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f74,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f52,f61])).

fof(f70,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_partfun1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f49,f61])).

fof(f57,plain,(
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
    inference(equality_resolution,[],[f57])).

fof(f71,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_566,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_942,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_566])).

cnf(c_7,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_574,plain,
    ( ~ v1_funct_1(X0_48)
    | ~ v1_relat_1(X0_48)
    | v1_relat_1(k2_funct_1(X0_48)) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_934,plain,
    ( v1_funct_1(X0_48) != iProver_top
    | v1_relat_1(X0_48) != iProver_top
    | v1_relat_1(k2_funct_1(X0_48)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_574])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_567,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_941,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_567])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_578,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(X1_48))
    | ~ v1_relat_1(X1_48)
    | v1_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_930,plain,
    ( m1_subset_1(X0_48,k1_zfmisc_1(X1_48)) != iProver_top
    | v1_relat_1(X1_48) != iProver_top
    | v1_relat_1(X0_48) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_578])).

cnf(c_1442,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
    | v1_relat_1(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_941,c_930])).

cnf(c_29,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_78,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_80,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_78])).

cnf(c_1101,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | v1_relat_1(X0_48)
    | ~ v1_relat_1(k2_zfmisc_1(X0_49,X1_49)) ),
    inference(instantiation,[status(thm)],[c_578])).

cnf(c_1102,plain,
    ( m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_relat_1(X0_48) = iProver_top
    | v1_relat_1(k2_zfmisc_1(X0_49,X1_49)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1101])).

cnf(c_1104,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
    | v1_relat_1(sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1102])).

cnf(c_1748,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1442,c_29,c_80,c_1104])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_569,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_939,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_569])).

cnf(c_1441,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_939,c_930])).

cnf(c_32,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1393,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ v1_relat_1(k2_zfmisc_1(X0_49,X1_49))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1101])).

cnf(c_1394,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(X0_49,X1_49)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1393])).

cnf(c_1396,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1394])).

cnf(c_1522,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1441,c_32,c_80,c_1396])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_576,plain,
    ( ~ v1_relat_1(X0_48)
    | ~ v1_relat_1(X1_48)
    | ~ v1_relat_1(X2_48)
    | k5_relat_1(k5_relat_1(X0_48,X1_48),X2_48) = k5_relat_1(X0_48,k5_relat_1(X1_48,X2_48)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_932,plain,
    ( k5_relat_1(k5_relat_1(X0_48,X1_48),X2_48) = k5_relat_1(X0_48,k5_relat_1(X1_48,X2_48))
    | v1_relat_1(X0_48) != iProver_top
    | v1_relat_1(X1_48) != iProver_top
    | v1_relat_1(X2_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_576])).

cnf(c_1618,plain,
    ( k5_relat_1(sK2,k5_relat_1(X0_48,X1_48)) = k5_relat_1(k5_relat_1(sK2,X0_48),X1_48)
    | v1_relat_1(X0_48) != iProver_top
    | v1_relat_1(X1_48) != iProver_top ),
    inference(superposition,[status(thm)],[c_1522,c_932])).

cnf(c_2404,plain,
    ( k5_relat_1(k5_relat_1(sK2,sK1),X0_48) = k5_relat_1(sK2,k5_relat_1(sK1,X0_48))
    | v1_relat_1(X0_48) != iProver_top ),
    inference(superposition,[status(thm)],[c_1748,c_1618])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_570,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49)))
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(X1_48)
    | k1_partfun1(X2_49,X3_49,X0_49,X1_49,X1_48,X0_48) = k5_relat_1(X1_48,X0_48) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_938,plain,
    ( k1_partfun1(X0_49,X1_49,X2_49,X3_49,X0_48,X1_48) = k5_relat_1(X0_48,X1_48)
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(X1_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_570])).

cnf(c_1706,plain,
    ( k1_partfun1(X0_49,X1_49,sK0,sK0,X0_48,sK1) = k5_relat_1(X0_48,sK1)
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_941,c_938])).

cnf(c_27,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_1977,plain,
    ( v1_funct_1(X0_48) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | k1_partfun1(X0_49,X1_49,sK0,sK0,X0_48,sK1) = k5_relat_1(X0_48,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1706,c_27])).

cnf(c_1978,plain,
    ( k1_partfun1(X0_49,X1_49,sK0,sK0,X0_48,sK1) = k5_relat_1(X0_48,sK1)
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(renaming,[status(thm)],[c_1977])).

cnf(c_1984,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) = k5_relat_1(sK2,sK1)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_939,c_1978])).

cnf(c_13,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_20,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_396,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) != X0
    | sK1 != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_20])).

cnf(c_397,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) ),
    inference(unflattening,[status(thm)],[c_396])).

cnf(c_399,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_397,c_24])).

cnf(c_559,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) ),
    inference(subtyping,[status(esa)],[c_399])).

cnf(c_947,plain,
    ( sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1)
    | m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_559])).

cnf(c_23,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_572,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49)))
    | m1_subset_1(k1_partfun1(X2_49,X3_49,X0_49,X1_49,X1_48,X0_48),k1_zfmisc_1(k2_zfmisc_1(X2_49,X1_49)))
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(X1_48) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1123,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_572])).

cnf(c_1365,plain,
    ( sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_947,c_26,c_24,c_23,c_21,c_559,c_1123])).

cnf(c_2005,plain,
    ( k5_relat_1(sK2,sK1) = sK1
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1984,c_1365])).

cnf(c_30,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2099,plain,
    ( k5_relat_1(sK2,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2005,c_30])).

cnf(c_2426,plain,
    ( k5_relat_1(sK2,k5_relat_1(sK1,X0_48)) = k5_relat_1(sK1,X0_48)
    | v1_relat_1(X0_48) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2404,c_2099])).

cnf(c_16057,plain,
    ( k5_relat_1(sK2,k5_relat_1(sK1,k2_funct_1(X0_48))) = k5_relat_1(sK1,k2_funct_1(X0_48))
    | v1_funct_1(X0_48) != iProver_top
    | v1_relat_1(X0_48) != iProver_top ),
    inference(superposition,[status(thm)],[c_934,c_2426])).

cnf(c_16383,plain,
    ( k5_relat_1(sK2,k5_relat_1(sK1,k2_funct_1(sK1))) = k5_relat_1(sK1,k2_funct_1(sK1))
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_942,c_16057])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_573,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | k1_relset_1(X0_49,X1_49,X0_48) = k1_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_935,plain,
    ( k1_relset_1(X0_49,X1_49,X0_48) = k1_relat_1(X0_48)
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_573])).

cnf(c_1262,plain,
    ( k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_941,c_935])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(X1,X1,X0) = X1 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_25,negated_conjecture,
    ( v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_337,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(X1,X1,X0) = X1
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_25])).

cnf(c_338,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | k1_relset_1(sK0,sK0,sK1) = sK0 ),
    inference(unflattening,[status(thm)],[c_337])).

cnf(c_340,plain,
    ( k1_relset_1(sK0,sK0,sK1) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_338,c_26,c_24])).

cnf(c_562,plain,
    ( k1_relset_1(sK0,sK0,sK1) = sK0 ),
    inference(subtyping,[status(esa)],[c_340])).

cnf(c_1264,plain,
    ( k1_relat_1(sK1) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_1262,c_562])).

cnf(c_9,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_19,negated_conjecture,
    ( v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_295,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_19])).

cnf(c_296,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
    inference(unflattening,[status(thm)],[c_295])).

cnf(c_298,plain,
    ( ~ v1_relat_1(sK1)
    | k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_296,c_26])).

cnf(c_565,plain,
    ( ~ v1_relat_1(sK1)
    | k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
    inference(subtyping,[status(esa)],[c_298])).

cnf(c_943,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
    | v1_relat_1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_565])).

cnf(c_79,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1103,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_1101])).

cnf(c_1157,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_943,c_24,c_79,c_565,c_1103])).

cnf(c_1270,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(sK0) ),
    inference(demodulation,[status(thm)],[c_1264,c_1157])).

cnf(c_10,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_347,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_10,c_2])).

cnf(c_5,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_partfun1(X1)) = X0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_366,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_partfun1(X2)) = X0 ),
    inference(resolution,[status(thm)],[c_347,c_5])).

cnf(c_561,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ v1_relat_1(X0_48)
    | k5_relat_1(X0_48,k6_partfun1(X1_49)) = X0_48 ),
    inference(subtyping,[status(esa)],[c_366])).

cnf(c_945,plain,
    ( k5_relat_1(X0_48,k6_partfun1(X0_49)) = X0_48
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_49,X0_49))) != iProver_top
    | v1_relat_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_561])).

cnf(c_2300,plain,
    ( k5_relat_1(sK2,k6_partfun1(sK0)) = sK2
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_939,c_945])).

cnf(c_1194,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ v1_relat_1(sK2)
    | k5_relat_1(sK2,k6_partfun1(X1_49)) = sK2 ),
    inference(instantiation,[status(thm)],[c_561])).

cnf(c_1197,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_relat_1(sK2)
    | k5_relat_1(sK2,k6_partfun1(sK0)) = sK2 ),
    inference(instantiation,[status(thm)],[c_1194])).

cnf(c_1395,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1393])).

cnf(c_2329,plain,
    ( k5_relat_1(sK2,k6_partfun1(sK0)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2300,c_21,c_79,c_1197,c_1395])).

cnf(c_16423,plain,
    ( k6_partfun1(sK0) = sK2
    | v1_relat_1(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_16383,c_1270,c_2329])).

cnf(c_16837,plain,
    ( k6_partfun1(sK0) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_16423,c_29,c_80,c_1104])).

cnf(c_12,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_18,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_386,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k6_partfun1(sK0) != X0
    | sK2 != X0
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_18])).

cnf(c_387,plain,
    ( ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK2 != k6_partfun1(sK0) ),
    inference(unflattening,[status(thm)],[c_386])).

cnf(c_560,plain,
    ( ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK2 != k6_partfun1(sK0) ),
    inference(subtyping,[status(esa)],[c_387])).

cnf(c_946,plain,
    ( sK2 != k6_partfun1(sK0)
    | m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_560])).

cnf(c_16851,plain,
    ( sK2 != sK2
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_16837,c_946])).

cnf(c_16852,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_16851])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_16852,c_32])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:49:22 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.35  % Running in FOF mode
% 6.88/1.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.88/1.50  
% 6.88/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.88/1.50  
% 6.88/1.50  ------  iProver source info
% 6.88/1.50  
% 6.88/1.50  git: date: 2020-06-30 10:37:57 +0100
% 6.88/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.88/1.50  git: non_committed_changes: false
% 6.88/1.50  git: last_make_outside_of_git: false
% 6.88/1.50  
% 6.88/1.50  ------ 
% 6.88/1.50  
% 6.88/1.50  ------ Input Options
% 6.88/1.50  
% 6.88/1.50  --out_options                           all
% 6.88/1.50  --tptp_safe_out                         true
% 6.88/1.50  --problem_path                          ""
% 6.88/1.50  --include_path                          ""
% 6.88/1.50  --clausifier                            res/vclausify_rel
% 6.88/1.50  --clausifier_options                    --mode clausify
% 6.88/1.50  --stdin                                 false
% 6.88/1.50  --stats_out                             all
% 6.88/1.50  
% 6.88/1.50  ------ General Options
% 6.88/1.50  
% 6.88/1.50  --fof                                   false
% 6.88/1.50  --time_out_real                         305.
% 6.88/1.50  --time_out_virtual                      -1.
% 6.88/1.50  --symbol_type_check                     false
% 6.88/1.50  --clausify_out                          false
% 6.88/1.50  --sig_cnt_out                           false
% 6.88/1.50  --trig_cnt_out                          false
% 6.88/1.50  --trig_cnt_out_tolerance                1.
% 6.88/1.50  --trig_cnt_out_sk_spl                   false
% 6.88/1.50  --abstr_cl_out                          false
% 6.88/1.50  
% 6.88/1.50  ------ Global Options
% 6.88/1.50  
% 6.88/1.50  --schedule                              default
% 6.88/1.50  --add_important_lit                     false
% 6.88/1.50  --prop_solver_per_cl                    1000
% 6.88/1.50  --min_unsat_core                        false
% 6.88/1.50  --soft_assumptions                      false
% 6.88/1.50  --soft_lemma_size                       3
% 6.88/1.50  --prop_impl_unit_size                   0
% 6.88/1.50  --prop_impl_unit                        []
% 6.88/1.50  --share_sel_clauses                     true
% 6.88/1.50  --reset_solvers                         false
% 6.88/1.50  --bc_imp_inh                            [conj_cone]
% 6.88/1.50  --conj_cone_tolerance                   3.
% 6.88/1.50  --extra_neg_conj                        none
% 6.88/1.50  --large_theory_mode                     true
% 6.88/1.50  --prolific_symb_bound                   200
% 6.88/1.50  --lt_threshold                          2000
% 6.88/1.50  --clause_weak_htbl                      true
% 6.88/1.50  --gc_record_bc_elim                     false
% 6.88/1.50  
% 6.88/1.50  ------ Preprocessing Options
% 6.88/1.50  
% 6.88/1.50  --preprocessing_flag                    true
% 6.88/1.50  --time_out_prep_mult                    0.1
% 6.88/1.50  --splitting_mode                        input
% 6.88/1.50  --splitting_grd                         true
% 6.88/1.50  --splitting_cvd                         false
% 6.88/1.50  --splitting_cvd_svl                     false
% 6.88/1.50  --splitting_nvd                         32
% 6.88/1.50  --sub_typing                            true
% 6.88/1.50  --prep_gs_sim                           true
% 6.88/1.50  --prep_unflatten                        true
% 6.88/1.50  --prep_res_sim                          true
% 6.88/1.50  --prep_upred                            true
% 6.88/1.50  --prep_sem_filter                       exhaustive
% 6.88/1.50  --prep_sem_filter_out                   false
% 6.88/1.50  --pred_elim                             true
% 6.88/1.50  --res_sim_input                         true
% 6.88/1.50  --eq_ax_congr_red                       true
% 6.88/1.50  --pure_diseq_elim                       true
% 6.88/1.50  --brand_transform                       false
% 6.88/1.50  --non_eq_to_eq                          false
% 6.88/1.50  --prep_def_merge                        true
% 6.88/1.50  --prep_def_merge_prop_impl              false
% 6.88/1.50  --prep_def_merge_mbd                    true
% 6.88/1.50  --prep_def_merge_tr_red                 false
% 6.88/1.50  --prep_def_merge_tr_cl                  false
% 6.88/1.50  --smt_preprocessing                     true
% 6.88/1.50  --smt_ac_axioms                         fast
% 6.88/1.50  --preprocessed_out                      false
% 6.88/1.50  --preprocessed_stats                    false
% 6.88/1.50  
% 6.88/1.50  ------ Abstraction refinement Options
% 6.88/1.50  
% 6.88/1.50  --abstr_ref                             []
% 6.88/1.50  --abstr_ref_prep                        false
% 6.88/1.50  --abstr_ref_until_sat                   false
% 6.88/1.50  --abstr_ref_sig_restrict                funpre
% 6.88/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 6.88/1.50  --abstr_ref_under                       []
% 6.88/1.50  
% 6.88/1.50  ------ SAT Options
% 6.88/1.50  
% 6.88/1.50  --sat_mode                              false
% 6.88/1.50  --sat_fm_restart_options                ""
% 6.88/1.50  --sat_gr_def                            false
% 6.88/1.50  --sat_epr_types                         true
% 6.88/1.50  --sat_non_cyclic_types                  false
% 6.88/1.50  --sat_finite_models                     false
% 6.88/1.50  --sat_fm_lemmas                         false
% 6.88/1.50  --sat_fm_prep                           false
% 6.88/1.50  --sat_fm_uc_incr                        true
% 6.88/1.50  --sat_out_model                         small
% 6.88/1.50  --sat_out_clauses                       false
% 6.88/1.50  
% 6.88/1.50  ------ QBF Options
% 6.88/1.50  
% 6.88/1.50  --qbf_mode                              false
% 6.88/1.50  --qbf_elim_univ                         false
% 6.88/1.50  --qbf_dom_inst                          none
% 6.88/1.50  --qbf_dom_pre_inst                      false
% 6.88/1.50  --qbf_sk_in                             false
% 6.88/1.50  --qbf_pred_elim                         true
% 6.88/1.50  --qbf_split                             512
% 6.88/1.50  
% 6.88/1.50  ------ BMC1 Options
% 6.88/1.50  
% 6.88/1.50  --bmc1_incremental                      false
% 6.88/1.50  --bmc1_axioms                           reachable_all
% 6.88/1.50  --bmc1_min_bound                        0
% 6.88/1.50  --bmc1_max_bound                        -1
% 6.88/1.50  --bmc1_max_bound_default                -1
% 6.88/1.50  --bmc1_symbol_reachability              true
% 6.88/1.50  --bmc1_property_lemmas                  false
% 6.88/1.50  --bmc1_k_induction                      false
% 6.88/1.50  --bmc1_non_equiv_states                 false
% 6.88/1.50  --bmc1_deadlock                         false
% 6.88/1.50  --bmc1_ucm                              false
% 6.88/1.50  --bmc1_add_unsat_core                   none
% 6.88/1.50  --bmc1_unsat_core_children              false
% 6.88/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 6.88/1.50  --bmc1_out_stat                         full
% 6.88/1.50  --bmc1_ground_init                      false
% 6.88/1.50  --bmc1_pre_inst_next_state              false
% 6.88/1.50  --bmc1_pre_inst_state                   false
% 6.88/1.50  --bmc1_pre_inst_reach_state             false
% 6.88/1.50  --bmc1_out_unsat_core                   false
% 6.88/1.50  --bmc1_aig_witness_out                  false
% 6.88/1.50  --bmc1_verbose                          false
% 6.88/1.50  --bmc1_dump_clauses_tptp                false
% 6.88/1.50  --bmc1_dump_unsat_core_tptp             false
% 6.88/1.50  --bmc1_dump_file                        -
% 6.88/1.50  --bmc1_ucm_expand_uc_limit              128
% 6.88/1.50  --bmc1_ucm_n_expand_iterations          6
% 6.88/1.50  --bmc1_ucm_extend_mode                  1
% 6.88/1.50  --bmc1_ucm_init_mode                    2
% 6.88/1.50  --bmc1_ucm_cone_mode                    none
% 6.88/1.50  --bmc1_ucm_reduced_relation_type        0
% 6.88/1.50  --bmc1_ucm_relax_model                  4
% 6.88/1.50  --bmc1_ucm_full_tr_after_sat            true
% 6.88/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 6.88/1.50  --bmc1_ucm_layered_model                none
% 6.88/1.50  --bmc1_ucm_max_lemma_size               10
% 6.88/1.50  
% 6.88/1.50  ------ AIG Options
% 6.88/1.50  
% 6.88/1.50  --aig_mode                              false
% 6.88/1.50  
% 6.88/1.50  ------ Instantiation Options
% 6.88/1.50  
% 6.88/1.50  --instantiation_flag                    true
% 6.88/1.50  --inst_sos_flag                         false
% 6.88/1.50  --inst_sos_phase                        true
% 6.88/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.88/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.88/1.50  --inst_lit_sel_side                     num_symb
% 6.88/1.50  --inst_solver_per_active                1400
% 6.88/1.50  --inst_solver_calls_frac                1.
% 6.88/1.50  --inst_passive_queue_type               priority_queues
% 6.88/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.88/1.50  --inst_passive_queues_freq              [25;2]
% 6.88/1.50  --inst_dismatching                      true
% 6.88/1.50  --inst_eager_unprocessed_to_passive     true
% 6.88/1.50  --inst_prop_sim_given                   true
% 6.88/1.50  --inst_prop_sim_new                     false
% 6.88/1.50  --inst_subs_new                         false
% 6.88/1.50  --inst_eq_res_simp                      false
% 6.88/1.50  --inst_subs_given                       false
% 6.88/1.50  --inst_orphan_elimination               true
% 6.88/1.50  --inst_learning_loop_flag               true
% 6.88/1.50  --inst_learning_start                   3000
% 6.88/1.50  --inst_learning_factor                  2
% 6.88/1.50  --inst_start_prop_sim_after_learn       3
% 6.88/1.50  --inst_sel_renew                        solver
% 6.88/1.50  --inst_lit_activity_flag                true
% 6.88/1.50  --inst_restr_to_given                   false
% 6.88/1.50  --inst_activity_threshold               500
% 6.88/1.50  --inst_out_proof                        true
% 6.88/1.50  
% 6.88/1.50  ------ Resolution Options
% 6.88/1.50  
% 6.88/1.50  --resolution_flag                       true
% 6.88/1.50  --res_lit_sel                           adaptive
% 6.88/1.50  --res_lit_sel_side                      none
% 6.88/1.50  --res_ordering                          kbo
% 6.88/1.50  --res_to_prop_solver                    active
% 6.88/1.50  --res_prop_simpl_new                    false
% 6.88/1.50  --res_prop_simpl_given                  true
% 6.88/1.50  --res_passive_queue_type                priority_queues
% 6.88/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.88/1.50  --res_passive_queues_freq               [15;5]
% 6.88/1.50  --res_forward_subs                      full
% 6.88/1.50  --res_backward_subs                     full
% 6.88/1.50  --res_forward_subs_resolution           true
% 6.88/1.50  --res_backward_subs_resolution          true
% 6.88/1.50  --res_orphan_elimination                true
% 6.88/1.50  --res_time_limit                        2.
% 6.88/1.50  --res_out_proof                         true
% 6.88/1.50  
% 6.88/1.50  ------ Superposition Options
% 6.88/1.50  
% 6.88/1.50  --superposition_flag                    true
% 6.88/1.50  --sup_passive_queue_type                priority_queues
% 6.88/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.88/1.50  --sup_passive_queues_freq               [8;1;4]
% 6.88/1.50  --demod_completeness_check              fast
% 6.88/1.50  --demod_use_ground                      true
% 6.88/1.50  --sup_to_prop_solver                    passive
% 6.88/1.50  --sup_prop_simpl_new                    true
% 6.88/1.50  --sup_prop_simpl_given                  true
% 6.88/1.50  --sup_fun_splitting                     false
% 6.88/1.50  --sup_smt_interval                      50000
% 6.88/1.50  
% 6.88/1.50  ------ Superposition Simplification Setup
% 6.88/1.50  
% 6.88/1.50  --sup_indices_passive                   []
% 6.88/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.88/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.88/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.88/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 6.88/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.88/1.50  --sup_full_bw                           [BwDemod]
% 6.88/1.50  --sup_immed_triv                        [TrivRules]
% 6.88/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.88/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.88/1.50  --sup_immed_bw_main                     []
% 6.88/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.88/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 6.88/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.88/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.88/1.50  
% 6.88/1.50  ------ Combination Options
% 6.88/1.50  
% 6.88/1.50  --comb_res_mult                         3
% 6.88/1.50  --comb_sup_mult                         2
% 6.88/1.50  --comb_inst_mult                        10
% 6.88/1.50  
% 6.88/1.50  ------ Debug Options
% 6.88/1.50  
% 6.88/1.50  --dbg_backtrace                         false
% 6.88/1.50  --dbg_dump_prop_clauses                 false
% 6.88/1.50  --dbg_dump_prop_clauses_file            -
% 6.88/1.50  --dbg_out_stat                          false
% 6.88/1.50  ------ Parsing...
% 6.88/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.88/1.50  
% 6.88/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 6.88/1.50  
% 6.88/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.88/1.50  
% 6.88/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.88/1.50  ------ Proving...
% 6.88/1.50  ------ Problem Properties 
% 6.88/1.50  
% 6.88/1.50  
% 6.88/1.50  clauses                                 21
% 6.88/1.50  conjectures                             4
% 6.88/1.50  EPR                                     2
% 6.88/1.50  Horn                                    21
% 6.88/1.50  unary                                   7
% 6.88/1.50  binary                                  6
% 6.88/1.50  lits                                    50
% 6.88/1.50  lits eq                                 12
% 6.88/1.50  fd_pure                                 0
% 6.88/1.50  fd_pseudo                               0
% 6.88/1.50  fd_cond                                 0
% 6.88/1.50  fd_pseudo_cond                          0
% 6.88/1.50  AC symbols                              0
% 6.88/1.50  
% 6.88/1.50  ------ Schedule dynamic 5 is on 
% 6.88/1.50  
% 6.88/1.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 6.88/1.50  
% 6.88/1.50  
% 6.88/1.50  ------ 
% 6.88/1.50  Current options:
% 6.88/1.50  ------ 
% 6.88/1.50  
% 6.88/1.50  ------ Input Options
% 6.88/1.50  
% 6.88/1.50  --out_options                           all
% 6.88/1.50  --tptp_safe_out                         true
% 6.88/1.50  --problem_path                          ""
% 6.88/1.50  --include_path                          ""
% 6.88/1.50  --clausifier                            res/vclausify_rel
% 6.88/1.50  --clausifier_options                    --mode clausify
% 6.88/1.50  --stdin                                 false
% 6.88/1.50  --stats_out                             all
% 6.88/1.50  
% 6.88/1.50  ------ General Options
% 6.88/1.50  
% 6.88/1.50  --fof                                   false
% 6.88/1.50  --time_out_real                         305.
% 6.88/1.50  --time_out_virtual                      -1.
% 6.88/1.50  --symbol_type_check                     false
% 6.88/1.50  --clausify_out                          false
% 6.88/1.50  --sig_cnt_out                           false
% 6.88/1.50  --trig_cnt_out                          false
% 6.88/1.50  --trig_cnt_out_tolerance                1.
% 6.88/1.50  --trig_cnt_out_sk_spl                   false
% 6.88/1.50  --abstr_cl_out                          false
% 6.88/1.50  
% 6.88/1.50  ------ Global Options
% 6.88/1.50  
% 6.88/1.50  --schedule                              default
% 6.88/1.50  --add_important_lit                     false
% 6.88/1.50  --prop_solver_per_cl                    1000
% 6.88/1.50  --min_unsat_core                        false
% 6.88/1.50  --soft_assumptions                      false
% 6.88/1.50  --soft_lemma_size                       3
% 6.88/1.50  --prop_impl_unit_size                   0
% 6.88/1.50  --prop_impl_unit                        []
% 6.88/1.50  --share_sel_clauses                     true
% 6.88/1.50  --reset_solvers                         false
% 6.88/1.50  --bc_imp_inh                            [conj_cone]
% 6.88/1.50  --conj_cone_tolerance                   3.
% 6.88/1.50  --extra_neg_conj                        none
% 6.88/1.50  --large_theory_mode                     true
% 6.88/1.50  --prolific_symb_bound                   200
% 6.88/1.50  --lt_threshold                          2000
% 6.88/1.50  --clause_weak_htbl                      true
% 6.88/1.50  --gc_record_bc_elim                     false
% 6.88/1.50  
% 6.88/1.50  ------ Preprocessing Options
% 6.88/1.50  
% 6.88/1.50  --preprocessing_flag                    true
% 6.88/1.50  --time_out_prep_mult                    0.1
% 6.88/1.50  --splitting_mode                        input
% 6.88/1.50  --splitting_grd                         true
% 6.88/1.50  --splitting_cvd                         false
% 6.88/1.50  --splitting_cvd_svl                     false
% 6.88/1.50  --splitting_nvd                         32
% 6.88/1.50  --sub_typing                            true
% 6.88/1.50  --prep_gs_sim                           true
% 6.88/1.50  --prep_unflatten                        true
% 6.88/1.50  --prep_res_sim                          true
% 6.88/1.50  --prep_upred                            true
% 6.88/1.50  --prep_sem_filter                       exhaustive
% 6.88/1.50  --prep_sem_filter_out                   false
% 6.88/1.50  --pred_elim                             true
% 6.88/1.50  --res_sim_input                         true
% 6.88/1.50  --eq_ax_congr_red                       true
% 6.88/1.50  --pure_diseq_elim                       true
% 6.88/1.50  --brand_transform                       false
% 6.88/1.50  --non_eq_to_eq                          false
% 6.88/1.50  --prep_def_merge                        true
% 6.88/1.50  --prep_def_merge_prop_impl              false
% 6.88/1.50  --prep_def_merge_mbd                    true
% 6.88/1.50  --prep_def_merge_tr_red                 false
% 6.88/1.50  --prep_def_merge_tr_cl                  false
% 6.88/1.50  --smt_preprocessing                     true
% 6.88/1.50  --smt_ac_axioms                         fast
% 6.88/1.50  --preprocessed_out                      false
% 6.88/1.50  --preprocessed_stats                    false
% 6.88/1.50  
% 6.88/1.50  ------ Abstraction refinement Options
% 6.88/1.50  
% 6.88/1.50  --abstr_ref                             []
% 6.88/1.50  --abstr_ref_prep                        false
% 6.88/1.50  --abstr_ref_until_sat                   false
% 6.88/1.50  --abstr_ref_sig_restrict                funpre
% 6.88/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 6.88/1.50  --abstr_ref_under                       []
% 6.88/1.50  
% 6.88/1.50  ------ SAT Options
% 6.88/1.50  
% 6.88/1.50  --sat_mode                              false
% 6.88/1.50  --sat_fm_restart_options                ""
% 6.88/1.50  --sat_gr_def                            false
% 6.88/1.50  --sat_epr_types                         true
% 6.88/1.50  --sat_non_cyclic_types                  false
% 6.88/1.50  --sat_finite_models                     false
% 6.88/1.50  --sat_fm_lemmas                         false
% 6.88/1.50  --sat_fm_prep                           false
% 6.88/1.50  --sat_fm_uc_incr                        true
% 6.88/1.50  --sat_out_model                         small
% 6.88/1.50  --sat_out_clauses                       false
% 6.88/1.50  
% 6.88/1.50  ------ QBF Options
% 6.88/1.50  
% 6.88/1.50  --qbf_mode                              false
% 6.88/1.50  --qbf_elim_univ                         false
% 6.88/1.50  --qbf_dom_inst                          none
% 6.88/1.50  --qbf_dom_pre_inst                      false
% 6.88/1.50  --qbf_sk_in                             false
% 6.88/1.50  --qbf_pred_elim                         true
% 6.88/1.50  --qbf_split                             512
% 6.88/1.50  
% 6.88/1.50  ------ BMC1 Options
% 6.88/1.50  
% 6.88/1.50  --bmc1_incremental                      false
% 6.88/1.50  --bmc1_axioms                           reachable_all
% 6.88/1.50  --bmc1_min_bound                        0
% 6.88/1.50  --bmc1_max_bound                        -1
% 6.88/1.50  --bmc1_max_bound_default                -1
% 6.88/1.50  --bmc1_symbol_reachability              true
% 6.88/1.50  --bmc1_property_lemmas                  false
% 6.88/1.50  --bmc1_k_induction                      false
% 6.88/1.50  --bmc1_non_equiv_states                 false
% 6.88/1.50  --bmc1_deadlock                         false
% 6.88/1.50  --bmc1_ucm                              false
% 6.88/1.50  --bmc1_add_unsat_core                   none
% 6.88/1.50  --bmc1_unsat_core_children              false
% 6.88/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 6.88/1.50  --bmc1_out_stat                         full
% 6.88/1.50  --bmc1_ground_init                      false
% 6.88/1.50  --bmc1_pre_inst_next_state              false
% 6.88/1.50  --bmc1_pre_inst_state                   false
% 6.88/1.50  --bmc1_pre_inst_reach_state             false
% 6.88/1.50  --bmc1_out_unsat_core                   false
% 6.88/1.50  --bmc1_aig_witness_out                  false
% 6.88/1.50  --bmc1_verbose                          false
% 6.88/1.50  --bmc1_dump_clauses_tptp                false
% 6.88/1.50  --bmc1_dump_unsat_core_tptp             false
% 6.88/1.50  --bmc1_dump_file                        -
% 6.88/1.50  --bmc1_ucm_expand_uc_limit              128
% 6.88/1.50  --bmc1_ucm_n_expand_iterations          6
% 6.88/1.50  --bmc1_ucm_extend_mode                  1
% 6.88/1.50  --bmc1_ucm_init_mode                    2
% 6.88/1.50  --bmc1_ucm_cone_mode                    none
% 6.88/1.50  --bmc1_ucm_reduced_relation_type        0
% 6.88/1.50  --bmc1_ucm_relax_model                  4
% 6.88/1.50  --bmc1_ucm_full_tr_after_sat            true
% 6.88/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 6.88/1.50  --bmc1_ucm_layered_model                none
% 6.88/1.50  --bmc1_ucm_max_lemma_size               10
% 6.88/1.50  
% 6.88/1.50  ------ AIG Options
% 6.88/1.50  
% 6.88/1.50  --aig_mode                              false
% 6.88/1.50  
% 6.88/1.50  ------ Instantiation Options
% 6.88/1.50  
% 6.88/1.50  --instantiation_flag                    true
% 6.88/1.50  --inst_sos_flag                         false
% 6.88/1.50  --inst_sos_phase                        true
% 6.88/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.88/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.88/1.50  --inst_lit_sel_side                     none
% 6.88/1.50  --inst_solver_per_active                1400
% 6.88/1.50  --inst_solver_calls_frac                1.
% 6.88/1.50  --inst_passive_queue_type               priority_queues
% 6.88/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.88/1.50  --inst_passive_queues_freq              [25;2]
% 6.88/1.50  --inst_dismatching                      true
% 6.88/1.50  --inst_eager_unprocessed_to_passive     true
% 6.88/1.50  --inst_prop_sim_given                   true
% 6.88/1.50  --inst_prop_sim_new                     false
% 6.88/1.50  --inst_subs_new                         false
% 6.88/1.50  --inst_eq_res_simp                      false
% 6.88/1.50  --inst_subs_given                       false
% 6.88/1.50  --inst_orphan_elimination               true
% 6.88/1.50  --inst_learning_loop_flag               true
% 6.88/1.50  --inst_learning_start                   3000
% 6.88/1.50  --inst_learning_factor                  2
% 6.88/1.50  --inst_start_prop_sim_after_learn       3
% 6.88/1.50  --inst_sel_renew                        solver
% 6.88/1.50  --inst_lit_activity_flag                true
% 6.88/1.50  --inst_restr_to_given                   false
% 6.88/1.50  --inst_activity_threshold               500
% 6.88/1.50  --inst_out_proof                        true
% 6.88/1.50  
% 6.88/1.50  ------ Resolution Options
% 6.88/1.50  
% 6.88/1.50  --resolution_flag                       false
% 6.88/1.50  --res_lit_sel                           adaptive
% 6.88/1.50  --res_lit_sel_side                      none
% 6.88/1.50  --res_ordering                          kbo
% 6.88/1.50  --res_to_prop_solver                    active
% 6.88/1.50  --res_prop_simpl_new                    false
% 6.88/1.50  --res_prop_simpl_given                  true
% 6.88/1.50  --res_passive_queue_type                priority_queues
% 6.88/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.88/1.50  --res_passive_queues_freq               [15;5]
% 6.88/1.50  --res_forward_subs                      full
% 6.88/1.50  --res_backward_subs                     full
% 6.88/1.50  --res_forward_subs_resolution           true
% 6.88/1.50  --res_backward_subs_resolution          true
% 6.88/1.50  --res_orphan_elimination                true
% 6.88/1.50  --res_time_limit                        2.
% 6.88/1.50  --res_out_proof                         true
% 6.88/1.50  
% 6.88/1.50  ------ Superposition Options
% 6.88/1.50  
% 6.88/1.50  --superposition_flag                    true
% 6.88/1.50  --sup_passive_queue_type                priority_queues
% 6.88/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.88/1.50  --sup_passive_queues_freq               [8;1;4]
% 6.88/1.50  --demod_completeness_check              fast
% 6.88/1.50  --demod_use_ground                      true
% 6.88/1.50  --sup_to_prop_solver                    passive
% 6.88/1.50  --sup_prop_simpl_new                    true
% 6.88/1.50  --sup_prop_simpl_given                  true
% 6.88/1.50  --sup_fun_splitting                     false
% 6.88/1.50  --sup_smt_interval                      50000
% 6.88/1.50  
% 6.88/1.50  ------ Superposition Simplification Setup
% 6.88/1.50  
% 6.88/1.50  --sup_indices_passive                   []
% 6.88/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.88/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.88/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.88/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 6.88/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.88/1.50  --sup_full_bw                           [BwDemod]
% 6.88/1.50  --sup_immed_triv                        [TrivRules]
% 6.88/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.88/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.88/1.50  --sup_immed_bw_main                     []
% 6.88/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.88/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 6.88/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.88/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.88/1.50  
% 6.88/1.50  ------ Combination Options
% 6.88/1.50  
% 6.88/1.50  --comb_res_mult                         3
% 6.88/1.50  --comb_sup_mult                         2
% 6.88/1.50  --comb_inst_mult                        10
% 6.88/1.50  
% 6.88/1.50  ------ Debug Options
% 6.88/1.50  
% 6.88/1.50  --dbg_backtrace                         false
% 6.88/1.50  --dbg_dump_prop_clauses                 false
% 6.88/1.50  --dbg_dump_prop_clauses_file            -
% 6.88/1.50  --dbg_out_stat                          false
% 6.88/1.50  
% 6.88/1.50  
% 6.88/1.50  
% 6.88/1.50  
% 6.88/1.50  ------ Proving...
% 6.88/1.50  
% 6.88/1.50  
% 6.88/1.50  % SZS status Theorem for theBenchmark.p
% 6.88/1.50  
% 6.88/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 6.88/1.50  
% 6.88/1.50  fof(f15,conjecture,(
% 6.88/1.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)) => r2_relset_1(X0,X0,X2,k6_partfun1(X0)))))),
% 6.88/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.88/1.50  
% 6.88/1.50  fof(f16,negated_conjecture,(
% 6.88/1.50    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)) => r2_relset_1(X0,X0,X2,k6_partfun1(X0)))))),
% 6.88/1.50    inference(negated_conjecture,[],[f15])).
% 6.88/1.50  
% 6.88/1.50  fof(f37,plain,(
% 6.88/1.50    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & (v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 6.88/1.50    inference(ennf_transformation,[],[f16])).
% 6.88/1.50  
% 6.88/1.50  fof(f38,plain,(
% 6.88/1.50    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 6.88/1.50    inference(flattening,[],[f37])).
% 6.88/1.50  
% 6.88/1.50  fof(f42,plain,(
% 6.88/1.50    ( ! [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (~r2_relset_1(X0,X0,sK2,k6_partfun1(X0)) & v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,sK2,X1),X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(sK2,X0,X0) & v1_funct_1(sK2))) )),
% 6.88/1.50    introduced(choice_axiom,[])).
% 6.88/1.50  
% 6.88/1.50  fof(f41,plain,(
% 6.88/1.50    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK0,sK0,X2,k6_partfun1(sK0)) & v2_funct_1(sK1) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,X2,sK1),sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 6.88/1.50    introduced(choice_axiom,[])).
% 6.88/1.50  
% 6.88/1.50  fof(f43,plain,(
% 6.88/1.50    (~r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0)) & v2_funct_1(sK1) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 6.88/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f38,f42,f41])).
% 6.88/1.50  
% 6.88/1.50  fof(f63,plain,(
% 6.88/1.50    v1_funct_1(sK1)),
% 6.88/1.50    inference(cnf_transformation,[],[f43])).
% 6.88/1.50  
% 6.88/1.50  fof(f6,axiom,(
% 6.88/1.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 6.88/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.88/1.50  
% 6.88/1.50  fof(f23,plain,(
% 6.88/1.50    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 6.88/1.50    inference(ennf_transformation,[],[f6])).
% 6.88/1.50  
% 6.88/1.50  fof(f24,plain,(
% 6.88/1.50    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 6.88/1.50    inference(flattening,[],[f23])).
% 6.88/1.50  
% 6.88/1.50  fof(f50,plain,(
% 6.88/1.50    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.88/1.50    inference(cnf_transformation,[],[f24])).
% 6.88/1.50  
% 6.88/1.50  fof(f65,plain,(
% 6.88/1.50    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 6.88/1.50    inference(cnf_transformation,[],[f43])).
% 6.88/1.50  
% 6.88/1.50  fof(f1,axiom,(
% 6.88/1.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 6.88/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.88/1.50  
% 6.88/1.50  fof(f18,plain,(
% 6.88/1.50    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 6.88/1.50    inference(ennf_transformation,[],[f1])).
% 6.88/1.50  
% 6.88/1.50  fof(f44,plain,(
% 6.88/1.50    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 6.88/1.50    inference(cnf_transformation,[],[f18])).
% 6.88/1.50  
% 6.88/1.50  fof(f3,axiom,(
% 6.88/1.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 6.88/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.88/1.50  
% 6.88/1.50  fof(f47,plain,(
% 6.88/1.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 6.88/1.50    inference(cnf_transformation,[],[f3])).
% 6.88/1.50  
% 6.88/1.50  fof(f68,plain,(
% 6.88/1.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 6.88/1.50    inference(cnf_transformation,[],[f43])).
% 6.88/1.50  
% 6.88/1.50  fof(f4,axiom,(
% 6.88/1.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2))))),
% 6.88/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.88/1.50  
% 6.88/1.50  fof(f20,plain,(
% 6.88/1.50    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 6.88/1.50    inference(ennf_transformation,[],[f4])).
% 6.88/1.50  
% 6.88/1.50  fof(f48,plain,(
% 6.88/1.50    ( ! [X2,X0,X1] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 6.88/1.50    inference(cnf_transformation,[],[f20])).
% 6.88/1.50  
% 6.88/1.50  fof(f12,axiom,(
% 6.88/1.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 6.88/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.88/1.50  
% 6.88/1.50  fof(f33,plain,(
% 6.88/1.50    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 6.88/1.50    inference(ennf_transformation,[],[f12])).
% 6.88/1.50  
% 6.88/1.50  fof(f34,plain,(
% 6.88/1.50    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 6.88/1.50    inference(flattening,[],[f33])).
% 6.88/1.50  
% 6.88/1.50  fof(f60,plain,(
% 6.88/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 6.88/1.50    inference(cnf_transformation,[],[f34])).
% 6.88/1.50  
% 6.88/1.50  fof(f10,axiom,(
% 6.88/1.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 6.88/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.88/1.50  
% 6.88/1.50  fof(f29,plain,(
% 6.88/1.50    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 6.88/1.50    inference(ennf_transformation,[],[f10])).
% 6.88/1.50  
% 6.88/1.50  fof(f30,plain,(
% 6.88/1.50    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.88/1.50    inference(flattening,[],[f29])).
% 6.88/1.50  
% 6.88/1.50  fof(f40,plain,(
% 6.88/1.50    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.88/1.50    inference(nnf_transformation,[],[f30])).
% 6.88/1.50  
% 6.88/1.50  fof(f56,plain,(
% 6.88/1.50    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.88/1.50    inference(cnf_transformation,[],[f40])).
% 6.88/1.50  
% 6.88/1.50  fof(f69,plain,(
% 6.88/1.50    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1)),
% 6.88/1.50    inference(cnf_transformation,[],[f43])).
% 6.88/1.50  
% 6.88/1.50  fof(f66,plain,(
% 6.88/1.50    v1_funct_1(sK2)),
% 6.88/1.50    inference(cnf_transformation,[],[f43])).
% 6.88/1.50  
% 6.88/1.50  fof(f11,axiom,(
% 6.88/1.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 6.88/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.88/1.50  
% 6.88/1.50  fof(f31,plain,(
% 6.88/1.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 6.88/1.50    inference(ennf_transformation,[],[f11])).
% 6.88/1.50  
% 6.88/1.50  fof(f32,plain,(
% 6.88/1.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 6.88/1.50    inference(flattening,[],[f31])).
% 6.88/1.50  
% 6.88/1.50  fof(f59,plain,(
% 6.88/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 6.88/1.50    inference(cnf_transformation,[],[f32])).
% 6.88/1.50  
% 6.88/1.50  fof(f9,axiom,(
% 6.88/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 6.88/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.88/1.50  
% 6.88/1.50  fof(f28,plain,(
% 6.88/1.50    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.88/1.50    inference(ennf_transformation,[],[f9])).
% 6.88/1.50  
% 6.88/1.50  fof(f55,plain,(
% 6.88/1.50    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.88/1.50    inference(cnf_transformation,[],[f28])).
% 6.88/1.50  
% 6.88/1.50  fof(f14,axiom,(
% 6.88/1.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 6.88/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.88/1.50  
% 6.88/1.50  fof(f35,plain,(
% 6.88/1.50    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 6.88/1.50    inference(ennf_transformation,[],[f14])).
% 6.88/1.50  
% 6.88/1.50  fof(f36,plain,(
% 6.88/1.50    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 6.88/1.50    inference(flattening,[],[f35])).
% 6.88/1.50  
% 6.88/1.50  fof(f62,plain,(
% 6.88/1.50    ( ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 6.88/1.50    inference(cnf_transformation,[],[f36])).
% 6.88/1.50  
% 6.88/1.50  fof(f64,plain,(
% 6.88/1.50    v1_funct_2(sK1,sK0,sK0)),
% 6.88/1.50    inference(cnf_transformation,[],[f43])).
% 6.88/1.50  
% 6.88/1.50  fof(f7,axiom,(
% 6.88/1.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 6.88/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.88/1.50  
% 6.88/1.50  fof(f25,plain,(
% 6.88/1.50    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 6.88/1.50    inference(ennf_transformation,[],[f7])).
% 6.88/1.50  
% 6.88/1.50  fof(f26,plain,(
% 6.88/1.50    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 6.88/1.50    inference(flattening,[],[f25])).
% 6.88/1.50  
% 6.88/1.50  fof(f52,plain,(
% 6.88/1.50    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.88/1.50    inference(cnf_transformation,[],[f26])).
% 6.88/1.50  
% 6.88/1.50  fof(f13,axiom,(
% 6.88/1.50    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 6.88/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.88/1.50  
% 6.88/1.50  fof(f61,plain,(
% 6.88/1.50    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 6.88/1.50    inference(cnf_transformation,[],[f13])).
% 6.88/1.50  
% 6.88/1.50  fof(f74,plain,(
% 6.88/1.50    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.88/1.50    inference(definition_unfolding,[],[f52,f61])).
% 6.88/1.50  
% 6.88/1.50  fof(f70,plain,(
% 6.88/1.50    v2_funct_1(sK1)),
% 6.88/1.50    inference(cnf_transformation,[],[f43])).
% 6.88/1.50  
% 6.88/1.50  fof(f8,axiom,(
% 6.88/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 6.88/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.88/1.50  
% 6.88/1.50  fof(f17,plain,(
% 6.88/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 6.88/1.50    inference(pure_predicate_removal,[],[f8])).
% 6.88/1.50  
% 6.88/1.50  fof(f27,plain,(
% 6.88/1.50    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.88/1.50    inference(ennf_transformation,[],[f17])).
% 6.88/1.50  
% 6.88/1.50  fof(f54,plain,(
% 6.88/1.50    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.88/1.50    inference(cnf_transformation,[],[f27])).
% 6.88/1.50  
% 6.88/1.50  fof(f2,axiom,(
% 6.88/1.50    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 6.88/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.88/1.50  
% 6.88/1.50  fof(f19,plain,(
% 6.88/1.50    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 6.88/1.51    inference(ennf_transformation,[],[f2])).
% 6.88/1.51  
% 6.88/1.51  fof(f39,plain,(
% 6.88/1.51    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 6.88/1.51    inference(nnf_transformation,[],[f19])).
% 6.88/1.51  
% 6.88/1.51  fof(f45,plain,(
% 6.88/1.51    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 6.88/1.51    inference(cnf_transformation,[],[f39])).
% 6.88/1.51  
% 6.88/1.51  fof(f5,axiom,(
% 6.88/1.51    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 6.88/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.88/1.51  
% 6.88/1.51  fof(f21,plain,(
% 6.88/1.51    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 6.88/1.51    inference(ennf_transformation,[],[f5])).
% 6.88/1.51  
% 6.88/1.51  fof(f22,plain,(
% 6.88/1.51    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 6.88/1.51    inference(flattening,[],[f21])).
% 6.88/1.51  
% 6.88/1.51  fof(f49,plain,(
% 6.88/1.51    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 6.88/1.51    inference(cnf_transformation,[],[f22])).
% 6.88/1.51  
% 6.88/1.51  fof(f72,plain,(
% 6.88/1.51    ( ! [X0,X1] : (k5_relat_1(X1,k6_partfun1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 6.88/1.51    inference(definition_unfolding,[],[f49,f61])).
% 6.88/1.51  
% 6.88/1.51  fof(f57,plain,(
% 6.88/1.51    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.88/1.51    inference(cnf_transformation,[],[f40])).
% 6.88/1.51  
% 6.88/1.51  fof(f75,plain,(
% 6.88/1.51    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.88/1.51    inference(equality_resolution,[],[f57])).
% 6.88/1.51  
% 6.88/1.51  fof(f71,plain,(
% 6.88/1.51    ~r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0))),
% 6.88/1.51    inference(cnf_transformation,[],[f43])).
% 6.88/1.51  
% 6.88/1.51  cnf(c_26,negated_conjecture,
% 6.88/1.51      ( v1_funct_1(sK1) ),
% 6.88/1.51      inference(cnf_transformation,[],[f63]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_566,negated_conjecture,
% 6.88/1.51      ( v1_funct_1(sK1) ),
% 6.88/1.51      inference(subtyping,[status(esa)],[c_26]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_942,plain,
% 6.88/1.51      ( v1_funct_1(sK1) = iProver_top ),
% 6.88/1.51      inference(predicate_to_equality,[status(thm)],[c_566]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_7,plain,
% 6.88/1.51      ( ~ v1_funct_1(X0)
% 6.88/1.51      | ~ v1_relat_1(X0)
% 6.88/1.51      | v1_relat_1(k2_funct_1(X0)) ),
% 6.88/1.51      inference(cnf_transformation,[],[f50]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_574,plain,
% 6.88/1.51      ( ~ v1_funct_1(X0_48)
% 6.88/1.51      | ~ v1_relat_1(X0_48)
% 6.88/1.51      | v1_relat_1(k2_funct_1(X0_48)) ),
% 6.88/1.51      inference(subtyping,[status(esa)],[c_7]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_934,plain,
% 6.88/1.51      ( v1_funct_1(X0_48) != iProver_top
% 6.88/1.51      | v1_relat_1(X0_48) != iProver_top
% 6.88/1.51      | v1_relat_1(k2_funct_1(X0_48)) = iProver_top ),
% 6.88/1.51      inference(predicate_to_equality,[status(thm)],[c_574]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_24,negated_conjecture,
% 6.88/1.51      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 6.88/1.51      inference(cnf_transformation,[],[f65]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_567,negated_conjecture,
% 6.88/1.51      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 6.88/1.51      inference(subtyping,[status(esa)],[c_24]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_941,plain,
% 6.88/1.51      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 6.88/1.51      inference(predicate_to_equality,[status(thm)],[c_567]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_0,plain,
% 6.88/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 6.88/1.51      | ~ v1_relat_1(X1)
% 6.88/1.51      | v1_relat_1(X0) ),
% 6.88/1.51      inference(cnf_transformation,[],[f44]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_578,plain,
% 6.88/1.51      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(X1_48))
% 6.88/1.51      | ~ v1_relat_1(X1_48)
% 6.88/1.51      | v1_relat_1(X0_48) ),
% 6.88/1.51      inference(subtyping,[status(esa)],[c_0]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_930,plain,
% 6.88/1.51      ( m1_subset_1(X0_48,k1_zfmisc_1(X1_48)) != iProver_top
% 6.88/1.51      | v1_relat_1(X1_48) != iProver_top
% 6.88/1.51      | v1_relat_1(X0_48) = iProver_top ),
% 6.88/1.51      inference(predicate_to_equality,[status(thm)],[c_578]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_1442,plain,
% 6.88/1.51      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
% 6.88/1.51      | v1_relat_1(sK1) = iProver_top ),
% 6.88/1.51      inference(superposition,[status(thm)],[c_941,c_930]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_29,plain,
% 6.88/1.51      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 6.88/1.51      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_3,plain,
% 6.88/1.51      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 6.88/1.51      inference(cnf_transformation,[],[f47]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_78,plain,
% 6.88/1.51      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 6.88/1.51      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_80,plain,
% 6.88/1.51      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) = iProver_top ),
% 6.88/1.51      inference(instantiation,[status(thm)],[c_78]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_1101,plain,
% 6.88/1.51      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 6.88/1.51      | v1_relat_1(X0_48)
% 6.88/1.51      | ~ v1_relat_1(k2_zfmisc_1(X0_49,X1_49)) ),
% 6.88/1.51      inference(instantiation,[status(thm)],[c_578]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_1102,plain,
% 6.88/1.51      ( m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 6.88/1.51      | v1_relat_1(X0_48) = iProver_top
% 6.88/1.51      | v1_relat_1(k2_zfmisc_1(X0_49,X1_49)) != iProver_top ),
% 6.88/1.51      inference(predicate_to_equality,[status(thm)],[c_1101]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_1104,plain,
% 6.88/1.51      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 6.88/1.51      | v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
% 6.88/1.51      | v1_relat_1(sK1) = iProver_top ),
% 6.88/1.51      inference(instantiation,[status(thm)],[c_1102]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_1748,plain,
% 6.88/1.51      ( v1_relat_1(sK1) = iProver_top ),
% 6.88/1.51      inference(global_propositional_subsumption,
% 6.88/1.51                [status(thm)],
% 6.88/1.51                [c_1442,c_29,c_80,c_1104]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_21,negated_conjecture,
% 6.88/1.51      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 6.88/1.51      inference(cnf_transformation,[],[f68]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_569,negated_conjecture,
% 6.88/1.51      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 6.88/1.51      inference(subtyping,[status(esa)],[c_21]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_939,plain,
% 6.88/1.51      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 6.88/1.51      inference(predicate_to_equality,[status(thm)],[c_569]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_1441,plain,
% 6.88/1.51      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
% 6.88/1.51      | v1_relat_1(sK2) = iProver_top ),
% 6.88/1.51      inference(superposition,[status(thm)],[c_939,c_930]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_32,plain,
% 6.88/1.51      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 6.88/1.51      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_1393,plain,
% 6.88/1.51      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 6.88/1.51      | ~ v1_relat_1(k2_zfmisc_1(X0_49,X1_49))
% 6.88/1.51      | v1_relat_1(sK2) ),
% 6.88/1.51      inference(instantiation,[status(thm)],[c_1101]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_1394,plain,
% 6.88/1.51      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 6.88/1.51      | v1_relat_1(k2_zfmisc_1(X0_49,X1_49)) != iProver_top
% 6.88/1.51      | v1_relat_1(sK2) = iProver_top ),
% 6.88/1.51      inference(predicate_to_equality,[status(thm)],[c_1393]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_1396,plain,
% 6.88/1.51      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 6.88/1.51      | v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
% 6.88/1.51      | v1_relat_1(sK2) = iProver_top ),
% 6.88/1.51      inference(instantiation,[status(thm)],[c_1394]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_1522,plain,
% 6.88/1.51      ( v1_relat_1(sK2) = iProver_top ),
% 6.88/1.51      inference(global_propositional_subsumption,
% 6.88/1.51                [status(thm)],
% 6.88/1.51                [c_1441,c_32,c_80,c_1396]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_4,plain,
% 6.88/1.51      ( ~ v1_relat_1(X0)
% 6.88/1.51      | ~ v1_relat_1(X1)
% 6.88/1.51      | ~ v1_relat_1(X2)
% 6.88/1.51      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ),
% 6.88/1.51      inference(cnf_transformation,[],[f48]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_576,plain,
% 6.88/1.51      ( ~ v1_relat_1(X0_48)
% 6.88/1.51      | ~ v1_relat_1(X1_48)
% 6.88/1.51      | ~ v1_relat_1(X2_48)
% 6.88/1.51      | k5_relat_1(k5_relat_1(X0_48,X1_48),X2_48) = k5_relat_1(X0_48,k5_relat_1(X1_48,X2_48)) ),
% 6.88/1.51      inference(subtyping,[status(esa)],[c_4]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_932,plain,
% 6.88/1.51      ( k5_relat_1(k5_relat_1(X0_48,X1_48),X2_48) = k5_relat_1(X0_48,k5_relat_1(X1_48,X2_48))
% 6.88/1.51      | v1_relat_1(X0_48) != iProver_top
% 6.88/1.51      | v1_relat_1(X1_48) != iProver_top
% 6.88/1.51      | v1_relat_1(X2_48) != iProver_top ),
% 6.88/1.51      inference(predicate_to_equality,[status(thm)],[c_576]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_1618,plain,
% 6.88/1.51      ( k5_relat_1(sK2,k5_relat_1(X0_48,X1_48)) = k5_relat_1(k5_relat_1(sK2,X0_48),X1_48)
% 6.88/1.51      | v1_relat_1(X0_48) != iProver_top
% 6.88/1.51      | v1_relat_1(X1_48) != iProver_top ),
% 6.88/1.51      inference(superposition,[status(thm)],[c_1522,c_932]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_2404,plain,
% 6.88/1.51      ( k5_relat_1(k5_relat_1(sK2,sK1),X0_48) = k5_relat_1(sK2,k5_relat_1(sK1,X0_48))
% 6.88/1.51      | v1_relat_1(X0_48) != iProver_top ),
% 6.88/1.51      inference(superposition,[status(thm)],[c_1748,c_1618]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_16,plain,
% 6.88/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.88/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 6.88/1.51      | ~ v1_funct_1(X0)
% 6.88/1.51      | ~ v1_funct_1(X3)
% 6.88/1.51      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 6.88/1.51      inference(cnf_transformation,[],[f60]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_570,plain,
% 6.88/1.51      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 6.88/1.51      | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49)))
% 6.88/1.51      | ~ v1_funct_1(X0_48)
% 6.88/1.51      | ~ v1_funct_1(X1_48)
% 6.88/1.51      | k1_partfun1(X2_49,X3_49,X0_49,X1_49,X1_48,X0_48) = k5_relat_1(X1_48,X0_48) ),
% 6.88/1.51      inference(subtyping,[status(esa)],[c_16]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_938,plain,
% 6.88/1.51      ( k1_partfun1(X0_49,X1_49,X2_49,X3_49,X0_48,X1_48) = k5_relat_1(X0_48,X1_48)
% 6.88/1.51      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 6.88/1.51      | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49))) != iProver_top
% 6.88/1.51      | v1_funct_1(X0_48) != iProver_top
% 6.88/1.51      | v1_funct_1(X1_48) != iProver_top ),
% 6.88/1.51      inference(predicate_to_equality,[status(thm)],[c_570]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_1706,plain,
% 6.88/1.51      ( k1_partfun1(X0_49,X1_49,sK0,sK0,X0_48,sK1) = k5_relat_1(X0_48,sK1)
% 6.88/1.51      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 6.88/1.51      | v1_funct_1(X0_48) != iProver_top
% 6.88/1.51      | v1_funct_1(sK1) != iProver_top ),
% 6.88/1.51      inference(superposition,[status(thm)],[c_941,c_938]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_27,plain,
% 6.88/1.51      ( v1_funct_1(sK1) = iProver_top ),
% 6.88/1.51      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_1977,plain,
% 6.88/1.51      ( v1_funct_1(X0_48) != iProver_top
% 6.88/1.51      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 6.88/1.51      | k1_partfun1(X0_49,X1_49,sK0,sK0,X0_48,sK1) = k5_relat_1(X0_48,sK1) ),
% 6.88/1.51      inference(global_propositional_subsumption,
% 6.88/1.51                [status(thm)],
% 6.88/1.51                [c_1706,c_27]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_1978,plain,
% 6.88/1.51      ( k1_partfun1(X0_49,X1_49,sK0,sK0,X0_48,sK1) = k5_relat_1(X0_48,sK1)
% 6.88/1.51      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 6.88/1.51      | v1_funct_1(X0_48) != iProver_top ),
% 6.88/1.51      inference(renaming,[status(thm)],[c_1977]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_1984,plain,
% 6.88/1.51      ( k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) = k5_relat_1(sK2,sK1)
% 6.88/1.51      | v1_funct_1(sK2) != iProver_top ),
% 6.88/1.51      inference(superposition,[status(thm)],[c_939,c_1978]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_13,plain,
% 6.88/1.51      ( ~ r2_relset_1(X0,X1,X2,X3)
% 6.88/1.51      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 6.88/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 6.88/1.51      | X3 = X2 ),
% 6.88/1.51      inference(cnf_transformation,[],[f56]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_20,negated_conjecture,
% 6.88/1.51      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1) ),
% 6.88/1.51      inference(cnf_transformation,[],[f69]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_396,plain,
% 6.88/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.88/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.88/1.51      | X3 = X0
% 6.88/1.51      | k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) != X0
% 6.88/1.51      | sK1 != X3
% 6.88/1.51      | sK0 != X2
% 6.88/1.51      | sK0 != X1 ),
% 6.88/1.51      inference(resolution_lifted,[status(thm)],[c_13,c_20]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_397,plain,
% 6.88/1.51      ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 6.88/1.51      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 6.88/1.51      | sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) ),
% 6.88/1.51      inference(unflattening,[status(thm)],[c_396]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_399,plain,
% 6.88/1.51      ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 6.88/1.51      | sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) ),
% 6.88/1.51      inference(global_propositional_subsumption,
% 6.88/1.51                [status(thm)],
% 6.88/1.51                [c_397,c_24]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_559,plain,
% 6.88/1.51      ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 6.88/1.51      | sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) ),
% 6.88/1.51      inference(subtyping,[status(esa)],[c_399]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_947,plain,
% 6.88/1.51      ( sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1)
% 6.88/1.51      | m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 6.88/1.51      inference(predicate_to_equality,[status(thm)],[c_559]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_23,negated_conjecture,
% 6.88/1.51      ( v1_funct_1(sK2) ),
% 6.88/1.51      inference(cnf_transformation,[],[f66]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_14,plain,
% 6.88/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.88/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 6.88/1.51      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 6.88/1.51      | ~ v1_funct_1(X0)
% 6.88/1.51      | ~ v1_funct_1(X3) ),
% 6.88/1.51      inference(cnf_transformation,[],[f59]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_572,plain,
% 6.88/1.51      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 6.88/1.51      | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49)))
% 6.88/1.51      | m1_subset_1(k1_partfun1(X2_49,X3_49,X0_49,X1_49,X1_48,X0_48),k1_zfmisc_1(k2_zfmisc_1(X2_49,X1_49)))
% 6.88/1.51      | ~ v1_funct_1(X0_48)
% 6.88/1.51      | ~ v1_funct_1(X1_48) ),
% 6.88/1.51      inference(subtyping,[status(esa)],[c_14]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_1123,plain,
% 6.88/1.51      ( m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 6.88/1.51      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 6.88/1.51      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 6.88/1.51      | ~ v1_funct_1(sK1)
% 6.88/1.51      | ~ v1_funct_1(sK2) ),
% 6.88/1.51      inference(instantiation,[status(thm)],[c_572]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_1365,plain,
% 6.88/1.51      ( sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) ),
% 6.88/1.51      inference(global_propositional_subsumption,
% 6.88/1.51                [status(thm)],
% 6.88/1.51                [c_947,c_26,c_24,c_23,c_21,c_559,c_1123]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_2005,plain,
% 6.88/1.51      ( k5_relat_1(sK2,sK1) = sK1 | v1_funct_1(sK2) != iProver_top ),
% 6.88/1.51      inference(light_normalisation,[status(thm)],[c_1984,c_1365]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_30,plain,
% 6.88/1.51      ( v1_funct_1(sK2) = iProver_top ),
% 6.88/1.51      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_2099,plain,
% 6.88/1.51      ( k5_relat_1(sK2,sK1) = sK1 ),
% 6.88/1.51      inference(global_propositional_subsumption,
% 6.88/1.51                [status(thm)],
% 6.88/1.51                [c_2005,c_30]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_2426,plain,
% 6.88/1.51      ( k5_relat_1(sK2,k5_relat_1(sK1,X0_48)) = k5_relat_1(sK1,X0_48)
% 6.88/1.51      | v1_relat_1(X0_48) != iProver_top ),
% 6.88/1.51      inference(light_normalisation,[status(thm)],[c_2404,c_2099]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_16057,plain,
% 6.88/1.51      ( k5_relat_1(sK2,k5_relat_1(sK1,k2_funct_1(X0_48))) = k5_relat_1(sK1,k2_funct_1(X0_48))
% 6.88/1.51      | v1_funct_1(X0_48) != iProver_top
% 6.88/1.51      | v1_relat_1(X0_48) != iProver_top ),
% 6.88/1.51      inference(superposition,[status(thm)],[c_934,c_2426]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_16383,plain,
% 6.88/1.51      ( k5_relat_1(sK2,k5_relat_1(sK1,k2_funct_1(sK1))) = k5_relat_1(sK1,k2_funct_1(sK1))
% 6.88/1.51      | v1_relat_1(sK1) != iProver_top ),
% 6.88/1.51      inference(superposition,[status(thm)],[c_942,c_16057]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_11,plain,
% 6.88/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.88/1.51      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 6.88/1.51      inference(cnf_transformation,[],[f55]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_573,plain,
% 6.88/1.51      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 6.88/1.51      | k1_relset_1(X0_49,X1_49,X0_48) = k1_relat_1(X0_48) ),
% 6.88/1.51      inference(subtyping,[status(esa)],[c_11]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_935,plain,
% 6.88/1.51      ( k1_relset_1(X0_49,X1_49,X0_48) = k1_relat_1(X0_48)
% 6.88/1.51      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top ),
% 6.88/1.51      inference(predicate_to_equality,[status(thm)],[c_573]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_1262,plain,
% 6.88/1.51      ( k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) ),
% 6.88/1.51      inference(superposition,[status(thm)],[c_941,c_935]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_17,plain,
% 6.88/1.51      ( ~ v1_funct_2(X0,X1,X1)
% 6.88/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 6.88/1.51      | ~ v1_funct_1(X0)
% 6.88/1.51      | k1_relset_1(X1,X1,X0) = X1 ),
% 6.88/1.51      inference(cnf_transformation,[],[f62]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_25,negated_conjecture,
% 6.88/1.51      ( v1_funct_2(sK1,sK0,sK0) ),
% 6.88/1.51      inference(cnf_transformation,[],[f64]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_337,plain,
% 6.88/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 6.88/1.51      | ~ v1_funct_1(X0)
% 6.88/1.51      | k1_relset_1(X1,X1,X0) = X1
% 6.88/1.51      | sK1 != X0
% 6.88/1.51      | sK0 != X1 ),
% 6.88/1.51      inference(resolution_lifted,[status(thm)],[c_17,c_25]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_338,plain,
% 6.88/1.51      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 6.88/1.51      | ~ v1_funct_1(sK1)
% 6.88/1.51      | k1_relset_1(sK0,sK0,sK1) = sK0 ),
% 6.88/1.51      inference(unflattening,[status(thm)],[c_337]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_340,plain,
% 6.88/1.51      ( k1_relset_1(sK0,sK0,sK1) = sK0 ),
% 6.88/1.51      inference(global_propositional_subsumption,
% 6.88/1.51                [status(thm)],
% 6.88/1.51                [c_338,c_26,c_24]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_562,plain,
% 6.88/1.51      ( k1_relset_1(sK0,sK0,sK1) = sK0 ),
% 6.88/1.51      inference(subtyping,[status(esa)],[c_340]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_1264,plain,
% 6.88/1.51      ( k1_relat_1(sK1) = sK0 ),
% 6.88/1.51      inference(light_normalisation,[status(thm)],[c_1262,c_562]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_9,plain,
% 6.88/1.51      ( ~ v2_funct_1(X0)
% 6.88/1.51      | ~ v1_funct_1(X0)
% 6.88/1.51      | ~ v1_relat_1(X0)
% 6.88/1.51      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
% 6.88/1.51      inference(cnf_transformation,[],[f74]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_19,negated_conjecture,
% 6.88/1.51      ( v2_funct_1(sK1) ),
% 6.88/1.51      inference(cnf_transformation,[],[f70]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_295,plain,
% 6.88/1.51      ( ~ v1_funct_1(X0)
% 6.88/1.51      | ~ v1_relat_1(X0)
% 6.88/1.51      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
% 6.88/1.51      | sK1 != X0 ),
% 6.88/1.51      inference(resolution_lifted,[status(thm)],[c_9,c_19]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_296,plain,
% 6.88/1.51      ( ~ v1_funct_1(sK1)
% 6.88/1.51      | ~ v1_relat_1(sK1)
% 6.88/1.51      | k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
% 6.88/1.51      inference(unflattening,[status(thm)],[c_295]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_298,plain,
% 6.88/1.51      ( ~ v1_relat_1(sK1)
% 6.88/1.51      | k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
% 6.88/1.51      inference(global_propositional_subsumption,
% 6.88/1.51                [status(thm)],
% 6.88/1.51                [c_296,c_26]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_565,plain,
% 6.88/1.51      ( ~ v1_relat_1(sK1)
% 6.88/1.51      | k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
% 6.88/1.51      inference(subtyping,[status(esa)],[c_298]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_943,plain,
% 6.88/1.51      ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
% 6.88/1.51      | v1_relat_1(sK1) != iProver_top ),
% 6.88/1.51      inference(predicate_to_equality,[status(thm)],[c_565]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_79,plain,
% 6.88/1.51      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
% 6.88/1.51      inference(instantiation,[status(thm)],[c_3]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_1103,plain,
% 6.88/1.51      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 6.88/1.51      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
% 6.88/1.51      | v1_relat_1(sK1) ),
% 6.88/1.51      inference(instantiation,[status(thm)],[c_1101]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_1157,plain,
% 6.88/1.51      ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
% 6.88/1.51      inference(global_propositional_subsumption,
% 6.88/1.51                [status(thm)],
% 6.88/1.51                [c_943,c_24,c_79,c_565,c_1103]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_1270,plain,
% 6.88/1.51      ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(sK0) ),
% 6.88/1.51      inference(demodulation,[status(thm)],[c_1264,c_1157]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_10,plain,
% 6.88/1.51      ( v5_relat_1(X0,X1)
% 6.88/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 6.88/1.51      inference(cnf_transformation,[],[f54]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_2,plain,
% 6.88/1.51      ( r1_tarski(k2_relat_1(X0),X1)
% 6.88/1.51      | ~ v5_relat_1(X0,X1)
% 6.88/1.51      | ~ v1_relat_1(X0) ),
% 6.88/1.51      inference(cnf_transformation,[],[f45]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_347,plain,
% 6.88/1.51      ( r1_tarski(k2_relat_1(X0),X1)
% 6.88/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 6.88/1.51      | ~ v1_relat_1(X0) ),
% 6.88/1.51      inference(resolution,[status(thm)],[c_10,c_2]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_5,plain,
% 6.88/1.51      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 6.88/1.51      | ~ v1_relat_1(X0)
% 6.88/1.51      | k5_relat_1(X0,k6_partfun1(X1)) = X0 ),
% 6.88/1.51      inference(cnf_transformation,[],[f72]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_366,plain,
% 6.88/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.88/1.51      | ~ v1_relat_1(X0)
% 6.88/1.51      | k5_relat_1(X0,k6_partfun1(X2)) = X0 ),
% 6.88/1.51      inference(resolution,[status(thm)],[c_347,c_5]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_561,plain,
% 6.88/1.51      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 6.88/1.51      | ~ v1_relat_1(X0_48)
% 6.88/1.51      | k5_relat_1(X0_48,k6_partfun1(X1_49)) = X0_48 ),
% 6.88/1.51      inference(subtyping,[status(esa)],[c_366]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_945,plain,
% 6.88/1.51      ( k5_relat_1(X0_48,k6_partfun1(X0_49)) = X0_48
% 6.88/1.51      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_49,X0_49))) != iProver_top
% 6.88/1.51      | v1_relat_1(X0_48) != iProver_top ),
% 6.88/1.51      inference(predicate_to_equality,[status(thm)],[c_561]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_2300,plain,
% 6.88/1.51      ( k5_relat_1(sK2,k6_partfun1(sK0)) = sK2
% 6.88/1.51      | v1_relat_1(sK2) != iProver_top ),
% 6.88/1.51      inference(superposition,[status(thm)],[c_939,c_945]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_1194,plain,
% 6.88/1.51      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 6.88/1.51      | ~ v1_relat_1(sK2)
% 6.88/1.51      | k5_relat_1(sK2,k6_partfun1(X1_49)) = sK2 ),
% 6.88/1.51      inference(instantiation,[status(thm)],[c_561]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_1197,plain,
% 6.88/1.51      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 6.88/1.51      | ~ v1_relat_1(sK2)
% 6.88/1.51      | k5_relat_1(sK2,k6_partfun1(sK0)) = sK2 ),
% 6.88/1.51      inference(instantiation,[status(thm)],[c_1194]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_1395,plain,
% 6.88/1.51      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 6.88/1.51      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
% 6.88/1.51      | v1_relat_1(sK2) ),
% 6.88/1.51      inference(instantiation,[status(thm)],[c_1393]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_2329,plain,
% 6.88/1.51      ( k5_relat_1(sK2,k6_partfun1(sK0)) = sK2 ),
% 6.88/1.51      inference(global_propositional_subsumption,
% 6.88/1.51                [status(thm)],
% 6.88/1.51                [c_2300,c_21,c_79,c_1197,c_1395]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_16423,plain,
% 6.88/1.51      ( k6_partfun1(sK0) = sK2 | v1_relat_1(sK1) != iProver_top ),
% 6.88/1.51      inference(light_normalisation,
% 6.88/1.51                [status(thm)],
% 6.88/1.51                [c_16383,c_1270,c_2329]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_16837,plain,
% 6.88/1.51      ( k6_partfun1(sK0) = sK2 ),
% 6.88/1.51      inference(global_propositional_subsumption,
% 6.88/1.51                [status(thm)],
% 6.88/1.51                [c_16423,c_29,c_80,c_1104]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_12,plain,
% 6.88/1.51      ( r2_relset_1(X0,X1,X2,X2)
% 6.88/1.51      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 6.88/1.51      inference(cnf_transformation,[],[f75]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_18,negated_conjecture,
% 6.88/1.51      ( ~ r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0)) ),
% 6.88/1.51      inference(cnf_transformation,[],[f71]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_386,plain,
% 6.88/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.88/1.51      | k6_partfun1(sK0) != X0
% 6.88/1.51      | sK2 != X0
% 6.88/1.51      | sK0 != X2
% 6.88/1.51      | sK0 != X1 ),
% 6.88/1.51      inference(resolution_lifted,[status(thm)],[c_12,c_18]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_387,plain,
% 6.88/1.51      ( ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 6.88/1.51      | sK2 != k6_partfun1(sK0) ),
% 6.88/1.51      inference(unflattening,[status(thm)],[c_386]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_560,plain,
% 6.88/1.51      ( ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 6.88/1.51      | sK2 != k6_partfun1(sK0) ),
% 6.88/1.51      inference(subtyping,[status(esa)],[c_387]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_946,plain,
% 6.88/1.51      ( sK2 != k6_partfun1(sK0)
% 6.88/1.51      | m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 6.88/1.51      inference(predicate_to_equality,[status(thm)],[c_560]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_16851,plain,
% 6.88/1.51      ( sK2 != sK2
% 6.88/1.51      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 6.88/1.51      inference(demodulation,[status(thm)],[c_16837,c_946]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(c_16852,plain,
% 6.88/1.51      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 6.88/1.51      inference(equality_resolution_simp,[status(thm)],[c_16851]) ).
% 6.88/1.51  
% 6.88/1.51  cnf(contradiction,plain,
% 6.88/1.51      ( $false ),
% 6.88/1.51      inference(minisat,[status(thm)],[c_16852,c_32]) ).
% 6.88/1.51  
% 6.88/1.51  
% 6.88/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 6.88/1.51  
% 6.88/1.51  ------                               Statistics
% 6.88/1.51  
% 6.88/1.51  ------ General
% 6.88/1.51  
% 6.88/1.51  abstr_ref_over_cycles:                  0
% 6.88/1.51  abstr_ref_under_cycles:                 0
% 6.88/1.51  gc_basic_clause_elim:                   0
% 6.88/1.51  forced_gc_time:                         0
% 6.88/1.51  parsing_time:                           0.011
% 6.88/1.51  unif_index_cands_time:                  0.
% 6.88/1.51  unif_index_add_time:                    0.
% 6.88/1.51  orderings_time:                         0.
% 6.88/1.51  out_proof_time:                         0.012
% 6.88/1.51  total_time:                             0.533
% 6.88/1.51  num_of_symbols:                         54
% 6.88/1.51  num_of_terms:                           11728
% 6.88/1.51  
% 6.88/1.51  ------ Preprocessing
% 6.88/1.51  
% 6.88/1.51  num_of_splits:                          0
% 6.88/1.51  num_of_split_atoms:                     0
% 6.88/1.51  num_of_reused_defs:                     0
% 6.88/1.51  num_eq_ax_congr_red:                    9
% 6.88/1.51  num_of_sem_filtered_clauses:            1
% 6.88/1.51  num_of_subtypes:                        3
% 6.88/1.51  monotx_restored_types:                  0
% 6.88/1.51  sat_num_of_epr_types:                   0
% 6.88/1.51  sat_num_of_non_cyclic_types:            0
% 6.88/1.51  sat_guarded_non_collapsed_types:        1
% 6.88/1.51  num_pure_diseq_elim:                    0
% 6.88/1.51  simp_replaced_by:                       0
% 6.88/1.51  res_preprocessed:                       125
% 6.88/1.51  prep_upred:                             0
% 6.88/1.51  prep_unflattend:                        17
% 6.88/1.51  smt_new_axioms:                         0
% 6.88/1.51  pred_elim_cands:                        3
% 6.88/1.51  pred_elim:                              5
% 6.88/1.51  pred_elim_cl:                           6
% 6.88/1.51  pred_elim_cycles:                       7
% 6.88/1.51  merged_defs:                            0
% 6.88/1.51  merged_defs_ncl:                        0
% 6.88/1.51  bin_hyper_res:                          0
% 6.88/1.51  prep_cycles:                            4
% 6.88/1.51  pred_elim_time:                         0.003
% 6.88/1.51  splitting_time:                         0.
% 6.88/1.51  sem_filter_time:                        0.
% 6.88/1.51  monotx_time:                            0.
% 6.88/1.51  subtype_inf_time:                       0.
% 6.88/1.51  
% 6.88/1.51  ------ Problem properties
% 6.88/1.51  
% 6.88/1.51  clauses:                                21
% 6.88/1.51  conjectures:                            4
% 6.88/1.51  epr:                                    2
% 6.88/1.51  horn:                                   21
% 6.88/1.51  ground:                                 11
% 6.88/1.51  unary:                                  7
% 6.88/1.51  binary:                                 6
% 6.88/1.51  lits:                                   50
% 6.88/1.51  lits_eq:                                12
% 6.88/1.51  fd_pure:                                0
% 6.88/1.51  fd_pseudo:                              0
% 6.88/1.51  fd_cond:                                0
% 6.88/1.51  fd_pseudo_cond:                         0
% 6.88/1.51  ac_symbols:                             0
% 6.88/1.51  
% 6.88/1.51  ------ Propositional Solver
% 6.88/1.51  
% 6.88/1.51  prop_solver_calls:                      35
% 6.88/1.51  prop_fast_solver_calls:                 1248
% 6.88/1.51  smt_solver_calls:                       0
% 6.88/1.51  smt_fast_solver_calls:                  0
% 6.88/1.51  prop_num_of_clauses:                    5104
% 6.88/1.51  prop_preprocess_simplified:             11132
% 6.88/1.51  prop_fo_subsumed:                       97
% 6.88/1.51  prop_solver_time:                       0.
% 6.88/1.51  smt_solver_time:                        0.
% 6.88/1.51  smt_fast_solver_time:                   0.
% 6.88/1.51  prop_fast_solver_time:                  0.
% 6.88/1.51  prop_unsat_core_time:                   0.001
% 6.88/1.51  
% 6.88/1.51  ------ QBF
% 6.88/1.51  
% 6.88/1.51  qbf_q_res:                              0
% 6.88/1.51  qbf_num_tautologies:                    0
% 6.88/1.51  qbf_prep_cycles:                        0
% 6.88/1.51  
% 6.88/1.51  ------ BMC1
% 6.88/1.51  
% 6.88/1.51  bmc1_current_bound:                     -1
% 6.88/1.51  bmc1_last_solved_bound:                 -1
% 6.88/1.51  bmc1_unsat_core_size:                   -1
% 6.88/1.51  bmc1_unsat_core_parents_size:           -1
% 6.88/1.51  bmc1_merge_next_fun:                    0
% 6.88/1.51  bmc1_unsat_core_clauses_time:           0.
% 6.88/1.51  
% 6.88/1.51  ------ Instantiation
% 6.88/1.51  
% 6.88/1.51  inst_num_of_clauses:                    2211
% 6.88/1.51  inst_num_in_passive:                    371
% 6.88/1.51  inst_num_in_active:                     945
% 6.88/1.51  inst_num_in_unprocessed:                895
% 6.88/1.51  inst_num_of_loops:                      990
% 6.88/1.51  inst_num_of_learning_restarts:          0
% 6.88/1.51  inst_num_moves_active_passive:          35
% 6.88/1.51  inst_lit_activity:                      0
% 6.88/1.51  inst_lit_activity_moves:                0
% 6.88/1.51  inst_num_tautologies:                   0
% 6.88/1.51  inst_num_prop_implied:                  0
% 6.88/1.51  inst_num_existing_simplified:           0
% 6.88/1.51  inst_num_eq_res_simplified:             0
% 6.88/1.51  inst_num_child_elim:                    0
% 6.88/1.51  inst_num_of_dismatching_blockings:      2223
% 6.88/1.51  inst_num_of_non_proper_insts:           3574
% 6.88/1.51  inst_num_of_duplicates:                 0
% 6.88/1.51  inst_inst_num_from_inst_to_res:         0
% 6.88/1.51  inst_dismatching_checking_time:         0.
% 6.88/1.51  
% 6.88/1.51  ------ Resolution
% 6.88/1.51  
% 6.88/1.51  res_num_of_clauses:                     0
% 6.88/1.51  res_num_in_passive:                     0
% 6.88/1.51  res_num_in_active:                      0
% 6.88/1.51  res_num_of_loops:                       129
% 6.88/1.51  res_forward_subset_subsumed:            229
% 6.88/1.51  res_backward_subset_subsumed:           2
% 6.88/1.51  res_forward_subsumed:                   0
% 6.88/1.51  res_backward_subsumed:                  0
% 6.88/1.51  res_forward_subsumption_resolution:     0
% 6.88/1.51  res_backward_subsumption_resolution:    0
% 6.88/1.51  res_clause_to_clause_subsumption:       1346
% 6.88/1.51  res_orphan_elimination:                 0
% 6.88/1.51  res_tautology_del:                      380
% 6.88/1.51  res_num_eq_res_simplified:              1
% 6.88/1.51  res_num_sel_changes:                    0
% 6.88/1.51  res_moves_from_active_to_pass:          0
% 6.88/1.51  
% 6.88/1.51  ------ Superposition
% 6.88/1.51  
% 6.88/1.51  sup_time_total:                         0.
% 6.88/1.51  sup_time_generating:                    0.
% 6.88/1.51  sup_time_sim_full:                      0.
% 6.88/1.51  sup_time_sim_immed:                     0.
% 6.88/1.51  
% 6.88/1.51  sup_num_of_clauses:                     505
% 6.88/1.51  sup_num_in_active:                      181
% 6.88/1.51  sup_num_in_passive:                     324
% 6.88/1.51  sup_num_of_loops:                       197
% 6.88/1.51  sup_fw_superposition:                   382
% 6.88/1.51  sup_bw_superposition:                   133
% 6.88/1.51  sup_immediate_simplified:               79
% 6.88/1.51  sup_given_eliminated:                   0
% 6.88/1.51  comparisons_done:                       0
% 6.88/1.51  comparisons_avoided:                    0
% 6.88/1.51  
% 6.88/1.51  ------ Simplifications
% 6.88/1.51  
% 6.88/1.51  
% 6.88/1.51  sim_fw_subset_subsumed:                 4
% 6.88/1.51  sim_bw_subset_subsumed:                 8
% 6.88/1.51  sim_fw_subsumed:                        0
% 6.88/1.51  sim_bw_subsumed:                        0
% 6.88/1.51  sim_fw_subsumption_res:                 4
% 6.88/1.51  sim_bw_subsumption_res:                 0
% 6.88/1.51  sim_tautology_del:                      1
% 6.88/1.51  sim_eq_tautology_del:                   9
% 6.88/1.51  sim_eq_res_simp:                        1
% 6.88/1.51  sim_fw_demodulated:                     0
% 6.88/1.51  sim_bw_demodulated:                     16
% 6.88/1.51  sim_light_normalised:                   76
% 6.88/1.51  sim_joinable_taut:                      0
% 6.88/1.51  sim_joinable_simp:                      0
% 6.88/1.51  sim_ac_normalised:                      0
% 6.88/1.51  sim_smt_subsumption:                    0
% 6.88/1.51  
%------------------------------------------------------------------------------
