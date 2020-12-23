%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:06:48 EST 2020

% Result     : Theorem 3.25s
% Output     : CNFRefutation 3.25s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 384 expanded)
%              Number of clauses        :   94 ( 130 expanded)
%              Number of leaves         :   18 (  94 expanded)
%              Depth                    :   19
%              Number of atoms          :  476 (2390 expanded)
%              Number of equality atoms :  211 ( 447 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

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
    inference(ennf_transformation,[],[f13])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f33,plain,(
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

fof(f32,plain,
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

fof(f34,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0))
    & k2_relset_1(sK0,sK0,sK1) = sK0
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK2,sK0,sK0)
    & v1_funct_1(sK2)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f33,f32])).

fof(f49,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f52,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f25])).

fof(f44,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f50,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f47,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f23])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f53,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f21])).

fof(f41,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f18,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f17])).

fof(f38,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f54,plain,(
    k2_relset_1(sK0,sK0,sK1) = sK0 ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X0,X1) = X0
              & k2_relat_1(X0) = k1_relat_1(X1) )
           => k6_relat_1(k1_relat_1(X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_relat_1(k1_relat_1(X1)) = X1
          | k5_relat_1(X0,X1) != X0
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_relat_1(k1_relat_1(X1)) = X1
          | k5_relat_1(X0,X1) != X0
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k6_relat_1(k1_relat_1(X1)) = X1
      | k5_relat_1(X0,X1) != X0
      | k2_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f10,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k6_partfun1(k1_relat_1(X1)) = X1
      | k5_relat_1(X0,X1) != X0
      | k2_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f37,f45])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f51,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f43])).

fof(f55,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_398,plain,
    ( ~ m1_subset_1(X0_46,X0_48)
    | m1_subset_1(X1_46,X1_48)
    | X1_48 != X0_48
    | X1_46 != X0_46 ),
    theory(equality)).

cnf(c_898,plain,
    ( m1_subset_1(X0_46,X0_48)
    | ~ m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | X0_48 != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | X0_46 != X1_46 ),
    inference(instantiation,[status(thm)],[c_398])).

cnf(c_1001,plain,
    ( m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
    | ~ m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | X0_46 != X1_46 ),
    inference(instantiation,[status(thm)],[c_898])).

cnf(c_3286,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | k6_partfun1(sK0) != X0_46 ),
    inference(instantiation,[status(thm)],[c_1001])).

cnf(c_4987,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | k6_partfun1(sK0) != sK2 ),
    inference(instantiation,[status(thm)],[c_3286])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_378,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_683,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_378])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_380,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_681,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_380])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_382,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
    | ~ m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(X2_47,X3_47)))
    | ~ v1_funct_1(X0_46)
    | ~ v1_funct_1(X1_46)
    | k1_partfun1(X2_47,X3_47,X0_47,X1_47,X1_46,X0_46) = k5_relat_1(X1_46,X0_46) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_680,plain,
    ( k1_partfun1(X0_47,X1_47,X2_47,X3_47,X0_46,X1_46) = k5_relat_1(X0_46,X1_46)
    | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
    | m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(X2_47,X3_47))) != iProver_top
    | v1_funct_1(X0_46) != iProver_top
    | v1_funct_1(X1_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_382])).

cnf(c_1372,plain,
    ( k1_partfun1(X0_47,X1_47,sK0,sK0,X0_46,sK2) = k5_relat_1(X0_46,sK2)
    | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
    | v1_funct_1(X0_46) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_681,c_680])).

cnf(c_16,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_23,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1678,plain,
    ( v1_funct_1(X0_46) != iProver_top
    | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
    | k1_partfun1(X0_47,X1_47,sK0,sK0,X0_46,sK2) = k5_relat_1(X0_46,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1372,c_23])).

cnf(c_1679,plain,
    ( k1_partfun1(X0_47,X1_47,sK0,sK0,X0_46,sK2) = k5_relat_1(X0_46,sK2)
    | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
    | v1_funct_1(X0_46) != iProver_top ),
    inference(renaming,[status(thm)],[c_1678])).

cnf(c_1688,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2)
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_683,c_1679])).

cnf(c_19,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1052,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_382])).

cnf(c_1810,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1688,c_19,c_17,c_16,c_14,c_1052])).

cnf(c_8,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_13,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),sK1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_238,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) != X0
    | sK1 != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_13])).

cnf(c_239,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) ),
    inference(unflattening,[status(thm)],[c_238])).

cnf(c_241,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_239,c_17])).

cnf(c_373,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) ),
    inference(subtyping,[status(esa)],[c_241])).

cnf(c_686,plain,
    ( sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2)
    | m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_373])).

cnf(c_1813,plain,
    ( k5_relat_1(sK1,sK2) = sK1
    | m1_subset_1(k5_relat_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1810,c_686])).

cnf(c_22,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_25,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | k4_relset_1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_383,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
    | ~ m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(X2_47,X3_47)))
    | k4_relset_1(X2_47,X3_47,X0_47,X1_47,X1_46,X0_46) = k5_relat_1(X1_46,X0_46) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_679,plain,
    ( k4_relset_1(X0_47,X1_47,X2_47,X3_47,X0_46,X1_46) = k5_relat_1(X0_46,X1_46)
    | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
    | m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(X2_47,X3_47))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_383])).

cnf(c_1232,plain,
    ( k4_relset_1(X0_47,X1_47,sK0,sK0,X0_46,sK2) = k5_relat_1(X0_46,sK2)
    | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top ),
    inference(superposition,[status(thm)],[c_681,c_679])).

cnf(c_1485,plain,
    ( k4_relset_1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_683,c_1232])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_386,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
    | ~ m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(X2_47,X3_47)))
    | m1_subset_1(k4_relset_1(X2_47,X3_47,X0_47,X1_47,X1_46,X0_46),k1_zfmisc_1(k2_zfmisc_1(X2_47,X1_47))) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_676,plain,
    ( m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
    | m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(X2_47,X3_47))) != iProver_top
    | m1_subset_1(k4_relset_1(X0_47,X1_47,X2_47,X3_47,X0_46,X1_46),k1_zfmisc_1(k2_zfmisc_1(X0_47,X3_47))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_386])).

cnf(c_1560,plain,
    ( m1_subset_1(k5_relat_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1485,c_676])).

cnf(c_2315,plain,
    ( k5_relat_1(sK1,sK2) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1813,c_22,c_25,c_1560])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_384,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
    | k2_relset_1(X0_47,X1_47,X0_46) = k2_relat_1(X0_46) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_678,plain,
    ( k2_relset_1(X0_47,X1_47,X0_46) = k2_relat_1(X0_46)
    | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_384])).

cnf(c_974,plain,
    ( k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_683,c_678])).

cnf(c_12,negated_conjecture,
    ( k2_relset_1(sK0,sK0,sK1) = sK0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_381,negated_conjecture,
    ( k2_relset_1(sK0,sK0,sK1) = sK0 ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_976,plain,
    ( k2_relat_1(sK1) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_974,c_381])).

cnf(c_2,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X1,X0) != X1
    | k2_relat_1(X1) != k1_relat_1(X0)
    | k6_partfun1(k1_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_387,plain,
    ( ~ v1_funct_1(X0_46)
    | ~ v1_funct_1(X1_46)
    | ~ v1_relat_1(X1_46)
    | ~ v1_relat_1(X0_46)
    | k2_relat_1(X1_46) != k1_relat_1(X0_46)
    | k5_relat_1(X1_46,X0_46) != X1_46
    | k6_partfun1(k1_relat_1(X0_46)) = X0_46 ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_675,plain,
    ( k2_relat_1(X0_46) != k1_relat_1(X1_46)
    | k5_relat_1(X0_46,X1_46) != X0_46
    | k6_partfun1(k1_relat_1(X1_46)) = X1_46
    | v1_funct_1(X0_46) != iProver_top
    | v1_funct_1(X1_46) != iProver_top
    | v1_relat_1(X1_46) != iProver_top
    | v1_relat_1(X0_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_387])).

cnf(c_1254,plain,
    ( k1_relat_1(X0_46) != sK0
    | k5_relat_1(sK1,X0_46) != sK1
    | k6_partfun1(k1_relat_1(X0_46)) = X0_46
    | v1_funct_1(X0_46) != iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v1_relat_1(X0_46) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_976,c_675])).

cnf(c_20,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_55,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_57,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_55])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_389,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(X1_46))
    | ~ v1_relat_1(X1_46)
    | v1_relat_1(X0_46) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_799,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
    | v1_relat_1(X0_46)
    | ~ v1_relat_1(k2_zfmisc_1(X0_47,X1_47)) ),
    inference(instantiation,[status(thm)],[c_389])).

cnf(c_800,plain,
    ( m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
    | v1_relat_1(X0_46) = iProver_top
    | v1_relat_1(k2_zfmisc_1(X0_47,X1_47)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_799])).

cnf(c_802,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
    | v1_relat_1(sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_800])).

cnf(c_1943,plain,
    ( v1_relat_1(X0_46) != iProver_top
    | k1_relat_1(X0_46) != sK0
    | k5_relat_1(sK1,X0_46) != sK1
    | k6_partfun1(k1_relat_1(X0_46)) = X0_46
    | v1_funct_1(X0_46) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1254,c_20,c_22,c_57,c_802])).

cnf(c_1944,plain,
    ( k1_relat_1(X0_46) != sK0
    | k5_relat_1(sK1,X0_46) != sK1
    | k6_partfun1(k1_relat_1(X0_46)) = X0_46
    | v1_funct_1(X0_46) != iProver_top
    | v1_relat_1(X0_46) != iProver_top ),
    inference(renaming,[status(thm)],[c_1943])).

cnf(c_2329,plain,
    ( k1_relat_1(sK2) != sK0
    | k6_partfun1(k1_relat_1(sK2)) = sK2
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2315,c_1944])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_385,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
    | k1_relset_1(X0_47,X1_47,X0_46) = k1_relat_1(X0_46) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_677,plain,
    ( k1_relset_1(X0_47,X1_47,X0_46) = k1_relat_1(X0_46)
    | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_385])).

cnf(c_962,plain,
    ( k1_relset_1(sK0,sK0,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_681,c_677])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(X1,X1,X0) = X1 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_15,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_208,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(X1,X1,X0) = X1
    | sK2 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_15])).

cnf(c_209,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | k1_relset_1(sK0,sK0,sK2) = sK0 ),
    inference(unflattening,[status(thm)],[c_208])).

cnf(c_211,plain,
    ( k1_relset_1(sK0,sK0,sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_209,c_16,c_14])).

cnf(c_376,plain,
    ( k1_relset_1(sK0,sK0,sK2) = sK0 ),
    inference(subtyping,[status(esa)],[c_211])).

cnf(c_968,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_962,c_376])).

cnf(c_2330,plain,
    ( sK0 != sK0
    | k6_partfun1(sK0) = sK2
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2329,c_968])).

cnf(c_2331,plain,
    ( k6_partfun1(sK0) = sK2
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2330])).

cnf(c_673,plain,
    ( m1_subset_1(X0_46,k1_zfmisc_1(X1_46)) != iProver_top
    | v1_relat_1(X1_46) != iProver_top
    | v1_relat_1(X0_46) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_389])).

cnf(c_907,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_681,c_673])).

cnf(c_394,plain,
    ( X0_46 != X1_46
    | X2_46 != X1_46
    | X2_46 = X0_46 ),
    theory(equality)).

cnf(c_810,plain,
    ( k6_partfun1(sK0) != X0_46
    | sK2 != X0_46
    | sK2 = k6_partfun1(sK0) ),
    inference(instantiation,[status(thm)],[c_394])).

cnf(c_886,plain,
    ( k6_partfun1(sK0) != sK2
    | sK2 = k6_partfun1(sK0)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_810])).

cnf(c_393,plain,
    ( X0_48 = X0_48 ),
    theory(equality)).

cnf(c_847,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_393])).

cnf(c_391,plain,
    ( X0_46 = X0_46 ),
    theory(equality)).

cnf(c_839,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_391])).

cnf(c_7,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_11,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_228,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k6_partfun1(sK0) != X0
    | sK2 != X0
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_11])).

cnf(c_229,plain,
    ( ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK2 != k6_partfun1(sK0) ),
    inference(unflattening,[status(thm)],[c_228])).

cnf(c_374,plain,
    ( ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK2 != k6_partfun1(sK0) ),
    inference(subtyping,[status(esa)],[c_229])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4987,c_2331,c_907,c_886,c_847,c_839,c_374,c_57,c_14,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:00:33 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.25/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.25/1.00  
% 3.25/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.25/1.00  
% 3.25/1.00  ------  iProver source info
% 3.25/1.00  
% 3.25/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.25/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.25/1.00  git: non_committed_changes: false
% 3.25/1.00  git: last_make_outside_of_git: false
% 3.25/1.00  
% 3.25/1.00  ------ 
% 3.25/1.00  
% 3.25/1.00  ------ Input Options
% 3.25/1.00  
% 3.25/1.00  --out_options                           all
% 3.25/1.00  --tptp_safe_out                         true
% 3.25/1.00  --problem_path                          ""
% 3.25/1.00  --include_path                          ""
% 3.25/1.00  --clausifier                            res/vclausify_rel
% 3.25/1.00  --clausifier_options                    --mode clausify
% 3.25/1.00  --stdin                                 false
% 3.25/1.00  --stats_out                             all
% 3.25/1.00  
% 3.25/1.00  ------ General Options
% 3.25/1.00  
% 3.25/1.00  --fof                                   false
% 3.25/1.00  --time_out_real                         305.
% 3.25/1.00  --time_out_virtual                      -1.
% 3.25/1.00  --symbol_type_check                     false
% 3.25/1.00  --clausify_out                          false
% 3.25/1.00  --sig_cnt_out                           false
% 3.25/1.00  --trig_cnt_out                          false
% 3.25/1.00  --trig_cnt_out_tolerance                1.
% 3.25/1.00  --trig_cnt_out_sk_spl                   false
% 3.25/1.00  --abstr_cl_out                          false
% 3.25/1.00  
% 3.25/1.00  ------ Global Options
% 3.25/1.00  
% 3.25/1.00  --schedule                              default
% 3.25/1.00  --add_important_lit                     false
% 3.25/1.00  --prop_solver_per_cl                    1000
% 3.25/1.00  --min_unsat_core                        false
% 3.25/1.00  --soft_assumptions                      false
% 3.25/1.00  --soft_lemma_size                       3
% 3.25/1.00  --prop_impl_unit_size                   0
% 3.25/1.00  --prop_impl_unit                        []
% 3.25/1.00  --share_sel_clauses                     true
% 3.25/1.00  --reset_solvers                         false
% 3.25/1.00  --bc_imp_inh                            [conj_cone]
% 3.25/1.00  --conj_cone_tolerance                   3.
% 3.25/1.00  --extra_neg_conj                        none
% 3.25/1.00  --large_theory_mode                     true
% 3.25/1.00  --prolific_symb_bound                   200
% 3.25/1.00  --lt_threshold                          2000
% 3.25/1.00  --clause_weak_htbl                      true
% 3.25/1.00  --gc_record_bc_elim                     false
% 3.25/1.00  
% 3.25/1.00  ------ Preprocessing Options
% 3.25/1.00  
% 3.25/1.00  --preprocessing_flag                    true
% 3.25/1.00  --time_out_prep_mult                    0.1
% 3.25/1.00  --splitting_mode                        input
% 3.25/1.00  --splitting_grd                         true
% 3.25/1.00  --splitting_cvd                         false
% 3.25/1.00  --splitting_cvd_svl                     false
% 3.25/1.00  --splitting_nvd                         32
% 3.25/1.00  --sub_typing                            true
% 3.25/1.00  --prep_gs_sim                           true
% 3.25/1.00  --prep_unflatten                        true
% 3.25/1.00  --prep_res_sim                          true
% 3.25/1.00  --prep_upred                            true
% 3.25/1.00  --prep_sem_filter                       exhaustive
% 3.25/1.00  --prep_sem_filter_out                   false
% 3.25/1.00  --pred_elim                             true
% 3.25/1.00  --res_sim_input                         true
% 3.25/1.00  --eq_ax_congr_red                       true
% 3.25/1.00  --pure_diseq_elim                       true
% 3.25/1.00  --brand_transform                       false
% 3.25/1.00  --non_eq_to_eq                          false
% 3.25/1.00  --prep_def_merge                        true
% 3.25/1.00  --prep_def_merge_prop_impl              false
% 3.25/1.00  --prep_def_merge_mbd                    true
% 3.25/1.00  --prep_def_merge_tr_red                 false
% 3.25/1.00  --prep_def_merge_tr_cl                  false
% 3.25/1.00  --smt_preprocessing                     true
% 3.25/1.00  --smt_ac_axioms                         fast
% 3.25/1.00  --preprocessed_out                      false
% 3.25/1.00  --preprocessed_stats                    false
% 3.25/1.00  
% 3.25/1.00  ------ Abstraction refinement Options
% 3.25/1.00  
% 3.25/1.00  --abstr_ref                             []
% 3.25/1.00  --abstr_ref_prep                        false
% 3.25/1.00  --abstr_ref_until_sat                   false
% 3.25/1.00  --abstr_ref_sig_restrict                funpre
% 3.25/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.25/1.00  --abstr_ref_under                       []
% 3.25/1.00  
% 3.25/1.00  ------ SAT Options
% 3.25/1.00  
% 3.25/1.00  --sat_mode                              false
% 3.25/1.00  --sat_fm_restart_options                ""
% 3.25/1.00  --sat_gr_def                            false
% 3.25/1.00  --sat_epr_types                         true
% 3.25/1.00  --sat_non_cyclic_types                  false
% 3.25/1.00  --sat_finite_models                     false
% 3.25/1.00  --sat_fm_lemmas                         false
% 3.25/1.00  --sat_fm_prep                           false
% 3.25/1.00  --sat_fm_uc_incr                        true
% 3.25/1.00  --sat_out_model                         small
% 3.25/1.00  --sat_out_clauses                       false
% 3.25/1.00  
% 3.25/1.00  ------ QBF Options
% 3.25/1.00  
% 3.25/1.00  --qbf_mode                              false
% 3.25/1.00  --qbf_elim_univ                         false
% 3.25/1.00  --qbf_dom_inst                          none
% 3.25/1.00  --qbf_dom_pre_inst                      false
% 3.25/1.00  --qbf_sk_in                             false
% 3.25/1.00  --qbf_pred_elim                         true
% 3.25/1.00  --qbf_split                             512
% 3.25/1.00  
% 3.25/1.00  ------ BMC1 Options
% 3.25/1.00  
% 3.25/1.00  --bmc1_incremental                      false
% 3.25/1.00  --bmc1_axioms                           reachable_all
% 3.25/1.00  --bmc1_min_bound                        0
% 3.25/1.00  --bmc1_max_bound                        -1
% 3.25/1.00  --bmc1_max_bound_default                -1
% 3.25/1.00  --bmc1_symbol_reachability              true
% 3.25/1.00  --bmc1_property_lemmas                  false
% 3.25/1.00  --bmc1_k_induction                      false
% 3.25/1.00  --bmc1_non_equiv_states                 false
% 3.25/1.00  --bmc1_deadlock                         false
% 3.25/1.00  --bmc1_ucm                              false
% 3.25/1.00  --bmc1_add_unsat_core                   none
% 3.25/1.00  --bmc1_unsat_core_children              false
% 3.25/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.25/1.00  --bmc1_out_stat                         full
% 3.25/1.00  --bmc1_ground_init                      false
% 3.25/1.00  --bmc1_pre_inst_next_state              false
% 3.25/1.00  --bmc1_pre_inst_state                   false
% 3.25/1.00  --bmc1_pre_inst_reach_state             false
% 3.25/1.00  --bmc1_out_unsat_core                   false
% 3.25/1.00  --bmc1_aig_witness_out                  false
% 3.25/1.00  --bmc1_verbose                          false
% 3.25/1.00  --bmc1_dump_clauses_tptp                false
% 3.25/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.25/1.00  --bmc1_dump_file                        -
% 3.25/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.25/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.25/1.00  --bmc1_ucm_extend_mode                  1
% 3.25/1.00  --bmc1_ucm_init_mode                    2
% 3.25/1.00  --bmc1_ucm_cone_mode                    none
% 3.25/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.25/1.00  --bmc1_ucm_relax_model                  4
% 3.25/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.25/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.25/1.00  --bmc1_ucm_layered_model                none
% 3.25/1.00  --bmc1_ucm_max_lemma_size               10
% 3.25/1.00  
% 3.25/1.00  ------ AIG Options
% 3.25/1.00  
% 3.25/1.00  --aig_mode                              false
% 3.25/1.00  
% 3.25/1.00  ------ Instantiation Options
% 3.25/1.00  
% 3.25/1.00  --instantiation_flag                    true
% 3.25/1.00  --inst_sos_flag                         false
% 3.25/1.00  --inst_sos_phase                        true
% 3.25/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.25/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.25/1.00  --inst_lit_sel_side                     num_symb
% 3.25/1.00  --inst_solver_per_active                1400
% 3.25/1.00  --inst_solver_calls_frac                1.
% 3.25/1.00  --inst_passive_queue_type               priority_queues
% 3.25/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.25/1.00  --inst_passive_queues_freq              [25;2]
% 3.25/1.00  --inst_dismatching                      true
% 3.25/1.00  --inst_eager_unprocessed_to_passive     true
% 3.25/1.00  --inst_prop_sim_given                   true
% 3.25/1.00  --inst_prop_sim_new                     false
% 3.25/1.00  --inst_subs_new                         false
% 3.25/1.00  --inst_eq_res_simp                      false
% 3.25/1.00  --inst_subs_given                       false
% 3.25/1.00  --inst_orphan_elimination               true
% 3.25/1.00  --inst_learning_loop_flag               true
% 3.25/1.00  --inst_learning_start                   3000
% 3.25/1.00  --inst_learning_factor                  2
% 3.25/1.00  --inst_start_prop_sim_after_learn       3
% 3.25/1.00  --inst_sel_renew                        solver
% 3.25/1.00  --inst_lit_activity_flag                true
% 3.25/1.00  --inst_restr_to_given                   false
% 3.25/1.00  --inst_activity_threshold               500
% 3.25/1.00  --inst_out_proof                        true
% 3.25/1.00  
% 3.25/1.00  ------ Resolution Options
% 3.25/1.00  
% 3.25/1.00  --resolution_flag                       true
% 3.25/1.00  --res_lit_sel                           adaptive
% 3.25/1.00  --res_lit_sel_side                      none
% 3.25/1.00  --res_ordering                          kbo
% 3.25/1.00  --res_to_prop_solver                    active
% 3.25/1.00  --res_prop_simpl_new                    false
% 3.25/1.00  --res_prop_simpl_given                  true
% 3.25/1.00  --res_passive_queue_type                priority_queues
% 3.25/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.25/1.00  --res_passive_queues_freq               [15;5]
% 3.25/1.00  --res_forward_subs                      full
% 3.25/1.00  --res_backward_subs                     full
% 3.25/1.00  --res_forward_subs_resolution           true
% 3.25/1.00  --res_backward_subs_resolution          true
% 3.25/1.00  --res_orphan_elimination                true
% 3.25/1.00  --res_time_limit                        2.
% 3.25/1.00  --res_out_proof                         true
% 3.25/1.00  
% 3.25/1.00  ------ Superposition Options
% 3.25/1.00  
% 3.25/1.00  --superposition_flag                    true
% 3.25/1.00  --sup_passive_queue_type                priority_queues
% 3.25/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.25/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.25/1.00  --demod_completeness_check              fast
% 3.25/1.00  --demod_use_ground                      true
% 3.25/1.00  --sup_to_prop_solver                    passive
% 3.25/1.00  --sup_prop_simpl_new                    true
% 3.25/1.00  --sup_prop_simpl_given                  true
% 3.25/1.00  --sup_fun_splitting                     false
% 3.25/1.00  --sup_smt_interval                      50000
% 3.25/1.00  
% 3.25/1.00  ------ Superposition Simplification Setup
% 3.25/1.00  
% 3.25/1.00  --sup_indices_passive                   []
% 3.25/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.25/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.25/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.25/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.25/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.25/1.00  --sup_full_bw                           [BwDemod]
% 3.25/1.00  --sup_immed_triv                        [TrivRules]
% 3.25/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.25/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.25/1.00  --sup_immed_bw_main                     []
% 3.25/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.25/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.25/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.25/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.25/1.00  
% 3.25/1.00  ------ Combination Options
% 3.25/1.00  
% 3.25/1.00  --comb_res_mult                         3
% 3.25/1.00  --comb_sup_mult                         2
% 3.25/1.00  --comb_inst_mult                        10
% 3.25/1.00  
% 3.25/1.00  ------ Debug Options
% 3.25/1.00  
% 3.25/1.00  --dbg_backtrace                         false
% 3.25/1.00  --dbg_dump_prop_clauses                 false
% 3.25/1.00  --dbg_dump_prop_clauses_file            -
% 3.25/1.00  --dbg_out_stat                          false
% 3.25/1.00  ------ Parsing...
% 3.25/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.25/1.00  
% 3.25/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.25/1.00  
% 3.25/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.25/1.00  
% 3.25/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.25/1.00  ------ Proving...
% 3.25/1.00  ------ Problem Properties 
% 3.25/1.00  
% 3.25/1.00  
% 3.25/1.00  clauses                                 18
% 3.25/1.00  conjectures                             5
% 3.25/1.00  EPR                                     2
% 3.25/1.00  Horn                                    18
% 3.25/1.00  unary                                   8
% 3.25/1.00  binary                                  5
% 3.25/1.00  lits                                    39
% 3.25/1.00  lits eq                                 14
% 3.25/1.00  fd_pure                                 0
% 3.25/1.00  fd_pseudo                               0
% 3.25/1.00  fd_cond                                 0
% 3.25/1.00  fd_pseudo_cond                          0
% 3.25/1.00  AC symbols                              0
% 3.25/1.00  
% 3.25/1.00  ------ Schedule dynamic 5 is on 
% 3.25/1.00  
% 3.25/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.25/1.00  
% 3.25/1.00  
% 3.25/1.00  ------ 
% 3.25/1.00  Current options:
% 3.25/1.00  ------ 
% 3.25/1.00  
% 3.25/1.00  ------ Input Options
% 3.25/1.00  
% 3.25/1.00  --out_options                           all
% 3.25/1.00  --tptp_safe_out                         true
% 3.25/1.00  --problem_path                          ""
% 3.25/1.00  --include_path                          ""
% 3.25/1.00  --clausifier                            res/vclausify_rel
% 3.25/1.00  --clausifier_options                    --mode clausify
% 3.25/1.00  --stdin                                 false
% 3.25/1.00  --stats_out                             all
% 3.25/1.00  
% 3.25/1.00  ------ General Options
% 3.25/1.00  
% 3.25/1.00  --fof                                   false
% 3.25/1.00  --time_out_real                         305.
% 3.25/1.00  --time_out_virtual                      -1.
% 3.25/1.00  --symbol_type_check                     false
% 3.25/1.00  --clausify_out                          false
% 3.25/1.00  --sig_cnt_out                           false
% 3.25/1.00  --trig_cnt_out                          false
% 3.25/1.00  --trig_cnt_out_tolerance                1.
% 3.25/1.00  --trig_cnt_out_sk_spl                   false
% 3.25/1.00  --abstr_cl_out                          false
% 3.25/1.00  
% 3.25/1.00  ------ Global Options
% 3.25/1.00  
% 3.25/1.00  --schedule                              default
% 3.25/1.00  --add_important_lit                     false
% 3.25/1.00  --prop_solver_per_cl                    1000
% 3.25/1.00  --min_unsat_core                        false
% 3.25/1.00  --soft_assumptions                      false
% 3.25/1.00  --soft_lemma_size                       3
% 3.25/1.00  --prop_impl_unit_size                   0
% 3.25/1.00  --prop_impl_unit                        []
% 3.25/1.00  --share_sel_clauses                     true
% 3.25/1.00  --reset_solvers                         false
% 3.25/1.00  --bc_imp_inh                            [conj_cone]
% 3.25/1.00  --conj_cone_tolerance                   3.
% 3.25/1.00  --extra_neg_conj                        none
% 3.25/1.00  --large_theory_mode                     true
% 3.25/1.00  --prolific_symb_bound                   200
% 3.25/1.00  --lt_threshold                          2000
% 3.25/1.00  --clause_weak_htbl                      true
% 3.25/1.00  --gc_record_bc_elim                     false
% 3.25/1.00  
% 3.25/1.00  ------ Preprocessing Options
% 3.25/1.00  
% 3.25/1.00  --preprocessing_flag                    true
% 3.25/1.00  --time_out_prep_mult                    0.1
% 3.25/1.00  --splitting_mode                        input
% 3.25/1.00  --splitting_grd                         true
% 3.25/1.00  --splitting_cvd                         false
% 3.25/1.00  --splitting_cvd_svl                     false
% 3.25/1.00  --splitting_nvd                         32
% 3.25/1.00  --sub_typing                            true
% 3.25/1.00  --prep_gs_sim                           true
% 3.25/1.00  --prep_unflatten                        true
% 3.25/1.00  --prep_res_sim                          true
% 3.25/1.00  --prep_upred                            true
% 3.25/1.00  --prep_sem_filter                       exhaustive
% 3.25/1.00  --prep_sem_filter_out                   false
% 3.25/1.00  --pred_elim                             true
% 3.25/1.00  --res_sim_input                         true
% 3.25/1.00  --eq_ax_congr_red                       true
% 3.25/1.00  --pure_diseq_elim                       true
% 3.25/1.00  --brand_transform                       false
% 3.25/1.00  --non_eq_to_eq                          false
% 3.25/1.00  --prep_def_merge                        true
% 3.25/1.00  --prep_def_merge_prop_impl              false
% 3.25/1.00  --prep_def_merge_mbd                    true
% 3.25/1.00  --prep_def_merge_tr_red                 false
% 3.25/1.00  --prep_def_merge_tr_cl                  false
% 3.25/1.00  --smt_preprocessing                     true
% 3.25/1.00  --smt_ac_axioms                         fast
% 3.25/1.00  --preprocessed_out                      false
% 3.25/1.00  --preprocessed_stats                    false
% 3.25/1.00  
% 3.25/1.00  ------ Abstraction refinement Options
% 3.25/1.00  
% 3.25/1.00  --abstr_ref                             []
% 3.25/1.00  --abstr_ref_prep                        false
% 3.25/1.00  --abstr_ref_until_sat                   false
% 3.25/1.00  --abstr_ref_sig_restrict                funpre
% 3.25/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.25/1.00  --abstr_ref_under                       []
% 3.25/1.00  
% 3.25/1.00  ------ SAT Options
% 3.25/1.00  
% 3.25/1.00  --sat_mode                              false
% 3.25/1.00  --sat_fm_restart_options                ""
% 3.25/1.00  --sat_gr_def                            false
% 3.25/1.00  --sat_epr_types                         true
% 3.25/1.00  --sat_non_cyclic_types                  false
% 3.25/1.00  --sat_finite_models                     false
% 3.25/1.00  --sat_fm_lemmas                         false
% 3.25/1.00  --sat_fm_prep                           false
% 3.25/1.00  --sat_fm_uc_incr                        true
% 3.25/1.00  --sat_out_model                         small
% 3.25/1.00  --sat_out_clauses                       false
% 3.25/1.00  
% 3.25/1.00  ------ QBF Options
% 3.25/1.00  
% 3.25/1.00  --qbf_mode                              false
% 3.25/1.00  --qbf_elim_univ                         false
% 3.25/1.00  --qbf_dom_inst                          none
% 3.25/1.00  --qbf_dom_pre_inst                      false
% 3.25/1.00  --qbf_sk_in                             false
% 3.25/1.00  --qbf_pred_elim                         true
% 3.25/1.00  --qbf_split                             512
% 3.25/1.00  
% 3.25/1.00  ------ BMC1 Options
% 3.25/1.00  
% 3.25/1.00  --bmc1_incremental                      false
% 3.25/1.00  --bmc1_axioms                           reachable_all
% 3.25/1.00  --bmc1_min_bound                        0
% 3.25/1.00  --bmc1_max_bound                        -1
% 3.25/1.00  --bmc1_max_bound_default                -1
% 3.25/1.00  --bmc1_symbol_reachability              true
% 3.25/1.00  --bmc1_property_lemmas                  false
% 3.25/1.00  --bmc1_k_induction                      false
% 3.25/1.00  --bmc1_non_equiv_states                 false
% 3.25/1.00  --bmc1_deadlock                         false
% 3.25/1.00  --bmc1_ucm                              false
% 3.25/1.00  --bmc1_add_unsat_core                   none
% 3.25/1.00  --bmc1_unsat_core_children              false
% 3.25/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.25/1.00  --bmc1_out_stat                         full
% 3.25/1.00  --bmc1_ground_init                      false
% 3.25/1.00  --bmc1_pre_inst_next_state              false
% 3.25/1.00  --bmc1_pre_inst_state                   false
% 3.25/1.00  --bmc1_pre_inst_reach_state             false
% 3.25/1.00  --bmc1_out_unsat_core                   false
% 3.25/1.00  --bmc1_aig_witness_out                  false
% 3.25/1.00  --bmc1_verbose                          false
% 3.25/1.00  --bmc1_dump_clauses_tptp                false
% 3.25/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.25/1.00  --bmc1_dump_file                        -
% 3.25/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.25/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.25/1.00  --bmc1_ucm_extend_mode                  1
% 3.25/1.00  --bmc1_ucm_init_mode                    2
% 3.25/1.00  --bmc1_ucm_cone_mode                    none
% 3.25/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.25/1.00  --bmc1_ucm_relax_model                  4
% 3.25/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.25/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.25/1.00  --bmc1_ucm_layered_model                none
% 3.25/1.00  --bmc1_ucm_max_lemma_size               10
% 3.25/1.00  
% 3.25/1.00  ------ AIG Options
% 3.25/1.00  
% 3.25/1.00  --aig_mode                              false
% 3.25/1.00  
% 3.25/1.00  ------ Instantiation Options
% 3.25/1.00  
% 3.25/1.00  --instantiation_flag                    true
% 3.25/1.00  --inst_sos_flag                         false
% 3.25/1.00  --inst_sos_phase                        true
% 3.25/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.25/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.25/1.00  --inst_lit_sel_side                     none
% 3.25/1.00  --inst_solver_per_active                1400
% 3.25/1.00  --inst_solver_calls_frac                1.
% 3.25/1.00  --inst_passive_queue_type               priority_queues
% 3.25/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.25/1.00  --inst_passive_queues_freq              [25;2]
% 3.25/1.00  --inst_dismatching                      true
% 3.25/1.00  --inst_eager_unprocessed_to_passive     true
% 3.25/1.00  --inst_prop_sim_given                   true
% 3.25/1.00  --inst_prop_sim_new                     false
% 3.25/1.00  --inst_subs_new                         false
% 3.25/1.00  --inst_eq_res_simp                      false
% 3.25/1.00  --inst_subs_given                       false
% 3.25/1.00  --inst_orphan_elimination               true
% 3.25/1.00  --inst_learning_loop_flag               true
% 3.25/1.00  --inst_learning_start                   3000
% 3.25/1.00  --inst_learning_factor                  2
% 3.25/1.00  --inst_start_prop_sim_after_learn       3
% 3.25/1.00  --inst_sel_renew                        solver
% 3.25/1.00  --inst_lit_activity_flag                true
% 3.25/1.00  --inst_restr_to_given                   false
% 3.25/1.00  --inst_activity_threshold               500
% 3.25/1.00  --inst_out_proof                        true
% 3.25/1.00  
% 3.25/1.00  ------ Resolution Options
% 3.25/1.00  
% 3.25/1.00  --resolution_flag                       false
% 3.25/1.00  --res_lit_sel                           adaptive
% 3.25/1.00  --res_lit_sel_side                      none
% 3.25/1.00  --res_ordering                          kbo
% 3.25/1.00  --res_to_prop_solver                    active
% 3.25/1.00  --res_prop_simpl_new                    false
% 3.25/1.00  --res_prop_simpl_given                  true
% 3.25/1.00  --res_passive_queue_type                priority_queues
% 3.25/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.25/1.00  --res_passive_queues_freq               [15;5]
% 3.25/1.00  --res_forward_subs                      full
% 3.25/1.00  --res_backward_subs                     full
% 3.25/1.00  --res_forward_subs_resolution           true
% 3.25/1.00  --res_backward_subs_resolution          true
% 3.25/1.00  --res_orphan_elimination                true
% 3.25/1.00  --res_time_limit                        2.
% 3.25/1.00  --res_out_proof                         true
% 3.25/1.00  
% 3.25/1.00  ------ Superposition Options
% 3.25/1.00  
% 3.25/1.00  --superposition_flag                    true
% 3.25/1.00  --sup_passive_queue_type                priority_queues
% 3.25/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.25/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.25/1.00  --demod_completeness_check              fast
% 3.25/1.00  --demod_use_ground                      true
% 3.25/1.00  --sup_to_prop_solver                    passive
% 3.25/1.00  --sup_prop_simpl_new                    true
% 3.25/1.00  --sup_prop_simpl_given                  true
% 3.25/1.00  --sup_fun_splitting                     false
% 3.25/1.00  --sup_smt_interval                      50000
% 3.25/1.00  
% 3.25/1.00  ------ Superposition Simplification Setup
% 3.25/1.00  
% 3.25/1.00  --sup_indices_passive                   []
% 3.25/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.25/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.25/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.25/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.25/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.25/1.00  --sup_full_bw                           [BwDemod]
% 3.25/1.00  --sup_immed_triv                        [TrivRules]
% 3.25/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.25/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.25/1.00  --sup_immed_bw_main                     []
% 3.25/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.25/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.25/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.25/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.25/1.00  
% 3.25/1.00  ------ Combination Options
% 3.25/1.00  
% 3.25/1.00  --comb_res_mult                         3
% 3.25/1.00  --comb_sup_mult                         2
% 3.25/1.00  --comb_inst_mult                        10
% 3.25/1.00  
% 3.25/1.00  ------ Debug Options
% 3.25/1.00  
% 3.25/1.00  --dbg_backtrace                         false
% 3.25/1.00  --dbg_dump_prop_clauses                 false
% 3.25/1.00  --dbg_dump_prop_clauses_file            -
% 3.25/1.00  --dbg_out_stat                          false
% 3.25/1.00  
% 3.25/1.00  
% 3.25/1.00  
% 3.25/1.00  
% 3.25/1.00  ------ Proving...
% 3.25/1.00  
% 3.25/1.00  
% 3.25/1.00  % SZS status Theorem for theBenchmark.p
% 3.25/1.00  
% 3.25/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.25/1.00  
% 3.25/1.00  fof(f12,conjecture,(
% 3.25/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((k2_relset_1(X0,X0,X1) = X0 & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1)) => r2_relset_1(X0,X0,X2,k6_partfun1(X0)))))),
% 3.25/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/1.00  
% 3.25/1.00  fof(f13,negated_conjecture,(
% 3.25/1.00    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((k2_relset_1(X0,X0,X1) = X0 & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1)) => r2_relset_1(X0,X0,X2,k6_partfun1(X0)))))),
% 3.25/1.00    inference(negated_conjecture,[],[f12])).
% 3.25/1.00  
% 3.25/1.00  fof(f29,plain,(
% 3.25/1.00    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & (k2_relset_1(X0,X0,X1) = X0 & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 3.25/1.00    inference(ennf_transformation,[],[f13])).
% 3.25/1.00  
% 3.25/1.00  fof(f30,plain,(
% 3.25/1.00    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & k2_relset_1(X0,X0,X1) = X0 & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 3.25/1.00    inference(flattening,[],[f29])).
% 3.25/1.00  
% 3.25/1.00  fof(f33,plain,(
% 3.25/1.00    ( ! [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & k2_relset_1(X0,X0,X1) = X0 & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (~r2_relset_1(X0,X0,sK2,k6_partfun1(X0)) & k2_relset_1(X0,X0,X1) = X0 & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,sK2),X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(sK2,X0,X0) & v1_funct_1(sK2))) )),
% 3.25/1.00    introduced(choice_axiom,[])).
% 3.25/1.00  
% 3.25/1.00  fof(f32,plain,(
% 3.25/1.00    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & k2_relset_1(X0,X0,X1) = X0 & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK0,sK0,X2,k6_partfun1(sK0)) & k2_relset_1(sK0,sK0,sK1) = sK0 & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 3.25/1.00    introduced(choice_axiom,[])).
% 3.25/1.00  
% 3.25/1.00  fof(f34,plain,(
% 3.25/1.00    (~r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0)) & k2_relset_1(sK0,sK0,sK1) = sK0 & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 3.25/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f33,f32])).
% 3.25/1.00  
% 3.25/1.00  fof(f49,plain,(
% 3.25/1.00    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.25/1.00    inference(cnf_transformation,[],[f34])).
% 3.25/1.00  
% 3.25/1.00  fof(f52,plain,(
% 3.25/1.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.25/1.00    inference(cnf_transformation,[],[f34])).
% 3.25/1.00  
% 3.25/1.00  fof(f9,axiom,(
% 3.25/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.25/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/1.00  
% 3.25/1.00  fof(f25,plain,(
% 3.25/1.00    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.25/1.00    inference(ennf_transformation,[],[f9])).
% 3.25/1.00  
% 3.25/1.00  fof(f26,plain,(
% 3.25/1.00    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.25/1.00    inference(flattening,[],[f25])).
% 3.25/1.00  
% 3.25/1.00  fof(f44,plain,(
% 3.25/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.25/1.00    inference(cnf_transformation,[],[f26])).
% 3.25/1.00  
% 3.25/1.00  fof(f50,plain,(
% 3.25/1.00    v1_funct_1(sK2)),
% 3.25/1.00    inference(cnf_transformation,[],[f34])).
% 3.25/1.00  
% 3.25/1.00  fof(f47,plain,(
% 3.25/1.00    v1_funct_1(sK1)),
% 3.25/1.00    inference(cnf_transformation,[],[f34])).
% 3.25/1.00  
% 3.25/1.00  fof(f8,axiom,(
% 3.25/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.25/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/1.00  
% 3.25/1.00  fof(f23,plain,(
% 3.25/1.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.25/1.00    inference(ennf_transformation,[],[f8])).
% 3.25/1.00  
% 3.25/1.00  fof(f24,plain,(
% 3.25/1.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.25/1.00    inference(flattening,[],[f23])).
% 3.25/1.00  
% 3.25/1.00  fof(f31,plain,(
% 3.25/1.00    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.25/1.00    inference(nnf_transformation,[],[f24])).
% 3.25/1.00  
% 3.25/1.00  fof(f42,plain,(
% 3.25/1.00    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.25/1.00    inference(cnf_transformation,[],[f31])).
% 3.25/1.00  
% 3.25/1.00  fof(f53,plain,(
% 3.25/1.00    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),sK1)),
% 3.25/1.00    inference(cnf_transformation,[],[f34])).
% 3.25/1.00  
% 3.25/1.00  fof(f7,axiom,(
% 3.25/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5))),
% 3.25/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/1.00  
% 3.25/1.00  fof(f21,plain,(
% 3.25/1.00    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.25/1.00    inference(ennf_transformation,[],[f7])).
% 3.25/1.00  
% 3.25/1.00  fof(f22,plain,(
% 3.25/1.00    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.25/1.00    inference(flattening,[],[f21])).
% 3.25/1.00  
% 3.25/1.00  fof(f41,plain,(
% 3.25/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.25/1.00    inference(cnf_transformation,[],[f22])).
% 3.25/1.00  
% 3.25/1.00  fof(f4,axiom,(
% 3.25/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))))),
% 3.25/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/1.00  
% 3.25/1.00  fof(f17,plain,(
% 3.25/1.00    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.25/1.00    inference(ennf_transformation,[],[f4])).
% 3.25/1.00  
% 3.25/1.00  fof(f18,plain,(
% 3.25/1.00    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.25/1.00    inference(flattening,[],[f17])).
% 3.25/1.00  
% 3.25/1.00  fof(f38,plain,(
% 3.25/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.25/1.00    inference(cnf_transformation,[],[f18])).
% 3.25/1.00  
% 3.25/1.00  fof(f6,axiom,(
% 3.25/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.25/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/1.00  
% 3.25/1.00  fof(f20,plain,(
% 3.25/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.25/1.00    inference(ennf_transformation,[],[f6])).
% 3.25/1.00  
% 3.25/1.00  fof(f40,plain,(
% 3.25/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.25/1.00    inference(cnf_transformation,[],[f20])).
% 3.25/1.00  
% 3.25/1.00  fof(f54,plain,(
% 3.25/1.00    k2_relset_1(sK0,sK0,sK1) = sK0),
% 3.25/1.00    inference(cnf_transformation,[],[f34])).
% 3.25/1.00  
% 3.25/1.00  fof(f3,axiom,(
% 3.25/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = X0 & k2_relat_1(X0) = k1_relat_1(X1)) => k6_relat_1(k1_relat_1(X1)) = X1)))),
% 3.25/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/1.00  
% 3.25/1.00  fof(f15,plain,(
% 3.25/1.00    ! [X0] : (! [X1] : ((k6_relat_1(k1_relat_1(X1)) = X1 | (k5_relat_1(X0,X1) != X0 | k2_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.25/1.00    inference(ennf_transformation,[],[f3])).
% 3.25/1.00  
% 3.25/1.00  fof(f16,plain,(
% 3.25/1.00    ! [X0] : (! [X1] : (k6_relat_1(k1_relat_1(X1)) = X1 | k5_relat_1(X0,X1) != X0 | k2_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.25/1.00    inference(flattening,[],[f15])).
% 3.25/1.00  
% 3.25/1.00  fof(f37,plain,(
% 3.25/1.00    ( ! [X0,X1] : (k6_relat_1(k1_relat_1(X1)) = X1 | k5_relat_1(X0,X1) != X0 | k2_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.25/1.00    inference(cnf_transformation,[],[f16])).
% 3.25/1.00  
% 3.25/1.00  fof(f10,axiom,(
% 3.25/1.00    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.25/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/1.00  
% 3.25/1.00  fof(f45,plain,(
% 3.25/1.00    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.25/1.00    inference(cnf_transformation,[],[f10])).
% 3.25/1.00  
% 3.25/1.00  fof(f56,plain,(
% 3.25/1.00    ( ! [X0,X1] : (k6_partfun1(k1_relat_1(X1)) = X1 | k5_relat_1(X0,X1) != X0 | k2_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.25/1.00    inference(definition_unfolding,[],[f37,f45])).
% 3.25/1.00  
% 3.25/1.00  fof(f2,axiom,(
% 3.25/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.25/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/1.00  
% 3.25/1.00  fof(f36,plain,(
% 3.25/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.25/1.00    inference(cnf_transformation,[],[f2])).
% 3.25/1.00  
% 3.25/1.00  fof(f1,axiom,(
% 3.25/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.25/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/1.00  
% 3.25/1.00  fof(f14,plain,(
% 3.25/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.25/1.00    inference(ennf_transformation,[],[f1])).
% 3.25/1.00  
% 3.25/1.00  fof(f35,plain,(
% 3.25/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.25/1.00    inference(cnf_transformation,[],[f14])).
% 3.25/1.00  
% 3.25/1.00  fof(f5,axiom,(
% 3.25/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.25/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/1.00  
% 3.25/1.00  fof(f19,plain,(
% 3.25/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.25/1.00    inference(ennf_transformation,[],[f5])).
% 3.25/1.00  
% 3.25/1.00  fof(f39,plain,(
% 3.25/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.25/1.00    inference(cnf_transformation,[],[f19])).
% 3.25/1.00  
% 3.25/1.00  fof(f11,axiom,(
% 3.25/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 3.25/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.25/1.00  
% 3.25/1.00  fof(f27,plain,(
% 3.25/1.00    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.25/1.00    inference(ennf_transformation,[],[f11])).
% 3.25/1.00  
% 3.25/1.00  fof(f28,plain,(
% 3.25/1.00    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.25/1.00    inference(flattening,[],[f27])).
% 3.25/1.00  
% 3.25/1.00  fof(f46,plain,(
% 3.25/1.00    ( ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.25/1.00    inference(cnf_transformation,[],[f28])).
% 3.25/1.00  
% 3.25/1.00  fof(f51,plain,(
% 3.25/1.00    v1_funct_2(sK2,sK0,sK0)),
% 3.25/1.00    inference(cnf_transformation,[],[f34])).
% 3.25/1.00  
% 3.25/1.00  fof(f43,plain,(
% 3.25/1.00    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.25/1.00    inference(cnf_transformation,[],[f31])).
% 3.25/1.00  
% 3.25/1.00  fof(f57,plain,(
% 3.25/1.00    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.25/1.00    inference(equality_resolution,[],[f43])).
% 3.25/1.00  
% 3.25/1.00  fof(f55,plain,(
% 3.25/1.00    ~r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0))),
% 3.25/1.00    inference(cnf_transformation,[],[f34])).
% 3.25/1.00  
% 3.25/1.00  cnf(c_398,plain,
% 3.25/1.00      ( ~ m1_subset_1(X0_46,X0_48)
% 3.25/1.00      | m1_subset_1(X1_46,X1_48)
% 3.25/1.00      | X1_48 != X0_48
% 3.25/1.00      | X1_46 != X0_46 ),
% 3.25/1.00      theory(equality) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_898,plain,
% 3.25/1.00      ( m1_subset_1(X0_46,X0_48)
% 3.25/1.00      | ~ m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.25/1.00      | X0_48 != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
% 3.25/1.00      | X0_46 != X1_46 ),
% 3.25/1.00      inference(instantiation,[status(thm)],[c_398]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_1001,plain,
% 3.25/1.00      ( m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
% 3.25/1.00      | ~ m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.25/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
% 3.25/1.00      | X0_46 != X1_46 ),
% 3.25/1.00      inference(instantiation,[status(thm)],[c_898]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_3286,plain,
% 3.25/1.00      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.25/1.00      | m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.25/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
% 3.25/1.00      | k6_partfun1(sK0) != X0_46 ),
% 3.25/1.00      inference(instantiation,[status(thm)],[c_1001]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_4987,plain,
% 3.25/1.00      ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.25/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.25/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
% 3.25/1.00      | k6_partfun1(sK0) != sK2 ),
% 3.25/1.00      inference(instantiation,[status(thm)],[c_3286]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_17,negated_conjecture,
% 3.25/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.25/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_378,negated_conjecture,
% 3.25/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.25/1.00      inference(subtyping,[status(esa)],[c_17]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_683,plain,
% 3.25/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.25/1.00      inference(predicate_to_equality,[status(thm)],[c_378]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_14,negated_conjecture,
% 3.25/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.25/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_380,negated_conjecture,
% 3.25/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.25/1.00      inference(subtyping,[status(esa)],[c_14]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_681,plain,
% 3.25/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.25/1.00      inference(predicate_to_equality,[status(thm)],[c_380]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_9,plain,
% 3.25/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.25/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.25/1.00      | ~ v1_funct_1(X0)
% 3.25/1.00      | ~ v1_funct_1(X3)
% 3.25/1.00      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.25/1.00      inference(cnf_transformation,[],[f44]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_382,plain,
% 3.25/1.00      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
% 3.25/1.00      | ~ m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(X2_47,X3_47)))
% 3.25/1.00      | ~ v1_funct_1(X0_46)
% 3.25/1.00      | ~ v1_funct_1(X1_46)
% 3.25/1.00      | k1_partfun1(X2_47,X3_47,X0_47,X1_47,X1_46,X0_46) = k5_relat_1(X1_46,X0_46) ),
% 3.25/1.00      inference(subtyping,[status(esa)],[c_9]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_680,plain,
% 3.25/1.00      ( k1_partfun1(X0_47,X1_47,X2_47,X3_47,X0_46,X1_46) = k5_relat_1(X0_46,X1_46)
% 3.25/1.00      | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
% 3.25/1.00      | m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(X2_47,X3_47))) != iProver_top
% 3.25/1.00      | v1_funct_1(X0_46) != iProver_top
% 3.25/1.00      | v1_funct_1(X1_46) != iProver_top ),
% 3.25/1.00      inference(predicate_to_equality,[status(thm)],[c_382]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_1372,plain,
% 3.25/1.00      ( k1_partfun1(X0_47,X1_47,sK0,sK0,X0_46,sK2) = k5_relat_1(X0_46,sK2)
% 3.25/1.00      | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
% 3.25/1.00      | v1_funct_1(X0_46) != iProver_top
% 3.25/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.25/1.00      inference(superposition,[status(thm)],[c_681,c_680]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_16,negated_conjecture,
% 3.25/1.00      ( v1_funct_1(sK2) ),
% 3.25/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_23,plain,
% 3.25/1.00      ( v1_funct_1(sK2) = iProver_top ),
% 3.25/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_1678,plain,
% 3.25/1.00      ( v1_funct_1(X0_46) != iProver_top
% 3.25/1.00      | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
% 3.25/1.00      | k1_partfun1(X0_47,X1_47,sK0,sK0,X0_46,sK2) = k5_relat_1(X0_46,sK2) ),
% 3.25/1.00      inference(global_propositional_subsumption,
% 3.25/1.00                [status(thm)],
% 3.25/1.00                [c_1372,c_23]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_1679,plain,
% 3.25/1.00      ( k1_partfun1(X0_47,X1_47,sK0,sK0,X0_46,sK2) = k5_relat_1(X0_46,sK2)
% 3.25/1.00      | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
% 3.25/1.00      | v1_funct_1(X0_46) != iProver_top ),
% 3.25/1.00      inference(renaming,[status(thm)],[c_1678]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_1688,plain,
% 3.25/1.00      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2)
% 3.25/1.00      | v1_funct_1(sK1) != iProver_top ),
% 3.25/1.00      inference(superposition,[status(thm)],[c_683,c_1679]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_19,negated_conjecture,
% 3.25/1.00      ( v1_funct_1(sK1) ),
% 3.25/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_1052,plain,
% 3.25/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.25/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.25/1.00      | ~ v1_funct_1(sK1)
% 3.25/1.00      | ~ v1_funct_1(sK2)
% 3.25/1.00      | k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2) ),
% 3.25/1.00      inference(instantiation,[status(thm)],[c_382]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_1810,plain,
% 3.25/1.00      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2) ),
% 3.25/1.00      inference(global_propositional_subsumption,
% 3.25/1.00                [status(thm)],
% 3.25/1.00                [c_1688,c_19,c_17,c_16,c_14,c_1052]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_8,plain,
% 3.25/1.00      ( ~ r2_relset_1(X0,X1,X2,X3)
% 3.25/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.25/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.25/1.00      | X3 = X2 ),
% 3.25/1.00      inference(cnf_transformation,[],[f42]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_13,negated_conjecture,
% 3.25/1.00      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),sK1) ),
% 3.25/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_238,plain,
% 3.25/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.25/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.25/1.00      | X3 = X0
% 3.25/1.00      | k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) != X0
% 3.25/1.00      | sK1 != X3
% 3.25/1.00      | sK0 != X2
% 3.25/1.00      | sK0 != X1 ),
% 3.25/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_13]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_239,plain,
% 3.25/1.00      ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.25/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.25/1.00      | sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) ),
% 3.25/1.00      inference(unflattening,[status(thm)],[c_238]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_241,plain,
% 3.25/1.00      ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.25/1.00      | sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) ),
% 3.25/1.00      inference(global_propositional_subsumption,
% 3.25/1.00                [status(thm)],
% 3.25/1.00                [c_239,c_17]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_373,plain,
% 3.25/1.00      ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.25/1.00      | sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) ),
% 3.25/1.00      inference(subtyping,[status(esa)],[c_241]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_686,plain,
% 3.25/1.00      ( sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2)
% 3.25/1.00      | m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.25/1.00      inference(predicate_to_equality,[status(thm)],[c_373]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_1813,plain,
% 3.25/1.00      ( k5_relat_1(sK1,sK2) = sK1
% 3.25/1.00      | m1_subset_1(k5_relat_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.25/1.00      inference(demodulation,[status(thm)],[c_1810,c_686]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_22,plain,
% 3.25/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.25/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_25,plain,
% 3.25/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.25/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_6,plain,
% 3.25/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.25/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.25/1.00      | k4_relset_1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.25/1.00      inference(cnf_transformation,[],[f41]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_383,plain,
% 3.25/1.00      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
% 3.25/1.00      | ~ m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(X2_47,X3_47)))
% 3.25/1.00      | k4_relset_1(X2_47,X3_47,X0_47,X1_47,X1_46,X0_46) = k5_relat_1(X1_46,X0_46) ),
% 3.25/1.00      inference(subtyping,[status(esa)],[c_6]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_679,plain,
% 3.25/1.00      ( k4_relset_1(X0_47,X1_47,X2_47,X3_47,X0_46,X1_46) = k5_relat_1(X0_46,X1_46)
% 3.25/1.00      | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
% 3.25/1.00      | m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(X2_47,X3_47))) != iProver_top ),
% 3.25/1.00      inference(predicate_to_equality,[status(thm)],[c_383]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_1232,plain,
% 3.25/1.00      ( k4_relset_1(X0_47,X1_47,sK0,sK0,X0_46,sK2) = k5_relat_1(X0_46,sK2)
% 3.25/1.00      | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top ),
% 3.25/1.00      inference(superposition,[status(thm)],[c_681,c_679]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_1485,plain,
% 3.25/1.00      ( k4_relset_1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2) ),
% 3.25/1.00      inference(superposition,[status(thm)],[c_683,c_1232]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_3,plain,
% 3.25/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.25/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.25/1.00      | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) ),
% 3.25/1.00      inference(cnf_transformation,[],[f38]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_386,plain,
% 3.25/1.00      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
% 3.25/1.00      | ~ m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(X2_47,X3_47)))
% 3.25/1.00      | m1_subset_1(k4_relset_1(X2_47,X3_47,X0_47,X1_47,X1_46,X0_46),k1_zfmisc_1(k2_zfmisc_1(X2_47,X1_47))) ),
% 3.25/1.00      inference(subtyping,[status(esa)],[c_3]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_676,plain,
% 3.25/1.00      ( m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
% 3.25/1.00      | m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(X2_47,X3_47))) != iProver_top
% 3.25/1.00      | m1_subset_1(k4_relset_1(X0_47,X1_47,X2_47,X3_47,X0_46,X1_46),k1_zfmisc_1(k2_zfmisc_1(X0_47,X3_47))) = iProver_top ),
% 3.25/1.00      inference(predicate_to_equality,[status(thm)],[c_386]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_1560,plain,
% 3.25/1.00      ( m1_subset_1(k5_relat_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 3.25/1.00      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.25/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.25/1.00      inference(superposition,[status(thm)],[c_1485,c_676]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_2315,plain,
% 3.25/1.00      ( k5_relat_1(sK1,sK2) = sK1 ),
% 3.25/1.00      inference(global_propositional_subsumption,
% 3.25/1.00                [status(thm)],
% 3.25/1.00                [c_1813,c_22,c_25,c_1560]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_5,plain,
% 3.25/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.25/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.25/1.00      inference(cnf_transformation,[],[f40]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_384,plain,
% 3.25/1.00      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
% 3.25/1.00      | k2_relset_1(X0_47,X1_47,X0_46) = k2_relat_1(X0_46) ),
% 3.25/1.00      inference(subtyping,[status(esa)],[c_5]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_678,plain,
% 3.25/1.00      ( k2_relset_1(X0_47,X1_47,X0_46) = k2_relat_1(X0_46)
% 3.25/1.00      | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top ),
% 3.25/1.00      inference(predicate_to_equality,[status(thm)],[c_384]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_974,plain,
% 3.25/1.00      ( k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) ),
% 3.25/1.00      inference(superposition,[status(thm)],[c_683,c_678]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_12,negated_conjecture,
% 3.25/1.00      ( k2_relset_1(sK0,sK0,sK1) = sK0 ),
% 3.25/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_381,negated_conjecture,
% 3.25/1.00      ( k2_relset_1(sK0,sK0,sK1) = sK0 ),
% 3.25/1.00      inference(subtyping,[status(esa)],[c_12]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_976,plain,
% 3.25/1.00      ( k2_relat_1(sK1) = sK0 ),
% 3.25/1.00      inference(light_normalisation,[status(thm)],[c_974,c_381]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_2,plain,
% 3.25/1.00      ( ~ v1_funct_1(X0)
% 3.25/1.00      | ~ v1_funct_1(X1)
% 3.25/1.00      | ~ v1_relat_1(X1)
% 3.25/1.00      | ~ v1_relat_1(X0)
% 3.25/1.00      | k5_relat_1(X1,X0) != X1
% 3.25/1.00      | k2_relat_1(X1) != k1_relat_1(X0)
% 3.25/1.00      | k6_partfun1(k1_relat_1(X0)) = X0 ),
% 3.25/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_387,plain,
% 3.25/1.00      ( ~ v1_funct_1(X0_46)
% 3.25/1.00      | ~ v1_funct_1(X1_46)
% 3.25/1.00      | ~ v1_relat_1(X1_46)
% 3.25/1.00      | ~ v1_relat_1(X0_46)
% 3.25/1.00      | k2_relat_1(X1_46) != k1_relat_1(X0_46)
% 3.25/1.00      | k5_relat_1(X1_46,X0_46) != X1_46
% 3.25/1.00      | k6_partfun1(k1_relat_1(X0_46)) = X0_46 ),
% 3.25/1.00      inference(subtyping,[status(esa)],[c_2]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_675,plain,
% 3.25/1.00      ( k2_relat_1(X0_46) != k1_relat_1(X1_46)
% 3.25/1.00      | k5_relat_1(X0_46,X1_46) != X0_46
% 3.25/1.00      | k6_partfun1(k1_relat_1(X1_46)) = X1_46
% 3.25/1.00      | v1_funct_1(X0_46) != iProver_top
% 3.25/1.00      | v1_funct_1(X1_46) != iProver_top
% 3.25/1.00      | v1_relat_1(X1_46) != iProver_top
% 3.25/1.00      | v1_relat_1(X0_46) != iProver_top ),
% 3.25/1.00      inference(predicate_to_equality,[status(thm)],[c_387]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_1254,plain,
% 3.25/1.00      ( k1_relat_1(X0_46) != sK0
% 3.25/1.00      | k5_relat_1(sK1,X0_46) != sK1
% 3.25/1.00      | k6_partfun1(k1_relat_1(X0_46)) = X0_46
% 3.25/1.00      | v1_funct_1(X0_46) != iProver_top
% 3.25/1.00      | v1_funct_1(sK1) != iProver_top
% 3.25/1.00      | v1_relat_1(X0_46) != iProver_top
% 3.25/1.00      | v1_relat_1(sK1) != iProver_top ),
% 3.25/1.00      inference(superposition,[status(thm)],[c_976,c_675]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_20,plain,
% 3.25/1.00      ( v1_funct_1(sK1) = iProver_top ),
% 3.25/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_1,plain,
% 3.25/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.25/1.00      inference(cnf_transformation,[],[f36]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_55,plain,
% 3.25/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.25/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_57,plain,
% 3.25/1.00      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) = iProver_top ),
% 3.25/1.00      inference(instantiation,[status(thm)],[c_55]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_0,plain,
% 3.25/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.25/1.00      | ~ v1_relat_1(X1)
% 3.25/1.00      | v1_relat_1(X0) ),
% 3.25/1.00      inference(cnf_transformation,[],[f35]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_389,plain,
% 3.25/1.00      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(X1_46))
% 3.25/1.00      | ~ v1_relat_1(X1_46)
% 3.25/1.00      | v1_relat_1(X0_46) ),
% 3.25/1.00      inference(subtyping,[status(esa)],[c_0]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_799,plain,
% 3.25/1.00      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
% 3.25/1.00      | v1_relat_1(X0_46)
% 3.25/1.00      | ~ v1_relat_1(k2_zfmisc_1(X0_47,X1_47)) ),
% 3.25/1.00      inference(instantiation,[status(thm)],[c_389]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_800,plain,
% 3.25/1.00      ( m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
% 3.25/1.00      | v1_relat_1(X0_46) = iProver_top
% 3.25/1.00      | v1_relat_1(k2_zfmisc_1(X0_47,X1_47)) != iProver_top ),
% 3.25/1.00      inference(predicate_to_equality,[status(thm)],[c_799]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_802,plain,
% 3.25/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.25/1.00      | v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
% 3.25/1.00      | v1_relat_1(sK1) = iProver_top ),
% 3.25/1.00      inference(instantiation,[status(thm)],[c_800]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_1943,plain,
% 3.25/1.00      ( v1_relat_1(X0_46) != iProver_top
% 3.25/1.00      | k1_relat_1(X0_46) != sK0
% 3.25/1.00      | k5_relat_1(sK1,X0_46) != sK1
% 3.25/1.00      | k6_partfun1(k1_relat_1(X0_46)) = X0_46
% 3.25/1.00      | v1_funct_1(X0_46) != iProver_top ),
% 3.25/1.00      inference(global_propositional_subsumption,
% 3.25/1.00                [status(thm)],
% 3.25/1.00                [c_1254,c_20,c_22,c_57,c_802]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_1944,plain,
% 3.25/1.00      ( k1_relat_1(X0_46) != sK0
% 3.25/1.00      | k5_relat_1(sK1,X0_46) != sK1
% 3.25/1.00      | k6_partfun1(k1_relat_1(X0_46)) = X0_46
% 3.25/1.00      | v1_funct_1(X0_46) != iProver_top
% 3.25/1.00      | v1_relat_1(X0_46) != iProver_top ),
% 3.25/1.00      inference(renaming,[status(thm)],[c_1943]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_2329,plain,
% 3.25/1.00      ( k1_relat_1(sK2) != sK0
% 3.25/1.00      | k6_partfun1(k1_relat_1(sK2)) = sK2
% 3.25/1.00      | v1_funct_1(sK2) != iProver_top
% 3.25/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.25/1.00      inference(superposition,[status(thm)],[c_2315,c_1944]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_4,plain,
% 3.25/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.25/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.25/1.00      inference(cnf_transformation,[],[f39]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_385,plain,
% 3.25/1.00      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
% 3.25/1.00      | k1_relset_1(X0_47,X1_47,X0_46) = k1_relat_1(X0_46) ),
% 3.25/1.00      inference(subtyping,[status(esa)],[c_4]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_677,plain,
% 3.25/1.00      ( k1_relset_1(X0_47,X1_47,X0_46) = k1_relat_1(X0_46)
% 3.25/1.00      | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top ),
% 3.25/1.00      inference(predicate_to_equality,[status(thm)],[c_385]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_962,plain,
% 3.25/1.00      ( k1_relset_1(sK0,sK0,sK2) = k1_relat_1(sK2) ),
% 3.25/1.00      inference(superposition,[status(thm)],[c_681,c_677]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_10,plain,
% 3.25/1.00      ( ~ v1_funct_2(X0,X1,X1)
% 3.25/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.25/1.00      | ~ v1_funct_1(X0)
% 3.25/1.00      | k1_relset_1(X1,X1,X0) = X1 ),
% 3.25/1.00      inference(cnf_transformation,[],[f46]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_15,negated_conjecture,
% 3.25/1.00      ( v1_funct_2(sK2,sK0,sK0) ),
% 3.25/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_208,plain,
% 3.25/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.25/1.00      | ~ v1_funct_1(X0)
% 3.25/1.00      | k1_relset_1(X1,X1,X0) = X1
% 3.25/1.00      | sK2 != X0
% 3.25/1.00      | sK0 != X1 ),
% 3.25/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_15]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_209,plain,
% 3.25/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.25/1.00      | ~ v1_funct_1(sK2)
% 3.25/1.00      | k1_relset_1(sK0,sK0,sK2) = sK0 ),
% 3.25/1.00      inference(unflattening,[status(thm)],[c_208]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_211,plain,
% 3.25/1.00      ( k1_relset_1(sK0,sK0,sK2) = sK0 ),
% 3.25/1.00      inference(global_propositional_subsumption,
% 3.25/1.00                [status(thm)],
% 3.25/1.00                [c_209,c_16,c_14]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_376,plain,
% 3.25/1.00      ( k1_relset_1(sK0,sK0,sK2) = sK0 ),
% 3.25/1.00      inference(subtyping,[status(esa)],[c_211]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_968,plain,
% 3.25/1.00      ( k1_relat_1(sK2) = sK0 ),
% 3.25/1.00      inference(light_normalisation,[status(thm)],[c_962,c_376]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_2330,plain,
% 3.25/1.00      ( sK0 != sK0
% 3.25/1.00      | k6_partfun1(sK0) = sK2
% 3.25/1.00      | v1_funct_1(sK2) != iProver_top
% 3.25/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.25/1.00      inference(light_normalisation,[status(thm)],[c_2329,c_968]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_2331,plain,
% 3.25/1.00      ( k6_partfun1(sK0) = sK2
% 3.25/1.00      | v1_funct_1(sK2) != iProver_top
% 3.25/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.25/1.00      inference(equality_resolution_simp,[status(thm)],[c_2330]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_673,plain,
% 3.25/1.00      ( m1_subset_1(X0_46,k1_zfmisc_1(X1_46)) != iProver_top
% 3.25/1.00      | v1_relat_1(X1_46) != iProver_top
% 3.25/1.00      | v1_relat_1(X0_46) = iProver_top ),
% 3.25/1.00      inference(predicate_to_equality,[status(thm)],[c_389]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_907,plain,
% 3.25/1.00      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
% 3.25/1.00      | v1_relat_1(sK2) = iProver_top ),
% 3.25/1.00      inference(superposition,[status(thm)],[c_681,c_673]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_394,plain,
% 3.25/1.00      ( X0_46 != X1_46 | X2_46 != X1_46 | X2_46 = X0_46 ),
% 3.25/1.00      theory(equality) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_810,plain,
% 3.25/1.00      ( k6_partfun1(sK0) != X0_46
% 3.25/1.00      | sK2 != X0_46
% 3.25/1.00      | sK2 = k6_partfun1(sK0) ),
% 3.25/1.00      inference(instantiation,[status(thm)],[c_394]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_886,plain,
% 3.25/1.00      ( k6_partfun1(sK0) != sK2 | sK2 = k6_partfun1(sK0) | sK2 != sK2 ),
% 3.25/1.00      inference(instantiation,[status(thm)],[c_810]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_393,plain,( X0_48 = X0_48 ),theory(equality) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_847,plain,
% 3.25/1.00      ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
% 3.25/1.00      inference(instantiation,[status(thm)],[c_393]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_391,plain,( X0_46 = X0_46 ),theory(equality) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_839,plain,
% 3.25/1.00      ( sK2 = sK2 ),
% 3.25/1.00      inference(instantiation,[status(thm)],[c_391]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_7,plain,
% 3.25/1.00      ( r2_relset_1(X0,X1,X2,X2)
% 3.25/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.25/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_11,negated_conjecture,
% 3.25/1.00      ( ~ r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0)) ),
% 3.25/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_228,plain,
% 3.25/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.25/1.00      | k6_partfun1(sK0) != X0
% 3.25/1.00      | sK2 != X0
% 3.25/1.00      | sK0 != X2
% 3.25/1.00      | sK0 != X1 ),
% 3.25/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_11]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_229,plain,
% 3.25/1.00      ( ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.25/1.00      | sK2 != k6_partfun1(sK0) ),
% 3.25/1.00      inference(unflattening,[status(thm)],[c_228]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(c_374,plain,
% 3.25/1.00      ( ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.25/1.00      | sK2 != k6_partfun1(sK0) ),
% 3.25/1.00      inference(subtyping,[status(esa)],[c_229]) ).
% 3.25/1.00  
% 3.25/1.00  cnf(contradiction,plain,
% 3.25/1.00      ( $false ),
% 3.25/1.00      inference(minisat,
% 3.25/1.00                [status(thm)],
% 3.25/1.00                [c_4987,c_2331,c_907,c_886,c_847,c_839,c_374,c_57,c_14,
% 3.25/1.00                 c_23]) ).
% 3.25/1.00  
% 3.25/1.00  
% 3.25/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.25/1.00  
% 3.25/1.00  ------                               Statistics
% 3.25/1.00  
% 3.25/1.00  ------ General
% 3.25/1.00  
% 3.25/1.00  abstr_ref_over_cycles:                  0
% 3.25/1.00  abstr_ref_under_cycles:                 0
% 3.25/1.00  gc_basic_clause_elim:                   0
% 3.25/1.00  forced_gc_time:                         0
% 3.25/1.00  parsing_time:                           0.009
% 3.25/1.00  unif_index_cands_time:                  0.
% 3.25/1.00  unif_index_add_time:                    0.
% 3.25/1.00  orderings_time:                         0.
% 3.25/1.00  out_proof_time:                         0.008
% 3.25/1.00  total_time:                             0.175
% 3.25/1.00  num_of_symbols:                         52
% 3.25/1.00  num_of_terms:                           3721
% 3.25/1.00  
% 3.25/1.00  ------ Preprocessing
% 3.25/1.00  
% 3.25/1.00  num_of_splits:                          0
% 3.25/1.00  num_of_split_atoms:                     0
% 3.25/1.00  num_of_reused_defs:                     0
% 3.25/1.00  num_eq_ax_congr_red:                    33
% 3.25/1.00  num_of_sem_filtered_clauses:            1
% 3.25/1.00  num_of_subtypes:                        3
% 3.25/1.00  monotx_restored_types:                  0
% 3.25/1.00  sat_num_of_epr_types:                   0
% 3.25/1.00  sat_num_of_non_cyclic_types:            0
% 3.25/1.00  sat_guarded_non_collapsed_types:        1
% 3.25/1.00  num_pure_diseq_elim:                    0
% 3.25/1.00  simp_replaced_by:                       0
% 3.25/1.00  res_preprocessed:                       103
% 3.25/1.00  prep_upred:                             0
% 3.25/1.00  prep_unflattend:                        15
% 3.25/1.00  smt_new_axioms:                         0
% 3.25/1.00  pred_elim_cands:                        3
% 3.25/1.00  pred_elim:                              2
% 3.25/1.00  pred_elim_cl:                           2
% 3.25/1.00  pred_elim_cycles:                       4
% 3.25/1.00  merged_defs:                            0
% 3.25/1.00  merged_defs_ncl:                        0
% 3.25/1.00  bin_hyper_res:                          0
% 3.25/1.00  prep_cycles:                            4
% 3.25/1.00  pred_elim_time:                         0.002
% 3.25/1.00  splitting_time:                         0.
% 3.25/1.00  sem_filter_time:                        0.
% 3.25/1.00  monotx_time:                            0.
% 3.25/1.00  subtype_inf_time:                       0.
% 3.25/1.00  
% 3.25/1.00  ------ Problem properties
% 3.25/1.00  
% 3.25/1.00  clauses:                                18
% 3.25/1.00  conjectures:                            5
% 3.25/1.00  epr:                                    2
% 3.25/1.00  horn:                                   18
% 3.25/1.00  ground:                                 10
% 3.25/1.00  unary:                                  8
% 3.25/1.00  binary:                                 5
% 3.25/1.00  lits:                                   39
% 3.25/1.00  lits_eq:                                14
% 3.25/1.00  fd_pure:                                0
% 3.25/1.00  fd_pseudo:                              0
% 3.25/1.00  fd_cond:                                0
% 3.25/1.00  fd_pseudo_cond:                         0
% 3.25/1.00  ac_symbols:                             0
% 3.25/1.00  
% 3.25/1.00  ------ Propositional Solver
% 3.25/1.00  
% 3.25/1.00  prop_solver_calls:                      33
% 3.25/1.00  prop_fast_solver_calls:                 693
% 3.25/1.00  smt_solver_calls:                       0
% 3.25/1.00  smt_fast_solver_calls:                  0
% 3.25/1.00  prop_num_of_clauses:                    1422
% 3.25/1.00  prop_preprocess_simplified:             4389
% 3.25/1.00  prop_fo_subsumed:                       25
% 3.25/1.00  prop_solver_time:                       0.
% 3.25/1.00  smt_solver_time:                        0.
% 3.25/1.00  smt_fast_solver_time:                   0.
% 3.25/1.00  prop_fast_solver_time:                  0.
% 3.25/1.00  prop_unsat_core_time:                   0.
% 3.25/1.00  
% 3.25/1.00  ------ QBF
% 3.25/1.00  
% 3.25/1.00  qbf_q_res:                              0
% 3.25/1.00  qbf_num_tautologies:                    0
% 3.25/1.00  qbf_prep_cycles:                        0
% 3.25/1.00  
% 3.25/1.00  ------ BMC1
% 3.25/1.00  
% 3.25/1.00  bmc1_current_bound:                     -1
% 3.25/1.00  bmc1_last_solved_bound:                 -1
% 3.25/1.00  bmc1_unsat_core_size:                   -1
% 3.25/1.00  bmc1_unsat_core_parents_size:           -1
% 3.25/1.00  bmc1_merge_next_fun:                    0
% 3.25/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.25/1.00  
% 3.25/1.00  ------ Instantiation
% 3.25/1.00  
% 3.25/1.00  inst_num_of_clauses:                    621
% 3.25/1.00  inst_num_in_passive:                    168
% 3.25/1.00  inst_num_in_active:                     379
% 3.25/1.00  inst_num_in_unprocessed:                73
% 3.25/1.00  inst_num_of_loops:                      418
% 3.25/1.00  inst_num_of_learning_restarts:          0
% 3.25/1.00  inst_num_moves_active_passive:          31
% 3.25/1.00  inst_lit_activity:                      0
% 3.25/1.00  inst_lit_activity_moves:                0
% 3.25/1.00  inst_num_tautologies:                   0
% 3.25/1.00  inst_num_prop_implied:                  0
% 3.25/1.00  inst_num_existing_simplified:           0
% 3.25/1.00  inst_num_eq_res_simplified:             0
% 3.25/1.00  inst_num_child_elim:                    0
% 3.25/1.00  inst_num_of_dismatching_blockings:      318
% 3.25/1.00  inst_num_of_non_proper_insts:           809
% 3.25/1.00  inst_num_of_duplicates:                 0
% 3.25/1.00  inst_inst_num_from_inst_to_res:         0
% 3.25/1.00  inst_dismatching_checking_time:         0.
% 3.25/1.00  
% 3.25/1.00  ------ Resolution
% 3.25/1.00  
% 3.25/1.00  res_num_of_clauses:                     0
% 3.25/1.00  res_num_in_passive:                     0
% 3.25/1.00  res_num_in_active:                      0
% 3.25/1.00  res_num_of_loops:                       107
% 3.25/1.00  res_forward_subset_subsumed:            97
% 3.25/1.00  res_backward_subset_subsumed:           0
% 3.25/1.00  res_forward_subsumed:                   0
% 3.25/1.00  res_backward_subsumed:                  0
% 3.25/1.00  res_forward_subsumption_resolution:     0
% 3.25/1.00  res_backward_subsumption_resolution:    0
% 3.25/1.00  res_clause_to_clause_subsumption:       348
% 3.25/1.00  res_orphan_elimination:                 0
% 3.25/1.00  res_tautology_del:                      195
% 3.25/1.00  res_num_eq_res_simplified:              1
% 3.25/1.00  res_num_sel_changes:                    0
% 3.25/1.00  res_moves_from_active_to_pass:          0
% 3.25/1.00  
% 3.25/1.00  ------ Superposition
% 3.25/1.00  
% 3.25/1.00  sup_time_total:                         0.
% 3.25/1.00  sup_time_generating:                    0.
% 3.25/1.00  sup_time_sim_full:                      0.
% 3.25/1.00  sup_time_sim_immed:                     0.
% 3.25/1.00  
% 3.25/1.00  sup_num_of_clauses:                     158
% 3.25/1.00  sup_num_in_active:                      77
% 3.25/1.00  sup_num_in_passive:                     81
% 3.25/1.00  sup_num_of_loops:                       82
% 3.25/1.00  sup_fw_superposition:                   101
% 3.25/1.00  sup_bw_superposition:                   54
% 3.25/1.00  sup_immediate_simplified:               39
% 3.25/1.00  sup_given_eliminated:                   0
% 3.25/1.00  comparisons_done:                       0
% 3.25/1.00  comparisons_avoided:                    0
% 3.25/1.00  
% 3.25/1.00  ------ Simplifications
% 3.25/1.00  
% 3.25/1.00  
% 3.25/1.00  sim_fw_subset_subsumed:                 1
% 3.25/1.00  sim_bw_subset_subsumed:                 0
% 3.25/1.00  sim_fw_subsumed:                        0
% 3.25/1.00  sim_bw_subsumed:                        0
% 3.25/1.00  sim_fw_subsumption_res:                 0
% 3.25/1.00  sim_bw_subsumption_res:                 0
% 3.25/1.00  sim_tautology_del:                      0
% 3.25/1.00  sim_eq_tautology_del:                   11
% 3.25/1.00  sim_eq_res_simp:                        1
% 3.25/1.00  sim_fw_demodulated:                     0
% 3.25/1.00  sim_bw_demodulated:                     5
% 3.25/1.00  sim_light_normalised:                   40
% 3.25/1.00  sim_joinable_taut:                      0
% 3.25/1.00  sim_joinable_simp:                      0
% 3.25/1.00  sim_ac_normalised:                      0
% 3.25/1.00  sim_smt_subsumption:                    0
% 3.25/1.00  
%------------------------------------------------------------------------------
