%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:06:47 EST 2020

% Result     : Theorem 3.02s
% Output     : CNFRefutation 3.02s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 363 expanded)
%              Number of clauses        :   86 ( 120 expanded)
%              Number of leaves         :   17 (  90 expanded)
%              Depth                    :   18
%              Number of atoms          :  460 (2303 expanded)
%              Number of equality atoms :  191 ( 425 expanded)
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
    inference(ennf_transformation,[],[f12])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f30,plain,(
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

fof(f29,plain,
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

fof(f31,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0))
    & k2_relset_1(sK0,sK0,sK1) = sK0
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK2,sK0,sK0)
    & v1_funct_1(sK2)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f30,f29])).

fof(f46,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f31])).

fof(f49,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f31])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f22])).

fof(f41,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f47,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f18])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f50,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f44,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f20])).

fof(f40,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f51,plain,(
    k2_relset_1(sK0,sK0,sK1) = sK0 ),
    inference(cnf_transformation,[],[f31])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f3])).

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
    inference(flattening,[],[f14])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k6_relat_1(k1_relat_1(X1)) = X1
      | k5_relat_1(X0,X1) != X0
      | k2_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f9,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k6_partfun1(k1_relat_1(X1)) = X1
      | k5_relat_1(X0,X1) != X0
      | k2_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f34,f42])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f48,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f38])).

fof(f52,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_398,plain,
    ( ~ m1_subset_1(X0_45,X0_47)
    | m1_subset_1(X1_45,X1_47)
    | X1_47 != X0_47
    | X1_45 != X0_45 ),
    theory(equality)).

cnf(c_925,plain,
    ( m1_subset_1(X0_45,X0_47)
    | ~ m1_subset_1(X1_45,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | X0_47 != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | X0_45 != X1_45 ),
    inference(instantiation,[status(thm)],[c_398])).

cnf(c_1040,plain,
    ( m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)))
    | ~ m1_subset_1(X1_45,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | X0_45 != X1_45 ),
    inference(instantiation,[status(thm)],[c_925])).

cnf(c_2353,plain,
    ( ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | k6_partfun1(sK0) != X0_45 ),
    inference(instantiation,[status(thm)],[c_1040])).

cnf(c_5733,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | k6_partfun1(sK0) != sK2 ),
    inference(instantiation,[status(thm)],[c_2353])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_378,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_683,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_378])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f49])).

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
    inference(cnf_transformation,[],[f41])).

cnf(c_382,plain,
    ( ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)))
    | ~ m1_subset_1(X1_45,k1_zfmisc_1(k2_zfmisc_1(X2_46,X3_46)))
    | ~ v1_funct_1(X0_45)
    | ~ v1_funct_1(X1_45)
    | k1_partfun1(X2_46,X3_46,X0_46,X1_46,X1_45,X0_45) = k5_relat_1(X1_45,X0_45) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_680,plain,
    ( k1_partfun1(X0_46,X1_46,X2_46,X3_46,X0_45,X1_45) = k5_relat_1(X0_45,X1_45)
    | m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) != iProver_top
    | m1_subset_1(X1_45,k1_zfmisc_1(k2_zfmisc_1(X2_46,X3_46))) != iProver_top
    | v1_funct_1(X0_45) != iProver_top
    | v1_funct_1(X1_45) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_382])).

cnf(c_1283,plain,
    ( k1_partfun1(X0_46,X1_46,sK0,sK0,X0_45,sK2) = k5_relat_1(X0_45,sK2)
    | m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) != iProver_top
    | v1_funct_1(X0_45) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_681,c_680])).

cnf(c_16,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_23,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1433,plain,
    ( v1_funct_1(X0_45) != iProver_top
    | m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) != iProver_top
    | k1_partfun1(X0_46,X1_46,sK0,sK0,X0_45,sK2) = k5_relat_1(X0_45,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1283,c_23])).

cnf(c_1434,plain,
    ( k1_partfun1(X0_46,X1_46,sK0,sK0,X0_45,sK2) = k5_relat_1(X0_45,sK2)
    | m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) != iProver_top
    | v1_funct_1(X0_45) != iProver_top ),
    inference(renaming,[status(thm)],[c_1433])).

cnf(c_1443,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2)
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_683,c_1434])).

cnf(c_6,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_13,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),sK1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_238,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) != X0
    | sK1 != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_13])).

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

cnf(c_19,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_384,plain,
    ( ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)))
    | ~ m1_subset_1(X1_45,k1_zfmisc_1(k2_zfmisc_1(X2_46,X3_46)))
    | m1_subset_1(k1_partfun1(X2_46,X3_46,X0_46,X1_46,X1_45,X0_45),k1_zfmisc_1(k2_zfmisc_1(X2_46,X1_46)))
    | ~ v1_funct_1(X0_45)
    | ~ v1_funct_1(X1_45) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_841,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_384])).

cnf(c_1145,plain,
    ( sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_686,c_19,c_17,c_16,c_14,c_373,c_841])).

cnf(c_1459,plain,
    ( k5_relat_1(sK1,sK2) = sK1
    | v1_funct_1(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1443,c_1145])).

cnf(c_20,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1749,plain,
    ( k5_relat_1(sK1,sK2) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1459,c_20])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_385,plain,
    ( ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)))
    | k2_relset_1(X0_46,X1_46,X0_45) = k2_relat_1(X0_45) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_677,plain,
    ( k2_relset_1(X0_46,X1_46,X0_45) = k2_relat_1(X0_45)
    | m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_385])).

cnf(c_972,plain,
    ( k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_683,c_677])).

cnf(c_12,negated_conjecture,
    ( k2_relset_1(sK0,sK0,sK1) = sK0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_381,negated_conjecture,
    ( k2_relset_1(sK0,sK0,sK1) = sK0 ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_974,plain,
    ( k2_relat_1(sK1) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_972,c_381])).

cnf(c_2,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X1,X0) != X1
    | k2_relat_1(X1) != k1_relat_1(X0)
    | k6_partfun1(k1_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_387,plain,
    ( ~ v1_funct_1(X0_45)
    | ~ v1_funct_1(X1_45)
    | ~ v1_relat_1(X1_45)
    | ~ v1_relat_1(X0_45)
    | k2_relat_1(X1_45) != k1_relat_1(X0_45)
    | k5_relat_1(X1_45,X0_45) != X1_45
    | k6_partfun1(k1_relat_1(X0_45)) = X0_45 ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_675,plain,
    ( k2_relat_1(X0_45) != k1_relat_1(X1_45)
    | k5_relat_1(X0_45,X1_45) != X0_45
    | k6_partfun1(k1_relat_1(X1_45)) = X1_45
    | v1_funct_1(X0_45) != iProver_top
    | v1_funct_1(X1_45) != iProver_top
    | v1_relat_1(X1_45) != iProver_top
    | v1_relat_1(X0_45) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_387])).

cnf(c_1209,plain,
    ( k1_relat_1(X0_45) != sK0
    | k5_relat_1(sK1,X0_45) != sK1
    | k6_partfun1(k1_relat_1(X0_45)) = X0_45
    | v1_funct_1(X0_45) != iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v1_relat_1(X0_45) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_974,c_675])).

cnf(c_22,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f33])).

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
    inference(cnf_transformation,[],[f32])).

cnf(c_389,plain,
    ( ~ m1_subset_1(X0_45,k1_zfmisc_1(X1_45))
    | ~ v1_relat_1(X1_45)
    | v1_relat_1(X0_45) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_807,plain,
    ( ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)))
    | v1_relat_1(X0_45)
    | ~ v1_relat_1(k2_zfmisc_1(X0_46,X1_46)) ),
    inference(instantiation,[status(thm)],[c_389])).

cnf(c_808,plain,
    ( m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) != iProver_top
    | v1_relat_1(X0_45) = iProver_top
    | v1_relat_1(k2_zfmisc_1(X0_46,X1_46)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_807])).

cnf(c_810,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
    | v1_relat_1(sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_808])).

cnf(c_1739,plain,
    ( v1_relat_1(X0_45) != iProver_top
    | k1_relat_1(X0_45) != sK0
    | k5_relat_1(sK1,X0_45) != sK1
    | k6_partfun1(k1_relat_1(X0_45)) = X0_45
    | v1_funct_1(X0_45) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1209,c_20,c_22,c_57,c_810])).

cnf(c_1740,plain,
    ( k1_relat_1(X0_45) != sK0
    | k5_relat_1(sK1,X0_45) != sK1
    | k6_partfun1(k1_relat_1(X0_45)) = X0_45
    | v1_funct_1(X0_45) != iProver_top
    | v1_relat_1(X0_45) != iProver_top ),
    inference(renaming,[status(thm)],[c_1739])).

cnf(c_1752,plain,
    ( k1_relat_1(sK2) != sK0
    | k6_partfun1(k1_relat_1(sK2)) = sK2
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1749,c_1740])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_386,plain,
    ( ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)))
    | k1_relset_1(X0_46,X1_46,X0_45) = k1_relat_1(X0_45) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_676,plain,
    ( k1_relset_1(X0_46,X1_46,X0_45) = k1_relat_1(X0_45)
    | m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_386])).

cnf(c_960,plain,
    ( k1_relset_1(sK0,sK0,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_681,c_676])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(X1,X1,X0) = X1 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_15,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f48])).

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

cnf(c_966,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_960,c_376])).

cnf(c_1753,plain,
    ( sK0 != sK0
    | k6_partfun1(sK0) = sK2
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1752,c_966])).

cnf(c_1754,plain,
    ( k6_partfun1(sK0) = sK2
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_1753])).

cnf(c_673,plain,
    ( m1_subset_1(X0_45,k1_zfmisc_1(X1_45)) != iProver_top
    | v1_relat_1(X1_45) != iProver_top
    | v1_relat_1(X0_45) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_389])).

cnf(c_911,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_681,c_673])).

cnf(c_394,plain,
    ( X0_45 != X1_45
    | X2_45 != X1_45
    | X2_45 = X0_45 ),
    theory(equality)).

cnf(c_818,plain,
    ( k6_partfun1(sK0) != X0_45
    | sK2 != X0_45
    | sK2 = k6_partfun1(sK0) ),
    inference(instantiation,[status(thm)],[c_394])).

cnf(c_898,plain,
    ( k6_partfun1(sK0) != sK2
    | sK2 = k6_partfun1(sK0)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_818])).

cnf(c_393,plain,
    ( X0_47 = X0_47 ),
    theory(equality)).

cnf(c_858,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_393])).

cnf(c_391,plain,
    ( X0_45 = X0_45 ),
    theory(equality)).

cnf(c_850,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_391])).

cnf(c_5,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_11,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_228,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k6_partfun1(sK0) != X0
    | sK2 != X0
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_11])).

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
    inference(minisat,[status(thm)],[c_5733,c_1754,c_911,c_898,c_858,c_850,c_374,c_57,c_14,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:27:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.02/0.94  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.02/0.94  
% 3.02/0.94  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.02/0.94  
% 3.02/0.94  ------  iProver source info
% 3.02/0.94  
% 3.02/0.94  git: date: 2020-06-30 10:37:57 +0100
% 3.02/0.94  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.02/0.94  git: non_committed_changes: false
% 3.02/0.94  git: last_make_outside_of_git: false
% 3.02/0.94  
% 3.02/0.94  ------ 
% 3.02/0.94  
% 3.02/0.94  ------ Input Options
% 3.02/0.94  
% 3.02/0.94  --out_options                           all
% 3.02/0.94  --tptp_safe_out                         true
% 3.02/0.94  --problem_path                          ""
% 3.02/0.94  --include_path                          ""
% 3.02/0.94  --clausifier                            res/vclausify_rel
% 3.02/0.94  --clausifier_options                    --mode clausify
% 3.02/0.94  --stdin                                 false
% 3.02/0.94  --stats_out                             all
% 3.02/0.94  
% 3.02/0.94  ------ General Options
% 3.02/0.94  
% 3.02/0.94  --fof                                   false
% 3.02/0.94  --time_out_real                         305.
% 3.02/0.94  --time_out_virtual                      -1.
% 3.02/0.94  --symbol_type_check                     false
% 3.02/0.94  --clausify_out                          false
% 3.02/0.94  --sig_cnt_out                           false
% 3.02/0.94  --trig_cnt_out                          false
% 3.02/0.94  --trig_cnt_out_tolerance                1.
% 3.02/0.94  --trig_cnt_out_sk_spl                   false
% 3.02/0.94  --abstr_cl_out                          false
% 3.02/0.94  
% 3.02/0.94  ------ Global Options
% 3.02/0.94  
% 3.02/0.94  --schedule                              default
% 3.02/0.94  --add_important_lit                     false
% 3.02/0.94  --prop_solver_per_cl                    1000
% 3.02/0.94  --min_unsat_core                        false
% 3.02/0.94  --soft_assumptions                      false
% 3.02/0.94  --soft_lemma_size                       3
% 3.02/0.94  --prop_impl_unit_size                   0
% 3.02/0.94  --prop_impl_unit                        []
% 3.02/0.94  --share_sel_clauses                     true
% 3.02/0.94  --reset_solvers                         false
% 3.02/0.94  --bc_imp_inh                            [conj_cone]
% 3.02/0.94  --conj_cone_tolerance                   3.
% 3.02/0.94  --extra_neg_conj                        none
% 3.02/0.94  --large_theory_mode                     true
% 3.02/0.94  --prolific_symb_bound                   200
% 3.02/0.94  --lt_threshold                          2000
% 3.02/0.94  --clause_weak_htbl                      true
% 3.02/0.94  --gc_record_bc_elim                     false
% 3.02/0.94  
% 3.02/0.94  ------ Preprocessing Options
% 3.02/0.94  
% 3.02/0.94  --preprocessing_flag                    true
% 3.02/0.94  --time_out_prep_mult                    0.1
% 3.02/0.94  --splitting_mode                        input
% 3.02/0.94  --splitting_grd                         true
% 3.02/0.94  --splitting_cvd                         false
% 3.02/0.94  --splitting_cvd_svl                     false
% 3.02/0.94  --splitting_nvd                         32
% 3.02/0.94  --sub_typing                            true
% 3.02/0.94  --prep_gs_sim                           true
% 3.02/0.94  --prep_unflatten                        true
% 3.02/0.94  --prep_res_sim                          true
% 3.02/0.94  --prep_upred                            true
% 3.02/0.94  --prep_sem_filter                       exhaustive
% 3.02/0.94  --prep_sem_filter_out                   false
% 3.02/0.94  --pred_elim                             true
% 3.02/0.94  --res_sim_input                         true
% 3.02/0.94  --eq_ax_congr_red                       true
% 3.02/0.94  --pure_diseq_elim                       true
% 3.02/0.94  --brand_transform                       false
% 3.02/0.94  --non_eq_to_eq                          false
% 3.02/0.94  --prep_def_merge                        true
% 3.02/0.94  --prep_def_merge_prop_impl              false
% 3.02/0.94  --prep_def_merge_mbd                    true
% 3.02/0.94  --prep_def_merge_tr_red                 false
% 3.02/0.94  --prep_def_merge_tr_cl                  false
% 3.02/0.94  --smt_preprocessing                     true
% 3.02/0.94  --smt_ac_axioms                         fast
% 3.02/0.94  --preprocessed_out                      false
% 3.02/0.94  --preprocessed_stats                    false
% 3.02/0.94  
% 3.02/0.94  ------ Abstraction refinement Options
% 3.02/0.94  
% 3.02/0.94  --abstr_ref                             []
% 3.02/0.94  --abstr_ref_prep                        false
% 3.02/0.94  --abstr_ref_until_sat                   false
% 3.02/0.94  --abstr_ref_sig_restrict                funpre
% 3.02/0.94  --abstr_ref_af_restrict_to_split_sk     false
% 3.02/0.94  --abstr_ref_under                       []
% 3.02/0.94  
% 3.02/0.94  ------ SAT Options
% 3.02/0.94  
% 3.02/0.94  --sat_mode                              false
% 3.02/0.94  --sat_fm_restart_options                ""
% 3.02/0.94  --sat_gr_def                            false
% 3.02/0.94  --sat_epr_types                         true
% 3.02/0.94  --sat_non_cyclic_types                  false
% 3.02/0.94  --sat_finite_models                     false
% 3.02/0.94  --sat_fm_lemmas                         false
% 3.02/0.94  --sat_fm_prep                           false
% 3.02/0.94  --sat_fm_uc_incr                        true
% 3.02/0.94  --sat_out_model                         small
% 3.02/0.94  --sat_out_clauses                       false
% 3.02/0.94  
% 3.02/0.94  ------ QBF Options
% 3.02/0.94  
% 3.02/0.94  --qbf_mode                              false
% 3.02/0.94  --qbf_elim_univ                         false
% 3.02/0.94  --qbf_dom_inst                          none
% 3.02/0.94  --qbf_dom_pre_inst                      false
% 3.02/0.94  --qbf_sk_in                             false
% 3.02/0.94  --qbf_pred_elim                         true
% 3.02/0.94  --qbf_split                             512
% 3.02/0.94  
% 3.02/0.94  ------ BMC1 Options
% 3.02/0.94  
% 3.02/0.94  --bmc1_incremental                      false
% 3.02/0.94  --bmc1_axioms                           reachable_all
% 3.02/0.94  --bmc1_min_bound                        0
% 3.02/0.94  --bmc1_max_bound                        -1
% 3.02/0.94  --bmc1_max_bound_default                -1
% 3.02/0.94  --bmc1_symbol_reachability              true
% 3.02/0.94  --bmc1_property_lemmas                  false
% 3.02/0.94  --bmc1_k_induction                      false
% 3.02/0.94  --bmc1_non_equiv_states                 false
% 3.02/0.94  --bmc1_deadlock                         false
% 3.02/0.94  --bmc1_ucm                              false
% 3.02/0.94  --bmc1_add_unsat_core                   none
% 3.02/0.94  --bmc1_unsat_core_children              false
% 3.02/0.94  --bmc1_unsat_core_extrapolate_axioms    false
% 3.02/0.94  --bmc1_out_stat                         full
% 3.02/0.94  --bmc1_ground_init                      false
% 3.02/0.94  --bmc1_pre_inst_next_state              false
% 3.02/0.94  --bmc1_pre_inst_state                   false
% 3.02/0.94  --bmc1_pre_inst_reach_state             false
% 3.02/0.94  --bmc1_out_unsat_core                   false
% 3.02/0.94  --bmc1_aig_witness_out                  false
% 3.02/0.94  --bmc1_verbose                          false
% 3.02/0.94  --bmc1_dump_clauses_tptp                false
% 3.02/0.94  --bmc1_dump_unsat_core_tptp             false
% 3.02/0.94  --bmc1_dump_file                        -
% 3.02/0.94  --bmc1_ucm_expand_uc_limit              128
% 3.02/0.94  --bmc1_ucm_n_expand_iterations          6
% 3.02/0.94  --bmc1_ucm_extend_mode                  1
% 3.02/0.94  --bmc1_ucm_init_mode                    2
% 3.02/0.94  --bmc1_ucm_cone_mode                    none
% 3.02/0.94  --bmc1_ucm_reduced_relation_type        0
% 3.02/0.94  --bmc1_ucm_relax_model                  4
% 3.02/0.94  --bmc1_ucm_full_tr_after_sat            true
% 3.02/0.94  --bmc1_ucm_expand_neg_assumptions       false
% 3.02/0.94  --bmc1_ucm_layered_model                none
% 3.02/0.94  --bmc1_ucm_max_lemma_size               10
% 3.02/0.94  
% 3.02/0.94  ------ AIG Options
% 3.02/0.94  
% 3.02/0.94  --aig_mode                              false
% 3.02/0.94  
% 3.02/0.94  ------ Instantiation Options
% 3.02/0.94  
% 3.02/0.94  --instantiation_flag                    true
% 3.02/0.94  --inst_sos_flag                         false
% 3.02/0.94  --inst_sos_phase                        true
% 3.02/0.94  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.02/0.94  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.02/0.94  --inst_lit_sel_side                     num_symb
% 3.02/0.94  --inst_solver_per_active                1400
% 3.02/0.94  --inst_solver_calls_frac                1.
% 3.02/0.94  --inst_passive_queue_type               priority_queues
% 3.02/0.94  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.02/0.94  --inst_passive_queues_freq              [25;2]
% 3.02/0.94  --inst_dismatching                      true
% 3.02/0.94  --inst_eager_unprocessed_to_passive     true
% 3.02/0.94  --inst_prop_sim_given                   true
% 3.02/0.94  --inst_prop_sim_new                     false
% 3.02/0.94  --inst_subs_new                         false
% 3.02/0.94  --inst_eq_res_simp                      false
% 3.02/0.94  --inst_subs_given                       false
% 3.02/0.94  --inst_orphan_elimination               true
% 3.02/0.94  --inst_learning_loop_flag               true
% 3.02/0.94  --inst_learning_start                   3000
% 3.02/0.94  --inst_learning_factor                  2
% 3.02/0.94  --inst_start_prop_sim_after_learn       3
% 3.02/0.94  --inst_sel_renew                        solver
% 3.02/0.94  --inst_lit_activity_flag                true
% 3.02/0.94  --inst_restr_to_given                   false
% 3.02/0.94  --inst_activity_threshold               500
% 3.02/0.94  --inst_out_proof                        true
% 3.02/0.94  
% 3.02/0.94  ------ Resolution Options
% 3.02/0.94  
% 3.02/0.94  --resolution_flag                       true
% 3.02/0.94  --res_lit_sel                           adaptive
% 3.02/0.94  --res_lit_sel_side                      none
% 3.02/0.94  --res_ordering                          kbo
% 3.02/0.94  --res_to_prop_solver                    active
% 3.02/0.94  --res_prop_simpl_new                    false
% 3.02/0.94  --res_prop_simpl_given                  true
% 3.02/0.94  --res_passive_queue_type                priority_queues
% 3.02/0.94  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.02/0.94  --res_passive_queues_freq               [15;5]
% 3.02/0.94  --res_forward_subs                      full
% 3.02/0.94  --res_backward_subs                     full
% 3.02/0.94  --res_forward_subs_resolution           true
% 3.02/0.94  --res_backward_subs_resolution          true
% 3.02/0.94  --res_orphan_elimination                true
% 3.02/0.94  --res_time_limit                        2.
% 3.02/0.94  --res_out_proof                         true
% 3.02/0.94  
% 3.02/0.94  ------ Superposition Options
% 3.02/0.94  
% 3.02/0.94  --superposition_flag                    true
% 3.02/0.94  --sup_passive_queue_type                priority_queues
% 3.02/0.94  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.02/0.94  --sup_passive_queues_freq               [8;1;4]
% 3.02/0.94  --demod_completeness_check              fast
% 3.02/0.94  --demod_use_ground                      true
% 3.02/0.94  --sup_to_prop_solver                    passive
% 3.02/0.94  --sup_prop_simpl_new                    true
% 3.02/0.94  --sup_prop_simpl_given                  true
% 3.02/0.94  --sup_fun_splitting                     false
% 3.02/0.94  --sup_smt_interval                      50000
% 3.02/0.94  
% 3.02/0.94  ------ Superposition Simplification Setup
% 3.02/0.94  
% 3.02/0.94  --sup_indices_passive                   []
% 3.02/0.94  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/0.94  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/0.94  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/0.94  --sup_full_triv                         [TrivRules;PropSubs]
% 3.02/0.94  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/0.94  --sup_full_bw                           [BwDemod]
% 3.02/0.94  --sup_immed_triv                        [TrivRules]
% 3.02/0.94  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.02/0.94  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/0.94  --sup_immed_bw_main                     []
% 3.02/0.94  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.02/0.94  --sup_input_triv                        [Unflattening;TrivRules]
% 3.02/0.94  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/0.94  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.02/0.94  
% 3.02/0.94  ------ Combination Options
% 3.02/0.94  
% 3.02/0.94  --comb_res_mult                         3
% 3.02/0.94  --comb_sup_mult                         2
% 3.02/0.94  --comb_inst_mult                        10
% 3.02/0.94  
% 3.02/0.94  ------ Debug Options
% 3.02/0.94  
% 3.02/0.94  --dbg_backtrace                         false
% 3.02/0.94  --dbg_dump_prop_clauses                 false
% 3.02/0.94  --dbg_dump_prop_clauses_file            -
% 3.02/0.94  --dbg_out_stat                          false
% 3.02/0.94  ------ Parsing...
% 3.02/0.94  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.02/0.94  
% 3.02/0.94  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.02/0.94  
% 3.02/0.94  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.02/0.94  
% 3.02/0.94  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.02/0.94  ------ Proving...
% 3.02/0.94  ------ Problem Properties 
% 3.02/0.94  
% 3.02/0.94  
% 3.02/0.94  clauses                                 18
% 3.02/0.94  conjectures                             5
% 3.02/0.94  EPR                                     2
% 3.02/0.94  Horn                                    18
% 3.02/0.94  unary                                   8
% 3.02/0.94  binary                                  5
% 3.02/0.94  lits                                    43
% 3.02/0.94  lits eq                                 13
% 3.02/0.94  fd_pure                                 0
% 3.02/0.94  fd_pseudo                               0
% 3.02/0.94  fd_cond                                 0
% 3.02/0.94  fd_pseudo_cond                          0
% 3.02/0.94  AC symbols                              0
% 3.02/0.94  
% 3.02/0.94  ------ Schedule dynamic 5 is on 
% 3.02/0.94  
% 3.02/0.94  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.02/0.94  
% 3.02/0.94  
% 3.02/0.94  ------ 
% 3.02/0.94  Current options:
% 3.02/0.94  ------ 
% 3.02/0.94  
% 3.02/0.94  ------ Input Options
% 3.02/0.94  
% 3.02/0.94  --out_options                           all
% 3.02/0.94  --tptp_safe_out                         true
% 3.02/0.94  --problem_path                          ""
% 3.02/0.94  --include_path                          ""
% 3.02/0.94  --clausifier                            res/vclausify_rel
% 3.02/0.94  --clausifier_options                    --mode clausify
% 3.02/0.94  --stdin                                 false
% 3.02/0.94  --stats_out                             all
% 3.02/0.94  
% 3.02/0.94  ------ General Options
% 3.02/0.94  
% 3.02/0.94  --fof                                   false
% 3.02/0.94  --time_out_real                         305.
% 3.02/0.94  --time_out_virtual                      -1.
% 3.02/0.94  --symbol_type_check                     false
% 3.02/0.94  --clausify_out                          false
% 3.02/0.94  --sig_cnt_out                           false
% 3.02/0.94  --trig_cnt_out                          false
% 3.02/0.94  --trig_cnt_out_tolerance                1.
% 3.02/0.94  --trig_cnt_out_sk_spl                   false
% 3.02/0.94  --abstr_cl_out                          false
% 3.02/0.94  
% 3.02/0.94  ------ Global Options
% 3.02/0.94  
% 3.02/0.94  --schedule                              default
% 3.02/0.94  --add_important_lit                     false
% 3.02/0.94  --prop_solver_per_cl                    1000
% 3.02/0.94  --min_unsat_core                        false
% 3.02/0.94  --soft_assumptions                      false
% 3.02/0.94  --soft_lemma_size                       3
% 3.02/0.94  --prop_impl_unit_size                   0
% 3.02/0.94  --prop_impl_unit                        []
% 3.02/0.94  --share_sel_clauses                     true
% 3.02/0.94  --reset_solvers                         false
% 3.02/0.94  --bc_imp_inh                            [conj_cone]
% 3.02/0.94  --conj_cone_tolerance                   3.
% 3.02/0.94  --extra_neg_conj                        none
% 3.02/0.94  --large_theory_mode                     true
% 3.02/0.94  --prolific_symb_bound                   200
% 3.02/0.94  --lt_threshold                          2000
% 3.02/0.94  --clause_weak_htbl                      true
% 3.02/0.94  --gc_record_bc_elim                     false
% 3.02/0.94  
% 3.02/0.94  ------ Preprocessing Options
% 3.02/0.94  
% 3.02/0.94  --preprocessing_flag                    true
% 3.02/0.94  --time_out_prep_mult                    0.1
% 3.02/0.94  --splitting_mode                        input
% 3.02/0.94  --splitting_grd                         true
% 3.02/0.94  --splitting_cvd                         false
% 3.02/0.94  --splitting_cvd_svl                     false
% 3.02/0.94  --splitting_nvd                         32
% 3.02/0.94  --sub_typing                            true
% 3.02/0.94  --prep_gs_sim                           true
% 3.02/0.94  --prep_unflatten                        true
% 3.02/0.94  --prep_res_sim                          true
% 3.02/0.94  --prep_upred                            true
% 3.02/0.94  --prep_sem_filter                       exhaustive
% 3.02/0.94  --prep_sem_filter_out                   false
% 3.02/0.94  --pred_elim                             true
% 3.02/0.94  --res_sim_input                         true
% 3.02/0.94  --eq_ax_congr_red                       true
% 3.02/0.94  --pure_diseq_elim                       true
% 3.02/0.94  --brand_transform                       false
% 3.02/0.94  --non_eq_to_eq                          false
% 3.02/0.94  --prep_def_merge                        true
% 3.02/0.94  --prep_def_merge_prop_impl              false
% 3.02/0.94  --prep_def_merge_mbd                    true
% 3.02/0.94  --prep_def_merge_tr_red                 false
% 3.02/0.94  --prep_def_merge_tr_cl                  false
% 3.02/0.94  --smt_preprocessing                     true
% 3.02/0.94  --smt_ac_axioms                         fast
% 3.02/0.94  --preprocessed_out                      false
% 3.02/0.94  --preprocessed_stats                    false
% 3.02/0.94  
% 3.02/0.94  ------ Abstraction refinement Options
% 3.02/0.94  
% 3.02/0.94  --abstr_ref                             []
% 3.02/0.94  --abstr_ref_prep                        false
% 3.02/0.94  --abstr_ref_until_sat                   false
% 3.02/0.94  --abstr_ref_sig_restrict                funpre
% 3.02/0.94  --abstr_ref_af_restrict_to_split_sk     false
% 3.02/0.94  --abstr_ref_under                       []
% 3.02/0.94  
% 3.02/0.94  ------ SAT Options
% 3.02/0.94  
% 3.02/0.94  --sat_mode                              false
% 3.02/0.94  --sat_fm_restart_options                ""
% 3.02/0.94  --sat_gr_def                            false
% 3.02/0.94  --sat_epr_types                         true
% 3.02/0.94  --sat_non_cyclic_types                  false
% 3.02/0.94  --sat_finite_models                     false
% 3.02/0.94  --sat_fm_lemmas                         false
% 3.02/0.94  --sat_fm_prep                           false
% 3.02/0.94  --sat_fm_uc_incr                        true
% 3.02/0.94  --sat_out_model                         small
% 3.02/0.94  --sat_out_clauses                       false
% 3.02/0.94  
% 3.02/0.94  ------ QBF Options
% 3.02/0.94  
% 3.02/0.94  --qbf_mode                              false
% 3.02/0.94  --qbf_elim_univ                         false
% 3.02/0.94  --qbf_dom_inst                          none
% 3.02/0.94  --qbf_dom_pre_inst                      false
% 3.02/0.94  --qbf_sk_in                             false
% 3.02/0.94  --qbf_pred_elim                         true
% 3.02/0.94  --qbf_split                             512
% 3.02/0.94  
% 3.02/0.94  ------ BMC1 Options
% 3.02/0.94  
% 3.02/0.94  --bmc1_incremental                      false
% 3.02/0.94  --bmc1_axioms                           reachable_all
% 3.02/0.94  --bmc1_min_bound                        0
% 3.02/0.94  --bmc1_max_bound                        -1
% 3.02/0.94  --bmc1_max_bound_default                -1
% 3.02/0.94  --bmc1_symbol_reachability              true
% 3.02/0.94  --bmc1_property_lemmas                  false
% 3.02/0.94  --bmc1_k_induction                      false
% 3.02/0.94  --bmc1_non_equiv_states                 false
% 3.02/0.94  --bmc1_deadlock                         false
% 3.02/0.94  --bmc1_ucm                              false
% 3.02/0.94  --bmc1_add_unsat_core                   none
% 3.02/0.94  --bmc1_unsat_core_children              false
% 3.02/0.94  --bmc1_unsat_core_extrapolate_axioms    false
% 3.02/0.94  --bmc1_out_stat                         full
% 3.02/0.94  --bmc1_ground_init                      false
% 3.02/0.94  --bmc1_pre_inst_next_state              false
% 3.02/0.94  --bmc1_pre_inst_state                   false
% 3.02/0.94  --bmc1_pre_inst_reach_state             false
% 3.02/0.94  --bmc1_out_unsat_core                   false
% 3.02/0.94  --bmc1_aig_witness_out                  false
% 3.02/0.94  --bmc1_verbose                          false
% 3.02/0.94  --bmc1_dump_clauses_tptp                false
% 3.02/0.94  --bmc1_dump_unsat_core_tptp             false
% 3.02/0.94  --bmc1_dump_file                        -
% 3.02/0.94  --bmc1_ucm_expand_uc_limit              128
% 3.02/0.94  --bmc1_ucm_n_expand_iterations          6
% 3.02/0.94  --bmc1_ucm_extend_mode                  1
% 3.02/0.94  --bmc1_ucm_init_mode                    2
% 3.02/0.94  --bmc1_ucm_cone_mode                    none
% 3.02/0.94  --bmc1_ucm_reduced_relation_type        0
% 3.02/0.94  --bmc1_ucm_relax_model                  4
% 3.02/0.94  --bmc1_ucm_full_tr_after_sat            true
% 3.02/0.94  --bmc1_ucm_expand_neg_assumptions       false
% 3.02/0.94  --bmc1_ucm_layered_model                none
% 3.02/0.94  --bmc1_ucm_max_lemma_size               10
% 3.02/0.94  
% 3.02/0.94  ------ AIG Options
% 3.02/0.94  
% 3.02/0.94  --aig_mode                              false
% 3.02/0.94  
% 3.02/0.94  ------ Instantiation Options
% 3.02/0.94  
% 3.02/0.94  --instantiation_flag                    true
% 3.02/0.94  --inst_sos_flag                         false
% 3.02/0.94  --inst_sos_phase                        true
% 3.02/0.94  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.02/0.94  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.02/0.94  --inst_lit_sel_side                     none
% 3.02/0.94  --inst_solver_per_active                1400
% 3.02/0.94  --inst_solver_calls_frac                1.
% 3.02/0.94  --inst_passive_queue_type               priority_queues
% 3.02/0.94  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.02/0.94  --inst_passive_queues_freq              [25;2]
% 3.02/0.94  --inst_dismatching                      true
% 3.02/0.94  --inst_eager_unprocessed_to_passive     true
% 3.02/0.94  --inst_prop_sim_given                   true
% 3.02/0.94  --inst_prop_sim_new                     false
% 3.02/0.94  --inst_subs_new                         false
% 3.02/0.94  --inst_eq_res_simp                      false
% 3.02/0.94  --inst_subs_given                       false
% 3.02/0.94  --inst_orphan_elimination               true
% 3.02/0.94  --inst_learning_loop_flag               true
% 3.02/0.94  --inst_learning_start                   3000
% 3.02/0.94  --inst_learning_factor                  2
% 3.02/0.94  --inst_start_prop_sim_after_learn       3
% 3.02/0.94  --inst_sel_renew                        solver
% 3.02/0.94  --inst_lit_activity_flag                true
% 3.02/0.94  --inst_restr_to_given                   false
% 3.02/0.94  --inst_activity_threshold               500
% 3.02/0.94  --inst_out_proof                        true
% 3.02/0.94  
% 3.02/0.94  ------ Resolution Options
% 3.02/0.94  
% 3.02/0.94  --resolution_flag                       false
% 3.02/0.94  --res_lit_sel                           adaptive
% 3.02/0.94  --res_lit_sel_side                      none
% 3.02/0.94  --res_ordering                          kbo
% 3.02/0.94  --res_to_prop_solver                    active
% 3.02/0.94  --res_prop_simpl_new                    false
% 3.02/0.94  --res_prop_simpl_given                  true
% 3.02/0.94  --res_passive_queue_type                priority_queues
% 3.02/0.94  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.02/0.94  --res_passive_queues_freq               [15;5]
% 3.02/0.94  --res_forward_subs                      full
% 3.02/0.94  --res_backward_subs                     full
% 3.02/0.94  --res_forward_subs_resolution           true
% 3.02/0.94  --res_backward_subs_resolution          true
% 3.02/0.94  --res_orphan_elimination                true
% 3.02/0.94  --res_time_limit                        2.
% 3.02/0.94  --res_out_proof                         true
% 3.02/0.94  
% 3.02/0.94  ------ Superposition Options
% 3.02/0.94  
% 3.02/0.94  --superposition_flag                    true
% 3.02/0.94  --sup_passive_queue_type                priority_queues
% 3.02/0.94  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.02/0.94  --sup_passive_queues_freq               [8;1;4]
% 3.02/0.94  --demod_completeness_check              fast
% 3.02/0.94  --demod_use_ground                      true
% 3.02/0.94  --sup_to_prop_solver                    passive
% 3.02/0.94  --sup_prop_simpl_new                    true
% 3.02/0.94  --sup_prop_simpl_given                  true
% 3.02/0.94  --sup_fun_splitting                     false
% 3.02/0.94  --sup_smt_interval                      50000
% 3.02/0.94  
% 3.02/0.94  ------ Superposition Simplification Setup
% 3.02/0.94  
% 3.02/0.94  --sup_indices_passive                   []
% 3.02/0.94  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/0.94  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/0.94  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/0.94  --sup_full_triv                         [TrivRules;PropSubs]
% 3.02/0.94  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/0.94  --sup_full_bw                           [BwDemod]
% 3.02/0.94  --sup_immed_triv                        [TrivRules]
% 3.02/0.94  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.02/0.94  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/0.94  --sup_immed_bw_main                     []
% 3.02/0.94  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.02/0.94  --sup_input_triv                        [Unflattening;TrivRules]
% 3.02/0.94  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/0.94  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.02/0.94  
% 3.02/0.94  ------ Combination Options
% 3.02/0.94  
% 3.02/0.94  --comb_res_mult                         3
% 3.02/0.94  --comb_sup_mult                         2
% 3.02/0.94  --comb_inst_mult                        10
% 3.02/0.94  
% 3.02/0.94  ------ Debug Options
% 3.02/0.94  
% 3.02/0.94  --dbg_backtrace                         false
% 3.02/0.94  --dbg_dump_prop_clauses                 false
% 3.02/0.94  --dbg_dump_prop_clauses_file            -
% 3.02/0.94  --dbg_out_stat                          false
% 3.02/0.94  
% 3.02/0.94  
% 3.02/0.94  
% 3.02/0.94  
% 3.02/0.94  ------ Proving...
% 3.02/0.94  
% 3.02/0.94  
% 3.02/0.94  % SZS status Theorem for theBenchmark.p
% 3.02/0.94  
% 3.02/0.94  % SZS output start CNFRefutation for theBenchmark.p
% 3.02/0.94  
% 3.02/0.94  fof(f11,conjecture,(
% 3.02/0.94    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((k2_relset_1(X0,X0,X1) = X0 & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1)) => r2_relset_1(X0,X0,X2,k6_partfun1(X0)))))),
% 3.02/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/0.94  
% 3.02/0.94  fof(f12,negated_conjecture,(
% 3.02/0.94    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((k2_relset_1(X0,X0,X1) = X0 & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1)) => r2_relset_1(X0,X0,X2,k6_partfun1(X0)))))),
% 3.02/0.94    inference(negated_conjecture,[],[f11])).
% 3.02/0.94  
% 3.02/0.94  fof(f26,plain,(
% 3.02/0.94    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & (k2_relset_1(X0,X0,X1) = X0 & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 3.02/0.94    inference(ennf_transformation,[],[f12])).
% 3.02/0.94  
% 3.02/0.94  fof(f27,plain,(
% 3.02/0.94    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & k2_relset_1(X0,X0,X1) = X0 & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 3.02/0.94    inference(flattening,[],[f26])).
% 3.02/0.94  
% 3.02/0.94  fof(f30,plain,(
% 3.02/0.94    ( ! [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & k2_relset_1(X0,X0,X1) = X0 & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (~r2_relset_1(X0,X0,sK2,k6_partfun1(X0)) & k2_relset_1(X0,X0,X1) = X0 & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,sK2),X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(sK2,X0,X0) & v1_funct_1(sK2))) )),
% 3.02/0.94    introduced(choice_axiom,[])).
% 3.02/0.94  
% 3.02/0.94  fof(f29,plain,(
% 3.02/0.94    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & k2_relset_1(X0,X0,X1) = X0 & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK0,sK0,X2,k6_partfun1(sK0)) & k2_relset_1(sK0,sK0,sK1) = sK0 & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 3.02/0.94    introduced(choice_axiom,[])).
% 3.02/0.94  
% 3.02/0.94  fof(f31,plain,(
% 3.02/0.94    (~r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0)) & k2_relset_1(sK0,sK0,sK1) = sK0 & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 3.02/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f30,f29])).
% 3.02/0.94  
% 3.02/0.94  fof(f46,plain,(
% 3.02/0.94    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.02/0.94    inference(cnf_transformation,[],[f31])).
% 3.02/0.94  
% 3.02/0.94  fof(f49,plain,(
% 3.02/0.94    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.02/0.94    inference(cnf_transformation,[],[f31])).
% 3.02/0.94  
% 3.02/0.94  fof(f8,axiom,(
% 3.02/0.94    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.02/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/0.94  
% 3.02/0.94  fof(f22,plain,(
% 3.02/0.94    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.02/0.94    inference(ennf_transformation,[],[f8])).
% 3.02/0.94  
% 3.02/0.94  fof(f23,plain,(
% 3.02/0.94    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.02/0.94    inference(flattening,[],[f22])).
% 3.02/0.94  
% 3.02/0.94  fof(f41,plain,(
% 3.02/0.94    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.02/0.94    inference(cnf_transformation,[],[f23])).
% 3.02/0.94  
% 3.02/0.94  fof(f47,plain,(
% 3.02/0.94    v1_funct_1(sK2)),
% 3.02/0.94    inference(cnf_transformation,[],[f31])).
% 3.02/0.94  
% 3.02/0.94  fof(f6,axiom,(
% 3.02/0.94    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.02/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/0.94  
% 3.02/0.94  fof(f18,plain,(
% 3.02/0.94    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.02/0.94    inference(ennf_transformation,[],[f6])).
% 3.02/0.94  
% 3.02/0.94  fof(f19,plain,(
% 3.02/0.94    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.02/0.94    inference(flattening,[],[f18])).
% 3.02/0.94  
% 3.02/0.94  fof(f28,plain,(
% 3.02/0.94    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.02/0.94    inference(nnf_transformation,[],[f19])).
% 3.02/0.94  
% 3.02/0.94  fof(f37,plain,(
% 3.02/0.94    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.02/0.94    inference(cnf_transformation,[],[f28])).
% 3.02/0.94  
% 3.02/0.94  fof(f50,plain,(
% 3.02/0.94    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),sK1)),
% 3.02/0.94    inference(cnf_transformation,[],[f31])).
% 3.02/0.94  
% 3.02/0.94  fof(f44,plain,(
% 3.02/0.94    v1_funct_1(sK1)),
% 3.02/0.94    inference(cnf_transformation,[],[f31])).
% 3.02/0.94  
% 3.02/0.94  fof(f7,axiom,(
% 3.02/0.94    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 3.02/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/0.94  
% 3.02/0.94  fof(f20,plain,(
% 3.02/0.94    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.02/0.94    inference(ennf_transformation,[],[f7])).
% 3.02/0.94  
% 3.02/0.94  fof(f21,plain,(
% 3.02/0.94    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.02/0.94    inference(flattening,[],[f20])).
% 3.02/0.94  
% 3.02/0.94  fof(f40,plain,(
% 3.02/0.94    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.02/0.94    inference(cnf_transformation,[],[f21])).
% 3.02/0.94  
% 3.02/0.94  fof(f5,axiom,(
% 3.02/0.94    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.02/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/0.94  
% 3.02/0.94  fof(f17,plain,(
% 3.02/0.94    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.02/0.94    inference(ennf_transformation,[],[f5])).
% 3.02/0.94  
% 3.02/0.94  fof(f36,plain,(
% 3.02/0.94    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.02/0.94    inference(cnf_transformation,[],[f17])).
% 3.02/0.94  
% 3.02/0.94  fof(f51,plain,(
% 3.02/0.94    k2_relset_1(sK0,sK0,sK1) = sK0),
% 3.02/0.94    inference(cnf_transformation,[],[f31])).
% 3.02/0.94  
% 3.02/0.94  fof(f3,axiom,(
% 3.02/0.94    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = X0 & k2_relat_1(X0) = k1_relat_1(X1)) => k6_relat_1(k1_relat_1(X1)) = X1)))),
% 3.02/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/0.94  
% 3.02/0.94  fof(f14,plain,(
% 3.02/0.94    ! [X0] : (! [X1] : ((k6_relat_1(k1_relat_1(X1)) = X1 | (k5_relat_1(X0,X1) != X0 | k2_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.02/0.94    inference(ennf_transformation,[],[f3])).
% 3.02/0.94  
% 3.02/0.94  fof(f15,plain,(
% 3.02/0.94    ! [X0] : (! [X1] : (k6_relat_1(k1_relat_1(X1)) = X1 | k5_relat_1(X0,X1) != X0 | k2_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.02/0.94    inference(flattening,[],[f14])).
% 3.02/0.94  
% 3.02/0.94  fof(f34,plain,(
% 3.02/0.94    ( ! [X0,X1] : (k6_relat_1(k1_relat_1(X1)) = X1 | k5_relat_1(X0,X1) != X0 | k2_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.02/0.94    inference(cnf_transformation,[],[f15])).
% 3.02/0.94  
% 3.02/0.94  fof(f9,axiom,(
% 3.02/0.94    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.02/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/0.94  
% 3.02/0.94  fof(f42,plain,(
% 3.02/0.94    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.02/0.94    inference(cnf_transformation,[],[f9])).
% 3.02/0.94  
% 3.02/0.94  fof(f53,plain,(
% 3.02/0.94    ( ! [X0,X1] : (k6_partfun1(k1_relat_1(X1)) = X1 | k5_relat_1(X0,X1) != X0 | k2_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.02/0.94    inference(definition_unfolding,[],[f34,f42])).
% 3.02/0.94  
% 3.02/0.94  fof(f2,axiom,(
% 3.02/0.94    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.02/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/0.94  
% 3.02/0.94  fof(f33,plain,(
% 3.02/0.94    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.02/0.94    inference(cnf_transformation,[],[f2])).
% 3.02/0.94  
% 3.02/0.94  fof(f1,axiom,(
% 3.02/0.94    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.02/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/0.94  
% 3.02/0.94  fof(f13,plain,(
% 3.02/0.94    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.02/0.94    inference(ennf_transformation,[],[f1])).
% 3.02/0.94  
% 3.02/0.94  fof(f32,plain,(
% 3.02/0.94    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.02/0.94    inference(cnf_transformation,[],[f13])).
% 3.02/0.94  
% 3.02/0.94  fof(f4,axiom,(
% 3.02/0.94    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.02/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/0.94  
% 3.02/0.94  fof(f16,plain,(
% 3.02/0.94    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.02/0.94    inference(ennf_transformation,[],[f4])).
% 3.02/0.94  
% 3.02/0.94  fof(f35,plain,(
% 3.02/0.94    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.02/0.94    inference(cnf_transformation,[],[f16])).
% 3.02/0.94  
% 3.02/0.94  fof(f10,axiom,(
% 3.02/0.94    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 3.02/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/0.94  
% 3.02/0.94  fof(f24,plain,(
% 3.02/0.94    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.02/0.94    inference(ennf_transformation,[],[f10])).
% 3.02/0.94  
% 3.02/0.94  fof(f25,plain,(
% 3.02/0.94    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.02/0.94    inference(flattening,[],[f24])).
% 3.02/0.94  
% 3.02/0.94  fof(f43,plain,(
% 3.02/0.94    ( ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.02/0.94    inference(cnf_transformation,[],[f25])).
% 3.02/0.94  
% 3.02/0.94  fof(f48,plain,(
% 3.02/0.94    v1_funct_2(sK2,sK0,sK0)),
% 3.02/0.94    inference(cnf_transformation,[],[f31])).
% 3.02/0.94  
% 3.02/0.94  fof(f38,plain,(
% 3.02/0.94    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.02/0.94    inference(cnf_transformation,[],[f28])).
% 3.02/0.94  
% 3.02/0.94  fof(f54,plain,(
% 3.02/0.94    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.02/0.94    inference(equality_resolution,[],[f38])).
% 3.02/0.94  
% 3.02/0.94  fof(f52,plain,(
% 3.02/0.94    ~r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0))),
% 3.02/0.94    inference(cnf_transformation,[],[f31])).
% 3.02/0.94  
% 3.02/0.94  cnf(c_398,plain,
% 3.02/0.94      ( ~ m1_subset_1(X0_45,X0_47)
% 3.02/0.94      | m1_subset_1(X1_45,X1_47)
% 3.02/0.94      | X1_47 != X0_47
% 3.02/0.94      | X1_45 != X0_45 ),
% 3.02/0.94      theory(equality) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_925,plain,
% 3.02/0.94      ( m1_subset_1(X0_45,X0_47)
% 3.02/0.94      | ~ m1_subset_1(X1_45,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.02/0.94      | X0_47 != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
% 3.02/0.94      | X0_45 != X1_45 ),
% 3.02/0.94      inference(instantiation,[status(thm)],[c_398]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_1040,plain,
% 3.02/0.94      ( m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)))
% 3.02/0.94      | ~ m1_subset_1(X1_45,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.02/0.94      | k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
% 3.02/0.94      | X0_45 != X1_45 ),
% 3.02/0.94      inference(instantiation,[status(thm)],[c_925]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_2353,plain,
% 3.02/0.94      ( ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.02/0.94      | m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.02/0.94      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
% 3.02/0.94      | k6_partfun1(sK0) != X0_45 ),
% 3.02/0.94      inference(instantiation,[status(thm)],[c_1040]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_5733,plain,
% 3.02/0.94      ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.02/0.94      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.02/0.94      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
% 3.02/0.94      | k6_partfun1(sK0) != sK2 ),
% 3.02/0.94      inference(instantiation,[status(thm)],[c_2353]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_17,negated_conjecture,
% 3.02/0.94      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.02/0.94      inference(cnf_transformation,[],[f46]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_378,negated_conjecture,
% 3.02/0.94      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.02/0.94      inference(subtyping,[status(esa)],[c_17]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_683,plain,
% 3.02/0.94      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.02/0.94      inference(predicate_to_equality,[status(thm)],[c_378]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_14,negated_conjecture,
% 3.02/0.94      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.02/0.94      inference(cnf_transformation,[],[f49]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_380,negated_conjecture,
% 3.02/0.94      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.02/0.94      inference(subtyping,[status(esa)],[c_14]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_681,plain,
% 3.02/0.94      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.02/0.94      inference(predicate_to_equality,[status(thm)],[c_380]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_9,plain,
% 3.02/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.02/0.94      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.02/0.94      | ~ v1_funct_1(X0)
% 3.02/0.94      | ~ v1_funct_1(X3)
% 3.02/0.94      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.02/0.94      inference(cnf_transformation,[],[f41]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_382,plain,
% 3.02/0.94      ( ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)))
% 3.02/0.94      | ~ m1_subset_1(X1_45,k1_zfmisc_1(k2_zfmisc_1(X2_46,X3_46)))
% 3.02/0.94      | ~ v1_funct_1(X0_45)
% 3.02/0.94      | ~ v1_funct_1(X1_45)
% 3.02/0.94      | k1_partfun1(X2_46,X3_46,X0_46,X1_46,X1_45,X0_45) = k5_relat_1(X1_45,X0_45) ),
% 3.02/0.94      inference(subtyping,[status(esa)],[c_9]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_680,plain,
% 3.02/0.94      ( k1_partfun1(X0_46,X1_46,X2_46,X3_46,X0_45,X1_45) = k5_relat_1(X0_45,X1_45)
% 3.02/0.94      | m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) != iProver_top
% 3.02/0.94      | m1_subset_1(X1_45,k1_zfmisc_1(k2_zfmisc_1(X2_46,X3_46))) != iProver_top
% 3.02/0.94      | v1_funct_1(X0_45) != iProver_top
% 3.02/0.94      | v1_funct_1(X1_45) != iProver_top ),
% 3.02/0.94      inference(predicate_to_equality,[status(thm)],[c_382]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_1283,plain,
% 3.02/0.94      ( k1_partfun1(X0_46,X1_46,sK0,sK0,X0_45,sK2) = k5_relat_1(X0_45,sK2)
% 3.02/0.94      | m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) != iProver_top
% 3.02/0.94      | v1_funct_1(X0_45) != iProver_top
% 3.02/0.94      | v1_funct_1(sK2) != iProver_top ),
% 3.02/0.94      inference(superposition,[status(thm)],[c_681,c_680]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_16,negated_conjecture,
% 3.02/0.94      ( v1_funct_1(sK2) ),
% 3.02/0.94      inference(cnf_transformation,[],[f47]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_23,plain,
% 3.02/0.94      ( v1_funct_1(sK2) = iProver_top ),
% 3.02/0.94      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_1433,plain,
% 3.02/0.94      ( v1_funct_1(X0_45) != iProver_top
% 3.02/0.94      | m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) != iProver_top
% 3.02/0.94      | k1_partfun1(X0_46,X1_46,sK0,sK0,X0_45,sK2) = k5_relat_1(X0_45,sK2) ),
% 3.02/0.94      inference(global_propositional_subsumption,
% 3.02/0.94                [status(thm)],
% 3.02/0.94                [c_1283,c_23]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_1434,plain,
% 3.02/0.94      ( k1_partfun1(X0_46,X1_46,sK0,sK0,X0_45,sK2) = k5_relat_1(X0_45,sK2)
% 3.02/0.94      | m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) != iProver_top
% 3.02/0.94      | v1_funct_1(X0_45) != iProver_top ),
% 3.02/0.94      inference(renaming,[status(thm)],[c_1433]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_1443,plain,
% 3.02/0.94      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2)
% 3.02/0.94      | v1_funct_1(sK1) != iProver_top ),
% 3.02/0.94      inference(superposition,[status(thm)],[c_683,c_1434]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_6,plain,
% 3.02/0.94      ( ~ r2_relset_1(X0,X1,X2,X3)
% 3.02/0.94      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.02/0.94      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.02/0.94      | X3 = X2 ),
% 3.02/0.94      inference(cnf_transformation,[],[f37]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_13,negated_conjecture,
% 3.02/0.94      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),sK1) ),
% 3.02/0.94      inference(cnf_transformation,[],[f50]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_238,plain,
% 3.02/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.02/0.94      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.02/0.94      | X3 = X0
% 3.02/0.94      | k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) != X0
% 3.02/0.94      | sK1 != X3
% 3.02/0.94      | sK0 != X2
% 3.02/0.94      | sK0 != X1 ),
% 3.02/0.94      inference(resolution_lifted,[status(thm)],[c_6,c_13]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_239,plain,
% 3.02/0.94      ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.02/0.94      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.02/0.94      | sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) ),
% 3.02/0.94      inference(unflattening,[status(thm)],[c_238]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_241,plain,
% 3.02/0.94      ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.02/0.94      | sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) ),
% 3.02/0.94      inference(global_propositional_subsumption,
% 3.02/0.94                [status(thm)],
% 3.02/0.94                [c_239,c_17]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_373,plain,
% 3.02/0.94      ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.02/0.94      | sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) ),
% 3.02/0.94      inference(subtyping,[status(esa)],[c_241]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_686,plain,
% 3.02/0.94      ( sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2)
% 3.02/0.94      | m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.02/0.94      inference(predicate_to_equality,[status(thm)],[c_373]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_19,negated_conjecture,
% 3.02/0.94      ( v1_funct_1(sK1) ),
% 3.02/0.94      inference(cnf_transformation,[],[f44]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_7,plain,
% 3.02/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.02/0.94      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.02/0.94      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.02/0.94      | ~ v1_funct_1(X0)
% 3.02/0.94      | ~ v1_funct_1(X3) ),
% 3.02/0.94      inference(cnf_transformation,[],[f40]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_384,plain,
% 3.02/0.94      ( ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)))
% 3.02/0.94      | ~ m1_subset_1(X1_45,k1_zfmisc_1(k2_zfmisc_1(X2_46,X3_46)))
% 3.02/0.94      | m1_subset_1(k1_partfun1(X2_46,X3_46,X0_46,X1_46,X1_45,X0_45),k1_zfmisc_1(k2_zfmisc_1(X2_46,X1_46)))
% 3.02/0.94      | ~ v1_funct_1(X0_45)
% 3.02/0.94      | ~ v1_funct_1(X1_45) ),
% 3.02/0.94      inference(subtyping,[status(esa)],[c_7]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_841,plain,
% 3.02/0.94      ( m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.02/0.94      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.02/0.94      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.02/0.94      | ~ v1_funct_1(sK1)
% 3.02/0.94      | ~ v1_funct_1(sK2) ),
% 3.02/0.94      inference(instantiation,[status(thm)],[c_384]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_1145,plain,
% 3.02/0.94      ( sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) ),
% 3.02/0.94      inference(global_propositional_subsumption,
% 3.02/0.94                [status(thm)],
% 3.02/0.94                [c_686,c_19,c_17,c_16,c_14,c_373,c_841]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_1459,plain,
% 3.02/0.94      ( k5_relat_1(sK1,sK2) = sK1 | v1_funct_1(sK1) != iProver_top ),
% 3.02/0.94      inference(light_normalisation,[status(thm)],[c_1443,c_1145]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_20,plain,
% 3.02/0.94      ( v1_funct_1(sK1) = iProver_top ),
% 3.02/0.94      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_1749,plain,
% 3.02/0.94      ( k5_relat_1(sK1,sK2) = sK1 ),
% 3.02/0.94      inference(global_propositional_subsumption,
% 3.02/0.94                [status(thm)],
% 3.02/0.94                [c_1459,c_20]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_4,plain,
% 3.02/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.02/0.94      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.02/0.94      inference(cnf_transformation,[],[f36]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_385,plain,
% 3.02/0.94      ( ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)))
% 3.02/0.94      | k2_relset_1(X0_46,X1_46,X0_45) = k2_relat_1(X0_45) ),
% 3.02/0.94      inference(subtyping,[status(esa)],[c_4]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_677,plain,
% 3.02/0.94      ( k2_relset_1(X0_46,X1_46,X0_45) = k2_relat_1(X0_45)
% 3.02/0.94      | m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) != iProver_top ),
% 3.02/0.94      inference(predicate_to_equality,[status(thm)],[c_385]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_972,plain,
% 3.02/0.94      ( k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) ),
% 3.02/0.94      inference(superposition,[status(thm)],[c_683,c_677]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_12,negated_conjecture,
% 3.02/0.94      ( k2_relset_1(sK0,sK0,sK1) = sK0 ),
% 3.02/0.94      inference(cnf_transformation,[],[f51]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_381,negated_conjecture,
% 3.02/0.94      ( k2_relset_1(sK0,sK0,sK1) = sK0 ),
% 3.02/0.94      inference(subtyping,[status(esa)],[c_12]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_974,plain,
% 3.02/0.94      ( k2_relat_1(sK1) = sK0 ),
% 3.02/0.94      inference(light_normalisation,[status(thm)],[c_972,c_381]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_2,plain,
% 3.02/0.94      ( ~ v1_funct_1(X0)
% 3.02/0.94      | ~ v1_funct_1(X1)
% 3.02/0.94      | ~ v1_relat_1(X1)
% 3.02/0.94      | ~ v1_relat_1(X0)
% 3.02/0.94      | k5_relat_1(X1,X0) != X1
% 3.02/0.94      | k2_relat_1(X1) != k1_relat_1(X0)
% 3.02/0.94      | k6_partfun1(k1_relat_1(X0)) = X0 ),
% 3.02/0.94      inference(cnf_transformation,[],[f53]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_387,plain,
% 3.02/0.94      ( ~ v1_funct_1(X0_45)
% 3.02/0.94      | ~ v1_funct_1(X1_45)
% 3.02/0.94      | ~ v1_relat_1(X1_45)
% 3.02/0.94      | ~ v1_relat_1(X0_45)
% 3.02/0.94      | k2_relat_1(X1_45) != k1_relat_1(X0_45)
% 3.02/0.94      | k5_relat_1(X1_45,X0_45) != X1_45
% 3.02/0.94      | k6_partfun1(k1_relat_1(X0_45)) = X0_45 ),
% 3.02/0.94      inference(subtyping,[status(esa)],[c_2]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_675,plain,
% 3.02/0.94      ( k2_relat_1(X0_45) != k1_relat_1(X1_45)
% 3.02/0.94      | k5_relat_1(X0_45,X1_45) != X0_45
% 3.02/0.94      | k6_partfun1(k1_relat_1(X1_45)) = X1_45
% 3.02/0.94      | v1_funct_1(X0_45) != iProver_top
% 3.02/0.94      | v1_funct_1(X1_45) != iProver_top
% 3.02/0.94      | v1_relat_1(X1_45) != iProver_top
% 3.02/0.94      | v1_relat_1(X0_45) != iProver_top ),
% 3.02/0.94      inference(predicate_to_equality,[status(thm)],[c_387]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_1209,plain,
% 3.02/0.94      ( k1_relat_1(X0_45) != sK0
% 3.02/0.94      | k5_relat_1(sK1,X0_45) != sK1
% 3.02/0.94      | k6_partfun1(k1_relat_1(X0_45)) = X0_45
% 3.02/0.94      | v1_funct_1(X0_45) != iProver_top
% 3.02/0.94      | v1_funct_1(sK1) != iProver_top
% 3.02/0.94      | v1_relat_1(X0_45) != iProver_top
% 3.02/0.94      | v1_relat_1(sK1) != iProver_top ),
% 3.02/0.94      inference(superposition,[status(thm)],[c_974,c_675]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_22,plain,
% 3.02/0.94      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.02/0.94      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_1,plain,
% 3.02/0.94      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.02/0.94      inference(cnf_transformation,[],[f33]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_55,plain,
% 3.02/0.94      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.02/0.94      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_57,plain,
% 3.02/0.94      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) = iProver_top ),
% 3.02/0.94      inference(instantiation,[status(thm)],[c_55]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_0,plain,
% 3.02/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.02/0.94      | ~ v1_relat_1(X1)
% 3.02/0.94      | v1_relat_1(X0) ),
% 3.02/0.94      inference(cnf_transformation,[],[f32]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_389,plain,
% 3.02/0.94      ( ~ m1_subset_1(X0_45,k1_zfmisc_1(X1_45))
% 3.02/0.94      | ~ v1_relat_1(X1_45)
% 3.02/0.94      | v1_relat_1(X0_45) ),
% 3.02/0.94      inference(subtyping,[status(esa)],[c_0]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_807,plain,
% 3.02/0.94      ( ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)))
% 3.02/0.94      | v1_relat_1(X0_45)
% 3.02/0.94      | ~ v1_relat_1(k2_zfmisc_1(X0_46,X1_46)) ),
% 3.02/0.94      inference(instantiation,[status(thm)],[c_389]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_808,plain,
% 3.02/0.94      ( m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) != iProver_top
% 3.02/0.94      | v1_relat_1(X0_45) = iProver_top
% 3.02/0.94      | v1_relat_1(k2_zfmisc_1(X0_46,X1_46)) != iProver_top ),
% 3.02/0.94      inference(predicate_to_equality,[status(thm)],[c_807]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_810,plain,
% 3.02/0.94      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.02/0.94      | v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
% 3.02/0.94      | v1_relat_1(sK1) = iProver_top ),
% 3.02/0.94      inference(instantiation,[status(thm)],[c_808]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_1739,plain,
% 3.02/0.94      ( v1_relat_1(X0_45) != iProver_top
% 3.02/0.94      | k1_relat_1(X0_45) != sK0
% 3.02/0.94      | k5_relat_1(sK1,X0_45) != sK1
% 3.02/0.94      | k6_partfun1(k1_relat_1(X0_45)) = X0_45
% 3.02/0.94      | v1_funct_1(X0_45) != iProver_top ),
% 3.02/0.94      inference(global_propositional_subsumption,
% 3.02/0.94                [status(thm)],
% 3.02/0.94                [c_1209,c_20,c_22,c_57,c_810]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_1740,plain,
% 3.02/0.94      ( k1_relat_1(X0_45) != sK0
% 3.02/0.94      | k5_relat_1(sK1,X0_45) != sK1
% 3.02/0.94      | k6_partfun1(k1_relat_1(X0_45)) = X0_45
% 3.02/0.94      | v1_funct_1(X0_45) != iProver_top
% 3.02/0.94      | v1_relat_1(X0_45) != iProver_top ),
% 3.02/0.94      inference(renaming,[status(thm)],[c_1739]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_1752,plain,
% 3.02/0.94      ( k1_relat_1(sK2) != sK0
% 3.02/0.94      | k6_partfun1(k1_relat_1(sK2)) = sK2
% 3.02/0.94      | v1_funct_1(sK2) != iProver_top
% 3.02/0.94      | v1_relat_1(sK2) != iProver_top ),
% 3.02/0.94      inference(superposition,[status(thm)],[c_1749,c_1740]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_3,plain,
% 3.02/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.02/0.94      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.02/0.94      inference(cnf_transformation,[],[f35]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_386,plain,
% 3.02/0.94      ( ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)))
% 3.02/0.94      | k1_relset_1(X0_46,X1_46,X0_45) = k1_relat_1(X0_45) ),
% 3.02/0.94      inference(subtyping,[status(esa)],[c_3]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_676,plain,
% 3.02/0.94      ( k1_relset_1(X0_46,X1_46,X0_45) = k1_relat_1(X0_45)
% 3.02/0.94      | m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) != iProver_top ),
% 3.02/0.94      inference(predicate_to_equality,[status(thm)],[c_386]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_960,plain,
% 3.02/0.94      ( k1_relset_1(sK0,sK0,sK2) = k1_relat_1(sK2) ),
% 3.02/0.94      inference(superposition,[status(thm)],[c_681,c_676]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_10,plain,
% 3.02/0.94      ( ~ v1_funct_2(X0,X1,X1)
% 3.02/0.94      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.02/0.94      | ~ v1_funct_1(X0)
% 3.02/0.94      | k1_relset_1(X1,X1,X0) = X1 ),
% 3.02/0.94      inference(cnf_transformation,[],[f43]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_15,negated_conjecture,
% 3.02/0.94      ( v1_funct_2(sK2,sK0,sK0) ),
% 3.02/0.94      inference(cnf_transformation,[],[f48]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_208,plain,
% 3.02/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.02/0.94      | ~ v1_funct_1(X0)
% 3.02/0.94      | k1_relset_1(X1,X1,X0) = X1
% 3.02/0.94      | sK2 != X0
% 3.02/0.94      | sK0 != X1 ),
% 3.02/0.94      inference(resolution_lifted,[status(thm)],[c_10,c_15]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_209,plain,
% 3.02/0.94      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.02/0.94      | ~ v1_funct_1(sK2)
% 3.02/0.94      | k1_relset_1(sK0,sK0,sK2) = sK0 ),
% 3.02/0.94      inference(unflattening,[status(thm)],[c_208]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_211,plain,
% 3.02/0.94      ( k1_relset_1(sK0,sK0,sK2) = sK0 ),
% 3.02/0.94      inference(global_propositional_subsumption,
% 3.02/0.94                [status(thm)],
% 3.02/0.94                [c_209,c_16,c_14]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_376,plain,
% 3.02/0.94      ( k1_relset_1(sK0,sK0,sK2) = sK0 ),
% 3.02/0.94      inference(subtyping,[status(esa)],[c_211]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_966,plain,
% 3.02/0.94      ( k1_relat_1(sK2) = sK0 ),
% 3.02/0.94      inference(light_normalisation,[status(thm)],[c_960,c_376]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_1753,plain,
% 3.02/0.94      ( sK0 != sK0
% 3.02/0.94      | k6_partfun1(sK0) = sK2
% 3.02/0.94      | v1_funct_1(sK2) != iProver_top
% 3.02/0.94      | v1_relat_1(sK2) != iProver_top ),
% 3.02/0.94      inference(light_normalisation,[status(thm)],[c_1752,c_966]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_1754,plain,
% 3.02/0.94      ( k6_partfun1(sK0) = sK2
% 3.02/0.94      | v1_funct_1(sK2) != iProver_top
% 3.02/0.94      | v1_relat_1(sK2) != iProver_top ),
% 3.02/0.94      inference(equality_resolution_simp,[status(thm)],[c_1753]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_673,plain,
% 3.02/0.94      ( m1_subset_1(X0_45,k1_zfmisc_1(X1_45)) != iProver_top
% 3.02/0.94      | v1_relat_1(X1_45) != iProver_top
% 3.02/0.94      | v1_relat_1(X0_45) = iProver_top ),
% 3.02/0.94      inference(predicate_to_equality,[status(thm)],[c_389]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_911,plain,
% 3.02/0.94      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
% 3.02/0.94      | v1_relat_1(sK2) = iProver_top ),
% 3.02/0.94      inference(superposition,[status(thm)],[c_681,c_673]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_394,plain,
% 3.02/0.94      ( X0_45 != X1_45 | X2_45 != X1_45 | X2_45 = X0_45 ),
% 3.02/0.94      theory(equality) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_818,plain,
% 3.02/0.94      ( k6_partfun1(sK0) != X0_45
% 3.02/0.94      | sK2 != X0_45
% 3.02/0.94      | sK2 = k6_partfun1(sK0) ),
% 3.02/0.94      inference(instantiation,[status(thm)],[c_394]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_898,plain,
% 3.02/0.94      ( k6_partfun1(sK0) != sK2 | sK2 = k6_partfun1(sK0) | sK2 != sK2 ),
% 3.02/0.94      inference(instantiation,[status(thm)],[c_818]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_393,plain,( X0_47 = X0_47 ),theory(equality) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_858,plain,
% 3.02/0.94      ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
% 3.02/0.94      inference(instantiation,[status(thm)],[c_393]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_391,plain,( X0_45 = X0_45 ),theory(equality) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_850,plain,
% 3.02/0.94      ( sK2 = sK2 ),
% 3.02/0.94      inference(instantiation,[status(thm)],[c_391]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_5,plain,
% 3.02/0.94      ( r2_relset_1(X0,X1,X2,X2)
% 3.02/0.94      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.02/0.94      inference(cnf_transformation,[],[f54]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_11,negated_conjecture,
% 3.02/0.94      ( ~ r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0)) ),
% 3.02/0.94      inference(cnf_transformation,[],[f52]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_228,plain,
% 3.02/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.02/0.94      | k6_partfun1(sK0) != X0
% 3.02/0.94      | sK2 != X0
% 3.02/0.94      | sK0 != X2
% 3.02/0.94      | sK0 != X1 ),
% 3.02/0.94      inference(resolution_lifted,[status(thm)],[c_5,c_11]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_229,plain,
% 3.02/0.94      ( ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.02/0.94      | sK2 != k6_partfun1(sK0) ),
% 3.02/0.94      inference(unflattening,[status(thm)],[c_228]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(c_374,plain,
% 3.02/0.94      ( ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.02/0.94      | sK2 != k6_partfun1(sK0) ),
% 3.02/0.94      inference(subtyping,[status(esa)],[c_229]) ).
% 3.02/0.94  
% 3.02/0.94  cnf(contradiction,plain,
% 3.02/0.94      ( $false ),
% 3.02/0.94      inference(minisat,
% 3.02/0.94                [status(thm)],
% 3.02/0.94                [c_5733,c_1754,c_911,c_898,c_858,c_850,c_374,c_57,c_14,
% 3.02/0.94                 c_23]) ).
% 3.02/0.94  
% 3.02/0.94  
% 3.02/0.94  % SZS output end CNFRefutation for theBenchmark.p
% 3.02/0.94  
% 3.02/0.94  ------                               Statistics
% 3.02/0.94  
% 3.02/0.94  ------ General
% 3.02/0.94  
% 3.02/0.94  abstr_ref_over_cycles:                  0
% 3.02/0.94  abstr_ref_under_cycles:                 0
% 3.02/0.94  gc_basic_clause_elim:                   0
% 3.02/0.94  forced_gc_time:                         0
% 3.02/0.94  parsing_time:                           0.008
% 3.02/0.94  unif_index_cands_time:                  0.
% 3.02/0.94  unif_index_add_time:                    0.
% 3.02/0.94  orderings_time:                         0.
% 3.02/0.94  out_proof_time:                         0.008
% 3.02/0.94  total_time:                             0.248
% 3.02/0.94  num_of_symbols:                         51
% 3.02/0.94  num_of_terms:                           4276
% 3.02/0.94  
% 3.02/0.94  ------ Preprocessing
% 3.02/0.94  
% 3.02/0.94  num_of_splits:                          0
% 3.02/0.94  num_of_split_atoms:                     0
% 3.02/0.94  num_of_reused_defs:                     0
% 3.02/0.94  num_eq_ax_congr_red:                    15
% 3.02/0.94  num_of_sem_filtered_clauses:            1
% 3.02/0.94  num_of_subtypes:                        3
% 3.02/0.94  monotx_restored_types:                  0
% 3.02/0.94  sat_num_of_epr_types:                   0
% 3.02/0.94  sat_num_of_non_cyclic_types:            0
% 3.02/0.94  sat_guarded_non_collapsed_types:        1
% 3.02/0.94  num_pure_diseq_elim:                    0
% 3.02/0.94  simp_replaced_by:                       0
% 3.02/0.94  res_preprocessed:                       103
% 3.02/0.94  prep_upred:                             0
% 3.02/0.94  prep_unflattend:                        15
% 3.02/0.94  smt_new_axioms:                         0
% 3.02/0.94  pred_elim_cands:                        3
% 3.02/0.94  pred_elim:                              2
% 3.02/0.94  pred_elim_cl:                           2
% 3.02/0.94  pred_elim_cycles:                       4
% 3.02/0.94  merged_defs:                            0
% 3.02/0.94  merged_defs_ncl:                        0
% 3.02/0.94  bin_hyper_res:                          0
% 3.02/0.94  prep_cycles:                            4
% 3.02/0.94  pred_elim_time:                         0.002
% 3.02/0.94  splitting_time:                         0.
% 3.02/0.94  sem_filter_time:                        0.
% 3.02/0.94  monotx_time:                            0.
% 3.02/0.94  subtype_inf_time:                       0.
% 3.02/0.94  
% 3.02/0.94  ------ Problem properties
% 3.02/0.94  
% 3.02/0.94  clauses:                                18
% 3.02/0.94  conjectures:                            5
% 3.02/0.94  epr:                                    2
% 3.02/0.94  horn:                                   18
% 3.02/0.94  ground:                                 10
% 3.02/0.94  unary:                                  8
% 3.02/0.94  binary:                                 5
% 3.02/0.94  lits:                                   43
% 3.02/0.94  lits_eq:                                13
% 3.02/0.94  fd_pure:                                0
% 3.02/0.94  fd_pseudo:                              0
% 3.02/0.94  fd_cond:                                0
% 3.02/0.94  fd_pseudo_cond:                         0
% 3.02/0.94  ac_symbols:                             0
% 3.02/0.94  
% 3.02/0.94  ------ Propositional Solver
% 3.02/0.94  
% 3.02/0.94  prop_solver_calls:                      33
% 3.02/0.94  prop_fast_solver_calls:                 846
% 3.02/0.94  smt_solver_calls:                       0
% 3.02/0.94  smt_fast_solver_calls:                  0
% 3.02/0.94  prop_num_of_clauses:                    1523
% 3.02/0.94  prop_preprocess_simplified:             4323
% 3.02/0.94  prop_fo_subsumed:                       61
% 3.02/0.94  prop_solver_time:                       0.
% 3.02/0.94  smt_solver_time:                        0.
% 3.02/0.94  smt_fast_solver_time:                   0.
% 3.02/0.94  prop_fast_solver_time:                  0.
% 3.02/0.94  prop_unsat_core_time:                   0.
% 3.02/0.94  
% 3.02/0.94  ------ QBF
% 3.02/0.94  
% 3.02/0.94  qbf_q_res:                              0
% 3.02/0.94  qbf_num_tautologies:                    0
% 3.02/0.94  qbf_prep_cycles:                        0
% 3.02/0.94  
% 3.02/0.94  ------ BMC1
% 3.02/0.94  
% 3.02/0.94  bmc1_current_bound:                     -1
% 3.02/0.94  bmc1_last_solved_bound:                 -1
% 3.02/0.94  bmc1_unsat_core_size:                   -1
% 3.02/0.94  bmc1_unsat_core_parents_size:           -1
% 3.02/0.94  bmc1_merge_next_fun:                    0
% 3.02/0.94  bmc1_unsat_core_clauses_time:           0.
% 3.02/0.94  
% 3.02/0.94  ------ Instantiation
% 3.02/0.94  
% 3.02/0.94  inst_num_of_clauses:                    616
% 3.02/0.94  inst_num_in_passive:                    222
% 3.02/0.94  inst_num_in_active:                     342
% 3.02/0.94  inst_num_in_unprocessed:                51
% 3.02/0.94  inst_num_of_loops:                      372
% 3.02/0.94  inst_num_of_learning_restarts:          0
% 3.02/0.94  inst_num_moves_active_passive:          18
% 3.02/0.94  inst_lit_activity:                      0
% 3.02/0.94  inst_lit_activity_moves:                0
% 3.02/0.94  inst_num_tautologies:                   0
% 3.02/0.94  inst_num_prop_implied:                  0
% 3.02/0.94  inst_num_existing_simplified:           0
% 3.02/0.94  inst_num_eq_res_simplified:             0
% 3.02/0.94  inst_num_child_elim:                    0
% 3.02/0.94  inst_num_of_dismatching_blockings:      401
% 3.02/0.94  inst_num_of_non_proper_insts:           876
% 3.02/0.94  inst_num_of_duplicates:                 0
% 3.02/0.94  inst_inst_num_from_inst_to_res:         0
% 3.02/0.94  inst_dismatching_checking_time:         0.
% 3.02/0.94  
% 3.02/0.94  ------ Resolution
% 3.02/0.94  
% 3.02/0.94  res_num_of_clauses:                     0
% 3.02/0.94  res_num_in_passive:                     0
% 3.02/0.94  res_num_in_active:                      0
% 3.02/0.94  res_num_of_loops:                       107
% 3.02/0.94  res_forward_subset_subsumed:            52
% 3.02/0.94  res_backward_subset_subsumed:           0
% 3.02/0.94  res_forward_subsumed:                   0
% 3.02/0.94  res_backward_subsumed:                  0
% 3.02/0.94  res_forward_subsumption_resolution:     0
% 3.02/0.94  res_backward_subsumption_resolution:    0
% 3.02/0.94  res_clause_to_clause_subsumption:       457
% 3.02/0.94  res_orphan_elimination:                 0
% 3.02/0.94  res_tautology_del:                      134
% 3.02/0.94  res_num_eq_res_simplified:              1
% 3.02/0.94  res_num_sel_changes:                    0
% 3.02/0.94  res_moves_from_active_to_pass:          0
% 3.02/0.94  
% 3.02/0.94  ------ Superposition
% 3.02/0.94  
% 3.02/0.94  sup_time_total:                         0.
% 3.02/0.94  sup_time_generating:                    0.
% 3.02/0.94  sup_time_sim_full:                      0.
% 3.02/0.94  sup_time_sim_immed:                     0.
% 3.02/0.94  
% 3.02/0.94  sup_num_of_clauses:                     169
% 3.02/0.94  sup_num_in_active:                      73
% 3.02/0.94  sup_num_in_passive:                     96
% 3.02/0.94  sup_num_of_loops:                       74
% 3.02/0.94  sup_fw_superposition:                   108
% 3.02/0.94  sup_bw_superposition:                   62
% 3.02/0.94  sup_immediate_simplified:               36
% 3.02/0.94  sup_given_eliminated:                   0
% 3.02/0.94  comparisons_done:                       0
% 3.02/0.94  comparisons_avoided:                    0
% 3.02/0.94  
% 3.02/0.94  ------ Simplifications
% 3.02/0.94  
% 3.02/0.94  
% 3.02/0.94  sim_fw_subset_subsumed:                 4
% 3.02/0.94  sim_bw_subset_subsumed:                 0
% 3.02/0.94  sim_fw_subsumed:                        0
% 3.02/0.94  sim_bw_subsumed:                        0
% 3.02/0.94  sim_fw_subsumption_res:                 2
% 3.02/0.94  sim_bw_subsumption_res:                 0
% 3.02/0.94  sim_tautology_del:                      1
% 3.02/0.94  sim_eq_tautology_del:                   11
% 3.02/0.94  sim_eq_res_simp:                        1
% 3.02/0.94  sim_fw_demodulated:                     0
% 3.02/0.94  sim_bw_demodulated:                     1
% 3.02/0.94  sim_light_normalised:                   34
% 3.02/0.94  sim_joinable_taut:                      0
% 3.02/0.94  sim_joinable_simp:                      0
% 3.02/0.94  sim_ac_normalised:                      0
% 3.02/0.94  sim_smt_subsumption:                    0
% 3.02/0.94  
%------------------------------------------------------------------------------
