%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:06:49 EST 2020

% Result     : Theorem 3.66s
% Output     : CNFRefutation 3.66s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 456 expanded)
%              Number of clauses        :   97 ( 145 expanded)
%              Number of leaves         :   17 ( 112 expanded)
%              Depth                    :   19
%              Number of atoms          :  555 (2997 expanded)
%              Number of equality atoms :  209 ( 290 expanded)
%              Maximal formula depth    :   14 (   5 average)
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
         => ( ( v2_funct_1(X1)
              & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) )
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
           => ( ( v2_funct_1(X1)
                & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) )
             => r2_relset_1(X0,X0,X2,k6_partfun1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f33,plain,(
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

fof(f32,plain,
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

fof(f34,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0))
    & v2_funct_1(sK1)
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK2,sK0,sK0)
    & v1_funct_1(sK2)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f33,f32])).

fof(f53,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f50,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f34])).

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

fof(f45,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f48,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f20])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f54,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f51,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f22])).

fof(f44,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
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

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f37,plain,(
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
    inference(cnf_transformation,[],[f16])).

fof(f9,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k6_partfun1(X0) = X2
      | k5_relat_1(X2,X1) != X1
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(k2_relat_1(X2),X0)
      | k1_relat_1(X2) != X0
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f37,f46])).

fof(f58,plain,(
    ! [X2,X1] :
      ( k6_partfun1(k1_relat_1(X2)) = X2
      | k5_relat_1(X2,X1) != X1
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(k2_relat_1(X2),k1_relat_1(X2))
      | k1_relat_1(X1) != k1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f57])).

fof(f55,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

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

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f49,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f52,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f59,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f42])).

fof(f56,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_560,plain,
    ( ~ m1_subset_1(X0_47,X0_49)
    | m1_subset_1(X1_47,X1_49)
    | X1_49 != X0_49
    | X1_47 != X0_47 ),
    theory(equality)).

cnf(c_1066,plain,
    ( m1_subset_1(X0_47,X0_49)
    | ~ m1_subset_1(X1_47,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | X0_49 != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | X0_47 != X1_47 ),
    inference(instantiation,[status(thm)],[c_560])).

cnf(c_1278,plain,
    ( m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)))
    | ~ m1_subset_1(X1_47,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | X0_47 != X1_47 ),
    inference(instantiation,[status(thm)],[c_1066])).

cnf(c_5744,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | k6_partfun1(sK0) != X0_47 ),
    inference(instantiation,[status(thm)],[c_1278])).

cnf(c_7499,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | k6_partfun1(sK0) != sK2 ),
    inference(instantiation,[status(thm)],[c_5744])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_538,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_847,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_538])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_536,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_849,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_536])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_539,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)))
    | ~ m1_subset_1(X1_47,k1_zfmisc_1(k2_zfmisc_1(X2_48,X3_48)))
    | ~ v1_funct_1(X0_47)
    | ~ v1_funct_1(X1_47)
    | k1_partfun1(X2_48,X3_48,X0_48,X1_48,X1_47,X0_47) = k5_relat_1(X1_47,X0_47) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_846,plain,
    ( k1_partfun1(X0_48,X1_48,X2_48,X3_48,X0_47,X1_47) = k5_relat_1(X0_47,X1_47)
    | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top
    | m1_subset_1(X1_47,k1_zfmisc_1(k2_zfmisc_1(X2_48,X3_48))) != iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | v1_funct_1(X1_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_539])).

cnf(c_1138,plain,
    ( k1_partfun1(X0_48,X1_48,sK0,sK0,X0_47,sK1) = k5_relat_1(X0_47,sK1)
    | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_849,c_846])).

cnf(c_20,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_21,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1775,plain,
    ( v1_funct_1(X0_47) != iProver_top
    | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top
    | k1_partfun1(X0_48,X1_48,sK0,sK0,X0_47,sK1) = k5_relat_1(X0_47,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1138,c_21])).

cnf(c_1776,plain,
    ( k1_partfun1(X0_48,X1_48,sK0,sK0,X0_47,sK1) = k5_relat_1(X0_47,sK1)
    | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top
    | v1_funct_1(X0_47) != iProver_top ),
    inference(renaming,[status(thm)],[c_1775])).

cnf(c_1782,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) = k5_relat_1(sK2,sK1)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_847,c_1776])).

cnf(c_7,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_14,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_361,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) != X0
    | sK1 != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_14])).

cnf(c_362,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) ),
    inference(unflattening,[status(thm)],[c_361])).

cnf(c_364,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_362,c_18])).

cnf(c_529,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) ),
    inference(subtyping,[status(esa)],[c_364])).

cnf(c_854,plain,
    ( sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1)
    | m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_529])).

cnf(c_17,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_541,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)))
    | ~ m1_subset_1(X1_47,k1_zfmisc_1(k2_zfmisc_1(X2_48,X3_48)))
    | m1_subset_1(k1_partfun1(X2_48,X3_48,X0_48,X1_48,X1_47,X0_47),k1_zfmisc_1(k2_zfmisc_1(X2_48,X1_48)))
    | ~ v1_funct_1(X0_47)
    | ~ v1_funct_1(X1_47) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_981,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_541])).

cnf(c_1368,plain,
    ( sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_854,c_20,c_18,c_17,c_15,c_529,c_981])).

cnf(c_1808,plain,
    ( k5_relat_1(sK2,sK1) = sK1
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1782,c_1368])).

cnf(c_24,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2012,plain,
    ( k5_relat_1(sK2,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1808,c_24])).

cnf(c_2,plain,
    ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,X1) != X1
    | k6_partfun1(k1_relat_1(X0)) = X0
    | k1_relat_1(X1) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_13,negated_conjecture,
    ( v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_270,plain,
    ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(X0,X1) != X1
    | k6_partfun1(k1_relat_1(X0)) = X0
    | k1_relat_1(X1) != k1_relat_1(X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_13])).

cnf(c_271,plain,
    ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK1)
    | k5_relat_1(X0,sK1) != sK1
    | k6_partfun1(k1_relat_1(X0)) = X0
    | k1_relat_1(sK1) != k1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_270])).

cnf(c_275,plain,
    ( ~ v1_funct_1(X0)
    | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK1)
    | k5_relat_1(X0,sK1) != sK1
    | k6_partfun1(k1_relat_1(X0)) = X0
    | k1_relat_1(sK1) != k1_relat_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_271,c_20])).

cnf(c_276,plain,
    ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK1)
    | k5_relat_1(X0,sK1) != sK1
    | k6_partfun1(k1_relat_1(X0)) = X0
    | k1_relat_1(sK1) != k1_relat_1(X0) ),
    inference(renaming,[status(thm)],[c_275])).

cnf(c_531,plain,
    ( ~ r1_tarski(k2_relat_1(X0_47),k1_relat_1(X0_47))
    | ~ v1_funct_1(X0_47)
    | ~ v1_relat_1(X0_47)
    | ~ v1_relat_1(sK1)
    | k1_relat_1(sK1) != k1_relat_1(X0_47)
    | k5_relat_1(X0_47,sK1) != sK1
    | k6_partfun1(k1_relat_1(X0_47)) = X0_47 ),
    inference(subtyping,[status(esa)],[c_276])).

cnf(c_852,plain,
    ( k1_relat_1(sK1) != k1_relat_1(X0_47)
    | k5_relat_1(X0_47,sK1) != sK1
    | k6_partfun1(k1_relat_1(X0_47)) = X0_47
    | r1_tarski(k2_relat_1(X0_47),k1_relat_1(X0_47)) != iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | v1_relat_1(X0_47) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_531])).

cnf(c_23,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_543,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)))
    | v1_relat_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_580,plain,
    ( m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top
    | v1_relat_1(X0_47) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_543])).

cnf(c_582,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_relat_1(sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_580])).

cnf(c_602,plain,
    ( k1_relat_1(sK1) != k1_relat_1(X0_47)
    | k5_relat_1(X0_47,sK1) != sK1
    | k6_partfun1(k1_relat_1(X0_47)) = X0_47
    | r1_tarski(k2_relat_1(X0_47),k1_relat_1(X0_47)) != iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | v1_relat_1(X0_47) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_531])).

cnf(c_1932,plain,
    ( v1_relat_1(X0_47) != iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | r1_tarski(k2_relat_1(X0_47),k1_relat_1(X0_47)) != iProver_top
    | k6_partfun1(k1_relat_1(X0_47)) = X0_47
    | k5_relat_1(X0_47,sK1) != sK1
    | k1_relat_1(sK1) != k1_relat_1(X0_47) ),
    inference(global_propositional_subsumption,[status(thm)],[c_852,c_23,c_582,c_602])).

cnf(c_1933,plain,
    ( k1_relat_1(sK1) != k1_relat_1(X0_47)
    | k5_relat_1(X0_47,sK1) != sK1
    | k6_partfun1(k1_relat_1(X0_47)) = X0_47
    | r1_tarski(k2_relat_1(X0_47),k1_relat_1(X0_47)) != iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | v1_relat_1(X0_47) != iProver_top ),
    inference(renaming,[status(thm)],[c_1932])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_542,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)))
    | k1_relset_1(X0_48,X1_48,X0_47) = k1_relat_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_843,plain,
    ( k1_relset_1(X0_48,X1_48,X0_47) = k1_relat_1(X0_47)
    | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_542])).

cnf(c_1086,plain,
    ( k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_849,c_843])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(X1,X1,X0) = X1 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_19,negated_conjecture,
    ( v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_238,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(X1,X1,X0) = X1
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_19])).

cnf(c_239,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | k1_relset_1(sK0,sK0,sK1) = sK0 ),
    inference(unflattening,[status(thm)],[c_238])).

cnf(c_241,plain,
    ( k1_relset_1(sK0,sK0,sK1) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_239,c_20,c_18])).

cnf(c_533,plain,
    ( k1_relset_1(sK0,sK0,sK1) = sK0 ),
    inference(subtyping,[status(esa)],[c_241])).

cnf(c_1088,plain,
    ( k1_relat_1(sK1) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_1086,c_533])).

cnf(c_1936,plain,
    ( k1_relat_1(X0_47) != sK0
    | k5_relat_1(X0_47,sK1) != sK1
    | k6_partfun1(k1_relat_1(X0_47)) = X0_47
    | r1_tarski(k2_relat_1(X0_47),k1_relat_1(X0_47)) != iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | v1_relat_1(X0_47) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1933,c_1088])).

cnf(c_2015,plain,
    ( k1_relat_1(sK2) != sK0
    | k6_partfun1(k1_relat_1(sK2)) = sK2
    | r1_tarski(k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2012,c_1936])).

cnf(c_1085,plain,
    ( k1_relset_1(sK0,sK0,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_847,c_843])).

cnf(c_16,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_230,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(X1,X1,X0) = X1
    | sK2 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_16])).

cnf(c_231,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | k1_relset_1(sK0,sK0,sK2) = sK0 ),
    inference(unflattening,[status(thm)],[c_230])).

cnf(c_233,plain,
    ( k1_relset_1(sK0,sK0,sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_231,c_17,c_15])).

cnf(c_534,plain,
    ( k1_relset_1(sK0,sK0,sK2) = sK0 ),
    inference(subtyping,[status(esa)],[c_233])).

cnf(c_1091,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_1085,c_534])).

cnf(c_2016,plain,
    ( sK0 != sK0
    | k6_partfun1(sK0) = sK2
    | r1_tarski(k2_relat_1(sK2),sK0) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2015,c_1091])).

cnf(c_2017,plain,
    ( k6_partfun1(sK0) = sK2
    | r1_tarski(k2_relat_1(sK2),sK0) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2016])).

cnf(c_1,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v5_relat_1(X0,X2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_249,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X3),X4)
    | ~ v1_relat_1(X3)
    | X0 != X3
    | X2 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_4])).

cnf(c_250,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_249])).

cnf(c_254,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_250,c_3])).

cnf(c_255,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_254])).

cnf(c_532,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)))
    | r1_tarski(k2_relat_1(X0_47),X1_48) ),
    inference(subtyping,[status(esa)],[c_255])).

cnf(c_851,plain,
    ( m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top
    | r1_tarski(k2_relat_1(X0_47),X1_48) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_532])).

cnf(c_1547,plain,
    ( r1_tarski(k2_relat_1(sK2),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_847,c_851])).

cnf(c_842,plain,
    ( m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top
    | v1_relat_1(X0_47) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_543])).

cnf(c_1074,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_847,c_842])).

cnf(c_550,plain,
    ( X0_47 != X1_47
    | X2_47 != X1_47
    | X2_47 = X0_47 ),
    theory(equality)).

cnf(c_990,plain,
    ( k6_partfun1(sK0) != X0_47
    | sK2 != X0_47
    | sK2 = k6_partfun1(sK0) ),
    inference(instantiation,[status(thm)],[c_550])).

cnf(c_1058,plain,
    ( k6_partfun1(sK0) != sK2
    | sK2 = k6_partfun1(sK0)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_990])).

cnf(c_547,plain,
    ( X0_49 = X0_49 ),
    theory(equality)).

cnf(c_1011,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_547])).

cnf(c_545,plain,
    ( X0_47 = X0_47 ),
    theory(equality)).

cnf(c_1003,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_545])).

cnf(c_6,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_12,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_351,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k6_partfun1(sK0) != X0
    | sK2 != X0
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_12])).

cnf(c_352,plain,
    ( ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK2 != k6_partfun1(sK0) ),
    inference(unflattening,[status(thm)],[c_351])).

cnf(c_530,plain,
    ( ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK2 != k6_partfun1(sK0) ),
    inference(subtyping,[status(esa)],[c_352])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7499,c_2017,c_1547,c_1074,c_1058,c_1011,c_1003,c_530,c_15,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:40:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.66/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.66/0.98  
% 3.66/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.66/0.98  
% 3.66/0.98  ------  iProver source info
% 3.66/0.98  
% 3.66/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.66/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.66/0.98  git: non_committed_changes: false
% 3.66/0.98  git: last_make_outside_of_git: false
% 3.66/0.98  
% 3.66/0.98  ------ 
% 3.66/0.98  
% 3.66/0.98  ------ Input Options
% 3.66/0.98  
% 3.66/0.98  --out_options                           all
% 3.66/0.98  --tptp_safe_out                         true
% 3.66/0.98  --problem_path                          ""
% 3.66/0.98  --include_path                          ""
% 3.66/0.98  --clausifier                            res/vclausify_rel
% 3.66/0.98  --clausifier_options                    --mode clausify
% 3.66/0.98  --stdin                                 false
% 3.66/0.98  --stats_out                             all
% 3.66/0.98  
% 3.66/0.98  ------ General Options
% 3.66/0.98  
% 3.66/0.98  --fof                                   false
% 3.66/0.98  --time_out_real                         305.
% 3.66/0.98  --time_out_virtual                      -1.
% 3.66/0.98  --symbol_type_check                     false
% 3.66/0.98  --clausify_out                          false
% 3.66/0.98  --sig_cnt_out                           false
% 3.66/0.98  --trig_cnt_out                          false
% 3.66/0.98  --trig_cnt_out_tolerance                1.
% 3.66/0.98  --trig_cnt_out_sk_spl                   false
% 3.66/0.98  --abstr_cl_out                          false
% 3.66/0.98  
% 3.66/0.98  ------ Global Options
% 3.66/0.98  
% 3.66/0.98  --schedule                              default
% 3.66/0.98  --add_important_lit                     false
% 3.66/0.98  --prop_solver_per_cl                    1000
% 3.66/0.98  --min_unsat_core                        false
% 3.66/0.98  --soft_assumptions                      false
% 3.66/0.98  --soft_lemma_size                       3
% 3.66/0.98  --prop_impl_unit_size                   0
% 3.66/0.98  --prop_impl_unit                        []
% 3.66/0.98  --share_sel_clauses                     true
% 3.66/0.98  --reset_solvers                         false
% 3.66/0.98  --bc_imp_inh                            [conj_cone]
% 3.66/0.98  --conj_cone_tolerance                   3.
% 3.66/0.98  --extra_neg_conj                        none
% 3.66/0.98  --large_theory_mode                     true
% 3.66/0.98  --prolific_symb_bound                   200
% 3.66/0.98  --lt_threshold                          2000
% 3.66/0.98  --clause_weak_htbl                      true
% 3.66/0.98  --gc_record_bc_elim                     false
% 3.66/0.98  
% 3.66/0.98  ------ Preprocessing Options
% 3.66/0.98  
% 3.66/0.98  --preprocessing_flag                    true
% 3.66/0.98  --time_out_prep_mult                    0.1
% 3.66/0.98  --splitting_mode                        input
% 3.66/0.98  --splitting_grd                         true
% 3.66/0.98  --splitting_cvd                         false
% 3.66/0.98  --splitting_cvd_svl                     false
% 3.66/0.98  --splitting_nvd                         32
% 3.66/0.98  --sub_typing                            true
% 3.66/0.98  --prep_gs_sim                           true
% 3.66/0.98  --prep_unflatten                        true
% 3.66/0.98  --prep_res_sim                          true
% 3.66/0.98  --prep_upred                            true
% 3.66/0.98  --prep_sem_filter                       exhaustive
% 3.66/0.98  --prep_sem_filter_out                   false
% 3.66/0.98  --pred_elim                             true
% 3.66/0.98  --res_sim_input                         true
% 3.66/0.98  --eq_ax_congr_red                       true
% 3.66/0.98  --pure_diseq_elim                       true
% 3.66/0.98  --brand_transform                       false
% 3.66/0.98  --non_eq_to_eq                          false
% 3.66/0.98  --prep_def_merge                        true
% 3.66/0.98  --prep_def_merge_prop_impl              false
% 3.66/0.98  --prep_def_merge_mbd                    true
% 3.66/0.98  --prep_def_merge_tr_red                 false
% 3.66/0.98  --prep_def_merge_tr_cl                  false
% 3.66/0.98  --smt_preprocessing                     true
% 3.66/0.98  --smt_ac_axioms                         fast
% 3.66/0.98  --preprocessed_out                      false
% 3.66/0.98  --preprocessed_stats                    false
% 3.66/0.98  
% 3.66/0.98  ------ Abstraction refinement Options
% 3.66/0.98  
% 3.66/0.98  --abstr_ref                             []
% 3.66/0.98  --abstr_ref_prep                        false
% 3.66/0.98  --abstr_ref_until_sat                   false
% 3.66/0.98  --abstr_ref_sig_restrict                funpre
% 3.66/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.66/0.98  --abstr_ref_under                       []
% 3.66/0.98  
% 3.66/0.98  ------ SAT Options
% 3.66/0.98  
% 3.66/0.98  --sat_mode                              false
% 3.66/0.98  --sat_fm_restart_options                ""
% 3.66/0.98  --sat_gr_def                            false
% 3.66/0.98  --sat_epr_types                         true
% 3.66/0.98  --sat_non_cyclic_types                  false
% 3.66/0.98  --sat_finite_models                     false
% 3.66/0.98  --sat_fm_lemmas                         false
% 3.66/0.98  --sat_fm_prep                           false
% 3.66/0.98  --sat_fm_uc_incr                        true
% 3.66/0.98  --sat_out_model                         small
% 3.66/0.98  --sat_out_clauses                       false
% 3.66/0.98  
% 3.66/0.98  ------ QBF Options
% 3.66/0.98  
% 3.66/0.98  --qbf_mode                              false
% 3.66/0.98  --qbf_elim_univ                         false
% 3.66/0.98  --qbf_dom_inst                          none
% 3.66/0.98  --qbf_dom_pre_inst                      false
% 3.66/0.98  --qbf_sk_in                             false
% 3.66/0.98  --qbf_pred_elim                         true
% 3.66/0.98  --qbf_split                             512
% 3.66/0.98  
% 3.66/0.98  ------ BMC1 Options
% 3.66/0.98  
% 3.66/0.98  --bmc1_incremental                      false
% 3.66/0.98  --bmc1_axioms                           reachable_all
% 3.66/0.98  --bmc1_min_bound                        0
% 3.66/0.98  --bmc1_max_bound                        -1
% 3.66/0.98  --bmc1_max_bound_default                -1
% 3.66/0.98  --bmc1_symbol_reachability              true
% 3.66/0.98  --bmc1_property_lemmas                  false
% 3.66/0.98  --bmc1_k_induction                      false
% 3.66/0.98  --bmc1_non_equiv_states                 false
% 3.66/0.98  --bmc1_deadlock                         false
% 3.66/0.98  --bmc1_ucm                              false
% 3.66/0.98  --bmc1_add_unsat_core                   none
% 3.66/0.98  --bmc1_unsat_core_children              false
% 3.66/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.66/0.98  --bmc1_out_stat                         full
% 3.66/0.98  --bmc1_ground_init                      false
% 3.66/0.98  --bmc1_pre_inst_next_state              false
% 3.66/0.98  --bmc1_pre_inst_state                   false
% 3.66/0.98  --bmc1_pre_inst_reach_state             false
% 3.66/0.98  --bmc1_out_unsat_core                   false
% 3.66/0.98  --bmc1_aig_witness_out                  false
% 3.66/0.98  --bmc1_verbose                          false
% 3.66/0.98  --bmc1_dump_clauses_tptp                false
% 3.66/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.66/0.98  --bmc1_dump_file                        -
% 3.66/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.66/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.66/0.98  --bmc1_ucm_extend_mode                  1
% 3.66/0.98  --bmc1_ucm_init_mode                    2
% 3.66/0.98  --bmc1_ucm_cone_mode                    none
% 3.66/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.66/0.98  --bmc1_ucm_relax_model                  4
% 3.66/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.66/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.66/0.98  --bmc1_ucm_layered_model                none
% 3.66/0.98  --bmc1_ucm_max_lemma_size               10
% 3.66/0.98  
% 3.66/0.98  ------ AIG Options
% 3.66/0.98  
% 3.66/0.98  --aig_mode                              false
% 3.66/0.98  
% 3.66/0.98  ------ Instantiation Options
% 3.66/0.98  
% 3.66/0.98  --instantiation_flag                    true
% 3.66/0.98  --inst_sos_flag                         false
% 3.66/0.98  --inst_sos_phase                        true
% 3.66/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.66/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.66/0.98  --inst_lit_sel_side                     num_symb
% 3.66/0.98  --inst_solver_per_active                1400
% 3.66/0.98  --inst_solver_calls_frac                1.
% 3.66/0.98  --inst_passive_queue_type               priority_queues
% 3.66/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.66/0.98  --inst_passive_queues_freq              [25;2]
% 3.66/0.98  --inst_dismatching                      true
% 3.66/0.98  --inst_eager_unprocessed_to_passive     true
% 3.66/0.98  --inst_prop_sim_given                   true
% 3.66/0.98  --inst_prop_sim_new                     false
% 3.66/0.98  --inst_subs_new                         false
% 3.66/0.98  --inst_eq_res_simp                      false
% 3.66/0.98  --inst_subs_given                       false
% 3.66/0.98  --inst_orphan_elimination               true
% 3.66/0.98  --inst_learning_loop_flag               true
% 3.66/0.98  --inst_learning_start                   3000
% 3.66/0.98  --inst_learning_factor                  2
% 3.66/0.98  --inst_start_prop_sim_after_learn       3
% 3.66/0.98  --inst_sel_renew                        solver
% 3.66/0.98  --inst_lit_activity_flag                true
% 3.66/0.98  --inst_restr_to_given                   false
% 3.66/0.98  --inst_activity_threshold               500
% 3.66/0.98  --inst_out_proof                        true
% 3.66/0.98  
% 3.66/0.98  ------ Resolution Options
% 3.66/0.98  
% 3.66/0.98  --resolution_flag                       true
% 3.66/0.98  --res_lit_sel                           adaptive
% 3.66/0.98  --res_lit_sel_side                      none
% 3.66/0.98  --res_ordering                          kbo
% 3.66/0.98  --res_to_prop_solver                    active
% 3.66/0.98  --res_prop_simpl_new                    false
% 3.66/0.98  --res_prop_simpl_given                  true
% 3.66/0.98  --res_passive_queue_type                priority_queues
% 3.66/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.66/0.98  --res_passive_queues_freq               [15;5]
% 3.66/0.98  --res_forward_subs                      full
% 3.66/0.98  --res_backward_subs                     full
% 3.66/0.98  --res_forward_subs_resolution           true
% 3.66/0.98  --res_backward_subs_resolution          true
% 3.66/0.98  --res_orphan_elimination                true
% 3.66/0.98  --res_time_limit                        2.
% 3.66/0.98  --res_out_proof                         true
% 3.66/0.98  
% 3.66/0.98  ------ Superposition Options
% 3.66/0.98  
% 3.66/0.98  --superposition_flag                    true
% 3.66/0.98  --sup_passive_queue_type                priority_queues
% 3.66/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.66/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.66/0.98  --demod_completeness_check              fast
% 3.66/0.98  --demod_use_ground                      true
% 3.66/0.98  --sup_to_prop_solver                    passive
% 3.66/0.98  --sup_prop_simpl_new                    true
% 3.66/0.98  --sup_prop_simpl_given                  true
% 3.66/0.98  --sup_fun_splitting                     false
% 3.66/0.98  --sup_smt_interval                      50000
% 3.66/0.98  
% 3.66/0.98  ------ Superposition Simplification Setup
% 3.66/0.98  
% 3.66/0.98  --sup_indices_passive                   []
% 3.66/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.66/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.66/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.66/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.66/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.66/0.98  --sup_full_bw                           [BwDemod]
% 3.66/0.98  --sup_immed_triv                        [TrivRules]
% 3.66/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.66/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.66/0.98  --sup_immed_bw_main                     []
% 3.66/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.66/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.66/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.66/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.66/0.98  
% 3.66/0.98  ------ Combination Options
% 3.66/0.98  
% 3.66/0.98  --comb_res_mult                         3
% 3.66/0.98  --comb_sup_mult                         2
% 3.66/0.98  --comb_inst_mult                        10
% 3.66/0.98  
% 3.66/0.98  ------ Debug Options
% 3.66/0.98  
% 3.66/0.98  --dbg_backtrace                         false
% 3.66/0.98  --dbg_dump_prop_clauses                 false
% 3.66/0.98  --dbg_dump_prop_clauses_file            -
% 3.66/0.98  --dbg_out_stat                          false
% 3.66/0.98  ------ Parsing...
% 3.66/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.66/0.98  
% 3.66/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.66/0.98  
% 3.66/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.66/0.98  
% 3.66/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.66/0.98  ------ Proving...
% 3.66/0.98  ------ Problem Properties 
% 3.66/0.98  
% 3.66/0.98  
% 3.66/0.98  clauses                                 16
% 3.66/0.98  conjectures                             4
% 3.66/0.98  EPR                                     2
% 3.66/0.98  Horn                                    16
% 3.66/0.98  unary                                   6
% 3.66/0.98  binary                                  6
% 3.66/0.98  lits                                    40
% 3.66/0.98  lits eq                                 11
% 3.66/0.98  fd_pure                                 0
% 3.66/0.98  fd_pseudo                               0
% 3.66/0.98  fd_cond                                 0
% 3.66/0.98  fd_pseudo_cond                          0
% 3.66/0.98  AC symbols                              0
% 3.66/0.98  
% 3.66/0.98  ------ Schedule dynamic 5 is on 
% 3.66/0.98  
% 3.66/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.66/0.98  
% 3.66/0.98  
% 3.66/0.98  ------ 
% 3.66/0.98  Current options:
% 3.66/0.98  ------ 
% 3.66/0.98  
% 3.66/0.98  ------ Input Options
% 3.66/0.98  
% 3.66/0.98  --out_options                           all
% 3.66/0.98  --tptp_safe_out                         true
% 3.66/0.98  --problem_path                          ""
% 3.66/0.98  --include_path                          ""
% 3.66/0.98  --clausifier                            res/vclausify_rel
% 3.66/0.98  --clausifier_options                    --mode clausify
% 3.66/0.98  --stdin                                 false
% 3.66/0.98  --stats_out                             all
% 3.66/0.98  
% 3.66/0.98  ------ General Options
% 3.66/0.98  
% 3.66/0.98  --fof                                   false
% 3.66/0.98  --time_out_real                         305.
% 3.66/0.98  --time_out_virtual                      -1.
% 3.66/0.98  --symbol_type_check                     false
% 3.66/0.98  --clausify_out                          false
% 3.66/0.98  --sig_cnt_out                           false
% 3.66/0.98  --trig_cnt_out                          false
% 3.66/0.98  --trig_cnt_out_tolerance                1.
% 3.66/0.98  --trig_cnt_out_sk_spl                   false
% 3.66/0.98  --abstr_cl_out                          false
% 3.66/0.98  
% 3.66/0.98  ------ Global Options
% 3.66/0.98  
% 3.66/0.98  --schedule                              default
% 3.66/0.98  --add_important_lit                     false
% 3.66/0.98  --prop_solver_per_cl                    1000
% 3.66/0.98  --min_unsat_core                        false
% 3.66/0.98  --soft_assumptions                      false
% 3.66/0.98  --soft_lemma_size                       3
% 3.66/0.98  --prop_impl_unit_size                   0
% 3.66/0.98  --prop_impl_unit                        []
% 3.66/0.98  --share_sel_clauses                     true
% 3.66/0.98  --reset_solvers                         false
% 3.66/0.98  --bc_imp_inh                            [conj_cone]
% 3.66/0.98  --conj_cone_tolerance                   3.
% 3.66/0.98  --extra_neg_conj                        none
% 3.66/0.98  --large_theory_mode                     true
% 3.66/0.98  --prolific_symb_bound                   200
% 3.66/0.98  --lt_threshold                          2000
% 3.66/0.98  --clause_weak_htbl                      true
% 3.66/0.98  --gc_record_bc_elim                     false
% 3.66/0.98  
% 3.66/0.98  ------ Preprocessing Options
% 3.66/0.98  
% 3.66/0.98  --preprocessing_flag                    true
% 3.66/0.98  --time_out_prep_mult                    0.1
% 3.66/0.98  --splitting_mode                        input
% 3.66/0.98  --splitting_grd                         true
% 3.66/0.98  --splitting_cvd                         false
% 3.66/0.98  --splitting_cvd_svl                     false
% 3.66/0.98  --splitting_nvd                         32
% 3.66/0.98  --sub_typing                            true
% 3.66/0.98  --prep_gs_sim                           true
% 3.66/0.98  --prep_unflatten                        true
% 3.66/0.98  --prep_res_sim                          true
% 3.66/0.98  --prep_upred                            true
% 3.66/0.98  --prep_sem_filter                       exhaustive
% 3.66/0.98  --prep_sem_filter_out                   false
% 3.66/0.98  --pred_elim                             true
% 3.66/0.98  --res_sim_input                         true
% 3.66/0.98  --eq_ax_congr_red                       true
% 3.66/0.98  --pure_diseq_elim                       true
% 3.66/0.98  --brand_transform                       false
% 3.66/0.98  --non_eq_to_eq                          false
% 3.66/0.98  --prep_def_merge                        true
% 3.66/0.98  --prep_def_merge_prop_impl              false
% 3.66/0.98  --prep_def_merge_mbd                    true
% 3.66/0.98  --prep_def_merge_tr_red                 false
% 3.66/0.98  --prep_def_merge_tr_cl                  false
% 3.66/0.98  --smt_preprocessing                     true
% 3.66/0.98  --smt_ac_axioms                         fast
% 3.66/0.98  --preprocessed_out                      false
% 3.66/0.98  --preprocessed_stats                    false
% 3.66/0.98  
% 3.66/0.98  ------ Abstraction refinement Options
% 3.66/0.98  
% 3.66/0.98  --abstr_ref                             []
% 3.66/0.98  --abstr_ref_prep                        false
% 3.66/0.98  --abstr_ref_until_sat                   false
% 3.66/0.98  --abstr_ref_sig_restrict                funpre
% 3.66/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.66/0.98  --abstr_ref_under                       []
% 3.66/0.98  
% 3.66/0.98  ------ SAT Options
% 3.66/0.98  
% 3.66/0.98  --sat_mode                              false
% 3.66/0.98  --sat_fm_restart_options                ""
% 3.66/0.98  --sat_gr_def                            false
% 3.66/0.98  --sat_epr_types                         true
% 3.66/0.98  --sat_non_cyclic_types                  false
% 3.66/0.98  --sat_finite_models                     false
% 3.66/0.98  --sat_fm_lemmas                         false
% 3.66/0.98  --sat_fm_prep                           false
% 3.66/0.98  --sat_fm_uc_incr                        true
% 3.66/0.98  --sat_out_model                         small
% 3.66/0.98  --sat_out_clauses                       false
% 3.66/0.98  
% 3.66/0.98  ------ QBF Options
% 3.66/0.98  
% 3.66/0.98  --qbf_mode                              false
% 3.66/0.98  --qbf_elim_univ                         false
% 3.66/0.98  --qbf_dom_inst                          none
% 3.66/0.98  --qbf_dom_pre_inst                      false
% 3.66/0.98  --qbf_sk_in                             false
% 3.66/0.98  --qbf_pred_elim                         true
% 3.66/0.98  --qbf_split                             512
% 3.66/0.98  
% 3.66/0.98  ------ BMC1 Options
% 3.66/0.98  
% 3.66/0.98  --bmc1_incremental                      false
% 3.66/0.98  --bmc1_axioms                           reachable_all
% 3.66/0.98  --bmc1_min_bound                        0
% 3.66/0.98  --bmc1_max_bound                        -1
% 3.66/0.98  --bmc1_max_bound_default                -1
% 3.66/0.98  --bmc1_symbol_reachability              true
% 3.66/0.98  --bmc1_property_lemmas                  false
% 3.66/0.98  --bmc1_k_induction                      false
% 3.66/0.98  --bmc1_non_equiv_states                 false
% 3.66/0.98  --bmc1_deadlock                         false
% 3.66/0.98  --bmc1_ucm                              false
% 3.66/0.98  --bmc1_add_unsat_core                   none
% 3.66/0.98  --bmc1_unsat_core_children              false
% 3.66/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.66/0.98  --bmc1_out_stat                         full
% 3.66/0.98  --bmc1_ground_init                      false
% 3.66/0.98  --bmc1_pre_inst_next_state              false
% 3.66/0.98  --bmc1_pre_inst_state                   false
% 3.66/0.98  --bmc1_pre_inst_reach_state             false
% 3.66/0.98  --bmc1_out_unsat_core                   false
% 3.66/0.98  --bmc1_aig_witness_out                  false
% 3.66/0.98  --bmc1_verbose                          false
% 3.66/0.98  --bmc1_dump_clauses_tptp                false
% 3.66/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.66/0.98  --bmc1_dump_file                        -
% 3.66/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.66/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.66/0.98  --bmc1_ucm_extend_mode                  1
% 3.66/0.98  --bmc1_ucm_init_mode                    2
% 3.66/0.98  --bmc1_ucm_cone_mode                    none
% 3.66/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.66/0.98  --bmc1_ucm_relax_model                  4
% 3.66/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.66/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.66/0.98  --bmc1_ucm_layered_model                none
% 3.66/0.98  --bmc1_ucm_max_lemma_size               10
% 3.66/0.98  
% 3.66/0.98  ------ AIG Options
% 3.66/0.98  
% 3.66/0.98  --aig_mode                              false
% 3.66/0.98  
% 3.66/0.98  ------ Instantiation Options
% 3.66/0.98  
% 3.66/0.98  --instantiation_flag                    true
% 3.66/0.98  --inst_sos_flag                         false
% 3.66/0.98  --inst_sos_phase                        true
% 3.66/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.66/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.66/0.98  --inst_lit_sel_side                     none
% 3.66/0.98  --inst_solver_per_active                1400
% 3.66/0.98  --inst_solver_calls_frac                1.
% 3.66/0.98  --inst_passive_queue_type               priority_queues
% 3.66/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.66/0.98  --inst_passive_queues_freq              [25;2]
% 3.66/0.98  --inst_dismatching                      true
% 3.66/0.98  --inst_eager_unprocessed_to_passive     true
% 3.66/0.98  --inst_prop_sim_given                   true
% 3.66/0.98  --inst_prop_sim_new                     false
% 3.66/0.98  --inst_subs_new                         false
% 3.66/0.98  --inst_eq_res_simp                      false
% 3.66/0.98  --inst_subs_given                       false
% 3.66/0.98  --inst_orphan_elimination               true
% 3.66/0.98  --inst_learning_loop_flag               true
% 3.66/0.98  --inst_learning_start                   3000
% 3.66/0.98  --inst_learning_factor                  2
% 3.66/0.98  --inst_start_prop_sim_after_learn       3
% 3.66/0.98  --inst_sel_renew                        solver
% 3.66/0.98  --inst_lit_activity_flag                true
% 3.66/0.98  --inst_restr_to_given                   false
% 3.66/0.98  --inst_activity_threshold               500
% 3.66/0.98  --inst_out_proof                        true
% 3.66/0.98  
% 3.66/0.98  ------ Resolution Options
% 3.66/0.98  
% 3.66/0.98  --resolution_flag                       false
% 3.66/0.98  --res_lit_sel                           adaptive
% 3.66/0.98  --res_lit_sel_side                      none
% 3.66/0.98  --res_ordering                          kbo
% 3.66/0.98  --res_to_prop_solver                    active
% 3.66/0.98  --res_prop_simpl_new                    false
% 3.66/0.98  --res_prop_simpl_given                  true
% 3.66/0.98  --res_passive_queue_type                priority_queues
% 3.66/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.66/0.98  --res_passive_queues_freq               [15;5]
% 3.66/0.98  --res_forward_subs                      full
% 3.66/0.98  --res_backward_subs                     full
% 3.66/0.98  --res_forward_subs_resolution           true
% 3.66/0.98  --res_backward_subs_resolution          true
% 3.66/0.98  --res_orphan_elimination                true
% 3.66/0.98  --res_time_limit                        2.
% 3.66/0.98  --res_out_proof                         true
% 3.66/0.98  
% 3.66/0.98  ------ Superposition Options
% 3.66/0.98  
% 3.66/0.98  --superposition_flag                    true
% 3.66/0.98  --sup_passive_queue_type                priority_queues
% 3.66/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.66/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.66/0.98  --demod_completeness_check              fast
% 3.66/0.98  --demod_use_ground                      true
% 3.66/0.98  --sup_to_prop_solver                    passive
% 3.66/0.98  --sup_prop_simpl_new                    true
% 3.66/0.98  --sup_prop_simpl_given                  true
% 3.66/0.98  --sup_fun_splitting                     false
% 3.66/0.98  --sup_smt_interval                      50000
% 3.66/0.98  
% 3.66/0.98  ------ Superposition Simplification Setup
% 3.66/0.98  
% 3.66/0.98  --sup_indices_passive                   []
% 3.66/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.66/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.66/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.66/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.66/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.66/0.98  --sup_full_bw                           [BwDemod]
% 3.66/0.98  --sup_immed_triv                        [TrivRules]
% 3.66/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.66/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.66/0.98  --sup_immed_bw_main                     []
% 3.66/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.66/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.66/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.66/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.66/0.98  
% 3.66/0.98  ------ Combination Options
% 3.66/0.98  
% 3.66/0.98  --comb_res_mult                         3
% 3.66/0.98  --comb_sup_mult                         2
% 3.66/0.98  --comb_inst_mult                        10
% 3.66/0.98  
% 3.66/0.98  ------ Debug Options
% 3.66/0.98  
% 3.66/0.98  --dbg_backtrace                         false
% 3.66/0.98  --dbg_dump_prop_clauses                 false
% 3.66/0.98  --dbg_dump_prop_clauses_file            -
% 3.66/0.98  --dbg_out_stat                          false
% 3.66/0.98  
% 3.66/0.98  
% 3.66/0.98  
% 3.66/0.98  
% 3.66/0.98  ------ Proving...
% 3.66/0.98  
% 3.66/0.98  
% 3.66/0.98  % SZS status Theorem for theBenchmark.p
% 3.66/0.98  
% 3.66/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.66/0.98  
% 3.66/0.98  fof(f11,conjecture,(
% 3.66/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)) => r2_relset_1(X0,X0,X2,k6_partfun1(X0)))))),
% 3.66/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.66/0.98  
% 3.66/0.98  fof(f12,negated_conjecture,(
% 3.66/0.98    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)) => r2_relset_1(X0,X0,X2,k6_partfun1(X0)))))),
% 3.66/0.98    inference(negated_conjecture,[],[f11])).
% 3.66/0.98  
% 3.66/0.98  fof(f28,plain,(
% 3.66/0.98    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & (v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 3.66/0.98    inference(ennf_transformation,[],[f12])).
% 3.66/0.98  
% 3.66/0.98  fof(f29,plain,(
% 3.66/0.98    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 3.66/0.98    inference(flattening,[],[f28])).
% 3.66/0.98  
% 3.66/0.98  fof(f33,plain,(
% 3.66/0.98    ( ! [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (~r2_relset_1(X0,X0,sK2,k6_partfun1(X0)) & v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,sK2,X1),X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(sK2,X0,X0) & v1_funct_1(sK2))) )),
% 3.66/0.98    introduced(choice_axiom,[])).
% 3.66/0.98  
% 3.66/0.98  fof(f32,plain,(
% 3.66/0.98    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK0,sK0,X2,k6_partfun1(sK0)) & v2_funct_1(sK1) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,X2,sK1),sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 3.66/0.98    introduced(choice_axiom,[])).
% 3.66/0.98  
% 3.66/0.98  fof(f34,plain,(
% 3.66/0.98    (~r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0)) & v2_funct_1(sK1) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 3.66/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f33,f32])).
% 3.66/0.98  
% 3.66/0.98  fof(f53,plain,(
% 3.66/0.98    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.66/0.98    inference(cnf_transformation,[],[f34])).
% 3.66/0.98  
% 3.66/0.98  fof(f50,plain,(
% 3.66/0.98    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.66/0.98    inference(cnf_transformation,[],[f34])).
% 3.66/0.98  
% 3.66/0.98  fof(f8,axiom,(
% 3.66/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.66/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.66/0.98  
% 3.66/0.98  fof(f24,plain,(
% 3.66/0.98    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.66/0.98    inference(ennf_transformation,[],[f8])).
% 3.66/0.98  
% 3.66/0.98  fof(f25,plain,(
% 3.66/0.98    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.66/0.98    inference(flattening,[],[f24])).
% 3.66/0.98  
% 3.66/0.98  fof(f45,plain,(
% 3.66/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.66/0.98    inference(cnf_transformation,[],[f25])).
% 3.66/0.98  
% 3.66/0.98  fof(f48,plain,(
% 3.66/0.98    v1_funct_1(sK1)),
% 3.66/0.98    inference(cnf_transformation,[],[f34])).
% 3.66/0.98  
% 3.66/0.98  fof(f6,axiom,(
% 3.66/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.66/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.66/0.98  
% 3.66/0.98  fof(f20,plain,(
% 3.66/0.98    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.66/0.98    inference(ennf_transformation,[],[f6])).
% 3.66/0.98  
% 3.66/0.98  fof(f21,plain,(
% 3.66/0.98    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.66/0.98    inference(flattening,[],[f20])).
% 3.66/0.98  
% 3.66/0.98  fof(f31,plain,(
% 3.66/0.98    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.66/0.98    inference(nnf_transformation,[],[f21])).
% 3.66/0.98  
% 3.66/0.98  fof(f41,plain,(
% 3.66/0.98    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.66/0.98    inference(cnf_transformation,[],[f31])).
% 3.66/0.98  
% 3.66/0.98  fof(f54,plain,(
% 3.66/0.98    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1)),
% 3.66/0.98    inference(cnf_transformation,[],[f34])).
% 3.66/0.98  
% 3.66/0.98  fof(f51,plain,(
% 3.66/0.98    v1_funct_1(sK2)),
% 3.66/0.98    inference(cnf_transformation,[],[f34])).
% 3.66/0.98  
% 3.66/0.98  fof(f7,axiom,(
% 3.66/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 3.66/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.66/0.98  
% 3.66/0.98  fof(f22,plain,(
% 3.66/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.66/0.98    inference(ennf_transformation,[],[f7])).
% 3.66/0.98  
% 3.66/0.98  fof(f23,plain,(
% 3.66/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.66/0.98    inference(flattening,[],[f22])).
% 3.66/0.98  
% 3.66/0.98  fof(f44,plain,(
% 3.66/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.66/0.98    inference(cnf_transformation,[],[f23])).
% 3.66/0.98  
% 3.66/0.98  fof(f2,axiom,(
% 3.66/0.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => k6_relat_1(X0) = X2)))),
% 3.66/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.66/0.98  
% 3.66/0.98  fof(f15,plain,(
% 3.66/0.98    ! [X0,X1] : (! [X2] : ((k6_relat_1(X0) = X2 | (k5_relat_1(X2,X1) != X1 | ~v2_funct_1(X1) | ~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.66/0.98    inference(ennf_transformation,[],[f2])).
% 3.66/0.98  
% 3.66/0.98  fof(f16,plain,(
% 3.66/0.98    ! [X0,X1] : (! [X2] : (k6_relat_1(X0) = X2 | k5_relat_1(X2,X1) != X1 | ~v2_funct_1(X1) | ~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.66/0.98    inference(flattening,[],[f15])).
% 3.66/0.98  
% 3.66/0.98  fof(f37,plain,(
% 3.66/0.98    ( ! [X2,X0,X1] : (k6_relat_1(X0) = X2 | k5_relat_1(X2,X1) != X1 | ~v2_funct_1(X1) | ~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.66/0.98    inference(cnf_transformation,[],[f16])).
% 3.66/0.98  
% 3.66/0.98  fof(f9,axiom,(
% 3.66/0.98    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.66/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.66/0.98  
% 3.66/0.98  fof(f46,plain,(
% 3.66/0.98    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.66/0.98    inference(cnf_transformation,[],[f9])).
% 3.66/0.98  
% 3.66/0.98  fof(f57,plain,(
% 3.66/0.98    ( ! [X2,X0,X1] : (k6_partfun1(X0) = X2 | k5_relat_1(X2,X1) != X1 | ~v2_funct_1(X1) | ~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.66/0.98    inference(definition_unfolding,[],[f37,f46])).
% 3.66/0.98  
% 3.66/0.98  fof(f58,plain,(
% 3.66/0.98    ( ! [X2,X1] : (k6_partfun1(k1_relat_1(X2)) = X2 | k5_relat_1(X2,X1) != X1 | ~v2_funct_1(X1) | ~r1_tarski(k2_relat_1(X2),k1_relat_1(X2)) | k1_relat_1(X1) != k1_relat_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.66/0.98    inference(equality_resolution,[],[f57])).
% 3.66/0.98  
% 3.66/0.98  fof(f55,plain,(
% 3.66/0.98    v2_funct_1(sK1)),
% 3.66/0.98    inference(cnf_transformation,[],[f34])).
% 3.66/0.98  
% 3.66/0.98  fof(f3,axiom,(
% 3.66/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.66/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.66/0.98  
% 3.66/0.98  fof(f17,plain,(
% 3.66/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.66/0.98    inference(ennf_transformation,[],[f3])).
% 3.66/0.98  
% 3.66/0.98  fof(f38,plain,(
% 3.66/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.66/0.98    inference(cnf_transformation,[],[f17])).
% 3.66/0.98  
% 3.66/0.98  fof(f5,axiom,(
% 3.66/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.66/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.66/0.98  
% 3.66/0.98  fof(f19,plain,(
% 3.66/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.66/0.98    inference(ennf_transformation,[],[f5])).
% 3.66/0.98  
% 3.66/0.98  fof(f40,plain,(
% 3.66/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.66/0.98    inference(cnf_transformation,[],[f19])).
% 3.66/0.98  
% 3.66/0.98  fof(f10,axiom,(
% 3.66/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 3.66/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.66/0.98  
% 3.66/0.98  fof(f26,plain,(
% 3.66/0.98    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.66/0.98    inference(ennf_transformation,[],[f10])).
% 3.66/0.98  
% 3.66/0.98  fof(f27,plain,(
% 3.66/0.98    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.66/0.98    inference(flattening,[],[f26])).
% 3.66/0.98  
% 3.66/0.98  fof(f47,plain,(
% 3.66/0.98    ( ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.66/0.98    inference(cnf_transformation,[],[f27])).
% 3.66/0.98  
% 3.66/0.98  fof(f49,plain,(
% 3.66/0.98    v1_funct_2(sK1,sK0,sK0)),
% 3.66/0.98    inference(cnf_transformation,[],[f34])).
% 3.66/0.98  
% 3.66/0.98  fof(f52,plain,(
% 3.66/0.98    v1_funct_2(sK2,sK0,sK0)),
% 3.66/0.98    inference(cnf_transformation,[],[f34])).
% 3.66/0.98  
% 3.66/0.98  fof(f1,axiom,(
% 3.66/0.98    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.66/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.66/0.98  
% 3.66/0.98  fof(f14,plain,(
% 3.66/0.98    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.66/0.98    inference(ennf_transformation,[],[f1])).
% 3.66/0.98  
% 3.66/0.98  fof(f30,plain,(
% 3.66/0.98    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.66/0.98    inference(nnf_transformation,[],[f14])).
% 3.66/0.98  
% 3.66/0.98  fof(f35,plain,(
% 3.66/0.98    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.66/0.98    inference(cnf_transformation,[],[f30])).
% 3.66/0.98  
% 3.66/0.98  fof(f4,axiom,(
% 3.66/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.66/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.66/0.98  
% 3.66/0.98  fof(f13,plain,(
% 3.66/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.66/0.98    inference(pure_predicate_removal,[],[f4])).
% 3.66/0.98  
% 3.66/0.98  fof(f18,plain,(
% 3.66/0.98    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.66/0.98    inference(ennf_transformation,[],[f13])).
% 3.66/0.98  
% 3.66/0.98  fof(f39,plain,(
% 3.66/0.98    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.66/0.98    inference(cnf_transformation,[],[f18])).
% 3.66/0.98  
% 3.66/0.98  fof(f42,plain,(
% 3.66/0.98    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.66/0.98    inference(cnf_transformation,[],[f31])).
% 3.66/0.98  
% 3.66/0.98  fof(f59,plain,(
% 3.66/0.98    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.66/0.98    inference(equality_resolution,[],[f42])).
% 3.66/0.98  
% 3.66/0.98  fof(f56,plain,(
% 3.66/0.98    ~r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0))),
% 3.66/0.98    inference(cnf_transformation,[],[f34])).
% 3.66/0.98  
% 3.66/0.98  cnf(c_560,plain,
% 3.66/0.98      ( ~ m1_subset_1(X0_47,X0_49)
% 3.66/0.98      | m1_subset_1(X1_47,X1_49)
% 3.66/0.98      | X1_49 != X0_49
% 3.66/0.98      | X1_47 != X0_47 ),
% 3.66/0.98      theory(equality) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1066,plain,
% 3.66/0.98      ( m1_subset_1(X0_47,X0_49)
% 3.66/0.98      | ~ m1_subset_1(X1_47,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.66/0.98      | X0_49 != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
% 3.66/0.98      | X0_47 != X1_47 ),
% 3.66/0.98      inference(instantiation,[status(thm)],[c_560]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1278,plain,
% 3.66/0.98      ( m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)))
% 3.66/0.98      | ~ m1_subset_1(X1_47,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.66/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
% 3.66/0.98      | X0_47 != X1_47 ),
% 3.66/0.98      inference(instantiation,[status(thm)],[c_1066]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_5744,plain,
% 3.66/0.98      ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.66/0.98      | m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.66/0.98      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
% 3.66/0.98      | k6_partfun1(sK0) != X0_47 ),
% 3.66/0.98      inference(instantiation,[status(thm)],[c_1278]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_7499,plain,
% 3.66/0.98      ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.66/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.66/0.98      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
% 3.66/0.98      | k6_partfun1(sK0) != sK2 ),
% 3.66/0.98      inference(instantiation,[status(thm)],[c_5744]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_15,negated_conjecture,
% 3.66/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.66/0.98      inference(cnf_transformation,[],[f53]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_538,negated_conjecture,
% 3.66/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.66/0.98      inference(subtyping,[status(esa)],[c_15]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_847,plain,
% 3.66/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.66/0.98      inference(predicate_to_equality,[status(thm)],[c_538]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_18,negated_conjecture,
% 3.66/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.66/0.98      inference(cnf_transformation,[],[f50]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_536,negated_conjecture,
% 3.66/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.66/0.98      inference(subtyping,[status(esa)],[c_18]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_849,plain,
% 3.66/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.66/0.98      inference(predicate_to_equality,[status(thm)],[c_536]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_10,plain,
% 3.66/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.66/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.66/0.98      | ~ v1_funct_1(X0)
% 3.66/0.98      | ~ v1_funct_1(X3)
% 3.66/0.98      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.66/0.98      inference(cnf_transformation,[],[f45]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_539,plain,
% 3.66/0.98      ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)))
% 3.66/0.98      | ~ m1_subset_1(X1_47,k1_zfmisc_1(k2_zfmisc_1(X2_48,X3_48)))
% 3.66/0.98      | ~ v1_funct_1(X0_47)
% 3.66/0.98      | ~ v1_funct_1(X1_47)
% 3.66/0.98      | k1_partfun1(X2_48,X3_48,X0_48,X1_48,X1_47,X0_47) = k5_relat_1(X1_47,X0_47) ),
% 3.66/0.98      inference(subtyping,[status(esa)],[c_10]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_846,plain,
% 3.66/0.98      ( k1_partfun1(X0_48,X1_48,X2_48,X3_48,X0_47,X1_47) = k5_relat_1(X0_47,X1_47)
% 3.66/0.98      | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top
% 3.66/0.98      | m1_subset_1(X1_47,k1_zfmisc_1(k2_zfmisc_1(X2_48,X3_48))) != iProver_top
% 3.66/0.98      | v1_funct_1(X0_47) != iProver_top
% 3.66/0.98      | v1_funct_1(X1_47) != iProver_top ),
% 3.66/0.98      inference(predicate_to_equality,[status(thm)],[c_539]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1138,plain,
% 3.66/0.98      ( k1_partfun1(X0_48,X1_48,sK0,sK0,X0_47,sK1) = k5_relat_1(X0_47,sK1)
% 3.66/0.98      | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top
% 3.66/0.98      | v1_funct_1(X0_47) != iProver_top
% 3.66/0.98      | v1_funct_1(sK1) != iProver_top ),
% 3.66/0.98      inference(superposition,[status(thm)],[c_849,c_846]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_20,negated_conjecture,
% 3.66/0.98      ( v1_funct_1(sK1) ),
% 3.66/0.98      inference(cnf_transformation,[],[f48]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_21,plain,
% 3.66/0.98      ( v1_funct_1(sK1) = iProver_top ),
% 3.66/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1775,plain,
% 3.66/0.98      ( v1_funct_1(X0_47) != iProver_top
% 3.66/0.98      | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top
% 3.66/0.98      | k1_partfun1(X0_48,X1_48,sK0,sK0,X0_47,sK1) = k5_relat_1(X0_47,sK1) ),
% 3.66/0.98      inference(global_propositional_subsumption,
% 3.66/0.98                [status(thm)],
% 3.66/0.98                [c_1138,c_21]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1776,plain,
% 3.66/0.98      ( k1_partfun1(X0_48,X1_48,sK0,sK0,X0_47,sK1) = k5_relat_1(X0_47,sK1)
% 3.66/0.98      | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top
% 3.66/0.98      | v1_funct_1(X0_47) != iProver_top ),
% 3.66/0.98      inference(renaming,[status(thm)],[c_1775]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1782,plain,
% 3.66/0.98      ( k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) = k5_relat_1(sK2,sK1)
% 3.66/0.98      | v1_funct_1(sK2) != iProver_top ),
% 3.66/0.98      inference(superposition,[status(thm)],[c_847,c_1776]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_7,plain,
% 3.66/0.98      ( ~ r2_relset_1(X0,X1,X2,X3)
% 3.66/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.66/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.66/0.98      | X3 = X2 ),
% 3.66/0.98      inference(cnf_transformation,[],[f41]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_14,negated_conjecture,
% 3.66/0.98      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1) ),
% 3.66/0.98      inference(cnf_transformation,[],[f54]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_361,plain,
% 3.66/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.66/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.66/0.98      | X3 = X0
% 3.66/0.98      | k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) != X0
% 3.66/0.98      | sK1 != X3
% 3.66/0.98      | sK0 != X2
% 3.66/0.98      | sK0 != X1 ),
% 3.66/0.98      inference(resolution_lifted,[status(thm)],[c_7,c_14]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_362,plain,
% 3.66/0.98      ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.66/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.66/0.98      | sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) ),
% 3.66/0.98      inference(unflattening,[status(thm)],[c_361]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_364,plain,
% 3.66/0.98      ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.66/0.98      | sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) ),
% 3.66/0.98      inference(global_propositional_subsumption,
% 3.66/0.98                [status(thm)],
% 3.66/0.98                [c_362,c_18]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_529,plain,
% 3.66/0.98      ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.66/0.98      | sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) ),
% 3.66/0.98      inference(subtyping,[status(esa)],[c_364]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_854,plain,
% 3.66/0.98      ( sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1)
% 3.66/0.98      | m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.66/0.98      inference(predicate_to_equality,[status(thm)],[c_529]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_17,negated_conjecture,
% 3.66/0.98      ( v1_funct_1(sK2) ),
% 3.66/0.98      inference(cnf_transformation,[],[f51]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_8,plain,
% 3.66/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.66/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.66/0.98      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.66/0.98      | ~ v1_funct_1(X0)
% 3.66/0.98      | ~ v1_funct_1(X3) ),
% 3.66/0.98      inference(cnf_transformation,[],[f44]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_541,plain,
% 3.66/0.98      ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)))
% 3.66/0.98      | ~ m1_subset_1(X1_47,k1_zfmisc_1(k2_zfmisc_1(X2_48,X3_48)))
% 3.66/0.98      | m1_subset_1(k1_partfun1(X2_48,X3_48,X0_48,X1_48,X1_47,X0_47),k1_zfmisc_1(k2_zfmisc_1(X2_48,X1_48)))
% 3.66/0.98      | ~ v1_funct_1(X0_47)
% 3.66/0.98      | ~ v1_funct_1(X1_47) ),
% 3.66/0.98      inference(subtyping,[status(esa)],[c_8]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_981,plain,
% 3.66/0.98      ( m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.66/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.66/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.66/0.98      | ~ v1_funct_1(sK1)
% 3.66/0.98      | ~ v1_funct_1(sK2) ),
% 3.66/0.98      inference(instantiation,[status(thm)],[c_541]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1368,plain,
% 3.66/0.98      ( sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) ),
% 3.66/0.98      inference(global_propositional_subsumption,
% 3.66/0.98                [status(thm)],
% 3.66/0.98                [c_854,c_20,c_18,c_17,c_15,c_529,c_981]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1808,plain,
% 3.66/0.98      ( k5_relat_1(sK2,sK1) = sK1 | v1_funct_1(sK2) != iProver_top ),
% 3.66/0.98      inference(light_normalisation,[status(thm)],[c_1782,c_1368]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_24,plain,
% 3.66/0.98      ( v1_funct_1(sK2) = iProver_top ),
% 3.66/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_2012,plain,
% 3.66/0.98      ( k5_relat_1(sK2,sK1) = sK1 ),
% 3.66/0.98      inference(global_propositional_subsumption,
% 3.66/0.98                [status(thm)],
% 3.66/0.98                [c_1808,c_24]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_2,plain,
% 3.66/0.98      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X0))
% 3.66/0.98      | ~ v1_funct_1(X0)
% 3.66/0.98      | ~ v1_funct_1(X1)
% 3.66/0.98      | ~ v2_funct_1(X1)
% 3.66/0.98      | ~ v1_relat_1(X1)
% 3.66/0.98      | ~ v1_relat_1(X0)
% 3.66/0.98      | k5_relat_1(X0,X1) != X1
% 3.66/0.98      | k6_partfun1(k1_relat_1(X0)) = X0
% 3.66/0.98      | k1_relat_1(X1) != k1_relat_1(X0) ),
% 3.66/0.98      inference(cnf_transformation,[],[f58]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_13,negated_conjecture,
% 3.66/0.98      ( v2_funct_1(sK1) ),
% 3.66/0.98      inference(cnf_transformation,[],[f55]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_270,plain,
% 3.66/0.98      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X0))
% 3.66/0.98      | ~ v1_funct_1(X0)
% 3.66/0.98      | ~ v1_funct_1(X1)
% 3.66/0.98      | ~ v1_relat_1(X0)
% 3.66/0.98      | ~ v1_relat_1(X1)
% 3.66/0.98      | k5_relat_1(X0,X1) != X1
% 3.66/0.98      | k6_partfun1(k1_relat_1(X0)) = X0
% 3.66/0.98      | k1_relat_1(X1) != k1_relat_1(X0)
% 3.66/0.98      | sK1 != X1 ),
% 3.66/0.98      inference(resolution_lifted,[status(thm)],[c_2,c_13]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_271,plain,
% 3.66/0.98      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X0))
% 3.66/0.98      | ~ v1_funct_1(X0)
% 3.66/0.98      | ~ v1_funct_1(sK1)
% 3.66/0.98      | ~ v1_relat_1(X0)
% 3.66/0.98      | ~ v1_relat_1(sK1)
% 3.66/0.98      | k5_relat_1(X0,sK1) != sK1
% 3.66/0.98      | k6_partfun1(k1_relat_1(X0)) = X0
% 3.66/0.98      | k1_relat_1(sK1) != k1_relat_1(X0) ),
% 3.66/0.98      inference(unflattening,[status(thm)],[c_270]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_275,plain,
% 3.66/0.98      ( ~ v1_funct_1(X0)
% 3.66/0.98      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X0))
% 3.66/0.98      | ~ v1_relat_1(X0)
% 3.66/0.98      | ~ v1_relat_1(sK1)
% 3.66/0.98      | k5_relat_1(X0,sK1) != sK1
% 3.66/0.98      | k6_partfun1(k1_relat_1(X0)) = X0
% 3.66/0.98      | k1_relat_1(sK1) != k1_relat_1(X0) ),
% 3.66/0.98      inference(global_propositional_subsumption,
% 3.66/0.98                [status(thm)],
% 3.66/0.98                [c_271,c_20]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_276,plain,
% 3.66/0.98      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X0))
% 3.66/0.98      | ~ v1_funct_1(X0)
% 3.66/0.98      | ~ v1_relat_1(X0)
% 3.66/0.98      | ~ v1_relat_1(sK1)
% 3.66/0.98      | k5_relat_1(X0,sK1) != sK1
% 3.66/0.98      | k6_partfun1(k1_relat_1(X0)) = X0
% 3.66/0.98      | k1_relat_1(sK1) != k1_relat_1(X0) ),
% 3.66/0.98      inference(renaming,[status(thm)],[c_275]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_531,plain,
% 3.66/0.98      ( ~ r1_tarski(k2_relat_1(X0_47),k1_relat_1(X0_47))
% 3.66/0.98      | ~ v1_funct_1(X0_47)
% 3.66/0.98      | ~ v1_relat_1(X0_47)
% 3.66/0.98      | ~ v1_relat_1(sK1)
% 3.66/0.98      | k1_relat_1(sK1) != k1_relat_1(X0_47)
% 3.66/0.98      | k5_relat_1(X0_47,sK1) != sK1
% 3.66/0.98      | k6_partfun1(k1_relat_1(X0_47)) = X0_47 ),
% 3.66/0.98      inference(subtyping,[status(esa)],[c_276]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_852,plain,
% 3.66/0.98      ( k1_relat_1(sK1) != k1_relat_1(X0_47)
% 3.66/0.98      | k5_relat_1(X0_47,sK1) != sK1
% 3.66/0.98      | k6_partfun1(k1_relat_1(X0_47)) = X0_47
% 3.66/0.98      | r1_tarski(k2_relat_1(X0_47),k1_relat_1(X0_47)) != iProver_top
% 3.66/0.98      | v1_funct_1(X0_47) != iProver_top
% 3.66/0.98      | v1_relat_1(X0_47) != iProver_top
% 3.66/0.98      | v1_relat_1(sK1) != iProver_top ),
% 3.66/0.98      inference(predicate_to_equality,[status(thm)],[c_531]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_23,plain,
% 3.66/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.66/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_3,plain,
% 3.66/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.66/0.98      | v1_relat_1(X0) ),
% 3.66/0.98      inference(cnf_transformation,[],[f38]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_543,plain,
% 3.66/0.98      ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)))
% 3.66/0.98      | v1_relat_1(X0_47) ),
% 3.66/0.98      inference(subtyping,[status(esa)],[c_3]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_580,plain,
% 3.66/0.98      ( m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top
% 3.66/0.98      | v1_relat_1(X0_47) = iProver_top ),
% 3.66/0.98      inference(predicate_to_equality,[status(thm)],[c_543]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_582,plain,
% 3.66/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.66/0.98      | v1_relat_1(sK1) = iProver_top ),
% 3.66/0.98      inference(instantiation,[status(thm)],[c_580]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_602,plain,
% 3.66/0.98      ( k1_relat_1(sK1) != k1_relat_1(X0_47)
% 3.66/0.98      | k5_relat_1(X0_47,sK1) != sK1
% 3.66/0.98      | k6_partfun1(k1_relat_1(X0_47)) = X0_47
% 3.66/0.98      | r1_tarski(k2_relat_1(X0_47),k1_relat_1(X0_47)) != iProver_top
% 3.66/0.98      | v1_funct_1(X0_47) != iProver_top
% 3.66/0.98      | v1_relat_1(X0_47) != iProver_top
% 3.66/0.98      | v1_relat_1(sK1) != iProver_top ),
% 3.66/0.98      inference(predicate_to_equality,[status(thm)],[c_531]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1932,plain,
% 3.66/0.98      ( v1_relat_1(X0_47) != iProver_top
% 3.66/0.98      | v1_funct_1(X0_47) != iProver_top
% 3.66/0.98      | r1_tarski(k2_relat_1(X0_47),k1_relat_1(X0_47)) != iProver_top
% 3.66/0.98      | k6_partfun1(k1_relat_1(X0_47)) = X0_47
% 3.66/0.98      | k5_relat_1(X0_47,sK1) != sK1
% 3.66/0.98      | k1_relat_1(sK1) != k1_relat_1(X0_47) ),
% 3.66/0.98      inference(global_propositional_subsumption,
% 3.66/0.98                [status(thm)],
% 3.66/0.98                [c_852,c_23,c_582,c_602]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1933,plain,
% 3.66/0.98      ( k1_relat_1(sK1) != k1_relat_1(X0_47)
% 3.66/0.98      | k5_relat_1(X0_47,sK1) != sK1
% 3.66/0.98      | k6_partfun1(k1_relat_1(X0_47)) = X0_47
% 3.66/0.98      | r1_tarski(k2_relat_1(X0_47),k1_relat_1(X0_47)) != iProver_top
% 3.66/0.98      | v1_funct_1(X0_47) != iProver_top
% 3.66/0.98      | v1_relat_1(X0_47) != iProver_top ),
% 3.66/0.98      inference(renaming,[status(thm)],[c_1932]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_5,plain,
% 3.66/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.66/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.66/0.98      inference(cnf_transformation,[],[f40]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_542,plain,
% 3.66/0.98      ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)))
% 3.66/0.98      | k1_relset_1(X0_48,X1_48,X0_47) = k1_relat_1(X0_47) ),
% 3.66/0.98      inference(subtyping,[status(esa)],[c_5]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_843,plain,
% 3.66/0.98      ( k1_relset_1(X0_48,X1_48,X0_47) = k1_relat_1(X0_47)
% 3.66/0.98      | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top ),
% 3.66/0.98      inference(predicate_to_equality,[status(thm)],[c_542]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1086,plain,
% 3.66/0.98      ( k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) ),
% 3.66/0.98      inference(superposition,[status(thm)],[c_849,c_843]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_11,plain,
% 3.66/0.98      ( ~ v1_funct_2(X0,X1,X1)
% 3.66/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.66/0.98      | ~ v1_funct_1(X0)
% 3.66/0.98      | k1_relset_1(X1,X1,X0) = X1 ),
% 3.66/0.98      inference(cnf_transformation,[],[f47]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_19,negated_conjecture,
% 3.66/0.98      ( v1_funct_2(sK1,sK0,sK0) ),
% 3.66/0.98      inference(cnf_transformation,[],[f49]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_238,plain,
% 3.66/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.66/0.98      | ~ v1_funct_1(X0)
% 3.66/0.98      | k1_relset_1(X1,X1,X0) = X1
% 3.66/0.98      | sK1 != X0
% 3.66/0.98      | sK0 != X1 ),
% 3.66/0.98      inference(resolution_lifted,[status(thm)],[c_11,c_19]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_239,plain,
% 3.66/0.98      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.66/0.98      | ~ v1_funct_1(sK1)
% 3.66/0.98      | k1_relset_1(sK0,sK0,sK1) = sK0 ),
% 3.66/0.98      inference(unflattening,[status(thm)],[c_238]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_241,plain,
% 3.66/0.98      ( k1_relset_1(sK0,sK0,sK1) = sK0 ),
% 3.66/0.98      inference(global_propositional_subsumption,
% 3.66/0.98                [status(thm)],
% 3.66/0.98                [c_239,c_20,c_18]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_533,plain,
% 3.66/0.98      ( k1_relset_1(sK0,sK0,sK1) = sK0 ),
% 3.66/0.98      inference(subtyping,[status(esa)],[c_241]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1088,plain,
% 3.66/0.98      ( k1_relat_1(sK1) = sK0 ),
% 3.66/0.98      inference(light_normalisation,[status(thm)],[c_1086,c_533]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1936,plain,
% 3.66/0.98      ( k1_relat_1(X0_47) != sK0
% 3.66/0.98      | k5_relat_1(X0_47,sK1) != sK1
% 3.66/0.98      | k6_partfun1(k1_relat_1(X0_47)) = X0_47
% 3.66/0.98      | r1_tarski(k2_relat_1(X0_47),k1_relat_1(X0_47)) != iProver_top
% 3.66/0.98      | v1_funct_1(X0_47) != iProver_top
% 3.66/0.98      | v1_relat_1(X0_47) != iProver_top ),
% 3.66/0.98      inference(light_normalisation,[status(thm)],[c_1933,c_1088]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_2015,plain,
% 3.66/0.98      ( k1_relat_1(sK2) != sK0
% 3.66/0.98      | k6_partfun1(k1_relat_1(sK2)) = sK2
% 3.66/0.98      | r1_tarski(k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 3.66/0.98      | v1_funct_1(sK2) != iProver_top
% 3.66/0.98      | v1_relat_1(sK2) != iProver_top ),
% 3.66/0.98      inference(superposition,[status(thm)],[c_2012,c_1936]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1085,plain,
% 3.66/0.98      ( k1_relset_1(sK0,sK0,sK2) = k1_relat_1(sK2) ),
% 3.66/0.98      inference(superposition,[status(thm)],[c_847,c_843]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_16,negated_conjecture,
% 3.66/0.98      ( v1_funct_2(sK2,sK0,sK0) ),
% 3.66/0.98      inference(cnf_transformation,[],[f52]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_230,plain,
% 3.66/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.66/0.98      | ~ v1_funct_1(X0)
% 3.66/0.98      | k1_relset_1(X1,X1,X0) = X1
% 3.66/0.98      | sK2 != X0
% 3.66/0.98      | sK0 != X1 ),
% 3.66/0.98      inference(resolution_lifted,[status(thm)],[c_11,c_16]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_231,plain,
% 3.66/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.66/0.98      | ~ v1_funct_1(sK2)
% 3.66/0.98      | k1_relset_1(sK0,sK0,sK2) = sK0 ),
% 3.66/0.98      inference(unflattening,[status(thm)],[c_230]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_233,plain,
% 3.66/0.98      ( k1_relset_1(sK0,sK0,sK2) = sK0 ),
% 3.66/0.98      inference(global_propositional_subsumption,
% 3.66/0.98                [status(thm)],
% 3.66/0.98                [c_231,c_17,c_15]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_534,plain,
% 3.66/0.98      ( k1_relset_1(sK0,sK0,sK2) = sK0 ),
% 3.66/0.98      inference(subtyping,[status(esa)],[c_233]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1091,plain,
% 3.66/0.98      ( k1_relat_1(sK2) = sK0 ),
% 3.66/0.98      inference(light_normalisation,[status(thm)],[c_1085,c_534]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_2016,plain,
% 3.66/0.98      ( sK0 != sK0
% 3.66/0.98      | k6_partfun1(sK0) = sK2
% 3.66/0.98      | r1_tarski(k2_relat_1(sK2),sK0) != iProver_top
% 3.66/0.98      | v1_funct_1(sK2) != iProver_top
% 3.66/0.98      | v1_relat_1(sK2) != iProver_top ),
% 3.66/0.98      inference(light_normalisation,[status(thm)],[c_2015,c_1091]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_2017,plain,
% 3.66/0.98      ( k6_partfun1(sK0) = sK2
% 3.66/0.98      | r1_tarski(k2_relat_1(sK2),sK0) != iProver_top
% 3.66/0.98      | v1_funct_1(sK2) != iProver_top
% 3.66/0.98      | v1_relat_1(sK2) != iProver_top ),
% 3.66/0.98      inference(equality_resolution_simp,[status(thm)],[c_2016]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1,plain,
% 3.66/0.98      ( r1_tarski(k2_relat_1(X0),X1)
% 3.66/0.98      | ~ v5_relat_1(X0,X1)
% 3.66/0.98      | ~ v1_relat_1(X0) ),
% 3.66/0.98      inference(cnf_transformation,[],[f35]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_4,plain,
% 3.66/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.66/0.98      | v5_relat_1(X0,X2) ),
% 3.66/0.98      inference(cnf_transformation,[],[f39]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_249,plain,
% 3.66/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.66/0.98      | r1_tarski(k2_relat_1(X3),X4)
% 3.66/0.98      | ~ v1_relat_1(X3)
% 3.66/0.98      | X0 != X3
% 3.66/0.98      | X2 != X4 ),
% 3.66/0.98      inference(resolution_lifted,[status(thm)],[c_1,c_4]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_250,plain,
% 3.66/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.66/0.98      | r1_tarski(k2_relat_1(X0),X2)
% 3.66/0.98      | ~ v1_relat_1(X0) ),
% 3.66/0.98      inference(unflattening,[status(thm)],[c_249]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_254,plain,
% 3.66/0.98      ( r1_tarski(k2_relat_1(X0),X2)
% 3.66/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.66/0.98      inference(global_propositional_subsumption,
% 3.66/0.98                [status(thm)],
% 3.66/0.98                [c_250,c_3]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_255,plain,
% 3.66/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.66/0.98      | r1_tarski(k2_relat_1(X0),X2) ),
% 3.66/0.98      inference(renaming,[status(thm)],[c_254]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_532,plain,
% 3.66/0.98      ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)))
% 3.66/0.98      | r1_tarski(k2_relat_1(X0_47),X1_48) ),
% 3.66/0.98      inference(subtyping,[status(esa)],[c_255]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_851,plain,
% 3.66/0.98      ( m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top
% 3.66/0.98      | r1_tarski(k2_relat_1(X0_47),X1_48) = iProver_top ),
% 3.66/0.98      inference(predicate_to_equality,[status(thm)],[c_532]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1547,plain,
% 3.66/0.98      ( r1_tarski(k2_relat_1(sK2),sK0) = iProver_top ),
% 3.66/0.98      inference(superposition,[status(thm)],[c_847,c_851]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_842,plain,
% 3.66/0.98      ( m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top
% 3.66/0.98      | v1_relat_1(X0_47) = iProver_top ),
% 3.66/0.98      inference(predicate_to_equality,[status(thm)],[c_543]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1074,plain,
% 3.66/0.98      ( v1_relat_1(sK2) = iProver_top ),
% 3.66/0.98      inference(superposition,[status(thm)],[c_847,c_842]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_550,plain,
% 3.66/0.98      ( X0_47 != X1_47 | X2_47 != X1_47 | X2_47 = X0_47 ),
% 3.66/0.98      theory(equality) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_990,plain,
% 3.66/0.98      ( k6_partfun1(sK0) != X0_47
% 3.66/0.98      | sK2 != X0_47
% 3.66/0.98      | sK2 = k6_partfun1(sK0) ),
% 3.66/0.98      inference(instantiation,[status(thm)],[c_550]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1058,plain,
% 3.66/0.98      ( k6_partfun1(sK0) != sK2 | sK2 = k6_partfun1(sK0) | sK2 != sK2 ),
% 3.66/0.98      inference(instantiation,[status(thm)],[c_990]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_547,plain,( X0_49 = X0_49 ),theory(equality) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1011,plain,
% 3.66/0.98      ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
% 3.66/0.98      inference(instantiation,[status(thm)],[c_547]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_545,plain,( X0_47 = X0_47 ),theory(equality) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_1003,plain,
% 3.66/0.98      ( sK2 = sK2 ),
% 3.66/0.98      inference(instantiation,[status(thm)],[c_545]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_6,plain,
% 3.66/0.98      ( r2_relset_1(X0,X1,X2,X2)
% 3.66/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.66/0.98      inference(cnf_transformation,[],[f59]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_12,negated_conjecture,
% 3.66/0.98      ( ~ r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0)) ),
% 3.66/0.98      inference(cnf_transformation,[],[f56]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_351,plain,
% 3.66/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.66/0.98      | k6_partfun1(sK0) != X0
% 3.66/0.98      | sK2 != X0
% 3.66/0.98      | sK0 != X2
% 3.66/0.98      | sK0 != X1 ),
% 3.66/0.98      inference(resolution_lifted,[status(thm)],[c_6,c_12]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_352,plain,
% 3.66/0.98      ( ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.66/0.98      | sK2 != k6_partfun1(sK0) ),
% 3.66/0.98      inference(unflattening,[status(thm)],[c_351]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(c_530,plain,
% 3.66/0.98      ( ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.66/0.98      | sK2 != k6_partfun1(sK0) ),
% 3.66/0.98      inference(subtyping,[status(esa)],[c_352]) ).
% 3.66/0.98  
% 3.66/0.98  cnf(contradiction,plain,
% 3.66/0.98      ( $false ),
% 3.66/0.98      inference(minisat,
% 3.66/0.98                [status(thm)],
% 3.66/0.98                [c_7499,c_2017,c_1547,c_1074,c_1058,c_1011,c_1003,c_530,
% 3.66/0.98                 c_15,c_24]) ).
% 3.66/0.98  
% 3.66/0.98  
% 3.66/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.66/0.98  
% 3.66/0.98  ------                               Statistics
% 3.66/0.98  
% 3.66/0.98  ------ General
% 3.66/0.98  
% 3.66/0.98  abstr_ref_over_cycles:                  0
% 3.66/0.98  abstr_ref_under_cycles:                 0
% 3.66/0.98  gc_basic_clause_elim:                   0
% 3.66/0.98  forced_gc_time:                         0
% 3.66/0.98  parsing_time:                           0.009
% 3.66/0.98  unif_index_cands_time:                  0.
% 3.66/0.98  unif_index_add_time:                    0.
% 3.66/0.98  orderings_time:                         0.
% 3.66/0.98  out_proof_time:                         0.01
% 3.66/0.98  total_time:                             0.239
% 3.66/0.98  num_of_symbols:                         55
% 3.66/0.98  num_of_terms:                           4053
% 3.66/0.98  
% 3.66/0.98  ------ Preprocessing
% 3.66/0.98  
% 3.66/0.98  num_of_splits:                          0
% 3.66/0.98  num_of_split_atoms:                     0
% 3.66/0.98  num_of_reused_defs:                     0
% 3.66/0.98  num_eq_ax_congr_red:                    14
% 3.66/0.98  num_of_sem_filtered_clauses:            1
% 3.66/0.98  num_of_subtypes:                        5
% 3.66/0.98  monotx_restored_types:                  0
% 3.66/0.98  sat_num_of_epr_types:                   0
% 3.66/0.98  sat_num_of_non_cyclic_types:            0
% 3.66/0.98  sat_guarded_non_collapsed_types:        1
% 3.66/0.98  num_pure_diseq_elim:                    0
% 3.66/0.98  simp_replaced_by:                       0
% 3.66/0.98  res_preprocessed:                       106
% 3.66/0.98  prep_upred:                             0
% 3.66/0.98  prep_unflattend:                        20
% 3.66/0.98  smt_new_axioms:                         0
% 3.66/0.98  pred_elim_cands:                        4
% 3.66/0.98  pred_elim:                              4
% 3.66/0.98  pred_elim_cl:                           5
% 3.66/0.98  pred_elim_cycles:                       7
% 3.66/0.98  merged_defs:                            0
% 3.66/0.98  merged_defs_ncl:                        0
% 3.66/0.98  bin_hyper_res:                          0
% 3.66/0.98  prep_cycles:                            4
% 3.66/0.98  pred_elim_time:                         0.005
% 3.66/0.98  splitting_time:                         0.
% 3.66/0.98  sem_filter_time:                        0.
% 3.66/0.98  monotx_time:                            0.
% 3.66/0.98  subtype_inf_time:                       0.
% 3.66/0.98  
% 3.66/0.98  ------ Problem properties
% 3.66/0.98  
% 3.66/0.98  clauses:                                16
% 3.66/0.98  conjectures:                            4
% 3.66/0.98  epr:                                    2
% 3.66/0.98  horn:                                   16
% 3.66/0.98  ground:                                 9
% 3.66/0.98  unary:                                  6
% 3.66/0.98  binary:                                 6
% 3.66/0.98  lits:                                   40
% 3.66/0.98  lits_eq:                                11
% 3.66/0.98  fd_pure:                                0
% 3.66/0.98  fd_pseudo:                              0
% 3.66/0.98  fd_cond:                                0
% 3.66/0.98  fd_pseudo_cond:                         0
% 3.66/0.98  ac_symbols:                             0
% 3.66/0.98  
% 3.66/0.98  ------ Propositional Solver
% 3.66/0.98  
% 3.66/0.98  prop_solver_calls:                      30
% 3.66/0.98  prop_fast_solver_calls:                 921
% 3.66/0.98  smt_solver_calls:                       0
% 3.66/0.98  smt_fast_solver_calls:                  0
% 3.66/0.98  prop_num_of_clauses:                    1503
% 3.66/0.98  prop_preprocess_simplified:             4662
% 3.66/0.98  prop_fo_subsumed:                       76
% 3.66/0.98  prop_solver_time:                       0.
% 3.66/0.98  smt_solver_time:                        0.
% 3.66/0.98  smt_fast_solver_time:                   0.
% 3.66/0.98  prop_fast_solver_time:                  0.
% 3.66/0.98  prop_unsat_core_time:                   0.
% 3.66/0.98  
% 3.66/0.98  ------ QBF
% 3.66/0.98  
% 3.66/0.98  qbf_q_res:                              0
% 3.66/0.98  qbf_num_tautologies:                    0
% 3.66/0.98  qbf_prep_cycles:                        0
% 3.66/0.98  
% 3.66/0.98  ------ BMC1
% 3.66/0.98  
% 3.66/0.98  bmc1_current_bound:                     -1
% 3.66/0.98  bmc1_last_solved_bound:                 -1
% 3.66/0.98  bmc1_unsat_core_size:                   -1
% 3.66/0.98  bmc1_unsat_core_parents_size:           -1
% 3.66/0.98  bmc1_merge_next_fun:                    0
% 3.66/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.66/0.98  
% 3.66/0.98  ------ Instantiation
% 3.66/0.98  
% 3.66/0.98  inst_num_of_clauses:                    667
% 3.66/0.98  inst_num_in_passive:                    228
% 3.66/0.98  inst_num_in_active:                     361
% 3.66/0.98  inst_num_in_unprocessed:                77
% 3.66/0.98  inst_num_of_loops:                      389
% 3.66/0.98  inst_num_of_learning_restarts:          0
% 3.66/0.98  inst_num_moves_active_passive:          19
% 3.66/0.98  inst_lit_activity:                      0
% 3.66/0.98  inst_lit_activity_moves:                0
% 3.66/0.98  inst_num_tautologies:                   0
% 3.66/0.98  inst_num_prop_implied:                  0
% 3.66/0.98  inst_num_existing_simplified:           0
% 3.66/0.98  inst_num_eq_res_simplified:             0
% 3.66/0.98  inst_num_child_elim:                    0
% 3.66/0.98  inst_num_of_dismatching_blockings:      752
% 3.66/0.98  inst_num_of_non_proper_insts:           1240
% 3.66/0.98  inst_num_of_duplicates:                 0
% 3.66/0.98  inst_inst_num_from_inst_to_res:         0
% 3.66/0.98  inst_dismatching_checking_time:         0.
% 3.66/0.98  
% 3.66/0.98  ------ Resolution
% 3.66/0.98  
% 3.66/0.98  res_num_of_clauses:                     0
% 3.66/0.98  res_num_in_passive:                     0
% 3.66/0.98  res_num_in_active:                      0
% 3.66/0.98  res_num_of_loops:                       110
% 3.66/0.98  res_forward_subset_subsumed:            118
% 3.66/0.98  res_backward_subset_subsumed:           0
% 3.66/0.98  res_forward_subsumed:                   0
% 3.66/0.98  res_backward_subsumed:                  0
% 3.66/0.98  res_forward_subsumption_resolution:     0
% 3.66/0.98  res_backward_subsumption_resolution:    0
% 3.66/0.98  res_clause_to_clause_subsumption:       519
% 3.66/0.98  res_orphan_elimination:                 0
% 3.66/0.98  res_tautology_del:                      247
% 3.66/0.98  res_num_eq_res_simplified:              1
% 3.66/0.98  res_num_sel_changes:                    0
% 3.66/0.98  res_moves_from_active_to_pass:          0
% 3.66/0.98  
% 3.66/0.98  ------ Superposition
% 3.66/0.98  
% 3.66/0.98  sup_time_total:                         0.
% 3.66/0.98  sup_time_generating:                    0.
% 3.66/0.98  sup_time_sim_full:                      0.
% 3.66/0.98  sup_time_sim_immed:                     0.
% 3.66/0.98  
% 3.66/0.98  sup_num_of_clauses:                     179
% 3.66/0.98  sup_num_in_active:                      75
% 3.66/0.98  sup_num_in_passive:                     104
% 3.66/0.98  sup_num_of_loops:                       76
% 3.66/0.98  sup_fw_superposition:                   119
% 3.66/0.98  sup_bw_superposition:                   66
% 3.66/0.98  sup_immediate_simplified:               38
% 3.66/0.98  sup_given_eliminated:                   0
% 3.66/0.98  comparisons_done:                       0
% 3.66/0.98  comparisons_avoided:                    0
% 3.66/0.98  
% 3.66/0.98  ------ Simplifications
% 3.66/0.98  
% 3.66/0.98  
% 3.66/0.98  sim_fw_subset_subsumed:                 8
% 3.66/0.98  sim_bw_subset_subsumed:                 0
% 3.66/0.98  sim_fw_subsumed:                        0
% 3.66/0.98  sim_bw_subsumed:                        0
% 3.66/0.98  sim_fw_subsumption_res:                 2
% 3.66/0.98  sim_bw_subsumption_res:                 0
% 3.66/0.98  sim_tautology_del:                      2
% 3.66/0.98  sim_eq_tautology_del:                   10
% 3.66/0.98  sim_eq_res_simp:                        1
% 3.66/0.98  sim_fw_demodulated:                     0
% 3.66/0.98  sim_bw_demodulated:                     1
% 3.66/0.98  sim_light_normalised:                   35
% 3.66/0.98  sim_joinable_taut:                      0
% 3.66/0.98  sim_joinable_simp:                      0
% 3.66/0.98  sim_ac_normalised:                      0
% 3.66/0.98  sim_smt_subsumption:                    0
% 3.66/0.98  
%------------------------------------------------------------------------------
