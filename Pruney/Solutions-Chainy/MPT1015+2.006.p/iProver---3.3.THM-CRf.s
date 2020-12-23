%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:06:48 EST 2020

% Result     : Theorem 3.78s
% Output     : CNFRefutation 3.78s
% Verified   : 
% Statistics : Number of formulae       :  177 ( 517 expanded)
%              Number of clauses        :  110 ( 174 expanded)
%              Number of leaves         :   20 ( 122 expanded)
%              Depth                    :   19
%              Number of atoms          :  533 (2988 expanded)
%              Number of equality atoms :  173 ( 232 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   18 (   2 average)
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
    inference(ennf_transformation,[],[f15])).

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
    inference(flattening,[],[f36])).

fof(f41,plain,(
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

fof(f40,plain,
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

fof(f42,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0))
    & v2_funct_1(sK1)
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK2,sK0,sK0)
    & v1_funct_1(sK2)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f37,f41,f40])).

fof(f61,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f47,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f63,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f42])).

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

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f66,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f42])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f11,axiom,(
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
    inference(ennf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f32])).

fof(f58,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f33])).

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

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f67,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f64,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f42])).

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

fof(f57,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f62,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f24,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f49,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f12,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f72,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f49,f59])).

fof(f68,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_partfun1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f46,f59])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f73,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f55])).

fof(f69,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_588,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_953,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_588])).

cnf(c_5,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_597,plain,
    ( ~ v1_funct_1(X0_48)
    | ~ v1_relat_1(X0_48)
    | v1_relat_1(k2_funct_1(X0_48)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_944,plain,
    ( v1_funct_1(X0_48) != iProver_top
    | v1_relat_1(X0_48) != iProver_top
    | v1_relat_1(k2_funct_1(X0_48)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_597])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_589,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_952,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_589])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_596,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | v1_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_945,plain,
    ( m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_relat_1(X0_48) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_596])).

cnf(c_1092,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_952,c_945])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_591,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_950,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_591])).

cnf(c_1091,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_950,c_945])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k5_relat_1(k5_relat_1(X2,X0),X1) = k5_relat_1(X2,k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_600,plain,
    ( ~ v1_relat_1(X0_48)
    | ~ v1_relat_1(X1_48)
    | ~ v1_relat_1(X2_48)
    | k5_relat_1(k5_relat_1(X2_48,X0_48),X1_48) = k5_relat_1(X2_48,k5_relat_1(X0_48,X1_48)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_941,plain,
    ( k5_relat_1(k5_relat_1(X0_48,X1_48),X2_48) = k5_relat_1(X0_48,k5_relat_1(X1_48,X2_48))
    | v1_relat_1(X1_48) != iProver_top
    | v1_relat_1(X2_48) != iProver_top
    | v1_relat_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_600])).

cnf(c_1507,plain,
    ( k5_relat_1(sK2,k5_relat_1(X0_48,X1_48)) = k5_relat_1(k5_relat_1(sK2,X0_48),X1_48)
    | v1_relat_1(X0_48) != iProver_top
    | v1_relat_1(X1_48) != iProver_top ),
    inference(superposition,[status(thm)],[c_1091,c_941])).

cnf(c_2543,plain,
    ( k5_relat_1(k5_relat_1(sK2,sK1),X0_48) = k5_relat_1(sK2,k5_relat_1(sK1,X0_48))
    | v1_relat_1(X0_48) != iProver_top ),
    inference(superposition,[status(thm)],[c_1092,c_1507])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_592,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49)))
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(X1_48)
    | k1_partfun1(X2_49,X3_49,X0_49,X1_49,X1_48,X0_48) = k5_relat_1(X1_48,X0_48) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_949,plain,
    ( k1_partfun1(X0_49,X1_49,X2_49,X3_49,X0_48,X1_48) = k5_relat_1(X0_48,X1_48)
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(X1_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_592])).

cnf(c_1582,plain,
    ( k1_partfun1(X0_49,X1_49,sK0,sK0,X0_48,sK1) = k5_relat_1(X0_48,sK1)
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_952,c_949])).

cnf(c_26,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1805,plain,
    ( v1_funct_1(X0_48) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | k1_partfun1(X0_49,X1_49,sK0,sK0,X0_48,sK1) = k5_relat_1(X0_48,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1582,c_26])).

cnf(c_1806,plain,
    ( k1_partfun1(X0_49,X1_49,sK0,sK0,X0_48,sK1) = k5_relat_1(X0_48,sK1)
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(renaming,[status(thm)],[c_1805])).

cnf(c_1809,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) = k5_relat_1(sK2,sK1)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_950,c_1806])).

cnf(c_12,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_19,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_395,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) != X0
    | sK1 != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_19])).

cnf(c_396,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) ),
    inference(unflattening,[status(thm)],[c_395])).

cnf(c_398,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_396,c_23])).

cnf(c_581,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) ),
    inference(subtyping,[status(esa)],[c_398])).

cnf(c_958,plain,
    ( sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1)
    | m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_581])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_594,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49)))
    | m1_subset_1(k1_partfun1(X2_49,X3_49,X0_49,X1_49,X1_48,X0_48),k1_zfmisc_1(k2_zfmisc_1(X2_49,X1_49)))
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(X1_48) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_983,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_594])).

cnf(c_1374,plain,
    ( sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_958,c_25,c_23,c_22,c_20,c_581,c_983])).

cnf(c_1812,plain,
    ( k5_relat_1(sK2,sK1) = sK1
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1809,c_1374])).

cnf(c_29,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1913,plain,
    ( k5_relat_1(sK2,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1812,c_29])).

cnf(c_2546,plain,
    ( k5_relat_1(sK2,k5_relat_1(sK1,X0_48)) = k5_relat_1(sK1,X0_48)
    | v1_relat_1(X0_48) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2543,c_1913])).

cnf(c_13087,plain,
    ( k5_relat_1(sK2,k5_relat_1(sK1,k2_funct_1(X0_48))) = k5_relat_1(sK1,k2_funct_1(X0_48))
    | v1_funct_1(X0_48) != iProver_top
    | v1_relat_1(X0_48) != iProver_top ),
    inference(superposition,[status(thm)],[c_944,c_2546])).

cnf(c_13101,plain,
    ( k5_relat_1(sK2,k5_relat_1(sK1,k2_funct_1(sK1))) = k5_relat_1(sK1,k2_funct_1(sK1))
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_953,c_13087])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_595,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | k1_relset_1(X0_49,X1_49,X0_48) = k1_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_946,plain,
    ( k1_relset_1(X0_49,X1_49,X0_48) = k1_relat_1(X0_48)
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_595])).

cnf(c_1182,plain,
    ( k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_952,c_946])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(X1,X1,X0) = X1 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_329,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(X1,X1,X0) = X1
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_24])).

cnf(c_330,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | k1_relset_1(sK0,sK0,sK1) = sK0 ),
    inference(unflattening,[status(thm)],[c_329])).

cnf(c_332,plain,
    ( k1_relset_1(sK0,sK0,sK1) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_330,c_25,c_23])).

cnf(c_584,plain,
    ( k1_relset_1(sK0,sK0,sK1) = sK0 ),
    inference(subtyping,[status(esa)],[c_332])).

cnf(c_1183,plain,
    ( k1_relat_1(sK1) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_1182,c_584])).

cnf(c_7,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_18,negated_conjecture,
    ( v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_287,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_18])).

cnf(c_288,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
    inference(unflattening,[status(thm)],[c_287])).

cnf(c_290,plain,
    ( ~ v1_relat_1(sK1)
    | k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_288,c_25])).

cnf(c_587,plain,
    ( ~ v1_relat_1(sK1)
    | k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
    inference(subtyping,[status(esa)],[c_290])).

cnf(c_954,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
    | v1_relat_1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_587])).

cnf(c_652,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_596])).

cnf(c_1067,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_954,c_23,c_652,c_587])).

cnf(c_1254,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(sK0) ),
    inference(demodulation,[status(thm)],[c_1183,c_1067])).

cnf(c_1,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v5_relat_1(X0,X2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_340,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X3),X4)
    | ~ v1_relat_1(X3)
    | X0 != X3
    | X2 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_9])).

cnf(c_341,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_340])).

cnf(c_345,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_341,c_8])).

cnf(c_346,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_345])).

cnf(c_583,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | r1_tarski(k2_relat_1(X0_48),X1_49) ),
    inference(subtyping,[status(esa)],[c_346])).

cnf(c_956,plain,
    ( m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | r1_tarski(k2_relat_1(X0_48),X1_49) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_583])).

cnf(c_2112,plain,
    ( r1_tarski(k2_relat_1(sK2),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_950,c_956])).

cnf(c_3,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_partfun1(X1)) = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_599,plain,
    ( ~ r1_tarski(k2_relat_1(X0_48),X0_49)
    | ~ v1_relat_1(X0_48)
    | k5_relat_1(X0_48,k6_partfun1(X0_49)) = X0_48 ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_942,plain,
    ( k5_relat_1(X0_48,k6_partfun1(X0_49)) = X0_48
    | r1_tarski(k2_relat_1(X0_48),X0_49) != iProver_top
    | v1_relat_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_599])).

cnf(c_2121,plain,
    ( k5_relat_1(sK2,k6_partfun1(sK0)) = sK2
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2112,c_942])).

cnf(c_1084,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),X0_49)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(sK2,k6_partfun1(X0_49)) = sK2 ),
    inference(instantiation,[status(thm)],[c_599])).

cnf(c_1086,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK0)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(sK2,k6_partfun1(sK0)) = sK2 ),
    inference(instantiation,[status(thm)],[c_1084])).

cnf(c_1093,plain,
    ( v1_relat_1(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1091])).

cnf(c_1196,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | r1_tarski(k2_relat_1(sK2),X1_49) ),
    inference(instantiation,[status(thm)],[c_583])).

cnf(c_1198,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | r1_tarski(k2_relat_1(sK2),sK0) ),
    inference(instantiation,[status(thm)],[c_1196])).

cnf(c_2241,plain,
    ( k5_relat_1(sK2,k6_partfun1(sK0)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2121,c_20,c_1086,c_1093,c_1198])).

cnf(c_13107,plain,
    ( k6_partfun1(sK0) = sK2
    | v1_relat_1(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13101,c_1254,c_2241])).

cnf(c_604,plain,
    ( X0_50 = X0_50 ),
    theory(equality)).

cnf(c_5244,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)) = k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)) ),
    inference(instantiation,[status(thm)],[c_604])).

cnf(c_5245,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_5244])).

cnf(c_618,plain,
    ( ~ m1_subset_1(X0_48,X0_50)
    | m1_subset_1(X1_48,X1_50)
    | X1_50 != X0_50
    | X1_48 != X0_48 ),
    theory(equality)).

cnf(c_2593,plain,
    ( ~ m1_subset_1(X0_48,X0_50)
    | m1_subset_1(k6_partfun1(X0_49),k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49)))
    | k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49)) != X0_50
    | k6_partfun1(X0_49) != X0_48 ),
    inference(instantiation,[status(thm)],[c_618])).

cnf(c_3671,plain,
    ( m1_subset_1(k6_partfun1(X0_49),k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | k6_partfun1(X0_49) != sK2 ),
    inference(instantiation,[status(thm)],[c_2593])).

cnf(c_3673,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | k6_partfun1(sK0) != sK2 ),
    inference(instantiation,[status(thm)],[c_3671])).

cnf(c_602,plain,
    ( X0_48 = X0_48 ),
    theory(equality)).

cnf(c_1001,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_602])).

cnf(c_606,plain,
    ( X0_48 != X1_48
    | X2_48 != X1_48
    | X2_48 = X0_48 ),
    theory(equality)).

cnf(c_991,plain,
    ( k6_partfun1(sK0) != X0_48
    | sK2 != X0_48
    | sK2 = k6_partfun1(sK0) ),
    inference(instantiation,[status(thm)],[c_606])).

cnf(c_996,plain,
    ( k6_partfun1(sK0) != sK2
    | sK2 = k6_partfun1(sK0)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_991])).

cnf(c_11,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_17,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_385,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k6_partfun1(sK0) != X0
    | sK2 != X0
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_17])).

cnf(c_386,plain,
    ( ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK2 != k6_partfun1(sK0) ),
    inference(unflattening,[status(thm)],[c_385])).

cnf(c_582,plain,
    ( ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK2 != k6_partfun1(sK0) ),
    inference(subtyping,[status(esa)],[c_386])).

cnf(c_651,plain,
    ( m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_relat_1(X0_48) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_596])).

cnf(c_653,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_relat_1(sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_651])).

cnf(c_28,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13107,c_5245,c_3673,c_1001,c_996,c_582,c_653,c_20,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:09:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.78/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.78/0.99  
% 3.78/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.78/0.99  
% 3.78/0.99  ------  iProver source info
% 3.78/0.99  
% 3.78/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.78/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.78/0.99  git: non_committed_changes: false
% 3.78/0.99  git: last_make_outside_of_git: false
% 3.78/0.99  
% 3.78/0.99  ------ 
% 3.78/0.99  
% 3.78/0.99  ------ Input Options
% 3.78/0.99  
% 3.78/0.99  --out_options                           all
% 3.78/0.99  --tptp_safe_out                         true
% 3.78/0.99  --problem_path                          ""
% 3.78/0.99  --include_path                          ""
% 3.78/0.99  --clausifier                            res/vclausify_rel
% 3.78/0.99  --clausifier_options                    ""
% 3.78/0.99  --stdin                                 false
% 3.78/0.99  --stats_out                             all
% 3.78/0.99  
% 3.78/0.99  ------ General Options
% 3.78/0.99  
% 3.78/0.99  --fof                                   false
% 3.78/0.99  --time_out_real                         305.
% 3.78/0.99  --time_out_virtual                      -1.
% 3.78/0.99  --symbol_type_check                     false
% 3.78/0.99  --clausify_out                          false
% 3.78/0.99  --sig_cnt_out                           false
% 3.78/0.99  --trig_cnt_out                          false
% 3.78/0.99  --trig_cnt_out_tolerance                1.
% 3.78/0.99  --trig_cnt_out_sk_spl                   false
% 3.78/0.99  --abstr_cl_out                          false
% 3.78/0.99  
% 3.78/0.99  ------ Global Options
% 3.78/0.99  
% 3.78/0.99  --schedule                              default
% 3.78/0.99  --add_important_lit                     false
% 3.78/0.99  --prop_solver_per_cl                    1000
% 3.78/0.99  --min_unsat_core                        false
% 3.78/0.99  --soft_assumptions                      false
% 3.78/0.99  --soft_lemma_size                       3
% 3.78/0.99  --prop_impl_unit_size                   0
% 3.78/0.99  --prop_impl_unit                        []
% 3.78/0.99  --share_sel_clauses                     true
% 3.78/0.99  --reset_solvers                         false
% 3.78/0.99  --bc_imp_inh                            [conj_cone]
% 3.78/0.99  --conj_cone_tolerance                   3.
% 3.78/0.99  --extra_neg_conj                        none
% 3.78/0.99  --large_theory_mode                     true
% 3.78/0.99  --prolific_symb_bound                   200
% 3.78/0.99  --lt_threshold                          2000
% 3.78/0.99  --clause_weak_htbl                      true
% 3.78/0.99  --gc_record_bc_elim                     false
% 3.78/0.99  
% 3.78/0.99  ------ Preprocessing Options
% 3.78/0.99  
% 3.78/0.99  --preprocessing_flag                    true
% 3.78/0.99  --time_out_prep_mult                    0.1
% 3.78/0.99  --splitting_mode                        input
% 3.78/0.99  --splitting_grd                         true
% 3.78/0.99  --splitting_cvd                         false
% 3.78/0.99  --splitting_cvd_svl                     false
% 3.78/0.99  --splitting_nvd                         32
% 3.78/0.99  --sub_typing                            true
% 3.78/0.99  --prep_gs_sim                           true
% 3.78/0.99  --prep_unflatten                        true
% 3.78/0.99  --prep_res_sim                          true
% 3.78/0.99  --prep_upred                            true
% 3.78/0.99  --prep_sem_filter                       exhaustive
% 3.78/0.99  --prep_sem_filter_out                   false
% 3.78/0.99  --pred_elim                             true
% 3.78/0.99  --res_sim_input                         true
% 3.78/0.99  --eq_ax_congr_red                       true
% 3.78/0.99  --pure_diseq_elim                       true
% 3.78/0.99  --brand_transform                       false
% 3.78/0.99  --non_eq_to_eq                          false
% 3.78/0.99  --prep_def_merge                        true
% 3.78/0.99  --prep_def_merge_prop_impl              false
% 3.78/0.99  --prep_def_merge_mbd                    true
% 3.78/0.99  --prep_def_merge_tr_red                 false
% 3.78/0.99  --prep_def_merge_tr_cl                  false
% 3.78/0.99  --smt_preprocessing                     true
% 3.78/0.99  --smt_ac_axioms                         fast
% 3.78/0.99  --preprocessed_out                      false
% 3.78/0.99  --preprocessed_stats                    false
% 3.78/0.99  
% 3.78/0.99  ------ Abstraction refinement Options
% 3.78/0.99  
% 3.78/0.99  --abstr_ref                             []
% 3.78/0.99  --abstr_ref_prep                        false
% 3.78/0.99  --abstr_ref_until_sat                   false
% 3.78/0.99  --abstr_ref_sig_restrict                funpre
% 3.78/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.78/0.99  --abstr_ref_under                       []
% 3.78/0.99  
% 3.78/0.99  ------ SAT Options
% 3.78/0.99  
% 3.78/0.99  --sat_mode                              false
% 3.78/0.99  --sat_fm_restart_options                ""
% 3.78/0.99  --sat_gr_def                            false
% 3.78/0.99  --sat_epr_types                         true
% 3.78/0.99  --sat_non_cyclic_types                  false
% 3.78/0.99  --sat_finite_models                     false
% 3.78/0.99  --sat_fm_lemmas                         false
% 3.78/0.99  --sat_fm_prep                           false
% 3.78/0.99  --sat_fm_uc_incr                        true
% 3.78/0.99  --sat_out_model                         small
% 3.78/0.99  --sat_out_clauses                       false
% 3.78/0.99  
% 3.78/0.99  ------ QBF Options
% 3.78/0.99  
% 3.78/0.99  --qbf_mode                              false
% 3.78/0.99  --qbf_elim_univ                         false
% 3.78/0.99  --qbf_dom_inst                          none
% 3.78/0.99  --qbf_dom_pre_inst                      false
% 3.78/0.99  --qbf_sk_in                             false
% 3.78/0.99  --qbf_pred_elim                         true
% 3.78/0.99  --qbf_split                             512
% 3.78/0.99  
% 3.78/0.99  ------ BMC1 Options
% 3.78/0.99  
% 3.78/0.99  --bmc1_incremental                      false
% 3.78/0.99  --bmc1_axioms                           reachable_all
% 3.78/0.99  --bmc1_min_bound                        0
% 3.78/0.99  --bmc1_max_bound                        -1
% 3.78/0.99  --bmc1_max_bound_default                -1
% 3.78/0.99  --bmc1_symbol_reachability              true
% 3.78/0.99  --bmc1_property_lemmas                  false
% 3.78/0.99  --bmc1_k_induction                      false
% 3.78/0.99  --bmc1_non_equiv_states                 false
% 3.78/0.99  --bmc1_deadlock                         false
% 3.78/0.99  --bmc1_ucm                              false
% 3.78/0.99  --bmc1_add_unsat_core                   none
% 3.78/0.99  --bmc1_unsat_core_children              false
% 3.78/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.78/0.99  --bmc1_out_stat                         full
% 3.78/0.99  --bmc1_ground_init                      false
% 3.78/0.99  --bmc1_pre_inst_next_state              false
% 3.78/0.99  --bmc1_pre_inst_state                   false
% 3.78/0.99  --bmc1_pre_inst_reach_state             false
% 3.78/0.99  --bmc1_out_unsat_core                   false
% 3.78/0.99  --bmc1_aig_witness_out                  false
% 3.78/0.99  --bmc1_verbose                          false
% 3.78/0.99  --bmc1_dump_clauses_tptp                false
% 3.78/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.78/0.99  --bmc1_dump_file                        -
% 3.78/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.78/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.78/0.99  --bmc1_ucm_extend_mode                  1
% 3.78/0.99  --bmc1_ucm_init_mode                    2
% 3.78/0.99  --bmc1_ucm_cone_mode                    none
% 3.78/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.78/0.99  --bmc1_ucm_relax_model                  4
% 3.78/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.78/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.78/0.99  --bmc1_ucm_layered_model                none
% 3.78/0.99  --bmc1_ucm_max_lemma_size               10
% 3.78/0.99  
% 3.78/0.99  ------ AIG Options
% 3.78/0.99  
% 3.78/0.99  --aig_mode                              false
% 3.78/0.99  
% 3.78/0.99  ------ Instantiation Options
% 3.78/0.99  
% 3.78/0.99  --instantiation_flag                    true
% 3.78/0.99  --inst_sos_flag                         true
% 3.78/0.99  --inst_sos_phase                        true
% 3.78/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.78/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.78/0.99  --inst_lit_sel_side                     num_symb
% 3.78/0.99  --inst_solver_per_active                1400
% 3.78/0.99  --inst_solver_calls_frac                1.
% 3.78/0.99  --inst_passive_queue_type               priority_queues
% 3.78/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.78/0.99  --inst_passive_queues_freq              [25;2]
% 3.78/0.99  --inst_dismatching                      true
% 3.78/0.99  --inst_eager_unprocessed_to_passive     true
% 3.78/0.99  --inst_prop_sim_given                   true
% 3.78/0.99  --inst_prop_sim_new                     false
% 3.78/0.99  --inst_subs_new                         false
% 3.78/0.99  --inst_eq_res_simp                      false
% 3.78/0.99  --inst_subs_given                       false
% 3.78/0.99  --inst_orphan_elimination               true
% 3.78/0.99  --inst_learning_loop_flag               true
% 3.78/0.99  --inst_learning_start                   3000
% 3.78/0.99  --inst_learning_factor                  2
% 3.78/0.99  --inst_start_prop_sim_after_learn       3
% 3.78/0.99  --inst_sel_renew                        solver
% 3.78/0.99  --inst_lit_activity_flag                true
% 3.78/0.99  --inst_restr_to_given                   false
% 3.78/0.99  --inst_activity_threshold               500
% 3.78/0.99  --inst_out_proof                        true
% 3.78/0.99  
% 3.78/0.99  ------ Resolution Options
% 3.78/0.99  
% 3.78/0.99  --resolution_flag                       true
% 3.78/0.99  --res_lit_sel                           adaptive
% 3.78/0.99  --res_lit_sel_side                      none
% 3.78/0.99  --res_ordering                          kbo
% 3.78/0.99  --res_to_prop_solver                    active
% 3.78/0.99  --res_prop_simpl_new                    false
% 3.78/0.99  --res_prop_simpl_given                  true
% 3.78/0.99  --res_passive_queue_type                priority_queues
% 3.78/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.78/0.99  --res_passive_queues_freq               [15;5]
% 3.78/0.99  --res_forward_subs                      full
% 3.78/0.99  --res_backward_subs                     full
% 3.78/0.99  --res_forward_subs_resolution           true
% 3.78/0.99  --res_backward_subs_resolution          true
% 3.78/0.99  --res_orphan_elimination                true
% 3.78/0.99  --res_time_limit                        2.
% 3.78/0.99  --res_out_proof                         true
% 3.78/0.99  
% 3.78/0.99  ------ Superposition Options
% 3.78/0.99  
% 3.78/0.99  --superposition_flag                    true
% 3.78/0.99  --sup_passive_queue_type                priority_queues
% 3.78/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.78/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.78/0.99  --demod_completeness_check              fast
% 3.78/0.99  --demod_use_ground                      true
% 3.78/0.99  --sup_to_prop_solver                    passive
% 3.78/0.99  --sup_prop_simpl_new                    true
% 3.78/0.99  --sup_prop_simpl_given                  true
% 3.78/0.99  --sup_fun_splitting                     true
% 3.78/0.99  --sup_smt_interval                      50000
% 3.78/0.99  
% 3.78/0.99  ------ Superposition Simplification Setup
% 3.78/0.99  
% 3.78/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.78/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.78/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.78/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.78/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.78/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.78/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.78/0.99  --sup_immed_triv                        [TrivRules]
% 3.78/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.78/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.78/0.99  --sup_immed_bw_main                     []
% 3.78/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.78/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.78/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.78/0.99  --sup_input_bw                          []
% 3.78/0.99  
% 3.78/0.99  ------ Combination Options
% 3.78/0.99  
% 3.78/0.99  --comb_res_mult                         3
% 3.78/0.99  --comb_sup_mult                         2
% 3.78/0.99  --comb_inst_mult                        10
% 3.78/0.99  
% 3.78/0.99  ------ Debug Options
% 3.78/0.99  
% 3.78/0.99  --dbg_backtrace                         false
% 3.78/0.99  --dbg_dump_prop_clauses                 false
% 3.78/0.99  --dbg_dump_prop_clauses_file            -
% 3.78/0.99  --dbg_out_stat                          false
% 3.78/0.99  ------ Parsing...
% 3.78/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.78/0.99  
% 3.78/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.78/0.99  
% 3.78/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.78/0.99  
% 3.78/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.78/0.99  ------ Proving...
% 3.78/0.99  ------ Problem Properties 
% 3.78/0.99  
% 3.78/0.99  
% 3.78/0.99  clauses                                 21
% 3.78/0.99  conjectures                             4
% 3.78/0.99  EPR                                     2
% 3.78/0.99  Horn                                    21
% 3.78/0.99  unary                                   6
% 3.78/0.99  binary                                  8
% 3.78/0.99  lits                                    50
% 3.78/0.99  lits eq                                 12
% 3.78/0.99  fd_pure                                 0
% 3.78/0.99  fd_pseudo                               0
% 3.78/0.99  fd_cond                                 0
% 3.78/0.99  fd_pseudo_cond                          0
% 3.78/0.99  AC symbols                              0
% 3.78/0.99  
% 3.78/0.99  ------ Schedule dynamic 5 is on 
% 3.78/0.99  
% 3.78/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.78/0.99  
% 3.78/0.99  
% 3.78/0.99  ------ 
% 3.78/0.99  Current options:
% 3.78/0.99  ------ 
% 3.78/0.99  
% 3.78/0.99  ------ Input Options
% 3.78/0.99  
% 3.78/0.99  --out_options                           all
% 3.78/0.99  --tptp_safe_out                         true
% 3.78/0.99  --problem_path                          ""
% 3.78/0.99  --include_path                          ""
% 3.78/0.99  --clausifier                            res/vclausify_rel
% 3.78/0.99  --clausifier_options                    ""
% 3.78/0.99  --stdin                                 false
% 3.78/0.99  --stats_out                             all
% 3.78/0.99  
% 3.78/0.99  ------ General Options
% 3.78/0.99  
% 3.78/0.99  --fof                                   false
% 3.78/0.99  --time_out_real                         305.
% 3.78/0.99  --time_out_virtual                      -1.
% 3.78/0.99  --symbol_type_check                     false
% 3.78/0.99  --clausify_out                          false
% 3.78/0.99  --sig_cnt_out                           false
% 3.78/0.99  --trig_cnt_out                          false
% 3.78/0.99  --trig_cnt_out_tolerance                1.
% 3.78/0.99  --trig_cnt_out_sk_spl                   false
% 3.78/0.99  --abstr_cl_out                          false
% 3.78/0.99  
% 3.78/0.99  ------ Global Options
% 3.78/0.99  
% 3.78/0.99  --schedule                              default
% 3.78/0.99  --add_important_lit                     false
% 3.78/0.99  --prop_solver_per_cl                    1000
% 3.78/0.99  --min_unsat_core                        false
% 3.78/0.99  --soft_assumptions                      false
% 3.78/0.99  --soft_lemma_size                       3
% 3.78/0.99  --prop_impl_unit_size                   0
% 3.78/0.99  --prop_impl_unit                        []
% 3.78/0.99  --share_sel_clauses                     true
% 3.78/0.99  --reset_solvers                         false
% 3.78/0.99  --bc_imp_inh                            [conj_cone]
% 3.78/0.99  --conj_cone_tolerance                   3.
% 3.78/0.99  --extra_neg_conj                        none
% 3.78/0.99  --large_theory_mode                     true
% 3.78/0.99  --prolific_symb_bound                   200
% 3.78/0.99  --lt_threshold                          2000
% 3.78/0.99  --clause_weak_htbl                      true
% 3.78/0.99  --gc_record_bc_elim                     false
% 3.78/0.99  
% 3.78/0.99  ------ Preprocessing Options
% 3.78/0.99  
% 3.78/0.99  --preprocessing_flag                    true
% 3.78/0.99  --time_out_prep_mult                    0.1
% 3.78/0.99  --splitting_mode                        input
% 3.78/0.99  --splitting_grd                         true
% 3.78/0.99  --splitting_cvd                         false
% 3.78/0.99  --splitting_cvd_svl                     false
% 3.78/0.99  --splitting_nvd                         32
% 3.78/0.99  --sub_typing                            true
% 3.78/0.99  --prep_gs_sim                           true
% 3.78/0.99  --prep_unflatten                        true
% 3.78/0.99  --prep_res_sim                          true
% 3.78/0.99  --prep_upred                            true
% 3.78/0.99  --prep_sem_filter                       exhaustive
% 3.78/0.99  --prep_sem_filter_out                   false
% 3.78/0.99  --pred_elim                             true
% 3.78/0.99  --res_sim_input                         true
% 3.78/0.99  --eq_ax_congr_red                       true
% 3.78/0.99  --pure_diseq_elim                       true
% 3.78/0.99  --brand_transform                       false
% 3.78/0.99  --non_eq_to_eq                          false
% 3.78/0.99  --prep_def_merge                        true
% 3.78/0.99  --prep_def_merge_prop_impl              false
% 3.78/0.99  --prep_def_merge_mbd                    true
% 3.78/0.99  --prep_def_merge_tr_red                 false
% 3.78/0.99  --prep_def_merge_tr_cl                  false
% 3.78/0.99  --smt_preprocessing                     true
% 3.78/0.99  --smt_ac_axioms                         fast
% 3.78/0.99  --preprocessed_out                      false
% 3.78/0.99  --preprocessed_stats                    false
% 3.78/0.99  
% 3.78/0.99  ------ Abstraction refinement Options
% 3.78/0.99  
% 3.78/0.99  --abstr_ref                             []
% 3.78/0.99  --abstr_ref_prep                        false
% 3.78/0.99  --abstr_ref_until_sat                   false
% 3.78/0.99  --abstr_ref_sig_restrict                funpre
% 3.78/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.78/0.99  --abstr_ref_under                       []
% 3.78/0.99  
% 3.78/0.99  ------ SAT Options
% 3.78/0.99  
% 3.78/0.99  --sat_mode                              false
% 3.78/0.99  --sat_fm_restart_options                ""
% 3.78/0.99  --sat_gr_def                            false
% 3.78/0.99  --sat_epr_types                         true
% 3.78/0.99  --sat_non_cyclic_types                  false
% 3.78/0.99  --sat_finite_models                     false
% 3.78/0.99  --sat_fm_lemmas                         false
% 3.78/0.99  --sat_fm_prep                           false
% 3.78/0.99  --sat_fm_uc_incr                        true
% 3.78/0.99  --sat_out_model                         small
% 3.78/0.99  --sat_out_clauses                       false
% 3.78/0.99  
% 3.78/0.99  ------ QBF Options
% 3.78/0.99  
% 3.78/0.99  --qbf_mode                              false
% 3.78/0.99  --qbf_elim_univ                         false
% 3.78/0.99  --qbf_dom_inst                          none
% 3.78/0.99  --qbf_dom_pre_inst                      false
% 3.78/0.99  --qbf_sk_in                             false
% 3.78/0.99  --qbf_pred_elim                         true
% 3.78/0.99  --qbf_split                             512
% 3.78/0.99  
% 3.78/0.99  ------ BMC1 Options
% 3.78/0.99  
% 3.78/0.99  --bmc1_incremental                      false
% 3.78/0.99  --bmc1_axioms                           reachable_all
% 3.78/0.99  --bmc1_min_bound                        0
% 3.78/0.99  --bmc1_max_bound                        -1
% 3.78/0.99  --bmc1_max_bound_default                -1
% 3.78/0.99  --bmc1_symbol_reachability              true
% 3.78/0.99  --bmc1_property_lemmas                  false
% 3.78/0.99  --bmc1_k_induction                      false
% 3.78/0.99  --bmc1_non_equiv_states                 false
% 3.78/0.99  --bmc1_deadlock                         false
% 3.78/0.99  --bmc1_ucm                              false
% 3.78/0.99  --bmc1_add_unsat_core                   none
% 3.78/0.99  --bmc1_unsat_core_children              false
% 3.78/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.78/0.99  --bmc1_out_stat                         full
% 3.78/0.99  --bmc1_ground_init                      false
% 3.78/0.99  --bmc1_pre_inst_next_state              false
% 3.78/0.99  --bmc1_pre_inst_state                   false
% 3.78/0.99  --bmc1_pre_inst_reach_state             false
% 3.78/0.99  --bmc1_out_unsat_core                   false
% 3.78/0.99  --bmc1_aig_witness_out                  false
% 3.78/0.99  --bmc1_verbose                          false
% 3.78/0.99  --bmc1_dump_clauses_tptp                false
% 3.78/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.78/0.99  --bmc1_dump_file                        -
% 3.78/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.78/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.78/0.99  --bmc1_ucm_extend_mode                  1
% 3.78/0.99  --bmc1_ucm_init_mode                    2
% 3.78/0.99  --bmc1_ucm_cone_mode                    none
% 3.78/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.78/0.99  --bmc1_ucm_relax_model                  4
% 3.78/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.78/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.78/0.99  --bmc1_ucm_layered_model                none
% 3.78/0.99  --bmc1_ucm_max_lemma_size               10
% 3.78/0.99  
% 3.78/0.99  ------ AIG Options
% 3.78/0.99  
% 3.78/0.99  --aig_mode                              false
% 3.78/0.99  
% 3.78/0.99  ------ Instantiation Options
% 3.78/0.99  
% 3.78/0.99  --instantiation_flag                    true
% 3.78/0.99  --inst_sos_flag                         true
% 3.78/0.99  --inst_sos_phase                        true
% 3.78/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.78/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.78/0.99  --inst_lit_sel_side                     none
% 3.78/0.99  --inst_solver_per_active                1400
% 3.78/0.99  --inst_solver_calls_frac                1.
% 3.78/0.99  --inst_passive_queue_type               priority_queues
% 3.78/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.78/0.99  --inst_passive_queues_freq              [25;2]
% 3.78/0.99  --inst_dismatching                      true
% 3.78/0.99  --inst_eager_unprocessed_to_passive     true
% 3.78/0.99  --inst_prop_sim_given                   true
% 3.78/0.99  --inst_prop_sim_new                     false
% 3.78/0.99  --inst_subs_new                         false
% 3.78/0.99  --inst_eq_res_simp                      false
% 3.78/0.99  --inst_subs_given                       false
% 3.78/0.99  --inst_orphan_elimination               true
% 3.78/0.99  --inst_learning_loop_flag               true
% 3.78/0.99  --inst_learning_start                   3000
% 3.78/0.99  --inst_learning_factor                  2
% 3.78/0.99  --inst_start_prop_sim_after_learn       3
% 3.78/0.99  --inst_sel_renew                        solver
% 3.78/0.99  --inst_lit_activity_flag                true
% 3.78/0.99  --inst_restr_to_given                   false
% 3.78/0.99  --inst_activity_threshold               500
% 3.78/0.99  --inst_out_proof                        true
% 3.78/0.99  
% 3.78/0.99  ------ Resolution Options
% 3.78/0.99  
% 3.78/0.99  --resolution_flag                       false
% 3.78/0.99  --res_lit_sel                           adaptive
% 3.78/0.99  --res_lit_sel_side                      none
% 3.78/0.99  --res_ordering                          kbo
% 3.78/0.99  --res_to_prop_solver                    active
% 3.78/0.99  --res_prop_simpl_new                    false
% 3.78/0.99  --res_prop_simpl_given                  true
% 3.78/0.99  --res_passive_queue_type                priority_queues
% 3.78/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.78/0.99  --res_passive_queues_freq               [15;5]
% 3.78/0.99  --res_forward_subs                      full
% 3.78/0.99  --res_backward_subs                     full
% 3.78/0.99  --res_forward_subs_resolution           true
% 3.78/0.99  --res_backward_subs_resolution          true
% 3.78/0.99  --res_orphan_elimination                true
% 3.78/0.99  --res_time_limit                        2.
% 3.78/0.99  --res_out_proof                         true
% 3.78/0.99  
% 3.78/0.99  ------ Superposition Options
% 3.78/0.99  
% 3.78/0.99  --superposition_flag                    true
% 3.78/0.99  --sup_passive_queue_type                priority_queues
% 3.78/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.78/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.78/0.99  --demod_completeness_check              fast
% 3.78/0.99  --demod_use_ground                      true
% 3.78/0.99  --sup_to_prop_solver                    passive
% 3.78/0.99  --sup_prop_simpl_new                    true
% 3.78/0.99  --sup_prop_simpl_given                  true
% 3.78/0.99  --sup_fun_splitting                     true
% 3.78/0.99  --sup_smt_interval                      50000
% 3.78/0.99  
% 3.78/0.99  ------ Superposition Simplification Setup
% 3.78/0.99  
% 3.78/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.78/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.78/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.78/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.78/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.78/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.78/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.78/0.99  --sup_immed_triv                        [TrivRules]
% 3.78/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.78/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.78/0.99  --sup_immed_bw_main                     []
% 3.78/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.78/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.78/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.78/0.99  --sup_input_bw                          []
% 3.78/0.99  
% 3.78/0.99  ------ Combination Options
% 3.78/0.99  
% 3.78/0.99  --comb_res_mult                         3
% 3.78/0.99  --comb_sup_mult                         2
% 3.78/0.99  --comb_inst_mult                        10
% 3.78/0.99  
% 3.78/0.99  ------ Debug Options
% 3.78/0.99  
% 3.78/0.99  --dbg_backtrace                         false
% 3.78/0.99  --dbg_dump_prop_clauses                 false
% 3.78/0.99  --dbg_dump_prop_clauses_file            -
% 3.78/0.99  --dbg_out_stat                          false
% 3.78/0.99  
% 3.78/0.99  
% 3.78/0.99  
% 3.78/0.99  
% 3.78/0.99  ------ Proving...
% 3.78/0.99  
% 3.78/0.99  
% 3.78/0.99  % SZS status Theorem for theBenchmark.p
% 3.78/0.99  
% 3.78/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.78/0.99  
% 3.78/0.99  fof(f14,conjecture,(
% 3.78/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)) => r2_relset_1(X0,X0,X2,k6_partfun1(X0)))))),
% 3.78/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f15,negated_conjecture,(
% 3.78/0.99    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)) => r2_relset_1(X0,X0,X2,k6_partfun1(X0)))))),
% 3.78/0.99    inference(negated_conjecture,[],[f14])).
% 3.78/0.99  
% 3.78/0.99  fof(f36,plain,(
% 3.78/0.99    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & (v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 3.78/0.99    inference(ennf_transformation,[],[f15])).
% 3.78/0.99  
% 3.78/0.99  fof(f37,plain,(
% 3.78/0.99    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 3.78/0.99    inference(flattening,[],[f36])).
% 3.78/0.99  
% 3.78/0.99  fof(f41,plain,(
% 3.78/0.99    ( ! [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (~r2_relset_1(X0,X0,sK2,k6_partfun1(X0)) & v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,sK2,X1),X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(sK2,X0,X0) & v1_funct_1(sK2))) )),
% 3.78/0.99    introduced(choice_axiom,[])).
% 3.78/0.99  
% 3.78/0.99  fof(f40,plain,(
% 3.78/0.99    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK0,sK0,X2,k6_partfun1(sK0)) & v2_funct_1(sK1) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,X2,sK1),sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 3.78/0.99    introduced(choice_axiom,[])).
% 3.78/0.99  
% 3.78/0.99  fof(f42,plain,(
% 3.78/0.99    (~r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0)) & v2_funct_1(sK1) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 3.78/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f37,f41,f40])).
% 3.78/0.99  
% 3.78/0.99  fof(f61,plain,(
% 3.78/0.99    v1_funct_1(sK1)),
% 3.78/0.99    inference(cnf_transformation,[],[f42])).
% 3.78/0.99  
% 3.78/0.99  fof(f4,axiom,(
% 3.78/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.78/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f21,plain,(
% 3.78/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.78/0.99    inference(ennf_transformation,[],[f4])).
% 3.78/0.99  
% 3.78/0.99  fof(f22,plain,(
% 3.78/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.78/0.99    inference(flattening,[],[f21])).
% 3.78/0.99  
% 3.78/0.99  fof(f47,plain,(
% 3.78/0.99    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.78/0.99    inference(cnf_transformation,[],[f22])).
% 3.78/0.99  
% 3.78/0.99  fof(f63,plain,(
% 3.78/0.99    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.78/0.99    inference(cnf_transformation,[],[f42])).
% 3.78/0.99  
% 3.78/0.99  fof(f6,axiom,(
% 3.78/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.78/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f25,plain,(
% 3.78/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.78/0.99    inference(ennf_transformation,[],[f6])).
% 3.78/0.99  
% 3.78/0.99  fof(f51,plain,(
% 3.78/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.78/0.99    inference(cnf_transformation,[],[f25])).
% 3.78/0.99  
% 3.78/0.99  fof(f66,plain,(
% 3.78/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.78/0.99    inference(cnf_transformation,[],[f42])).
% 3.78/0.99  
% 3.78/0.99  fof(f2,axiom,(
% 3.78/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2))))),
% 3.78/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f18,plain,(
% 3.78/0.99    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.78/0.99    inference(ennf_transformation,[],[f2])).
% 3.78/0.99  
% 3.78/0.99  fof(f45,plain,(
% 3.78/0.99    ( ! [X2,X0,X1] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.78/0.99    inference(cnf_transformation,[],[f18])).
% 3.78/0.99  
% 3.78/0.99  fof(f11,axiom,(
% 3.78/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.78/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f32,plain,(
% 3.78/0.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.78/0.99    inference(ennf_transformation,[],[f11])).
% 3.78/0.99  
% 3.78/0.99  fof(f33,plain,(
% 3.78/0.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.78/0.99    inference(flattening,[],[f32])).
% 3.78/0.99  
% 3.78/0.99  fof(f58,plain,(
% 3.78/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.78/0.99    inference(cnf_transformation,[],[f33])).
% 3.78/0.99  
% 3.78/0.99  fof(f9,axiom,(
% 3.78/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.78/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f28,plain,(
% 3.78/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.78/0.99    inference(ennf_transformation,[],[f9])).
% 3.78/0.99  
% 3.78/0.99  fof(f29,plain,(
% 3.78/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.78/0.99    inference(flattening,[],[f28])).
% 3.78/0.99  
% 3.78/0.99  fof(f39,plain,(
% 3.78/0.99    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.78/0.99    inference(nnf_transformation,[],[f29])).
% 3.78/0.99  
% 3.78/0.99  fof(f54,plain,(
% 3.78/0.99    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.78/0.99    inference(cnf_transformation,[],[f39])).
% 3.78/0.99  
% 3.78/0.99  fof(f67,plain,(
% 3.78/0.99    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1)),
% 3.78/0.99    inference(cnf_transformation,[],[f42])).
% 3.78/0.99  
% 3.78/0.99  fof(f64,plain,(
% 3.78/0.99    v1_funct_1(sK2)),
% 3.78/0.99    inference(cnf_transformation,[],[f42])).
% 3.78/0.99  
% 3.78/0.99  fof(f10,axiom,(
% 3.78/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 3.78/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f30,plain,(
% 3.78/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.78/0.99    inference(ennf_transformation,[],[f10])).
% 3.78/0.99  
% 3.78/0.99  fof(f31,plain,(
% 3.78/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.78/0.99    inference(flattening,[],[f30])).
% 3.78/0.99  
% 3.78/0.99  fof(f57,plain,(
% 3.78/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.78/0.99    inference(cnf_transformation,[],[f31])).
% 3.78/0.99  
% 3.78/0.99  fof(f8,axiom,(
% 3.78/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.78/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f27,plain,(
% 3.78/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.78/0.99    inference(ennf_transformation,[],[f8])).
% 3.78/0.99  
% 3.78/0.99  fof(f53,plain,(
% 3.78/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.78/0.99    inference(cnf_transformation,[],[f27])).
% 3.78/0.99  
% 3.78/0.99  fof(f13,axiom,(
% 3.78/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 3.78/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f34,plain,(
% 3.78/0.99    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.78/0.99    inference(ennf_transformation,[],[f13])).
% 3.78/0.99  
% 3.78/0.99  fof(f35,plain,(
% 3.78/0.99    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.78/0.99    inference(flattening,[],[f34])).
% 3.78/0.99  
% 3.78/0.99  fof(f60,plain,(
% 3.78/0.99    ( ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.78/0.99    inference(cnf_transformation,[],[f35])).
% 3.78/0.99  
% 3.78/0.99  fof(f62,plain,(
% 3.78/0.99    v1_funct_2(sK1,sK0,sK0)),
% 3.78/0.99    inference(cnf_transformation,[],[f42])).
% 3.78/0.99  
% 3.78/0.99  fof(f5,axiom,(
% 3.78/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 3.78/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f23,plain,(
% 3.78/0.99    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.78/0.99    inference(ennf_transformation,[],[f5])).
% 3.78/0.99  
% 3.78/0.99  fof(f24,plain,(
% 3.78/0.99    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.78/0.99    inference(flattening,[],[f23])).
% 3.78/0.99  
% 3.78/0.99  fof(f49,plain,(
% 3.78/0.99    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.78/0.99    inference(cnf_transformation,[],[f24])).
% 3.78/0.99  
% 3.78/0.99  fof(f12,axiom,(
% 3.78/0.99    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.78/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f59,plain,(
% 3.78/0.99    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.78/0.99    inference(cnf_transformation,[],[f12])).
% 3.78/0.99  
% 3.78/0.99  fof(f72,plain,(
% 3.78/0.99    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.78/0.99    inference(definition_unfolding,[],[f49,f59])).
% 3.78/0.99  
% 3.78/0.99  fof(f68,plain,(
% 3.78/0.99    v2_funct_1(sK1)),
% 3.78/0.99    inference(cnf_transformation,[],[f42])).
% 3.78/0.99  
% 3.78/0.99  fof(f1,axiom,(
% 3.78/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.78/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f17,plain,(
% 3.78/0.99    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.78/0.99    inference(ennf_transformation,[],[f1])).
% 3.78/0.99  
% 3.78/0.99  fof(f38,plain,(
% 3.78/0.99    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.78/0.99    inference(nnf_transformation,[],[f17])).
% 3.78/0.99  
% 3.78/0.99  fof(f43,plain,(
% 3.78/0.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.78/0.99    inference(cnf_transformation,[],[f38])).
% 3.78/0.99  
% 3.78/0.99  fof(f7,axiom,(
% 3.78/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.78/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f16,plain,(
% 3.78/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.78/0.99    inference(pure_predicate_removal,[],[f7])).
% 3.78/0.99  
% 3.78/0.99  fof(f26,plain,(
% 3.78/0.99    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.78/0.99    inference(ennf_transformation,[],[f16])).
% 3.78/0.99  
% 3.78/0.99  fof(f52,plain,(
% 3.78/0.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.78/0.99    inference(cnf_transformation,[],[f26])).
% 3.78/0.99  
% 3.78/0.99  fof(f3,axiom,(
% 3.78/0.99    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 3.78/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.78/0.99  
% 3.78/0.99  fof(f19,plain,(
% 3.78/0.99    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.78/0.99    inference(ennf_transformation,[],[f3])).
% 3.78/0.99  
% 3.78/0.99  fof(f20,plain,(
% 3.78/0.99    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 3.78/0.99    inference(flattening,[],[f19])).
% 3.78/0.99  
% 3.78/0.99  fof(f46,plain,(
% 3.78/0.99    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.78/0.99    inference(cnf_transformation,[],[f20])).
% 3.78/0.99  
% 3.78/0.99  fof(f70,plain,(
% 3.78/0.99    ( ! [X0,X1] : (k5_relat_1(X1,k6_partfun1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.78/0.99    inference(definition_unfolding,[],[f46,f59])).
% 3.78/0.99  
% 3.78/0.99  fof(f55,plain,(
% 3.78/0.99    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.78/0.99    inference(cnf_transformation,[],[f39])).
% 3.78/0.99  
% 3.78/0.99  fof(f73,plain,(
% 3.78/0.99    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.78/0.99    inference(equality_resolution,[],[f55])).
% 3.78/0.99  
% 3.78/0.99  fof(f69,plain,(
% 3.78/0.99    ~r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0))),
% 3.78/0.99    inference(cnf_transformation,[],[f42])).
% 3.78/0.99  
% 3.78/0.99  cnf(c_25,negated_conjecture,
% 3.78/0.99      ( v1_funct_1(sK1) ),
% 3.78/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_588,negated_conjecture,
% 3.78/0.99      ( v1_funct_1(sK1) ),
% 3.78/0.99      inference(subtyping,[status(esa)],[c_25]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_953,plain,
% 3.78/0.99      ( v1_funct_1(sK1) = iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_588]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_5,plain,
% 3.78/0.99      ( ~ v1_funct_1(X0)
% 3.78/0.99      | ~ v1_relat_1(X0)
% 3.78/0.99      | v1_relat_1(k2_funct_1(X0)) ),
% 3.78/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_597,plain,
% 3.78/0.99      ( ~ v1_funct_1(X0_48)
% 3.78/0.99      | ~ v1_relat_1(X0_48)
% 3.78/0.99      | v1_relat_1(k2_funct_1(X0_48)) ),
% 3.78/0.99      inference(subtyping,[status(esa)],[c_5]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_944,plain,
% 3.78/0.99      ( v1_funct_1(X0_48) != iProver_top
% 3.78/0.99      | v1_relat_1(X0_48) != iProver_top
% 3.78/0.99      | v1_relat_1(k2_funct_1(X0_48)) = iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_597]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_23,negated_conjecture,
% 3.78/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.78/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_589,negated_conjecture,
% 3.78/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.78/0.99      inference(subtyping,[status(esa)],[c_23]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_952,plain,
% 3.78/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_589]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_8,plain,
% 3.78/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.78/0.99      | v1_relat_1(X0) ),
% 3.78/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_596,plain,
% 3.78/0.99      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 3.78/0.99      | v1_relat_1(X0_48) ),
% 3.78/0.99      inference(subtyping,[status(esa)],[c_8]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_945,plain,
% 3.78/0.99      ( m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 3.78/0.99      | v1_relat_1(X0_48) = iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_596]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1092,plain,
% 3.78/0.99      ( v1_relat_1(sK1) = iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_952,c_945]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_20,negated_conjecture,
% 3.78/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.78/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_591,negated_conjecture,
% 3.78/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.78/0.99      inference(subtyping,[status(esa)],[c_20]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_950,plain,
% 3.78/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_591]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1091,plain,
% 3.78/0.99      ( v1_relat_1(sK2) = iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_950,c_945]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_2,plain,
% 3.78/0.99      ( ~ v1_relat_1(X0)
% 3.78/0.99      | ~ v1_relat_1(X1)
% 3.78/0.99      | ~ v1_relat_1(X2)
% 3.78/0.99      | k5_relat_1(k5_relat_1(X2,X0),X1) = k5_relat_1(X2,k5_relat_1(X0,X1)) ),
% 3.78/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_600,plain,
% 3.78/0.99      ( ~ v1_relat_1(X0_48)
% 3.78/0.99      | ~ v1_relat_1(X1_48)
% 3.78/0.99      | ~ v1_relat_1(X2_48)
% 3.78/0.99      | k5_relat_1(k5_relat_1(X2_48,X0_48),X1_48) = k5_relat_1(X2_48,k5_relat_1(X0_48,X1_48)) ),
% 3.78/0.99      inference(subtyping,[status(esa)],[c_2]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_941,plain,
% 3.78/0.99      ( k5_relat_1(k5_relat_1(X0_48,X1_48),X2_48) = k5_relat_1(X0_48,k5_relat_1(X1_48,X2_48))
% 3.78/0.99      | v1_relat_1(X1_48) != iProver_top
% 3.78/0.99      | v1_relat_1(X2_48) != iProver_top
% 3.78/0.99      | v1_relat_1(X0_48) != iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_600]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1507,plain,
% 3.78/0.99      ( k5_relat_1(sK2,k5_relat_1(X0_48,X1_48)) = k5_relat_1(k5_relat_1(sK2,X0_48),X1_48)
% 3.78/0.99      | v1_relat_1(X0_48) != iProver_top
% 3.78/0.99      | v1_relat_1(X1_48) != iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_1091,c_941]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_2543,plain,
% 3.78/0.99      ( k5_relat_1(k5_relat_1(sK2,sK1),X0_48) = k5_relat_1(sK2,k5_relat_1(sK1,X0_48))
% 3.78/0.99      | v1_relat_1(X0_48) != iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_1092,c_1507]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_15,plain,
% 3.78/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.78/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.78/0.99      | ~ v1_funct_1(X0)
% 3.78/0.99      | ~ v1_funct_1(X3)
% 3.78/0.99      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.78/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_592,plain,
% 3.78/0.99      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 3.78/0.99      | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49)))
% 3.78/0.99      | ~ v1_funct_1(X0_48)
% 3.78/0.99      | ~ v1_funct_1(X1_48)
% 3.78/0.99      | k1_partfun1(X2_49,X3_49,X0_49,X1_49,X1_48,X0_48) = k5_relat_1(X1_48,X0_48) ),
% 3.78/0.99      inference(subtyping,[status(esa)],[c_15]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_949,plain,
% 3.78/0.99      ( k1_partfun1(X0_49,X1_49,X2_49,X3_49,X0_48,X1_48) = k5_relat_1(X0_48,X1_48)
% 3.78/0.99      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 3.78/0.99      | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49))) != iProver_top
% 3.78/0.99      | v1_funct_1(X0_48) != iProver_top
% 3.78/0.99      | v1_funct_1(X1_48) != iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_592]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1582,plain,
% 3.78/0.99      ( k1_partfun1(X0_49,X1_49,sK0,sK0,X0_48,sK1) = k5_relat_1(X0_48,sK1)
% 3.78/0.99      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 3.78/0.99      | v1_funct_1(X0_48) != iProver_top
% 3.78/0.99      | v1_funct_1(sK1) != iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_952,c_949]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_26,plain,
% 3.78/0.99      ( v1_funct_1(sK1) = iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1805,plain,
% 3.78/0.99      ( v1_funct_1(X0_48) != iProver_top
% 3.78/0.99      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 3.78/0.99      | k1_partfun1(X0_49,X1_49,sK0,sK0,X0_48,sK1) = k5_relat_1(X0_48,sK1) ),
% 3.78/0.99      inference(global_propositional_subsumption,
% 3.78/0.99                [status(thm)],
% 3.78/0.99                [c_1582,c_26]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1806,plain,
% 3.78/0.99      ( k1_partfun1(X0_49,X1_49,sK0,sK0,X0_48,sK1) = k5_relat_1(X0_48,sK1)
% 3.78/0.99      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 3.78/0.99      | v1_funct_1(X0_48) != iProver_top ),
% 3.78/0.99      inference(renaming,[status(thm)],[c_1805]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1809,plain,
% 3.78/0.99      ( k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) = k5_relat_1(sK2,sK1)
% 3.78/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_950,c_1806]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_12,plain,
% 3.78/0.99      ( ~ r2_relset_1(X0,X1,X2,X3)
% 3.78/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.78/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.78/0.99      | X3 = X2 ),
% 3.78/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_19,negated_conjecture,
% 3.78/0.99      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1) ),
% 3.78/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_395,plain,
% 3.78/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.78/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.78/0.99      | X3 = X0
% 3.78/0.99      | k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) != X0
% 3.78/0.99      | sK1 != X3
% 3.78/0.99      | sK0 != X2
% 3.78/0.99      | sK0 != X1 ),
% 3.78/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_19]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_396,plain,
% 3.78/0.99      ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.78/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.78/0.99      | sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) ),
% 3.78/0.99      inference(unflattening,[status(thm)],[c_395]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_398,plain,
% 3.78/0.99      ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.78/0.99      | sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) ),
% 3.78/0.99      inference(global_propositional_subsumption,
% 3.78/0.99                [status(thm)],
% 3.78/0.99                [c_396,c_23]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_581,plain,
% 3.78/0.99      ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.78/0.99      | sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) ),
% 3.78/0.99      inference(subtyping,[status(esa)],[c_398]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_958,plain,
% 3.78/0.99      ( sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1)
% 3.78/0.99      | m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_581]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_22,negated_conjecture,
% 3.78/0.99      ( v1_funct_1(sK2) ),
% 3.78/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_13,plain,
% 3.78/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.78/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.78/0.99      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.78/0.99      | ~ v1_funct_1(X0)
% 3.78/0.99      | ~ v1_funct_1(X3) ),
% 3.78/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_594,plain,
% 3.78/0.99      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 3.78/0.99      | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49)))
% 3.78/0.99      | m1_subset_1(k1_partfun1(X2_49,X3_49,X0_49,X1_49,X1_48,X0_48),k1_zfmisc_1(k2_zfmisc_1(X2_49,X1_49)))
% 3.78/0.99      | ~ v1_funct_1(X0_48)
% 3.78/0.99      | ~ v1_funct_1(X1_48) ),
% 3.78/0.99      inference(subtyping,[status(esa)],[c_13]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_983,plain,
% 3.78/0.99      ( m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.78/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.78/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.78/0.99      | ~ v1_funct_1(sK1)
% 3.78/0.99      | ~ v1_funct_1(sK2) ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_594]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1374,plain,
% 3.78/0.99      ( sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) ),
% 3.78/0.99      inference(global_propositional_subsumption,
% 3.78/0.99                [status(thm)],
% 3.78/0.99                [c_958,c_25,c_23,c_22,c_20,c_581,c_983]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1812,plain,
% 3.78/0.99      ( k5_relat_1(sK2,sK1) = sK1 | v1_funct_1(sK2) != iProver_top ),
% 3.78/0.99      inference(light_normalisation,[status(thm)],[c_1809,c_1374]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_29,plain,
% 3.78/0.99      ( v1_funct_1(sK2) = iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1913,plain,
% 3.78/0.99      ( k5_relat_1(sK2,sK1) = sK1 ),
% 3.78/0.99      inference(global_propositional_subsumption,
% 3.78/0.99                [status(thm)],
% 3.78/0.99                [c_1812,c_29]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_2546,plain,
% 3.78/0.99      ( k5_relat_1(sK2,k5_relat_1(sK1,X0_48)) = k5_relat_1(sK1,X0_48)
% 3.78/0.99      | v1_relat_1(X0_48) != iProver_top ),
% 3.78/0.99      inference(light_normalisation,[status(thm)],[c_2543,c_1913]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_13087,plain,
% 3.78/0.99      ( k5_relat_1(sK2,k5_relat_1(sK1,k2_funct_1(X0_48))) = k5_relat_1(sK1,k2_funct_1(X0_48))
% 3.78/0.99      | v1_funct_1(X0_48) != iProver_top
% 3.78/0.99      | v1_relat_1(X0_48) != iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_944,c_2546]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_13101,plain,
% 3.78/0.99      ( k5_relat_1(sK2,k5_relat_1(sK1,k2_funct_1(sK1))) = k5_relat_1(sK1,k2_funct_1(sK1))
% 3.78/0.99      | v1_relat_1(sK1) != iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_953,c_13087]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_10,plain,
% 3.78/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.78/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.78/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_595,plain,
% 3.78/0.99      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 3.78/0.99      | k1_relset_1(X0_49,X1_49,X0_48) = k1_relat_1(X0_48) ),
% 3.78/0.99      inference(subtyping,[status(esa)],[c_10]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_946,plain,
% 3.78/0.99      ( k1_relset_1(X0_49,X1_49,X0_48) = k1_relat_1(X0_48)
% 3.78/0.99      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_595]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1182,plain,
% 3.78/0.99      ( k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_952,c_946]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_16,plain,
% 3.78/0.99      ( ~ v1_funct_2(X0,X1,X1)
% 3.78/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.78/0.99      | ~ v1_funct_1(X0)
% 3.78/0.99      | k1_relset_1(X1,X1,X0) = X1 ),
% 3.78/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_24,negated_conjecture,
% 3.78/0.99      ( v1_funct_2(sK1,sK0,sK0) ),
% 3.78/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_329,plain,
% 3.78/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.78/0.99      | ~ v1_funct_1(X0)
% 3.78/0.99      | k1_relset_1(X1,X1,X0) = X1
% 3.78/0.99      | sK1 != X0
% 3.78/0.99      | sK0 != X1 ),
% 3.78/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_24]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_330,plain,
% 3.78/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.78/0.99      | ~ v1_funct_1(sK1)
% 3.78/0.99      | k1_relset_1(sK0,sK0,sK1) = sK0 ),
% 3.78/0.99      inference(unflattening,[status(thm)],[c_329]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_332,plain,
% 3.78/0.99      ( k1_relset_1(sK0,sK0,sK1) = sK0 ),
% 3.78/0.99      inference(global_propositional_subsumption,
% 3.78/0.99                [status(thm)],
% 3.78/0.99                [c_330,c_25,c_23]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_584,plain,
% 3.78/0.99      ( k1_relset_1(sK0,sK0,sK1) = sK0 ),
% 3.78/0.99      inference(subtyping,[status(esa)],[c_332]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1183,plain,
% 3.78/0.99      ( k1_relat_1(sK1) = sK0 ),
% 3.78/0.99      inference(light_normalisation,[status(thm)],[c_1182,c_584]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_7,plain,
% 3.78/0.99      ( ~ v2_funct_1(X0)
% 3.78/0.99      | ~ v1_funct_1(X0)
% 3.78/0.99      | ~ v1_relat_1(X0)
% 3.78/0.99      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
% 3.78/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_18,negated_conjecture,
% 3.78/0.99      ( v2_funct_1(sK1) ),
% 3.78/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_287,plain,
% 3.78/0.99      ( ~ v1_funct_1(X0)
% 3.78/0.99      | ~ v1_relat_1(X0)
% 3.78/0.99      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
% 3.78/0.99      | sK1 != X0 ),
% 3.78/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_18]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_288,plain,
% 3.78/0.99      ( ~ v1_funct_1(sK1)
% 3.78/0.99      | ~ v1_relat_1(sK1)
% 3.78/0.99      | k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
% 3.78/0.99      inference(unflattening,[status(thm)],[c_287]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_290,plain,
% 3.78/0.99      ( ~ v1_relat_1(sK1)
% 3.78/0.99      | k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
% 3.78/0.99      inference(global_propositional_subsumption,
% 3.78/0.99                [status(thm)],
% 3.78/0.99                [c_288,c_25]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_587,plain,
% 3.78/0.99      ( ~ v1_relat_1(sK1)
% 3.78/0.99      | k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
% 3.78/0.99      inference(subtyping,[status(esa)],[c_290]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_954,plain,
% 3.78/0.99      ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
% 3.78/0.99      | v1_relat_1(sK1) != iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_587]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_652,plain,
% 3.78/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.78/0.99      | v1_relat_1(sK1) ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_596]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1067,plain,
% 3.78/0.99      ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
% 3.78/0.99      inference(global_propositional_subsumption,
% 3.78/0.99                [status(thm)],
% 3.78/0.99                [c_954,c_23,c_652,c_587]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1254,plain,
% 3.78/0.99      ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(sK0) ),
% 3.78/0.99      inference(demodulation,[status(thm)],[c_1183,c_1067]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1,plain,
% 3.78/0.99      ( r1_tarski(k2_relat_1(X0),X1)
% 3.78/0.99      | ~ v5_relat_1(X0,X1)
% 3.78/0.99      | ~ v1_relat_1(X0) ),
% 3.78/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_9,plain,
% 3.78/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.78/0.99      | v5_relat_1(X0,X2) ),
% 3.78/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_340,plain,
% 3.78/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.78/0.99      | r1_tarski(k2_relat_1(X3),X4)
% 3.78/0.99      | ~ v1_relat_1(X3)
% 3.78/0.99      | X0 != X3
% 3.78/0.99      | X2 != X4 ),
% 3.78/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_9]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_341,plain,
% 3.78/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.78/0.99      | r1_tarski(k2_relat_1(X0),X2)
% 3.78/0.99      | ~ v1_relat_1(X0) ),
% 3.78/0.99      inference(unflattening,[status(thm)],[c_340]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_345,plain,
% 3.78/0.99      ( r1_tarski(k2_relat_1(X0),X2)
% 3.78/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.78/0.99      inference(global_propositional_subsumption,
% 3.78/0.99                [status(thm)],
% 3.78/0.99                [c_341,c_8]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_346,plain,
% 3.78/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.78/0.99      | r1_tarski(k2_relat_1(X0),X2) ),
% 3.78/0.99      inference(renaming,[status(thm)],[c_345]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_583,plain,
% 3.78/0.99      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 3.78/0.99      | r1_tarski(k2_relat_1(X0_48),X1_49) ),
% 3.78/0.99      inference(subtyping,[status(esa)],[c_346]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_956,plain,
% 3.78/0.99      ( m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 3.78/0.99      | r1_tarski(k2_relat_1(X0_48),X1_49) = iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_583]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_2112,plain,
% 3.78/0.99      ( r1_tarski(k2_relat_1(sK2),sK0) = iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_950,c_956]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_3,plain,
% 3.78/0.99      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 3.78/0.99      | ~ v1_relat_1(X0)
% 3.78/0.99      | k5_relat_1(X0,k6_partfun1(X1)) = X0 ),
% 3.78/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_599,plain,
% 3.78/0.99      ( ~ r1_tarski(k2_relat_1(X0_48),X0_49)
% 3.78/0.99      | ~ v1_relat_1(X0_48)
% 3.78/0.99      | k5_relat_1(X0_48,k6_partfun1(X0_49)) = X0_48 ),
% 3.78/0.99      inference(subtyping,[status(esa)],[c_3]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_942,plain,
% 3.78/0.99      ( k5_relat_1(X0_48,k6_partfun1(X0_49)) = X0_48
% 3.78/0.99      | r1_tarski(k2_relat_1(X0_48),X0_49) != iProver_top
% 3.78/0.99      | v1_relat_1(X0_48) != iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_599]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_2121,plain,
% 3.78/0.99      ( k5_relat_1(sK2,k6_partfun1(sK0)) = sK2
% 3.78/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.78/0.99      inference(superposition,[status(thm)],[c_2112,c_942]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1084,plain,
% 3.78/0.99      ( ~ r1_tarski(k2_relat_1(sK2),X0_49)
% 3.78/0.99      | ~ v1_relat_1(sK2)
% 3.78/0.99      | k5_relat_1(sK2,k6_partfun1(X0_49)) = sK2 ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_599]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1086,plain,
% 3.78/0.99      ( ~ r1_tarski(k2_relat_1(sK2),sK0)
% 3.78/0.99      | ~ v1_relat_1(sK2)
% 3.78/0.99      | k5_relat_1(sK2,k6_partfun1(sK0)) = sK2 ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_1084]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1093,plain,
% 3.78/0.99      ( v1_relat_1(sK2) ),
% 3.78/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_1091]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1196,plain,
% 3.78/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 3.78/0.99      | r1_tarski(k2_relat_1(sK2),X1_49) ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_583]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1198,plain,
% 3.78/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.78/0.99      | r1_tarski(k2_relat_1(sK2),sK0) ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_1196]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_2241,plain,
% 3.78/0.99      ( k5_relat_1(sK2,k6_partfun1(sK0)) = sK2 ),
% 3.78/0.99      inference(global_propositional_subsumption,
% 3.78/0.99                [status(thm)],
% 3.78/0.99                [c_2121,c_20,c_1086,c_1093,c_1198]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_13107,plain,
% 3.78/0.99      ( k6_partfun1(sK0) = sK2 | v1_relat_1(sK1) != iProver_top ),
% 3.78/0.99      inference(light_normalisation,
% 3.78/0.99                [status(thm)],
% 3.78/0.99                [c_13101,c_1254,c_2241]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_604,plain,( X0_50 = X0_50 ),theory(equality) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_5244,plain,
% 3.78/0.99      ( k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)) = k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)) ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_604]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_5245,plain,
% 3.78/0.99      ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_5244]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_618,plain,
% 3.78/0.99      ( ~ m1_subset_1(X0_48,X0_50)
% 3.78/0.99      | m1_subset_1(X1_48,X1_50)
% 3.78/0.99      | X1_50 != X0_50
% 3.78/0.99      | X1_48 != X0_48 ),
% 3.78/0.99      theory(equality) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_2593,plain,
% 3.78/0.99      ( ~ m1_subset_1(X0_48,X0_50)
% 3.78/0.99      | m1_subset_1(k6_partfun1(X0_49),k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49)))
% 3.78/0.99      | k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49)) != X0_50
% 3.78/0.99      | k6_partfun1(X0_49) != X0_48 ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_618]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_3671,plain,
% 3.78/0.99      ( m1_subset_1(k6_partfun1(X0_49),k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49)))
% 3.78/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.78/0.99      | k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
% 3.78/0.99      | k6_partfun1(X0_49) != sK2 ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_2593]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_3673,plain,
% 3.78/0.99      ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.78/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.78/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
% 3.78/0.99      | k6_partfun1(sK0) != sK2 ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_3671]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_602,plain,( X0_48 = X0_48 ),theory(equality) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_1001,plain,
% 3.78/0.99      ( sK2 = sK2 ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_602]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_606,plain,
% 3.78/0.99      ( X0_48 != X1_48 | X2_48 != X1_48 | X2_48 = X0_48 ),
% 3.78/0.99      theory(equality) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_991,plain,
% 3.78/0.99      ( k6_partfun1(sK0) != X0_48
% 3.78/0.99      | sK2 != X0_48
% 3.78/0.99      | sK2 = k6_partfun1(sK0) ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_606]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_996,plain,
% 3.78/0.99      ( k6_partfun1(sK0) != sK2 | sK2 = k6_partfun1(sK0) | sK2 != sK2 ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_991]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_11,plain,
% 3.78/0.99      ( r2_relset_1(X0,X1,X2,X2)
% 3.78/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.78/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_17,negated_conjecture,
% 3.78/0.99      ( ~ r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0)) ),
% 3.78/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_385,plain,
% 3.78/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.78/0.99      | k6_partfun1(sK0) != X0
% 3.78/0.99      | sK2 != X0
% 3.78/0.99      | sK0 != X2
% 3.78/0.99      | sK0 != X1 ),
% 3.78/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_17]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_386,plain,
% 3.78/0.99      ( ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.78/0.99      | sK2 != k6_partfun1(sK0) ),
% 3.78/0.99      inference(unflattening,[status(thm)],[c_385]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_582,plain,
% 3.78/0.99      ( ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.78/0.99      | sK2 != k6_partfun1(sK0) ),
% 3.78/0.99      inference(subtyping,[status(esa)],[c_386]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_651,plain,
% 3.78/0.99      ( m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 3.78/0.99      | v1_relat_1(X0_48) = iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_596]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_653,plain,
% 3.78/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.78/0.99      | v1_relat_1(sK1) = iProver_top ),
% 3.78/0.99      inference(instantiation,[status(thm)],[c_651]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(c_28,plain,
% 3.78/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.78/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.78/0.99  
% 3.78/0.99  cnf(contradiction,plain,
% 3.78/0.99      ( $false ),
% 3.78/0.99      inference(minisat,
% 3.78/0.99                [status(thm)],
% 3.78/0.99                [c_13107,c_5245,c_3673,c_1001,c_996,c_582,c_653,c_20,
% 3.78/0.99                 c_28]) ).
% 3.78/0.99  
% 3.78/0.99  
% 3.78/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.78/0.99  
% 3.78/0.99  ------                               Statistics
% 3.78/0.99  
% 3.78/0.99  ------ General
% 3.78/0.99  
% 3.78/0.99  abstr_ref_over_cycles:                  0
% 3.78/0.99  abstr_ref_under_cycles:                 0
% 3.78/0.99  gc_basic_clause_elim:                   0
% 3.78/0.99  forced_gc_time:                         0
% 3.78/0.99  parsing_time:                           0.026
% 3.78/0.99  unif_index_cands_time:                  0.
% 3.78/0.99  unif_index_add_time:                    0.
% 3.78/0.99  orderings_time:                         0.
% 3.78/0.99  out_proof_time:                         0.01
% 3.78/0.99  total_time:                             0.502
% 3.78/0.99  num_of_symbols:                         55
% 3.78/0.99  num_of_terms:                           8796
% 3.78/0.99  
% 3.78/0.99  ------ Preprocessing
% 3.78/0.99  
% 3.78/0.99  num_of_splits:                          0
% 3.78/0.99  num_of_split_atoms:                     0
% 3.78/0.99  num_of_reused_defs:                     0
% 3.78/0.99  num_eq_ax_congr_red:                    11
% 3.78/0.99  num_of_sem_filtered_clauses:            1
% 3.78/0.99  num_of_subtypes:                        4
% 3.78/0.99  monotx_restored_types:                  1
% 3.78/0.99  sat_num_of_epr_types:                   0
% 3.78/0.99  sat_num_of_non_cyclic_types:            0
% 3.78/0.99  sat_guarded_non_collapsed_types:        0
% 3.78/0.99  num_pure_diseq_elim:                    0
% 3.78/0.99  simp_replaced_by:                       0
% 3.78/0.99  res_preprocessed:                       128
% 3.78/0.99  prep_upred:                             0
% 3.78/0.99  prep_unflattend:                        21
% 3.78/0.99  smt_new_axioms:                         0
% 3.78/0.99  pred_elim_cands:                        4
% 3.78/0.99  pred_elim:                              4
% 3.78/0.99  pred_elim_cl:                           5
% 3.78/0.99  pred_elim_cycles:                       7
% 3.78/0.99  merged_defs:                            0
% 3.78/0.99  merged_defs_ncl:                        0
% 3.78/0.99  bin_hyper_res:                          0
% 3.78/0.99  prep_cycles:                            4
% 3.78/0.99  pred_elim_time:                         0.004
% 3.78/0.99  splitting_time:                         0.
% 3.78/0.99  sem_filter_time:                        0.
% 3.78/0.99  monotx_time:                            0.001
% 3.78/0.99  subtype_inf_time:                       0.001
% 3.78/0.99  
% 3.78/0.99  ------ Problem properties
% 3.78/0.99  
% 3.78/0.99  clauses:                                21
% 3.78/0.99  conjectures:                            4
% 3.78/0.99  epr:                                    2
% 3.78/0.99  horn:                                   21
% 3.78/0.99  ground:                                 11
% 3.78/0.99  unary:                                  6
% 3.78/0.99  binary:                                 8
% 3.78/0.99  lits:                                   50
% 3.78/0.99  lits_eq:                                12
% 3.78/0.99  fd_pure:                                0
% 3.78/0.99  fd_pseudo:                              0
% 3.78/0.99  fd_cond:                                0
% 3.78/0.99  fd_pseudo_cond:                         0
% 3.78/0.99  ac_symbols:                             0
% 3.78/0.99  
% 3.78/0.99  ------ Propositional Solver
% 3.78/0.99  
% 3.78/0.99  prop_solver_calls:                      35
% 3.78/0.99  prop_fast_solver_calls:                 1159
% 3.78/0.99  smt_solver_calls:                       0
% 3.78/0.99  smt_fast_solver_calls:                  0
% 3.78/0.99  prop_num_of_clauses:                    3866
% 3.78/0.99  prop_preprocess_simplified:             10848
% 3.78/0.99  prop_fo_subsumed:                       87
% 3.78/0.99  prop_solver_time:                       0.
% 3.78/0.99  smt_solver_time:                        0.
% 3.78/0.99  smt_fast_solver_time:                   0.
% 3.78/0.99  prop_fast_solver_time:                  0.
% 3.78/0.99  prop_unsat_core_time:                   0.
% 3.78/0.99  
% 3.78/0.99  ------ QBF
% 3.78/0.99  
% 3.78/0.99  qbf_q_res:                              0
% 3.78/0.99  qbf_num_tautologies:                    0
% 3.78/0.99  qbf_prep_cycles:                        0
% 3.78/0.99  
% 3.78/0.99  ------ BMC1
% 3.78/0.99  
% 3.78/0.99  bmc1_current_bound:                     -1
% 3.78/0.99  bmc1_last_solved_bound:                 -1
% 3.78/0.99  bmc1_unsat_core_size:                   -1
% 3.78/0.99  bmc1_unsat_core_parents_size:           -1
% 3.78/0.99  bmc1_merge_next_fun:                    0
% 3.78/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.78/0.99  
% 3.78/0.99  ------ Instantiation
% 3.78/0.99  
% 3.78/0.99  inst_num_of_clauses:                    1750
% 3.78/0.99  inst_num_in_passive:                    861
% 3.78/0.99  inst_num_in_active:                     854
% 3.78/0.99  inst_num_in_unprocessed:                35
% 3.78/0.99  inst_num_of_loops:                      890
% 3.78/0.99  inst_num_of_learning_restarts:          0
% 3.78/0.99  inst_num_moves_active_passive:          28
% 3.78/0.99  inst_lit_activity:                      0
% 3.78/0.99  inst_lit_activity_moves:                0
% 3.78/0.99  inst_num_tautologies:                   0
% 3.78/0.99  inst_num_prop_implied:                  0
% 3.78/0.99  inst_num_existing_simplified:           0
% 3.78/0.99  inst_num_eq_res_simplified:             0
% 3.78/0.99  inst_num_child_elim:                    0
% 3.78/0.99  inst_num_of_dismatching_blockings:      1835
% 3.78/0.99  inst_num_of_non_proper_insts:           3055
% 3.78/0.99  inst_num_of_duplicates:                 0
% 3.78/0.99  inst_inst_num_from_inst_to_res:         0
% 3.78/0.99  inst_dismatching_checking_time:         0.
% 3.78/0.99  
% 3.78/0.99  ------ Resolution
% 3.78/0.99  
% 3.78/0.99  res_num_of_clauses:                     0
% 3.78/0.99  res_num_in_passive:                     0
% 3.78/0.99  res_num_in_active:                      0
% 3.78/0.99  res_num_of_loops:                       132
% 3.78/0.99  res_forward_subset_subsumed:            187
% 3.78/0.99  res_backward_subset_subsumed:           0
% 3.78/0.99  res_forward_subsumed:                   0
% 3.78/0.99  res_backward_subsumed:                  0
% 3.78/0.99  res_forward_subsumption_resolution:     0
% 3.78/0.99  res_backward_subsumption_resolution:    0
% 3.78/0.99  res_clause_to_clause_subsumption:       1015
% 3.78/0.99  res_orphan_elimination:                 0
% 3.78/0.99  res_tautology_del:                      537
% 3.78/0.99  res_num_eq_res_simplified:              1
% 3.78/0.99  res_num_sel_changes:                    0
% 3.78/0.99  res_moves_from_active_to_pass:          0
% 3.78/0.99  
% 3.78/0.99  ------ Superposition
% 3.78/0.99  
% 3.78/0.99  sup_time_total:                         0.
% 3.78/0.99  sup_time_generating:                    0.
% 3.78/0.99  sup_time_sim_full:                      0.
% 3.78/0.99  sup_time_sim_immed:                     0.
% 3.78/0.99  
% 3.78/0.99  sup_num_of_clauses:                     426
% 3.78/0.99  sup_num_in_active:                      173
% 3.78/0.99  sup_num_in_passive:                     253
% 3.78/0.99  sup_num_of_loops:                       177
% 3.78/0.99  sup_fw_superposition:                   325
% 3.78/0.99  sup_bw_superposition:                   99
% 3.78/0.99  sup_immediate_simplified:               95
% 3.78/0.99  sup_given_eliminated:                   0
% 3.78/0.99  comparisons_done:                       0
% 3.78/0.99  comparisons_avoided:                    0
% 3.78/0.99  
% 3.78/0.99  ------ Simplifications
% 3.78/0.99  
% 3.78/0.99  
% 3.78/0.99  sim_fw_subset_subsumed:                 7
% 3.78/0.99  sim_bw_subset_subsumed:                 6
% 3.78/0.99  sim_fw_subsumed:                        1
% 3.78/0.99  sim_bw_subsumed:                        0
% 3.78/0.99  sim_fw_subsumption_res:                 0
% 3.78/0.99  sim_bw_subsumption_res:                 0
% 3.78/0.99  sim_tautology_del:                      1
% 3.78/0.99  sim_eq_tautology_del:                   4
% 3.78/0.99  sim_eq_res_simp:                        0
% 3.78/0.99  sim_fw_demodulated:                     4
% 3.78/0.99  sim_bw_demodulated:                     2
% 3.78/0.99  sim_light_normalised:                   81
% 3.78/0.99  sim_joinable_taut:                      0
% 3.78/0.99  sim_joinable_simp:                      0
% 3.78/0.99  sim_ac_normalised:                      0
% 3.78/0.99  sim_smt_subsumption:                    0
% 3.78/0.99  
%------------------------------------------------------------------------------
