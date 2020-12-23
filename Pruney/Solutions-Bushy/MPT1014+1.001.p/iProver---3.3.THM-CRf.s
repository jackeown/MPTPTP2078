%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1014+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:39 EST 2020

% Result     : Theorem 3.66s
% Output     : CNFRefutation 3.66s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 673 expanded)
%              Number of clauses        :   95 ( 217 expanded)
%              Number of leaves         :   14 ( 160 expanded)
%              Depth                    :   23
%              Number of atoms          :  478 (4283 expanded)
%              Number of equality atoms :  180 ( 745 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   18 (   2 average)
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
    inference(ennf_transformation,[],[f13])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f34,plain,(
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

fof(f33,plain,
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

fof(f35,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0))
    & k2_relset_1(sK0,sK0,sK1) = sK0
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK2,sK0,sK0)
    & v1_funct_1(sK2)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f34,f33])).

fof(f51,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f35])).

fof(f54,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f35])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f19,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f18])).

fof(f40,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f52,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f49,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f16])).

fof(f38,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f22])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f55,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
       => r2_relset_1(X0,X1,X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X3,X2)
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X3,X2)
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f24])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X2)
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X0,X1) = X0
              & k1_relat_1(X1) = k2_relat_1(X0) )
           => k6_relat_1(k1_relat_1(X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_relat_1(k1_relat_1(X1)) = X1
          | k5_relat_1(X0,X1) != X0
          | k1_relat_1(X1) != k2_relat_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_relat_1(k1_relat_1(X1)) = X1
          | k5_relat_1(X0,X1) != X0
          | k1_relat_1(X1) != k2_relat_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k6_relat_1(k1_relat_1(X1)) = X1
      | k5_relat_1(X0,X1) != X0
      | k1_relat_1(X1) != k2_relat_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f53,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f56,plain,(
    k2_relset_1(sK0,sK0,sK1) = sK0 ),
    inference(cnf_transformation,[],[f35])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f3,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f39,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f7,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f58,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f39,f43])).

fof(f57,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f35])).

fof(f59,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k6_relat_1(sK0)) ),
    inference(definition_unfolding,[],[f57,f43])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f45])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_358,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_721,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_358])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_360,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_719,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_360])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_370,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45)))
    | ~ m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(X2_45,X3_45)))
    | ~ v1_funct_1(X0_46)
    | ~ v1_funct_1(X1_46)
    | k1_partfun1(X2_45,X3_45,X0_45,X1_45,X1_46,X0_46) = k5_relat_1(X1_46,X0_46) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_710,plain,
    ( k1_partfun1(X0_45,X1_45,X2_45,X3_45,X0_46,X1_46) = k5_relat_1(X0_46,X1_46)
    | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45))) != iProver_top
    | m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(X2_45,X3_45))) != iProver_top
    | v1_funct_1(X0_46) != iProver_top
    | v1_funct_1(X1_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_370])).

cnf(c_2244,plain,
    ( k1_partfun1(X0_45,X1_45,sK0,sK0,X0_46,sK2) = k5_relat_1(X0_46,sK2)
    | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45))) != iProver_top
    | v1_funct_1(X0_46) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_719,c_710])).

cnf(c_17,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_24,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2564,plain,
    ( v1_funct_1(X0_46) != iProver_top
    | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45))) != iProver_top
    | k1_partfun1(X0_45,X1_45,sK0,sK0,X0_46,sK2) = k5_relat_1(X0_46,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2244,c_24])).

cnf(c_2565,plain,
    ( k1_partfun1(X0_45,X1_45,sK0,sK0,X0_46,sK2) = k5_relat_1(X0_46,sK2)
    | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45))) != iProver_top
    | v1_funct_1(X0_46) != iProver_top ),
    inference(renaming,[status(thm)],[c_2564])).

cnf(c_2574,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2)
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_721,c_2565])).

cnf(c_20,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_21,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_23,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2289,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2)
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2244])).

cnf(c_2705,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2574,c_21,c_23,c_24,c_2289])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_373,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45)))
    | ~ m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(X2_45,X3_45)))
    | m1_subset_1(k1_partfun1(X2_45,X3_45,X0_45,X1_45,X1_46,X0_46),k1_zfmisc_1(k2_zfmisc_1(X2_45,X1_45)))
    | ~ v1_funct_1(X0_46)
    | ~ v1_funct_1(X1_46) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_707,plain,
    ( m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45))) != iProver_top
    | m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(X2_45,X3_45))) != iProver_top
    | m1_subset_1(k1_partfun1(X0_45,X1_45,X2_45,X3_45,X0_46,X1_46),k1_zfmisc_1(k2_zfmisc_1(X0_45,X3_45))) = iProver_top
    | v1_funct_1(X0_46) != iProver_top
    | v1_funct_1(X1_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_373])).

cnf(c_2711,plain,
    ( m1_subset_1(k5_relat_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2705,c_707])).

cnf(c_26,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_10928,plain,
    ( m1_subset_1(k5_relat_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2711,c_21,c_23,c_24,c_26])).

cnf(c_8,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_366,plain,
    ( ~ r2_relset_1(X0_45,X1_45,X0_46,X1_46)
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45)))
    | ~ m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45)))
    | X1_46 = X0_46 ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_714,plain,
    ( X0_46 = X1_46
    | r2_relset_1(X0_45,X1_45,X1_46,X0_46) != iProver_top
    | m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45))) != iProver_top
    | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_366])).

cnf(c_1536,plain,
    ( sK1 = X0_46
    | r2_relset_1(sK0,sK0,X0_46,sK1) != iProver_top
    | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_721,c_714])).

cnf(c_10950,plain,
    ( k5_relat_1(sK1,sK2) = sK1
    | r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_10928,c_1536])).

cnf(c_14,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),sK1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_361,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),sK1) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_718,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_361])).

cnf(c_2708,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2),sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2705,c_718])).

cnf(c_2709,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2),sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2708])).

cnf(c_2733,plain,
    ( m1_subset_1(k5_relat_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ v1_funct_1(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2711])).

cnf(c_9,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | r2_relset_1(X0,X1,X3,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_365,plain,
    ( ~ r2_relset_1(X0_45,X1_45,X0_46,X1_46)
    | r2_relset_1(X0_45,X1_45,X1_46,X0_46)
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45)))
    | ~ m1_subset_1(X1_46,k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45))) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_2402,plain,
    ( r2_relset_1(X0_45,X1_45,X0_46,k5_relat_1(X0_46,X1_46))
    | ~ r2_relset_1(X0_45,X1_45,k5_relat_1(X0_46,X1_46),X0_46)
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45)))
    | ~ m1_subset_1(k5_relat_1(X0_46,X1_46),k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45))) ),
    inference(instantiation,[status(thm)],[c_365])).

cnf(c_3058,plain,
    ( ~ r2_relset_1(X0_45,X1_45,k5_relat_1(sK1,sK2),sK1)
    | r2_relset_1(X0_45,X1_45,sK1,k5_relat_1(sK1,sK2))
    | ~ m1_subset_1(k5_relat_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45))) ),
    inference(instantiation,[status(thm)],[c_2402])).

cnf(c_3065,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2),sK1)
    | r2_relset_1(sK0,sK0,sK1,k5_relat_1(sK1,sK2))
    | ~ m1_subset_1(k5_relat_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_3058])).

cnf(c_1449,plain,
    ( ~ r2_relset_1(X0_45,X1_45,X0_46,k5_relat_1(X1_46,X2_46))
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45)))
    | ~ m1_subset_1(k5_relat_1(X1_46,X2_46),k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45)))
    | k5_relat_1(X1_46,X2_46) = X0_46 ),
    inference(instantiation,[status(thm)],[c_366])).

cnf(c_3368,plain,
    ( ~ r2_relset_1(sK0,sK0,sK1,k5_relat_1(sK1,sK2))
    | ~ m1_subset_1(k5_relat_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k5_relat_1(sK1,sK2) = sK1 ),
    inference(instantiation,[status(thm)],[c_1449])).

cnf(c_11074,plain,
    ( k5_relat_1(sK1,sK2) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10950,c_20,c_18,c_17,c_15,c_2709,c_2733,c_3065,c_3368])).

cnf(c_10,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(X1,X0) != X1
    | k2_relat_1(X1) != k1_relat_1(X0)
    | k6_relat_1(k1_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_364,plain,
    ( ~ v1_funct_1(X0_46)
    | ~ v1_funct_1(X1_46)
    | ~ v1_relat_1(X0_46)
    | ~ v1_relat_1(X1_46)
    | k5_relat_1(X1_46,X0_46) != X1_46
    | k6_relat_1(k1_relat_1(X0_46)) = X0_46
    | k2_relat_1(X1_46) != k1_relat_1(X0_46) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_716,plain,
    ( k5_relat_1(X0_46,X1_46) != X0_46
    | k6_relat_1(k1_relat_1(X1_46)) = X1_46
    | k2_relat_1(X0_46) != k1_relat_1(X1_46)
    | v1_funct_1(X0_46) != iProver_top
    | v1_funct_1(X1_46) != iProver_top
    | v1_relat_1(X0_46) != iProver_top
    | v1_relat_1(X1_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_364])).

cnf(c_11086,plain,
    ( k6_relat_1(k1_relat_1(sK2)) = sK2
    | k2_relat_1(sK1) != k1_relat_1(sK2)
    | v1_funct_1(sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK1) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_11074,c_716])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_369,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45)))
    | k1_relset_1(X0_45,X1_45,X0_46) = k1_relat_1(X0_46) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_711,plain,
    ( k1_relset_1(X0_45,X1_45,X0_46) = k1_relat_1(X0_46)
    | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_369])).

cnf(c_1083,plain,
    ( k1_relset_1(sK0,sK0,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_719,c_711])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(X1,X1,X0) = X1 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_16,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_219,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(X1,X1,X0) = X1
    | sK2 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_16])).

cnf(c_220,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | k1_relset_1(sK0,sK0,sK2) = sK0 ),
    inference(unflattening,[status(thm)],[c_219])).

cnf(c_222,plain,
    ( k1_relset_1(sK0,sK0,sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_220,c_17,c_15])).

cnf(c_356,plain,
    ( k1_relset_1(sK0,sK0,sK2) = sK0 ),
    inference(subtyping,[status(esa)],[c_222])).

cnf(c_1092,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_1083,c_356])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_368,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45)))
    | k2_relset_1(X0_45,X1_45,X0_46) = k2_relat_1(X0_46) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_712,plain,
    ( k2_relset_1(X0_45,X1_45,X0_46) = k2_relat_1(X0_46)
    | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_368])).

cnf(c_1146,plain,
    ( k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_721,c_712])).

cnf(c_13,negated_conjecture,
    ( k2_relset_1(sK0,sK0,sK1) = sK0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_362,negated_conjecture,
    ( k2_relset_1(sK0,sK0,sK1) = sK0 ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1151,plain,
    ( k2_relat_1(sK1) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_1146,c_362])).

cnf(c_11087,plain,
    ( k6_relat_1(sK0) = sK2
    | sK0 != sK0
    | v1_funct_1(sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK1) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11086,c_1092,c_1151])).

cnf(c_11088,plain,
    ( k6_relat_1(sK0) = sK2
    | v1_funct_1(sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK1) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_11087])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_374,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45)))
    | v1_relat_1(X0_46) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_405,plain,
    ( m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45))) != iProver_top
    | v1_relat_1(X0_46) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_374])).

cnf(c_407,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_relat_1(sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_405])).

cnf(c_706,plain,
    ( m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45))) != iProver_top
    | v1_relat_1(X0_46) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_374])).

cnf(c_994,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_719,c_706])).

cnf(c_11800,plain,
    ( k6_relat_1(sK0) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11088,c_21,c_23,c_24,c_407,c_994])).

cnf(c_3,plain,
    ( m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_371,plain,
    ( m1_subset_1(k6_relat_1(X0_45),k1_zfmisc_1(k2_zfmisc_1(X0_45,X0_45))) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_709,plain,
    ( m1_subset_1(k6_relat_1(X0_45),k1_zfmisc_1(k2_zfmisc_1(X0_45,X0_45))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_371])).

cnf(c_1535,plain,
    ( sK2 = X0_46
    | r2_relset_1(sK0,sK0,X0_46,sK2) != iProver_top
    | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_719,c_714])).

cnf(c_1864,plain,
    ( k6_relat_1(sK0) = sK2
    | r2_relset_1(sK0,sK0,k6_relat_1(sK0),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_709,c_1535])).

cnf(c_12,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK0,sK2,k6_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_28,plain,
    ( r2_relset_1(sK0,sK0,sK2,k6_relat_1(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_51,plain,
    ( m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_53,plain,
    ( m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_51])).

cnf(c_879,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_relat_1(sK0),sK2)
    | r2_relset_1(sK0,sK0,sK2,k6_relat_1(sK0))
    | ~ m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_365])).

cnf(c_880,plain,
    ( r2_relset_1(sK0,sK0,k6_relat_1(sK0),sK2) != iProver_top
    | r2_relset_1(sK0,sK0,sK2,k6_relat_1(sK0)) = iProver_top
    | m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_879])).

cnf(c_2470,plain,
    ( r2_relset_1(sK0,sK0,k6_relat_1(sK0),sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1864,c_26,c_28,c_53,c_880])).

cnf(c_11806,plain,
    ( r2_relset_1(sK0,sK0,sK2,sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11800,c_2470])).

cnf(c_7,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_367,plain,
    ( r2_relset_1(X0_45,X1_45,X0_46,X0_46)
    | ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45))) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1293,plain,
    ( r2_relset_1(X0_45,X1_45,sK2,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45))) ),
    inference(instantiation,[status(thm)],[c_367])).

cnf(c_1298,plain,
    ( r2_relset_1(X0_45,X1_45,sK2,sK2) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1293])).

cnf(c_1300,plain,
    ( r2_relset_1(sK0,sK0,sK2,sK2) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1298])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11806,c_1300,c_26])).


%------------------------------------------------------------------------------
