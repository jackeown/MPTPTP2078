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
% DateTime   : Thu Dec  3 12:02:16 EST 2020

% Result     : Theorem 27.36s
% Output     : CNFRefutation 27.36s
% Verified   : 
% Statistics : Number of formulae       :  195 ( 947 expanded)
%              Number of clauses        :  121 ( 312 expanded)
%              Number of leaves         :   23 ( 236 expanded)
%              Depth                    :   19
%              Number of atoms          :  624 (5996 expanded)
%              Number of equality atoms :  199 ( 445 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
           => ( v2_funct_2(X3,X0)
              & v2_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
             => ( v2_funct_2(X3,X0)
                & v2_funct_1(X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f40,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f41,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f40])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
     => ( ( ~ v2_funct_2(sK3,X0)
          | ~ v2_funct_1(X2) )
        & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0))
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(sK3,X1,X0)
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ( ~ v2_funct_2(X3,X0)
              | ~ v2_funct_1(X2) )
            & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ( ~ v2_funct_2(X3,sK0)
            | ~ v2_funct_1(sK2) )
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ( ~ v2_funct_2(sK3,sK0)
      | ~ v2_funct_1(sK2) )
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f41,f45,f44])).

fof(f73,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f46])).

fof(f16,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f72,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f46])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f67,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f68,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f69,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f46])).

fof(f70,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f71,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f78,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f61])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f34])).

fof(f62,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f28])).

fof(f56,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f26,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f25])).

fof(f54,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f30])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f12,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f15,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f76,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f59,f63])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
           => ( v2_funct_1(X3)
              | ( k1_xboole_0 != X1
                & k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f38])).

fof(f65,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v2_funct_1(X3)
      | k1_xboole_0 = X2
      | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f75,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f51,f63])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f74,plain,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_278,plain,
    ( ~ v2_funct_1(X0_50)
    | v2_funct_1(X1_50)
    | X1_50 != X0_50 ),
    theory(equality)).

cnf(c_93162,plain,
    ( ~ v2_funct_1(X0_50)
    | v2_funct_1(sK2)
    | sK2 != X0_50 ),
    inference(instantiation,[status(thm)],[c_278])).

cnf(c_93164,plain,
    ( v2_funct_1(sK2)
    | ~ v2_funct_1(sK0)
    | sK2 != sK0 ),
    inference(instantiation,[status(thm)],[c_93162])).

cnf(c_20,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_247,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_800,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_247])).

cnf(c_16,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_251,plain,
    ( ~ r2_relset_1(X0_50,X0_50,k1_partfun1(X0_50,X1_50,X1_50,X0_50,X2_50,X3_50),k6_partfun1(X0_50))
    | ~ v1_funct_2(X2_50,X0_50,X1_50)
    | ~ v1_funct_2(X3_50,X1_50,X0_50)
    | ~ m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X0_50)))
    | ~ m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
    | ~ v1_funct_1(X3_50)
    | ~ v1_funct_1(X2_50)
    | k2_relset_1(X1_50,X0_50,X3_50) = X0_50 ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_796,plain,
    ( k2_relset_1(X0_50,X1_50,X2_50) = X1_50
    | r2_relset_1(X1_50,X1_50,k1_partfun1(X1_50,X0_50,X0_50,X1_50,X3_50,X2_50),k6_partfun1(X1_50)) != iProver_top
    | v1_funct_2(X2_50,X0_50,X1_50) != iProver_top
    | v1_funct_2(X3_50,X1_50,X0_50) != iProver_top
    | m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X0_50))) != iProver_top
    | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
    | v1_funct_1(X3_50) != iProver_top
    | v1_funct_1(X2_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_251])).

cnf(c_6190,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_800,c_796])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_246,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_801,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_246])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_259,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
    | k2_relset_1(X1_50,X2_50,X0_50) = k2_relat_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_788,plain,
    ( k2_relset_1(X0_50,X1_50,X2_50) = k2_relat_1(X2_50)
    | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_259])).

cnf(c_2211,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_801,c_788])).

cnf(c_6191,plain,
    ( k2_relat_1(sK3) = sK0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6190,c_2211])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_27,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_25,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_28,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_29,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_30,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_22,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_31,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_32,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_31320,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6191,c_27,c_28,c_29,c_30,c_31,c_32])).

cnf(c_13,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_254,plain,
    ( v2_funct_2(X0_50,k2_relat_1(X0_50))
    | ~ v5_relat_1(X0_50,k2_relat_1(X0_50))
    | ~ v1_relat_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_793,plain,
    ( v2_funct_2(X0_50,k2_relat_1(X0_50)) = iProver_top
    | v5_relat_1(X0_50,k2_relat_1(X0_50)) != iProver_top
    | v1_relat_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_254])).

cnf(c_31324,plain,
    ( v2_funct_2(sK3,k2_relat_1(sK3)) = iProver_top
    | v5_relat_1(sK3,sK0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_31320,c_793])).

cnf(c_31325,plain,
    ( v2_funct_2(sK3,sK0) = iProver_top
    | v5_relat_1(sK3,sK0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_31324,c_31320])).

cnf(c_31326,plain,
    ( v2_funct_2(sK3,sK0)
    | ~ v5_relat_1(sK3,sK0)
    | ~ v1_relat_1(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_31325])).

cnf(c_243,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_804,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_243])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_252,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
    | ~ m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X4_50,X5_50)))
    | ~ v1_funct_1(X3_50)
    | ~ v1_funct_1(X0_50)
    | k1_partfun1(X4_50,X5_50,X1_50,X2_50,X3_50,X0_50) = k5_relat_1(X3_50,X0_50) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_795,plain,
    ( k1_partfun1(X0_50,X1_50,X2_50,X3_50,X4_50,X5_50) = k5_relat_1(X4_50,X5_50)
    | m1_subset_1(X5_50,k1_zfmisc_1(k2_zfmisc_1(X2_50,X3_50))) != iProver_top
    | m1_subset_1(X4_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
    | v1_funct_1(X5_50) != iProver_top
    | v1_funct_1(X4_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_252])).

cnf(c_4172,plain,
    ( k1_partfun1(X0_50,X1_50,sK1,sK0,X2_50,sK3) = k5_relat_1(X2_50,sK3)
    | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
    | v1_funct_1(X2_50) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_801,c_795])).

cnf(c_6408,plain,
    ( v1_funct_1(X2_50) != iProver_top
    | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
    | k1_partfun1(X0_50,X1_50,sK1,sK0,X2_50,sK3) = k5_relat_1(X2_50,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4172,c_30])).

cnf(c_6409,plain,
    ( k1_partfun1(X0_50,X1_50,sK1,sK0,X2_50,sK3) = k5_relat_1(X2_50,sK3)
    | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
    | v1_funct_1(X2_50) != iProver_top ),
    inference(renaming,[status(thm)],[c_6408])).

cnf(c_6418,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_804,c_6409])).

cnf(c_1200,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3_50,X4_50)))
    | ~ v1_funct_1(X0_50)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(X1_50,X2_50,X3_50,X4_50,X0_50,sK3) = k5_relat_1(X0_50,sK3) ),
    inference(instantiation,[status(thm)],[c_252])).

cnf(c_1522,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2_50,X3_50)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(X0_50,X1_50,X2_50,X3_50,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1200])).

cnf(c_2316,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(X0_50,X1_50,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1522])).

cnf(c_3580,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_2316])).

cnf(c_6500,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6418,c_26,c_24,c_23,c_21,c_3580])).

cnf(c_6503,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6500,c_800])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | k4_relset_1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_258,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
    | ~ m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X4_50,X5_50)))
    | k4_relset_1(X4_50,X5_50,X1_50,X2_50,X3_50,X0_50) = k5_relat_1(X3_50,X0_50) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_789,plain,
    ( k4_relset_1(X0_50,X1_50,X2_50,X3_50,X4_50,X5_50) = k5_relat_1(X4_50,X5_50)
    | m1_subset_1(X5_50,k1_zfmisc_1(k2_zfmisc_1(X2_50,X3_50))) != iProver_top
    | m1_subset_1(X4_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_258])).

cnf(c_3948,plain,
    ( k4_relset_1(X0_50,X1_50,sK1,sK0,X2_50,sK3) = k5_relat_1(X2_50,sK3)
    | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top ),
    inference(superposition,[status(thm)],[c_801,c_789])).

cnf(c_4564,plain,
    ( k4_relset_1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(superposition,[status(thm)],[c_804,c_3948])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_260,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
    | ~ m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X4_50,X5_50)))
    | m1_subset_1(k4_relset_1(X4_50,X5_50,X1_50,X2_50,X3_50,X0_50),k1_zfmisc_1(k2_zfmisc_1(X4_50,X2_50))) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_787,plain,
    ( m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50))) != iProver_top
    | m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X4_50,X5_50))) != iProver_top
    | m1_subset_1(k4_relset_1(X4_50,X5_50,X1_50,X2_50,X3_50,X0_50),k1_zfmisc_1(k2_zfmisc_1(X4_50,X2_50))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_260])).

cnf(c_4859,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4564,c_787])).

cnf(c_8403,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4859,c_29,c_32])).

cnf(c_11,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_256,plain,
    ( ~ r2_relset_1(X0_50,X1_50,X2_50,X3_50)
    | ~ m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
    | ~ m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
    | X3_50 = X2_50 ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_791,plain,
    ( X0_50 = X1_50
    | r2_relset_1(X2_50,X3_50,X1_50,X0_50) != iProver_top
    | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_50,X3_50))) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X2_50,X3_50))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_256])).

cnf(c_8417,plain,
    ( k5_relat_1(sK2,sK3) = X0_50
    | r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),X0_50) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8403,c_791])).

cnf(c_17544,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6503,c_8417])).

cnf(c_12,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_53,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_55,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_53])).

cnf(c_17685,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17544,c_55])).

cnf(c_17707,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    inference(demodulation,[status(thm)],[c_17685,c_6500])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ v2_funct_1(k1_partfun1(X1,X2,X2,X4,X0,X3))
    | k1_xboole_0 = X4 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_249,plain,
    ( ~ v1_funct_2(X0_50,X1_50,X2_50)
    | ~ v1_funct_2(X3_50,X2_50,X4_50)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
    | ~ m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X2_50,X4_50)))
    | ~ v1_funct_1(X3_50)
    | ~ v1_funct_1(X0_50)
    | v2_funct_1(X0_50)
    | ~ v2_funct_1(k1_partfun1(X1_50,X2_50,X2_50,X4_50,X0_50,X3_50))
    | k1_xboole_0 = X4_50 ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_798,plain,
    ( k1_xboole_0 = X0_50
    | v1_funct_2(X1_50,X2_50,X3_50) != iProver_top
    | v1_funct_2(X4_50,X3_50,X0_50) != iProver_top
    | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_50,X3_50))) != iProver_top
    | m1_subset_1(X4_50,k1_zfmisc_1(k2_zfmisc_1(X3_50,X0_50))) != iProver_top
    | v1_funct_1(X1_50) != iProver_top
    | v1_funct_1(X4_50) != iProver_top
    | v2_funct_1(X1_50) = iProver_top
    | v2_funct_1(k1_partfun1(X2_50,X3_50,X3_50,X0_50,X1_50,X4_50)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_249])).

cnf(c_17973,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_17707,c_798])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_266,plain,
    ( ~ v1_xboole_0(X0_50)
    | ~ v1_xboole_0(X1_50)
    | X1_50 = X0_50 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_6324,plain,
    ( ~ v2_funct_1(X0_50)
    | v2_funct_1(X1_50)
    | ~ v1_xboole_0(X1_50)
    | ~ v1_xboole_0(X0_50) ),
    inference(resolution,[status(thm)],[c_266,c_278])).

cnf(c_4,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_263,plain,
    ( v2_funct_1(k6_partfun1(X0_50)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1053,plain,
    ( v2_funct_1(X0_50)
    | ~ v2_funct_1(k6_partfun1(X1_50))
    | X0_50 != k6_partfun1(X1_50) ),
    inference(instantiation,[status(thm)],[c_278])).

cnf(c_1380,plain,
    ( ~ v1_xboole_0(X0_50)
    | ~ v1_xboole_0(k6_partfun1(X1_50))
    | X0_50 = k6_partfun1(X1_50) ),
    inference(instantiation,[status(thm)],[c_266])).

cnf(c_277,plain,
    ( X0_50 != X1_50
    | k6_partfun1(X0_50) = k6_partfun1(X1_50) ),
    theory(equality)).

cnf(c_1788,plain,
    ( ~ v2_funct_1(k6_partfun1(X0_50))
    | v2_funct_1(k6_partfun1(X1_50))
    | X1_50 != X0_50 ),
    inference(resolution,[status(thm)],[c_277,c_278])).

cnf(c_255,plain,
    ( m1_subset_1(k6_partfun1(X0_50),k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50))) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_792,plain,
    ( m1_subset_1(k6_partfun1(X0_50),k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_255])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_261,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
    | ~ v1_xboole_0(X1_50)
    | v1_xboole_0(X0_50) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_786,plain,
    ( m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50))) != iProver_top
    | v1_xboole_0(X1_50) != iProver_top
    | v1_xboole_0(X0_50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_261])).

cnf(c_2190,plain,
    ( v1_xboole_0(X0_50) != iProver_top
    | v1_xboole_0(k6_partfun1(X0_50)) = iProver_top ),
    inference(superposition,[status(thm)],[c_792,c_786])).

cnf(c_2205,plain,
    ( ~ v1_xboole_0(X0_50)
    | v1_xboole_0(k6_partfun1(X0_50)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2190])).

cnf(c_272,plain,
    ( ~ v1_xboole_0(X0_50)
    | v1_xboole_0(X1_50)
    | X1_50 != X0_50 ),
    theory(equality)).

cnf(c_4293,plain,
    ( ~ v1_xboole_0(k6_partfun1(X0_50))
    | v1_xboole_0(k6_partfun1(X1_50))
    | X1_50 != X0_50 ),
    inference(resolution,[status(thm)],[c_272,c_277])).

cnf(c_13098,plain,
    ( v2_funct_1(X1_50)
    | ~ v1_xboole_0(X1_50)
    | ~ v1_xboole_0(X0_50) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6324,c_266,c_263,c_1053,c_1380,c_1788,c_2205,c_4293])).

cnf(c_13099,plain,
    ( v2_funct_1(X0_50)
    | ~ v1_xboole_0(X0_50)
    | ~ v1_xboole_0(X1_50) ),
    inference(renaming,[status(thm)],[c_13098])).

cnf(c_13101,plain,
    ( v2_funct_1(sK0)
    | ~ v1_xboole_0(sK0) ),
    inference(instantiation,[status(thm)],[c_13099])).

cnf(c_2189,plain,
    ( v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_804,c_786])).

cnf(c_2204,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_xboole_0(sK0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2189])).

cnf(c_1640,plain,
    ( ~ v1_xboole_0(X0_50)
    | ~ v1_xboole_0(sK2)
    | sK2 = X0_50 ),
    inference(instantiation,[status(thm)],[c_266])).

cnf(c_1642,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ v1_xboole_0(sK0)
    | sK2 = sK0 ),
    inference(instantiation,[status(thm)],[c_1640])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_265,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(X1_50))
    | ~ v1_relat_1(X1_50)
    | v1_relat_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_782,plain,
    ( m1_subset_1(X0_50,k1_zfmisc_1(X1_50)) != iProver_top
    | v1_relat_1(X1_50) != iProver_top
    | v1_relat_1(X0_50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_265])).

cnf(c_1285,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_801,c_782])).

cnf(c_3,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_264,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_50,X1_50)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_783,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_50,X1_50)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_264])).

cnf(c_1555,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1285,c_783])).

cnf(c_1556,plain,
    ( v1_relat_1(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1555])).

cnf(c_1230,plain,
    ( v1_xboole_0(X0_50)
    | ~ v1_xboole_0(k1_xboole_0)
    | X0_50 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_272])).

cnf(c_1232,plain,
    ( v1_xboole_0(sK0)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1230])).

cnf(c_5,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_262,plain,
    ( v5_relat_1(X0_50,X1_50)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X2_50,X1_50))) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1068,plain,
    ( v5_relat_1(sK3,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(instantiation,[status(thm)],[c_262])).

cnf(c_1069,plain,
    ( v5_relat_1(sK3,sK0) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1068])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_75,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_77,plain,
    ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_75])).

cnf(c_19,negated_conjecture,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_34,plain,
    ( v2_funct_2(sK3,sK0) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_93164,c_31326,c_31325,c_17973,c_13101,c_2204,c_1642,c_1556,c_1555,c_1232,c_1069,c_1068,c_0,c_77,c_34,c_19,c_32,c_21,c_31,c_30,c_29,c_28,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:31:24 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 27.36/3.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.36/3.98  
% 27.36/3.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.36/3.98  
% 27.36/3.98  ------  iProver source info
% 27.36/3.98  
% 27.36/3.98  git: date: 2020-06-30 10:37:57 +0100
% 27.36/3.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.36/3.98  git: non_committed_changes: false
% 27.36/3.98  git: last_make_outside_of_git: false
% 27.36/3.98  
% 27.36/3.98  ------ 
% 27.36/3.98  ------ Parsing...
% 27.36/3.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.36/3.98  
% 27.36/3.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 27.36/3.98  
% 27.36/3.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.36/3.98  
% 27.36/3.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.36/3.98  ------ Proving...
% 27.36/3.98  ------ Problem Properties 
% 27.36/3.98  
% 27.36/3.98  
% 27.36/3.98  clauses                                 27
% 27.36/3.98  conjectures                             8
% 27.36/3.98  EPR                                     7
% 27.36/3.98  Horn                                    26
% 27.36/3.98  unary                                   11
% 27.36/3.98  binary                                  4
% 27.36/3.98  lits                                    75
% 27.36/3.98  lits eq                                 8
% 27.36/3.98  fd_pure                                 0
% 27.36/3.98  fd_pseudo                               0
% 27.36/3.98  fd_cond                                 1
% 27.36/3.98  fd_pseudo_cond                          3
% 27.36/3.98  AC symbols                              0
% 27.36/3.98  
% 27.36/3.98  ------ Input Options Time Limit: Unbounded
% 27.36/3.98  
% 27.36/3.98  
% 27.36/3.98  ------ 
% 27.36/3.98  Current options:
% 27.36/3.98  ------ 
% 27.36/3.98  
% 27.36/3.98  
% 27.36/3.98  
% 27.36/3.98  
% 27.36/3.98  ------ Proving...
% 27.36/3.98  
% 27.36/3.98  
% 27.36/3.98  % SZS status Theorem for theBenchmark.p
% 27.36/3.98  
% 27.36/3.98  % SZS output start CNFRefutation for theBenchmark.p
% 27.36/3.98  
% 27.36/3.98  fof(f18,conjecture,(
% 27.36/3.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 27.36/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.36/3.98  
% 27.36/3.98  fof(f19,negated_conjecture,(
% 27.36/3.98    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 27.36/3.98    inference(negated_conjecture,[],[f18])).
% 27.36/3.98  
% 27.36/3.98  fof(f40,plain,(
% 27.36/3.98    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 27.36/3.98    inference(ennf_transformation,[],[f19])).
% 27.36/3.98  
% 27.36/3.98  fof(f41,plain,(
% 27.36/3.98    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 27.36/3.98    inference(flattening,[],[f40])).
% 27.36/3.98  
% 27.36/3.98  fof(f45,plain,(
% 27.36/3.98    ( ! [X2,X0,X1] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((~v2_funct_2(sK3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 27.36/3.98    introduced(choice_axiom,[])).
% 27.36/3.98  
% 27.36/3.98  fof(f44,plain,(
% 27.36/3.98    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 27.36/3.98    introduced(choice_axiom,[])).
% 27.36/3.98  
% 27.36/3.98  fof(f46,plain,(
% 27.36/3.98    ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 27.36/3.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f41,f45,f44])).
% 27.36/3.98  
% 27.36/3.98  fof(f73,plain,(
% 27.36/3.98    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 27.36/3.98    inference(cnf_transformation,[],[f46])).
% 27.36/3.98  
% 27.36/3.98  fof(f16,axiom,(
% 27.36/3.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 27.36/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.36/3.98  
% 27.36/3.98  fof(f36,plain,(
% 27.36/3.98    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 27.36/3.98    inference(ennf_transformation,[],[f16])).
% 27.36/3.98  
% 27.36/3.98  fof(f37,plain,(
% 27.36/3.98    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 27.36/3.98    inference(flattening,[],[f36])).
% 27.36/3.98  
% 27.36/3.98  fof(f64,plain,(
% 27.36/3.98    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 27.36/3.98    inference(cnf_transformation,[],[f37])).
% 27.36/3.98  
% 27.36/3.98  fof(f72,plain,(
% 27.36/3.98    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 27.36/3.98    inference(cnf_transformation,[],[f46])).
% 27.36/3.98  
% 27.36/3.98  fof(f9,axiom,(
% 27.36/3.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 27.36/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.36/3.98  
% 27.36/3.98  fof(f27,plain,(
% 27.36/3.98    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 27.36/3.98    inference(ennf_transformation,[],[f9])).
% 27.36/3.98  
% 27.36/3.98  fof(f55,plain,(
% 27.36/3.98    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 27.36/3.98    inference(cnf_transformation,[],[f27])).
% 27.36/3.98  
% 27.36/3.98  fof(f67,plain,(
% 27.36/3.98    v1_funct_1(sK2)),
% 27.36/3.98    inference(cnf_transformation,[],[f46])).
% 27.36/3.98  
% 27.36/3.98  fof(f68,plain,(
% 27.36/3.98    v1_funct_2(sK2,sK0,sK1)),
% 27.36/3.98    inference(cnf_transformation,[],[f46])).
% 27.36/3.98  
% 27.36/3.98  fof(f69,plain,(
% 27.36/3.98    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 27.36/3.98    inference(cnf_transformation,[],[f46])).
% 27.36/3.98  
% 27.36/3.98  fof(f70,plain,(
% 27.36/3.98    v1_funct_1(sK3)),
% 27.36/3.98    inference(cnf_transformation,[],[f46])).
% 27.36/3.98  
% 27.36/3.98  fof(f71,plain,(
% 27.36/3.98    v1_funct_2(sK3,sK1,sK0)),
% 27.36/3.98    inference(cnf_transformation,[],[f46])).
% 27.36/3.98  
% 27.36/3.98  fof(f13,axiom,(
% 27.36/3.98    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 27.36/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.36/3.98  
% 27.36/3.98  fof(f32,plain,(
% 27.36/3.98    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 27.36/3.98    inference(ennf_transformation,[],[f13])).
% 27.36/3.98  
% 27.36/3.98  fof(f33,plain,(
% 27.36/3.98    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 27.36/3.98    inference(flattening,[],[f32])).
% 27.36/3.98  
% 27.36/3.98  fof(f43,plain,(
% 27.36/3.98    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 27.36/3.98    inference(nnf_transformation,[],[f33])).
% 27.36/3.98  
% 27.36/3.98  fof(f61,plain,(
% 27.36/3.98    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 27.36/3.98    inference(cnf_transformation,[],[f43])).
% 27.36/3.98  
% 27.36/3.98  fof(f78,plain,(
% 27.36/3.98    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 27.36/3.98    inference(equality_resolution,[],[f61])).
% 27.36/3.98  
% 27.36/3.98  fof(f14,axiom,(
% 27.36/3.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 27.36/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.36/3.98  
% 27.36/3.98  fof(f34,plain,(
% 27.36/3.98    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 27.36/3.98    inference(ennf_transformation,[],[f14])).
% 27.36/3.98  
% 27.36/3.98  fof(f35,plain,(
% 27.36/3.98    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 27.36/3.98    inference(flattening,[],[f34])).
% 27.36/3.98  
% 27.36/3.98  fof(f62,plain,(
% 27.36/3.98    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 27.36/3.98    inference(cnf_transformation,[],[f35])).
% 27.36/3.98  
% 27.36/3.98  fof(f10,axiom,(
% 27.36/3.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 27.36/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.36/3.98  
% 27.36/3.98  fof(f28,plain,(
% 27.36/3.98    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 27.36/3.98    inference(ennf_transformation,[],[f10])).
% 27.36/3.98  
% 27.36/3.98  fof(f29,plain,(
% 27.36/3.98    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 27.36/3.98    inference(flattening,[],[f28])).
% 27.36/3.98  
% 27.36/3.98  fof(f56,plain,(
% 27.36/3.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 27.36/3.98    inference(cnf_transformation,[],[f29])).
% 27.36/3.98  
% 27.36/3.98  fof(f8,axiom,(
% 27.36/3.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))))),
% 27.36/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.36/3.98  
% 27.36/3.98  fof(f25,plain,(
% 27.36/3.98    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 27.36/3.98    inference(ennf_transformation,[],[f8])).
% 27.36/3.98  
% 27.36/3.98  fof(f26,plain,(
% 27.36/3.98    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 27.36/3.98    inference(flattening,[],[f25])).
% 27.36/3.98  
% 27.36/3.98  fof(f54,plain,(
% 27.36/3.98    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 27.36/3.98    inference(cnf_transformation,[],[f26])).
% 27.36/3.98  
% 27.36/3.98  fof(f11,axiom,(
% 27.36/3.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 27.36/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.36/3.98  
% 27.36/3.98  fof(f30,plain,(
% 27.36/3.98    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 27.36/3.98    inference(ennf_transformation,[],[f11])).
% 27.36/3.98  
% 27.36/3.98  fof(f31,plain,(
% 27.36/3.98    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 27.36/3.98    inference(flattening,[],[f30])).
% 27.36/3.98  
% 27.36/3.98  fof(f42,plain,(
% 27.36/3.98    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 27.36/3.98    inference(nnf_transformation,[],[f31])).
% 27.36/3.98  
% 27.36/3.98  fof(f57,plain,(
% 27.36/3.98    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 27.36/3.98    inference(cnf_transformation,[],[f42])).
% 27.36/3.98  
% 27.36/3.98  fof(f12,axiom,(
% 27.36/3.98    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 27.36/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.36/3.98  
% 27.36/3.98  fof(f59,plain,(
% 27.36/3.98    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 27.36/3.98    inference(cnf_transformation,[],[f12])).
% 27.36/3.98  
% 27.36/3.98  fof(f15,axiom,(
% 27.36/3.98    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 27.36/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.36/3.98  
% 27.36/3.98  fof(f63,plain,(
% 27.36/3.98    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 27.36/3.98    inference(cnf_transformation,[],[f15])).
% 27.36/3.98  
% 27.36/3.98  fof(f76,plain,(
% 27.36/3.98    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 27.36/3.98    inference(definition_unfolding,[],[f59,f63])).
% 27.36/3.98  
% 27.36/3.98  fof(f17,axiom,(
% 27.36/3.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 27.36/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.36/3.98  
% 27.36/3.98  fof(f38,plain,(
% 27.36/3.98    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 27.36/3.98    inference(ennf_transformation,[],[f17])).
% 27.36/3.98  
% 27.36/3.98  fof(f39,plain,(
% 27.36/3.98    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 27.36/3.98    inference(flattening,[],[f38])).
% 27.36/3.98  
% 27.36/3.98  fof(f65,plain,(
% 27.36/3.98    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X3) | k1_xboole_0 = X2 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 27.36/3.98    inference(cnf_transformation,[],[f39])).
% 27.36/3.98  
% 27.36/3.98  fof(f2,axiom,(
% 27.36/3.98    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 27.36/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.36/3.98  
% 27.36/3.98  fof(f21,plain,(
% 27.36/3.98    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 27.36/3.98    inference(ennf_transformation,[],[f2])).
% 27.36/3.98  
% 27.36/3.98  fof(f48,plain,(
% 27.36/3.98    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 27.36/3.98    inference(cnf_transformation,[],[f21])).
% 27.36/3.98  
% 27.36/3.98  fof(f5,axiom,(
% 27.36/3.98    ! [X0] : v2_funct_1(k6_relat_1(X0))),
% 27.36/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.36/3.98  
% 27.36/3.98  fof(f51,plain,(
% 27.36/3.98    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 27.36/3.98    inference(cnf_transformation,[],[f5])).
% 27.36/3.98  
% 27.36/3.98  fof(f75,plain,(
% 27.36/3.98    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 27.36/3.98    inference(definition_unfolding,[],[f51,f63])).
% 27.36/3.98  
% 27.36/3.98  fof(f7,axiom,(
% 27.36/3.98    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 27.36/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.36/3.98  
% 27.36/3.98  fof(f24,plain,(
% 27.36/3.98    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 27.36/3.98    inference(ennf_transformation,[],[f7])).
% 27.36/3.98  
% 27.36/3.98  fof(f53,plain,(
% 27.36/3.98    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 27.36/3.98    inference(cnf_transformation,[],[f24])).
% 27.36/3.98  
% 27.36/3.98  fof(f3,axiom,(
% 27.36/3.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 27.36/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.36/3.98  
% 27.36/3.98  fof(f22,plain,(
% 27.36/3.98    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 27.36/3.98    inference(ennf_transformation,[],[f3])).
% 27.36/3.98  
% 27.36/3.98  fof(f49,plain,(
% 27.36/3.98    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 27.36/3.98    inference(cnf_transformation,[],[f22])).
% 27.36/3.98  
% 27.36/3.98  fof(f4,axiom,(
% 27.36/3.98    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 27.36/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.36/3.98  
% 27.36/3.98  fof(f50,plain,(
% 27.36/3.98    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 27.36/3.98    inference(cnf_transformation,[],[f4])).
% 27.36/3.98  
% 27.36/3.98  fof(f6,axiom,(
% 27.36/3.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 27.36/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.36/3.98  
% 27.36/3.98  fof(f20,plain,(
% 27.36/3.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 27.36/3.98    inference(pure_predicate_removal,[],[f6])).
% 27.36/3.98  
% 27.36/3.98  fof(f23,plain,(
% 27.36/3.98    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 27.36/3.98    inference(ennf_transformation,[],[f20])).
% 27.36/3.98  
% 27.36/3.98  fof(f52,plain,(
% 27.36/3.98    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 27.36/3.98    inference(cnf_transformation,[],[f23])).
% 27.36/3.98  
% 27.36/3.98  fof(f1,axiom,(
% 27.36/3.98    v1_xboole_0(k1_xboole_0)),
% 27.36/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.36/3.98  
% 27.36/3.98  fof(f47,plain,(
% 27.36/3.98    v1_xboole_0(k1_xboole_0)),
% 27.36/3.98    inference(cnf_transformation,[],[f1])).
% 27.36/3.98  
% 27.36/3.98  fof(f74,plain,(
% 27.36/3.98    ~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)),
% 27.36/3.98    inference(cnf_transformation,[],[f46])).
% 27.36/3.98  
% 27.36/3.98  cnf(c_278,plain,
% 27.36/3.98      ( ~ v2_funct_1(X0_50) | v2_funct_1(X1_50) | X1_50 != X0_50 ),
% 27.36/3.98      theory(equality) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_93162,plain,
% 27.36/3.98      ( ~ v2_funct_1(X0_50) | v2_funct_1(sK2) | sK2 != X0_50 ),
% 27.36/3.98      inference(instantiation,[status(thm)],[c_278]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_93164,plain,
% 27.36/3.98      ( v2_funct_1(sK2) | ~ v2_funct_1(sK0) | sK2 != sK0 ),
% 27.36/3.98      inference(instantiation,[status(thm)],[c_93162]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_20,negated_conjecture,
% 27.36/3.98      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 27.36/3.98      inference(cnf_transformation,[],[f73]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_247,negated_conjecture,
% 27.36/3.98      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 27.36/3.98      inference(subtyping,[status(esa)],[c_20]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_800,plain,
% 27.36/3.98      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) = iProver_top ),
% 27.36/3.98      inference(predicate_to_equality,[status(thm)],[c_247]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_16,plain,
% 27.36/3.98      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 27.36/3.98      | ~ v1_funct_2(X2,X0,X1)
% 27.36/3.98      | ~ v1_funct_2(X3,X1,X0)
% 27.36/3.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 27.36/3.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 27.36/3.98      | ~ v1_funct_1(X2)
% 27.36/3.98      | ~ v1_funct_1(X3)
% 27.36/3.98      | k2_relset_1(X1,X0,X3) = X0 ),
% 27.36/3.98      inference(cnf_transformation,[],[f64]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_251,plain,
% 27.36/3.98      ( ~ r2_relset_1(X0_50,X0_50,k1_partfun1(X0_50,X1_50,X1_50,X0_50,X2_50,X3_50),k6_partfun1(X0_50))
% 27.36/3.98      | ~ v1_funct_2(X2_50,X0_50,X1_50)
% 27.36/3.98      | ~ v1_funct_2(X3_50,X1_50,X0_50)
% 27.36/3.98      | ~ m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X0_50)))
% 27.36/3.98      | ~ m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
% 27.36/3.98      | ~ v1_funct_1(X3_50)
% 27.36/3.98      | ~ v1_funct_1(X2_50)
% 27.36/3.98      | k2_relset_1(X1_50,X0_50,X3_50) = X0_50 ),
% 27.36/3.98      inference(subtyping,[status(esa)],[c_16]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_796,plain,
% 27.36/3.98      ( k2_relset_1(X0_50,X1_50,X2_50) = X1_50
% 27.36/3.98      | r2_relset_1(X1_50,X1_50,k1_partfun1(X1_50,X0_50,X0_50,X1_50,X3_50,X2_50),k6_partfun1(X1_50)) != iProver_top
% 27.36/3.98      | v1_funct_2(X2_50,X0_50,X1_50) != iProver_top
% 27.36/3.98      | v1_funct_2(X3_50,X1_50,X0_50) != iProver_top
% 27.36/3.98      | m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X0_50))) != iProver_top
% 27.36/3.98      | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
% 27.36/3.98      | v1_funct_1(X3_50) != iProver_top
% 27.36/3.98      | v1_funct_1(X2_50) != iProver_top ),
% 27.36/3.98      inference(predicate_to_equality,[status(thm)],[c_251]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_6190,plain,
% 27.36/3.98      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 27.36/3.98      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 27.36/3.98      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 27.36/3.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 27.36/3.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 27.36/3.98      | v1_funct_1(sK2) != iProver_top
% 27.36/3.98      | v1_funct_1(sK3) != iProver_top ),
% 27.36/3.98      inference(superposition,[status(thm)],[c_800,c_796]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_21,negated_conjecture,
% 27.36/3.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 27.36/3.98      inference(cnf_transformation,[],[f72]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_246,negated_conjecture,
% 27.36/3.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 27.36/3.98      inference(subtyping,[status(esa)],[c_21]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_801,plain,
% 27.36/3.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 27.36/3.98      inference(predicate_to_equality,[status(thm)],[c_246]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_8,plain,
% 27.36/3.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.36/3.98      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 27.36/3.98      inference(cnf_transformation,[],[f55]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_259,plain,
% 27.36/3.98      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
% 27.36/3.98      | k2_relset_1(X1_50,X2_50,X0_50) = k2_relat_1(X0_50) ),
% 27.36/3.98      inference(subtyping,[status(esa)],[c_8]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_788,plain,
% 27.36/3.98      ( k2_relset_1(X0_50,X1_50,X2_50) = k2_relat_1(X2_50)
% 27.36/3.98      | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top ),
% 27.36/3.98      inference(predicate_to_equality,[status(thm)],[c_259]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_2211,plain,
% 27.36/3.98      ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 27.36/3.98      inference(superposition,[status(thm)],[c_801,c_788]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_6191,plain,
% 27.36/3.98      ( k2_relat_1(sK3) = sK0
% 27.36/3.98      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 27.36/3.98      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 27.36/3.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 27.36/3.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 27.36/3.98      | v1_funct_1(sK2) != iProver_top
% 27.36/3.98      | v1_funct_1(sK3) != iProver_top ),
% 27.36/3.98      inference(demodulation,[status(thm)],[c_6190,c_2211]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_26,negated_conjecture,
% 27.36/3.98      ( v1_funct_1(sK2) ),
% 27.36/3.98      inference(cnf_transformation,[],[f67]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_27,plain,
% 27.36/3.98      ( v1_funct_1(sK2) = iProver_top ),
% 27.36/3.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_25,negated_conjecture,
% 27.36/3.98      ( v1_funct_2(sK2,sK0,sK1) ),
% 27.36/3.98      inference(cnf_transformation,[],[f68]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_28,plain,
% 27.36/3.98      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 27.36/3.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_24,negated_conjecture,
% 27.36/3.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 27.36/3.98      inference(cnf_transformation,[],[f69]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_29,plain,
% 27.36/3.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 27.36/3.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_23,negated_conjecture,
% 27.36/3.98      ( v1_funct_1(sK3) ),
% 27.36/3.98      inference(cnf_transformation,[],[f70]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_30,plain,
% 27.36/3.98      ( v1_funct_1(sK3) = iProver_top ),
% 27.36/3.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_22,negated_conjecture,
% 27.36/3.98      ( v1_funct_2(sK3,sK1,sK0) ),
% 27.36/3.98      inference(cnf_transformation,[],[f71]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_31,plain,
% 27.36/3.98      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 27.36/3.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_32,plain,
% 27.36/3.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 27.36/3.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_31320,plain,
% 27.36/3.98      ( k2_relat_1(sK3) = sK0 ),
% 27.36/3.98      inference(global_propositional_subsumption,
% 27.36/3.98                [status(thm)],
% 27.36/3.98                [c_6191,c_27,c_28,c_29,c_30,c_31,c_32]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_13,plain,
% 27.36/3.98      ( v2_funct_2(X0,k2_relat_1(X0))
% 27.36/3.98      | ~ v5_relat_1(X0,k2_relat_1(X0))
% 27.36/3.98      | ~ v1_relat_1(X0) ),
% 27.36/3.98      inference(cnf_transformation,[],[f78]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_254,plain,
% 27.36/3.98      ( v2_funct_2(X0_50,k2_relat_1(X0_50))
% 27.36/3.98      | ~ v5_relat_1(X0_50,k2_relat_1(X0_50))
% 27.36/3.98      | ~ v1_relat_1(X0_50) ),
% 27.36/3.98      inference(subtyping,[status(esa)],[c_13]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_793,plain,
% 27.36/3.98      ( v2_funct_2(X0_50,k2_relat_1(X0_50)) = iProver_top
% 27.36/3.98      | v5_relat_1(X0_50,k2_relat_1(X0_50)) != iProver_top
% 27.36/3.98      | v1_relat_1(X0_50) != iProver_top ),
% 27.36/3.98      inference(predicate_to_equality,[status(thm)],[c_254]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_31324,plain,
% 27.36/3.98      ( v2_funct_2(sK3,k2_relat_1(sK3)) = iProver_top
% 27.36/3.98      | v5_relat_1(sK3,sK0) != iProver_top
% 27.36/3.98      | v1_relat_1(sK3) != iProver_top ),
% 27.36/3.98      inference(superposition,[status(thm)],[c_31320,c_793]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_31325,plain,
% 27.36/3.98      ( v2_funct_2(sK3,sK0) = iProver_top
% 27.36/3.98      | v5_relat_1(sK3,sK0) != iProver_top
% 27.36/3.98      | v1_relat_1(sK3) != iProver_top ),
% 27.36/3.98      inference(light_normalisation,[status(thm)],[c_31324,c_31320]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_31326,plain,
% 27.36/3.98      ( v2_funct_2(sK3,sK0) | ~ v5_relat_1(sK3,sK0) | ~ v1_relat_1(sK3) ),
% 27.36/3.98      inference(predicate_to_equality_rev,[status(thm)],[c_31325]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_243,negated_conjecture,
% 27.36/3.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 27.36/3.98      inference(subtyping,[status(esa)],[c_24]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_804,plain,
% 27.36/3.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 27.36/3.98      inference(predicate_to_equality,[status(thm)],[c_243]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_15,plain,
% 27.36/3.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.36/3.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 27.36/3.98      | ~ v1_funct_1(X0)
% 27.36/3.98      | ~ v1_funct_1(X3)
% 27.36/3.98      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 27.36/3.98      inference(cnf_transformation,[],[f62]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_252,plain,
% 27.36/3.98      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
% 27.36/3.98      | ~ m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X4_50,X5_50)))
% 27.36/3.98      | ~ v1_funct_1(X3_50)
% 27.36/3.98      | ~ v1_funct_1(X0_50)
% 27.36/3.98      | k1_partfun1(X4_50,X5_50,X1_50,X2_50,X3_50,X0_50) = k5_relat_1(X3_50,X0_50) ),
% 27.36/3.98      inference(subtyping,[status(esa)],[c_15]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_795,plain,
% 27.36/3.98      ( k1_partfun1(X0_50,X1_50,X2_50,X3_50,X4_50,X5_50) = k5_relat_1(X4_50,X5_50)
% 27.36/3.98      | m1_subset_1(X5_50,k1_zfmisc_1(k2_zfmisc_1(X2_50,X3_50))) != iProver_top
% 27.36/3.98      | m1_subset_1(X4_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
% 27.36/3.98      | v1_funct_1(X5_50) != iProver_top
% 27.36/3.98      | v1_funct_1(X4_50) != iProver_top ),
% 27.36/3.98      inference(predicate_to_equality,[status(thm)],[c_252]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_4172,plain,
% 27.36/3.98      ( k1_partfun1(X0_50,X1_50,sK1,sK0,X2_50,sK3) = k5_relat_1(X2_50,sK3)
% 27.36/3.98      | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
% 27.36/3.98      | v1_funct_1(X2_50) != iProver_top
% 27.36/3.98      | v1_funct_1(sK3) != iProver_top ),
% 27.36/3.98      inference(superposition,[status(thm)],[c_801,c_795]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_6408,plain,
% 27.36/3.98      ( v1_funct_1(X2_50) != iProver_top
% 27.36/3.98      | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
% 27.36/3.98      | k1_partfun1(X0_50,X1_50,sK1,sK0,X2_50,sK3) = k5_relat_1(X2_50,sK3) ),
% 27.36/3.98      inference(global_propositional_subsumption,
% 27.36/3.98                [status(thm)],
% 27.36/3.98                [c_4172,c_30]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_6409,plain,
% 27.36/3.98      ( k1_partfun1(X0_50,X1_50,sK1,sK0,X2_50,sK3) = k5_relat_1(X2_50,sK3)
% 27.36/3.98      | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
% 27.36/3.98      | v1_funct_1(X2_50) != iProver_top ),
% 27.36/3.98      inference(renaming,[status(thm)],[c_6408]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_6418,plain,
% 27.36/3.98      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 27.36/3.98      | v1_funct_1(sK2) != iProver_top ),
% 27.36/3.98      inference(superposition,[status(thm)],[c_804,c_6409]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_1200,plain,
% 27.36/3.98      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
% 27.36/3.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3_50,X4_50)))
% 27.36/3.98      | ~ v1_funct_1(X0_50)
% 27.36/3.98      | ~ v1_funct_1(sK3)
% 27.36/3.98      | k1_partfun1(X1_50,X2_50,X3_50,X4_50,X0_50,sK3) = k5_relat_1(X0_50,sK3) ),
% 27.36/3.98      inference(instantiation,[status(thm)],[c_252]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_1522,plain,
% 27.36/3.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
% 27.36/3.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2_50,X3_50)))
% 27.36/3.98      | ~ v1_funct_1(sK2)
% 27.36/3.98      | ~ v1_funct_1(sK3)
% 27.36/3.98      | k1_partfun1(X0_50,X1_50,X2_50,X3_50,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 27.36/3.98      inference(instantiation,[status(thm)],[c_1200]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_2316,plain,
% 27.36/3.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
% 27.36/3.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 27.36/3.98      | ~ v1_funct_1(sK2)
% 27.36/3.98      | ~ v1_funct_1(sK3)
% 27.36/3.98      | k1_partfun1(X0_50,X1_50,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 27.36/3.98      inference(instantiation,[status(thm)],[c_1522]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_3580,plain,
% 27.36/3.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 27.36/3.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 27.36/3.98      | ~ v1_funct_1(sK2)
% 27.36/3.98      | ~ v1_funct_1(sK3)
% 27.36/3.98      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 27.36/3.98      inference(instantiation,[status(thm)],[c_2316]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_6500,plain,
% 27.36/3.98      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 27.36/3.98      inference(global_propositional_subsumption,
% 27.36/3.98                [status(thm)],
% 27.36/3.98                [c_6418,c_26,c_24,c_23,c_21,c_3580]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_6503,plain,
% 27.36/3.98      ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) = iProver_top ),
% 27.36/3.98      inference(demodulation,[status(thm)],[c_6500,c_800]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_9,plain,
% 27.36/3.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.36/3.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 27.36/3.98      | k4_relset_1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 27.36/3.98      inference(cnf_transformation,[],[f56]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_258,plain,
% 27.36/3.98      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
% 27.36/3.98      | ~ m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X4_50,X5_50)))
% 27.36/3.98      | k4_relset_1(X4_50,X5_50,X1_50,X2_50,X3_50,X0_50) = k5_relat_1(X3_50,X0_50) ),
% 27.36/3.98      inference(subtyping,[status(esa)],[c_9]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_789,plain,
% 27.36/3.98      ( k4_relset_1(X0_50,X1_50,X2_50,X3_50,X4_50,X5_50) = k5_relat_1(X4_50,X5_50)
% 27.36/3.98      | m1_subset_1(X5_50,k1_zfmisc_1(k2_zfmisc_1(X2_50,X3_50))) != iProver_top
% 27.36/3.98      | m1_subset_1(X4_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top ),
% 27.36/3.98      inference(predicate_to_equality,[status(thm)],[c_258]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_3948,plain,
% 27.36/3.98      ( k4_relset_1(X0_50,X1_50,sK1,sK0,X2_50,sK3) = k5_relat_1(X2_50,sK3)
% 27.36/3.98      | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top ),
% 27.36/3.98      inference(superposition,[status(thm)],[c_801,c_789]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_4564,plain,
% 27.36/3.98      ( k4_relset_1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 27.36/3.98      inference(superposition,[status(thm)],[c_804,c_3948]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_7,plain,
% 27.36/3.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.36/3.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 27.36/3.98      | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) ),
% 27.36/3.98      inference(cnf_transformation,[],[f54]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_260,plain,
% 27.36/3.98      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
% 27.36/3.98      | ~ m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X4_50,X5_50)))
% 27.36/3.98      | m1_subset_1(k4_relset_1(X4_50,X5_50,X1_50,X2_50,X3_50,X0_50),k1_zfmisc_1(k2_zfmisc_1(X4_50,X2_50))) ),
% 27.36/3.98      inference(subtyping,[status(esa)],[c_7]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_787,plain,
% 27.36/3.98      ( m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50))) != iProver_top
% 27.36/3.98      | m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X4_50,X5_50))) != iProver_top
% 27.36/3.98      | m1_subset_1(k4_relset_1(X4_50,X5_50,X1_50,X2_50,X3_50,X0_50),k1_zfmisc_1(k2_zfmisc_1(X4_50,X2_50))) = iProver_top ),
% 27.36/3.98      inference(predicate_to_equality,[status(thm)],[c_260]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_4859,plain,
% 27.36/3.98      ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 27.36/3.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 27.36/3.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 27.36/3.98      inference(superposition,[status(thm)],[c_4564,c_787]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_8403,plain,
% 27.36/3.98      ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 27.36/3.98      inference(global_propositional_subsumption,
% 27.36/3.98                [status(thm)],
% 27.36/3.98                [c_4859,c_29,c_32]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_11,plain,
% 27.36/3.98      ( ~ r2_relset_1(X0,X1,X2,X3)
% 27.36/3.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 27.36/3.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 27.36/3.98      | X3 = X2 ),
% 27.36/3.98      inference(cnf_transformation,[],[f57]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_256,plain,
% 27.36/3.98      ( ~ r2_relset_1(X0_50,X1_50,X2_50,X3_50)
% 27.36/3.98      | ~ m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
% 27.36/3.98      | ~ m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
% 27.36/3.98      | X3_50 = X2_50 ),
% 27.36/3.98      inference(subtyping,[status(esa)],[c_11]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_791,plain,
% 27.36/3.98      ( X0_50 = X1_50
% 27.36/3.98      | r2_relset_1(X2_50,X3_50,X1_50,X0_50) != iProver_top
% 27.36/3.98      | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_50,X3_50))) != iProver_top
% 27.36/3.98      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X2_50,X3_50))) != iProver_top ),
% 27.36/3.98      inference(predicate_to_equality,[status(thm)],[c_256]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_8417,plain,
% 27.36/3.98      ( k5_relat_1(sK2,sK3) = X0_50
% 27.36/3.98      | r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),X0_50) != iProver_top
% 27.36/3.98      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 27.36/3.98      inference(superposition,[status(thm)],[c_8403,c_791]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_17544,plain,
% 27.36/3.98      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 27.36/3.98      | m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 27.36/3.98      inference(superposition,[status(thm)],[c_6503,c_8417]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_12,plain,
% 27.36/3.98      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 27.36/3.98      inference(cnf_transformation,[],[f76]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_53,plain,
% 27.36/3.98      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 27.36/3.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_55,plain,
% 27.36/3.98      ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 27.36/3.98      inference(instantiation,[status(thm)],[c_53]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_17685,plain,
% 27.36/3.98      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 27.36/3.98      inference(global_propositional_subsumption,
% 27.36/3.98                [status(thm)],
% 27.36/3.98                [c_17544,c_55]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_17707,plain,
% 27.36/3.98      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
% 27.36/3.98      inference(demodulation,[status(thm)],[c_17685,c_6500]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_18,plain,
% 27.36/3.98      ( ~ v1_funct_2(X0,X1,X2)
% 27.36/3.98      | ~ v1_funct_2(X3,X2,X4)
% 27.36/3.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.36/3.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
% 27.36/3.98      | ~ v1_funct_1(X3)
% 27.36/3.98      | ~ v1_funct_1(X0)
% 27.36/3.98      | v2_funct_1(X0)
% 27.36/3.98      | ~ v2_funct_1(k1_partfun1(X1,X2,X2,X4,X0,X3))
% 27.36/3.98      | k1_xboole_0 = X4 ),
% 27.36/3.98      inference(cnf_transformation,[],[f65]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_249,plain,
% 27.36/3.98      ( ~ v1_funct_2(X0_50,X1_50,X2_50)
% 27.36/3.98      | ~ v1_funct_2(X3_50,X2_50,X4_50)
% 27.36/3.98      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
% 27.36/3.98      | ~ m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X2_50,X4_50)))
% 27.36/3.98      | ~ v1_funct_1(X3_50)
% 27.36/3.98      | ~ v1_funct_1(X0_50)
% 27.36/3.98      | v2_funct_1(X0_50)
% 27.36/3.98      | ~ v2_funct_1(k1_partfun1(X1_50,X2_50,X2_50,X4_50,X0_50,X3_50))
% 27.36/3.98      | k1_xboole_0 = X4_50 ),
% 27.36/3.98      inference(subtyping,[status(esa)],[c_18]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_798,plain,
% 27.36/3.98      ( k1_xboole_0 = X0_50
% 27.36/3.98      | v1_funct_2(X1_50,X2_50,X3_50) != iProver_top
% 27.36/3.98      | v1_funct_2(X4_50,X3_50,X0_50) != iProver_top
% 27.36/3.98      | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_50,X3_50))) != iProver_top
% 27.36/3.98      | m1_subset_1(X4_50,k1_zfmisc_1(k2_zfmisc_1(X3_50,X0_50))) != iProver_top
% 27.36/3.98      | v1_funct_1(X1_50) != iProver_top
% 27.36/3.98      | v1_funct_1(X4_50) != iProver_top
% 27.36/3.98      | v2_funct_1(X1_50) = iProver_top
% 27.36/3.98      | v2_funct_1(k1_partfun1(X2_50,X3_50,X3_50,X0_50,X1_50,X4_50)) != iProver_top ),
% 27.36/3.98      inference(predicate_to_equality,[status(thm)],[c_249]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_17973,plain,
% 27.36/3.98      ( sK0 = k1_xboole_0
% 27.36/3.98      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 27.36/3.98      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 27.36/3.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 27.36/3.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 27.36/3.98      | v1_funct_1(sK2) != iProver_top
% 27.36/3.98      | v1_funct_1(sK3) != iProver_top
% 27.36/3.98      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 27.36/3.98      | v2_funct_1(sK2) = iProver_top ),
% 27.36/3.98      inference(superposition,[status(thm)],[c_17707,c_798]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_1,plain,
% 27.36/3.98      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X1 = X0 ),
% 27.36/3.98      inference(cnf_transformation,[],[f48]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_266,plain,
% 27.36/3.98      ( ~ v1_xboole_0(X0_50) | ~ v1_xboole_0(X1_50) | X1_50 = X0_50 ),
% 27.36/3.98      inference(subtyping,[status(esa)],[c_1]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_6324,plain,
% 27.36/3.98      ( ~ v2_funct_1(X0_50)
% 27.36/3.98      | v2_funct_1(X1_50)
% 27.36/3.98      | ~ v1_xboole_0(X1_50)
% 27.36/3.98      | ~ v1_xboole_0(X0_50) ),
% 27.36/3.98      inference(resolution,[status(thm)],[c_266,c_278]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_4,plain,
% 27.36/3.98      ( v2_funct_1(k6_partfun1(X0)) ),
% 27.36/3.98      inference(cnf_transformation,[],[f75]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_263,plain,
% 27.36/3.98      ( v2_funct_1(k6_partfun1(X0_50)) ),
% 27.36/3.98      inference(subtyping,[status(esa)],[c_4]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_1053,plain,
% 27.36/3.98      ( v2_funct_1(X0_50)
% 27.36/3.98      | ~ v2_funct_1(k6_partfun1(X1_50))
% 27.36/3.98      | X0_50 != k6_partfun1(X1_50) ),
% 27.36/3.98      inference(instantiation,[status(thm)],[c_278]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_1380,plain,
% 27.36/3.98      ( ~ v1_xboole_0(X0_50)
% 27.36/3.98      | ~ v1_xboole_0(k6_partfun1(X1_50))
% 27.36/3.98      | X0_50 = k6_partfun1(X1_50) ),
% 27.36/3.98      inference(instantiation,[status(thm)],[c_266]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_277,plain,
% 27.36/3.98      ( X0_50 != X1_50 | k6_partfun1(X0_50) = k6_partfun1(X1_50) ),
% 27.36/3.98      theory(equality) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_1788,plain,
% 27.36/3.98      ( ~ v2_funct_1(k6_partfun1(X0_50))
% 27.36/3.98      | v2_funct_1(k6_partfun1(X1_50))
% 27.36/3.98      | X1_50 != X0_50 ),
% 27.36/3.98      inference(resolution,[status(thm)],[c_277,c_278]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_255,plain,
% 27.36/3.98      ( m1_subset_1(k6_partfun1(X0_50),k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50))) ),
% 27.36/3.98      inference(subtyping,[status(esa)],[c_12]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_792,plain,
% 27.36/3.98      ( m1_subset_1(k6_partfun1(X0_50),k1_zfmisc_1(k2_zfmisc_1(X0_50,X0_50))) = iProver_top ),
% 27.36/3.98      inference(predicate_to_equality,[status(thm)],[c_255]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_6,plain,
% 27.36/3.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.36/3.98      | ~ v1_xboole_0(X1)
% 27.36/3.98      | v1_xboole_0(X0) ),
% 27.36/3.98      inference(cnf_transformation,[],[f53]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_261,plain,
% 27.36/3.98      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
% 27.36/3.98      | ~ v1_xboole_0(X1_50)
% 27.36/3.98      | v1_xboole_0(X0_50) ),
% 27.36/3.98      inference(subtyping,[status(esa)],[c_6]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_786,plain,
% 27.36/3.98      ( m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50))) != iProver_top
% 27.36/3.98      | v1_xboole_0(X1_50) != iProver_top
% 27.36/3.98      | v1_xboole_0(X0_50) = iProver_top ),
% 27.36/3.98      inference(predicate_to_equality,[status(thm)],[c_261]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_2190,plain,
% 27.36/3.98      ( v1_xboole_0(X0_50) != iProver_top
% 27.36/3.98      | v1_xboole_0(k6_partfun1(X0_50)) = iProver_top ),
% 27.36/3.98      inference(superposition,[status(thm)],[c_792,c_786]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_2205,plain,
% 27.36/3.98      ( ~ v1_xboole_0(X0_50) | v1_xboole_0(k6_partfun1(X0_50)) ),
% 27.36/3.98      inference(predicate_to_equality_rev,[status(thm)],[c_2190]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_272,plain,
% 27.36/3.98      ( ~ v1_xboole_0(X0_50) | v1_xboole_0(X1_50) | X1_50 != X0_50 ),
% 27.36/3.98      theory(equality) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_4293,plain,
% 27.36/3.98      ( ~ v1_xboole_0(k6_partfun1(X0_50))
% 27.36/3.98      | v1_xboole_0(k6_partfun1(X1_50))
% 27.36/3.98      | X1_50 != X0_50 ),
% 27.36/3.98      inference(resolution,[status(thm)],[c_272,c_277]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_13098,plain,
% 27.36/3.98      ( v2_funct_1(X1_50) | ~ v1_xboole_0(X1_50) | ~ v1_xboole_0(X0_50) ),
% 27.36/3.98      inference(global_propositional_subsumption,
% 27.36/3.98                [status(thm)],
% 27.36/3.98                [c_6324,c_266,c_263,c_1053,c_1380,c_1788,c_2205,c_4293]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_13099,plain,
% 27.36/3.98      ( v2_funct_1(X0_50) | ~ v1_xboole_0(X0_50) | ~ v1_xboole_0(X1_50) ),
% 27.36/3.98      inference(renaming,[status(thm)],[c_13098]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_13101,plain,
% 27.36/3.98      ( v2_funct_1(sK0) | ~ v1_xboole_0(sK0) ),
% 27.36/3.98      inference(instantiation,[status(thm)],[c_13099]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_2189,plain,
% 27.36/3.98      ( v1_xboole_0(sK2) = iProver_top
% 27.36/3.98      | v1_xboole_0(sK0) != iProver_top ),
% 27.36/3.98      inference(superposition,[status(thm)],[c_804,c_786]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_2204,plain,
% 27.36/3.98      ( v1_xboole_0(sK2) | ~ v1_xboole_0(sK0) ),
% 27.36/3.98      inference(predicate_to_equality_rev,[status(thm)],[c_2189]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_1640,plain,
% 27.36/3.98      ( ~ v1_xboole_0(X0_50) | ~ v1_xboole_0(sK2) | sK2 = X0_50 ),
% 27.36/3.98      inference(instantiation,[status(thm)],[c_266]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_1642,plain,
% 27.36/3.98      ( ~ v1_xboole_0(sK2) | ~ v1_xboole_0(sK0) | sK2 = sK0 ),
% 27.36/3.98      inference(instantiation,[status(thm)],[c_1640]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_2,plain,
% 27.36/3.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 27.36/3.98      | ~ v1_relat_1(X1)
% 27.36/3.98      | v1_relat_1(X0) ),
% 27.36/3.98      inference(cnf_transformation,[],[f49]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_265,plain,
% 27.36/3.98      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(X1_50))
% 27.36/3.98      | ~ v1_relat_1(X1_50)
% 27.36/3.98      | v1_relat_1(X0_50) ),
% 27.36/3.98      inference(subtyping,[status(esa)],[c_2]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_782,plain,
% 27.36/3.98      ( m1_subset_1(X0_50,k1_zfmisc_1(X1_50)) != iProver_top
% 27.36/3.98      | v1_relat_1(X1_50) != iProver_top
% 27.36/3.98      | v1_relat_1(X0_50) = iProver_top ),
% 27.36/3.98      inference(predicate_to_equality,[status(thm)],[c_265]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_1285,plain,
% 27.36/3.98      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 27.36/3.98      | v1_relat_1(sK3) = iProver_top ),
% 27.36/3.98      inference(superposition,[status(thm)],[c_801,c_782]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_3,plain,
% 27.36/3.98      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 27.36/3.98      inference(cnf_transformation,[],[f50]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_264,plain,
% 27.36/3.98      ( v1_relat_1(k2_zfmisc_1(X0_50,X1_50)) ),
% 27.36/3.98      inference(subtyping,[status(esa)],[c_3]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_783,plain,
% 27.36/3.98      ( v1_relat_1(k2_zfmisc_1(X0_50,X1_50)) = iProver_top ),
% 27.36/3.98      inference(predicate_to_equality,[status(thm)],[c_264]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_1555,plain,
% 27.36/3.98      ( v1_relat_1(sK3) = iProver_top ),
% 27.36/3.98      inference(forward_subsumption_resolution,
% 27.36/3.98                [status(thm)],
% 27.36/3.98                [c_1285,c_783]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_1556,plain,
% 27.36/3.98      ( v1_relat_1(sK3) ),
% 27.36/3.98      inference(predicate_to_equality_rev,[status(thm)],[c_1555]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_1230,plain,
% 27.36/3.98      ( v1_xboole_0(X0_50)
% 27.36/3.98      | ~ v1_xboole_0(k1_xboole_0)
% 27.36/3.98      | X0_50 != k1_xboole_0 ),
% 27.36/3.98      inference(instantiation,[status(thm)],[c_272]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_1232,plain,
% 27.36/3.98      ( v1_xboole_0(sK0)
% 27.36/3.98      | ~ v1_xboole_0(k1_xboole_0)
% 27.36/3.98      | sK0 != k1_xboole_0 ),
% 27.36/3.98      inference(instantiation,[status(thm)],[c_1230]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_5,plain,
% 27.36/3.98      ( v5_relat_1(X0,X1)
% 27.36/3.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 27.36/3.98      inference(cnf_transformation,[],[f52]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_262,plain,
% 27.36/3.98      ( v5_relat_1(X0_50,X1_50)
% 27.36/3.98      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X2_50,X1_50))) ),
% 27.36/3.98      inference(subtyping,[status(esa)],[c_5]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_1068,plain,
% 27.36/3.98      ( v5_relat_1(sK3,sK0)
% 27.36/3.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 27.36/3.98      inference(instantiation,[status(thm)],[c_262]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_1069,plain,
% 27.36/3.98      ( v5_relat_1(sK3,sK0) = iProver_top
% 27.36/3.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 27.36/3.98      inference(predicate_to_equality,[status(thm)],[c_1068]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_0,plain,
% 27.36/3.98      ( v1_xboole_0(k1_xboole_0) ),
% 27.36/3.98      inference(cnf_transformation,[],[f47]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_75,plain,
% 27.36/3.98      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 27.36/3.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_77,plain,
% 27.36/3.98      ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
% 27.36/3.98      inference(instantiation,[status(thm)],[c_75]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_19,negated_conjecture,
% 27.36/3.98      ( ~ v2_funct_2(sK3,sK0) | ~ v2_funct_1(sK2) ),
% 27.36/3.98      inference(cnf_transformation,[],[f74]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(c_34,plain,
% 27.36/3.98      ( v2_funct_2(sK3,sK0) != iProver_top
% 27.36/3.98      | v2_funct_1(sK2) != iProver_top ),
% 27.36/3.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 27.36/3.98  
% 27.36/3.98  cnf(contradiction,plain,
% 27.36/3.98      ( $false ),
% 27.36/3.98      inference(minisat,
% 27.36/3.98                [status(thm)],
% 27.36/3.98                [c_93164,c_31326,c_31325,c_17973,c_13101,c_2204,c_1642,
% 27.36/3.98                 c_1556,c_1555,c_1232,c_1069,c_1068,c_0,c_77,c_34,c_19,
% 27.36/3.98                 c_32,c_21,c_31,c_30,c_29,c_28,c_27]) ).
% 27.36/3.98  
% 27.36/3.98  
% 27.36/3.98  % SZS output end CNFRefutation for theBenchmark.p
% 27.36/3.98  
% 27.36/3.98  ------                               Statistics
% 27.36/3.98  
% 27.36/3.98  ------ Selected
% 27.36/3.98  
% 27.36/3.98  total_time:                             3.447
% 27.36/3.98  
%------------------------------------------------------------------------------
