%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:01:59 EST 2020

% Result     : Theorem 3.83s
% Output     : CNFRefutation 3.83s
% Verified   : 
% Statistics : Number of formulae       :  173 (1265 expanded)
%              Number of clauses        :   95 ( 339 expanded)
%              Number of leaves         :   20 ( 325 expanded)
%              Depth                    :   19
%              Number of atoms          :  615 (7978 expanded)
%              Number of equality atoms :  201 ( 570 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   2 average)

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

fof(f39,plain,(
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
    inference(flattening,[],[f39])).

fof(f47,plain,(
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

fof(f46,plain,
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

fof(f48,plain,
    ( ( ~ v2_funct_2(sK3,sK0)
      | ~ v2_funct_1(sK2) )
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f40,f47,f46])).

fof(f77,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f48])).

fof(f80,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f48])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f35])).

fof(f72,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f78,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f29])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f81,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f48])).

fof(f12,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f16,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f87,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f67,f73])).

fof(f75,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f33])).

fof(f71,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X0))
           => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
      | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f84,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f55,f73])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f41])).

fof(f51,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => v2_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_funct_1(X1)
          | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_funct_1(X1)
          | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f17,axiom,(
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
    inference(ennf_transformation,[],[f17])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f76,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f79,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f91,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f69])).

fof(f82,plain,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f5,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f85,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f58,f73])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1165,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1168,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1169,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3348,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1168,c_1169])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_36,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3604,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3348,c_36])).

cnf(c_3605,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_3604])).

cnf(c_3612,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1165,c_3605])).

cnf(c_17,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_26,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_469,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_26])).

cnf(c_470,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_469])).

cnf(c_18,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_60,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_472,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_470,c_60])).

cnf(c_1158,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_472])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1217,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_1808,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1158,c_32,c_30,c_29,c_27,c_60,c_470,c_1217])).

cnf(c_3613,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3612,c_1808])).

cnf(c_33,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_3853,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3613,c_33])).

cnf(c_10,plain,
    ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k1_relat_1(k5_relat_1(X0,X1)) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1176,plain,
    ( k1_relat_1(k5_relat_1(X0,X1)) != k1_relat_1(X0)
    | r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3855,plain,
    ( k1_relat_1(k6_partfun1(sK0)) != k1_relat_1(sK2)
    | r1_tarski(k2_relat_1(sK2),k1_relat_1(sK3)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3853,c_1176])).

cnf(c_7,plain,
    ( k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_3858,plain,
    ( k1_relat_1(sK2) != sK0
    | r1_tarski(k2_relat_1(sK2),k1_relat_1(sK3)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3855,c_7])).

cnf(c_35,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_38,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1268,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1296,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1268])).

cnf(c_1297,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1296])).

cnf(c_1351,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1352,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1351])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v4_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_4,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_347,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_14,c_4])).

cnf(c_351,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_347,c_12])).

cnf(c_352,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_351])).

cnf(c_1162,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_352])).

cnf(c_2154,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1165,c_1162])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1181,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2647,plain,
    ( k1_relat_1(sK2) = sK0
    | r1_tarski(sK0,k1_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2154,c_1181])).

cnf(c_5,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1179,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3856,plain,
    ( r1_tarski(k1_relat_1(k6_partfun1(sK0)),k1_relat_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3853,c_1179])).

cnf(c_3857,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3856,c_7])).

cnf(c_3970,plain,
    ( r1_tarski(k2_relat_1(sK2),k1_relat_1(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3858,c_33,c_35,c_36,c_38,c_1297,c_1352,c_2647,c_3857])).

cnf(c_11,plain,
    ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | v2_funct_1(X0)
    | ~ v2_funct_1(k5_relat_1(X0,X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1175,plain,
    ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v2_funct_1(X0) = iProver_top
    | v2_funct_1(k5_relat_1(X0,X1)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3975,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
    | v2_funct_1(sK2) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3970,c_1175])).

cnf(c_3976,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK2) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3975,c_3853])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1173,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2362,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1168,c_1173])).

cnf(c_24,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_483,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X2,X1,X1,X2,X3,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,X2,X0) = X2
    | k6_partfun1(X2) != k6_partfun1(sK0)
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_26])).

cnf(c_484,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0
    | k6_partfun1(sK0) != k6_partfun1(sK0) ),
    inference(unflattening,[status(thm)],[c_483])).

cnf(c_562,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_484])).

cnf(c_1157,plain,
    ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X0,sK0,X2) = sK0
    | v1_funct_2(X2,X0,sK0) != iProver_top
    | v1_funct_2(X1,sK0,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_562])).

cnf(c_1912,plain,
    ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k6_partfun1(sK0)
    | k2_relset_1(X0,sK0,X2) = sK0
    | v1_funct_2(X2,X0,sK0) != iProver_top
    | v1_funct_2(X1,sK0,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1157,c_1808])).

cnf(c_1916,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1808,c_1912])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_34,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_37,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_1919,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1916,c_33,c_34,c_35,c_36,c_37,c_38])).

cnf(c_2364,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_2362,c_1919])).

cnf(c_13,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_19,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_387,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X0)
    | X0 != X1
    | k2_relat_1(X0) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_19])).

cnf(c_388,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_387])).

cnf(c_398,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0)))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_388,c_12])).

cnf(c_25,negated_conjecture,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_413,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
    | ~ v2_funct_1(sK2)
    | k2_relat_1(X0) != sK0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_398,c_25])).

cnf(c_414,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3))))
    | ~ v2_funct_1(sK2)
    | k2_relat_1(sK3) != sK0 ),
    inference(unflattening,[status(thm)],[c_413])).

cnf(c_705,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3))))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_414])).

cnf(c_1161,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3)))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_705])).

cnf(c_2692,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(demodulation,[status(thm)],[c_2364,c_1161])).

cnf(c_3035,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_1168,c_2692])).

cnf(c_706,plain,
    ( ~ v2_funct_1(sK2)
    | sP0_iProver_split
    | k2_relat_1(sK3) != sK0 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_414])).

cnf(c_1160,plain,
    ( k2_relat_1(sK3) != sK0
    | v2_funct_1(sK2) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_706])).

cnf(c_2693,plain,
    ( sK0 != sK0
    | v2_funct_1(sK2) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_2364,c_1160])).

cnf(c_2694,plain,
    ( v2_funct_1(sK2) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2693])).

cnf(c_8,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_89,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_91,plain,
    ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_89])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3976,c_3035,c_2694,c_1352,c_1297,c_91,c_38,c_36,c_35,c_33])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:05:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.83/1.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.83/1.03  
% 3.83/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.83/1.03  
% 3.83/1.03  ------  iProver source info
% 3.83/1.03  
% 3.83/1.03  git: date: 2020-06-30 10:37:57 +0100
% 3.83/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.83/1.03  git: non_committed_changes: false
% 3.83/1.03  git: last_make_outside_of_git: false
% 3.83/1.03  
% 3.83/1.03  ------ 
% 3.83/1.03  
% 3.83/1.03  ------ Input Options
% 3.83/1.03  
% 3.83/1.03  --out_options                           all
% 3.83/1.03  --tptp_safe_out                         true
% 3.83/1.03  --problem_path                          ""
% 3.83/1.03  --include_path                          ""
% 3.83/1.03  --clausifier                            res/vclausify_rel
% 3.83/1.03  --clausifier_options                    ""
% 3.83/1.03  --stdin                                 false
% 3.83/1.03  --stats_out                             all
% 3.83/1.03  
% 3.83/1.03  ------ General Options
% 3.83/1.03  
% 3.83/1.03  --fof                                   false
% 3.83/1.03  --time_out_real                         305.
% 3.83/1.03  --time_out_virtual                      -1.
% 3.83/1.03  --symbol_type_check                     false
% 3.83/1.03  --clausify_out                          false
% 3.83/1.03  --sig_cnt_out                           false
% 3.83/1.03  --trig_cnt_out                          false
% 3.83/1.03  --trig_cnt_out_tolerance                1.
% 3.83/1.03  --trig_cnt_out_sk_spl                   false
% 3.83/1.03  --abstr_cl_out                          false
% 3.83/1.03  
% 3.83/1.03  ------ Global Options
% 3.83/1.03  
% 3.83/1.03  --schedule                              default
% 3.83/1.03  --add_important_lit                     false
% 3.83/1.03  --prop_solver_per_cl                    1000
% 3.83/1.03  --min_unsat_core                        false
% 3.83/1.03  --soft_assumptions                      false
% 3.83/1.03  --soft_lemma_size                       3
% 3.83/1.03  --prop_impl_unit_size                   0
% 3.83/1.03  --prop_impl_unit                        []
% 3.83/1.03  --share_sel_clauses                     true
% 3.83/1.03  --reset_solvers                         false
% 3.83/1.03  --bc_imp_inh                            [conj_cone]
% 3.83/1.03  --conj_cone_tolerance                   3.
% 3.83/1.03  --extra_neg_conj                        none
% 3.83/1.03  --large_theory_mode                     true
% 3.83/1.03  --prolific_symb_bound                   200
% 3.83/1.03  --lt_threshold                          2000
% 3.83/1.03  --clause_weak_htbl                      true
% 3.83/1.03  --gc_record_bc_elim                     false
% 3.83/1.03  
% 3.83/1.03  ------ Preprocessing Options
% 3.83/1.03  
% 3.83/1.03  --preprocessing_flag                    true
% 3.83/1.03  --time_out_prep_mult                    0.1
% 3.83/1.03  --splitting_mode                        input
% 3.83/1.03  --splitting_grd                         true
% 3.83/1.03  --splitting_cvd                         false
% 3.83/1.03  --splitting_cvd_svl                     false
% 3.83/1.03  --splitting_nvd                         32
% 3.83/1.03  --sub_typing                            true
% 3.83/1.03  --prep_gs_sim                           true
% 3.83/1.03  --prep_unflatten                        true
% 3.83/1.03  --prep_res_sim                          true
% 3.83/1.03  --prep_upred                            true
% 3.83/1.03  --prep_sem_filter                       exhaustive
% 3.83/1.03  --prep_sem_filter_out                   false
% 3.83/1.03  --pred_elim                             true
% 3.83/1.03  --res_sim_input                         true
% 3.83/1.03  --eq_ax_congr_red                       true
% 3.83/1.03  --pure_diseq_elim                       true
% 3.83/1.03  --brand_transform                       false
% 3.83/1.03  --non_eq_to_eq                          false
% 3.83/1.03  --prep_def_merge                        true
% 3.83/1.03  --prep_def_merge_prop_impl              false
% 3.83/1.03  --prep_def_merge_mbd                    true
% 3.83/1.03  --prep_def_merge_tr_red                 false
% 3.83/1.03  --prep_def_merge_tr_cl                  false
% 3.83/1.03  --smt_preprocessing                     true
% 3.83/1.03  --smt_ac_axioms                         fast
% 3.83/1.03  --preprocessed_out                      false
% 3.83/1.03  --preprocessed_stats                    false
% 3.83/1.03  
% 3.83/1.03  ------ Abstraction refinement Options
% 3.83/1.03  
% 3.83/1.03  --abstr_ref                             []
% 3.83/1.03  --abstr_ref_prep                        false
% 3.83/1.03  --abstr_ref_until_sat                   false
% 3.83/1.03  --abstr_ref_sig_restrict                funpre
% 3.83/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 3.83/1.03  --abstr_ref_under                       []
% 3.83/1.03  
% 3.83/1.03  ------ SAT Options
% 3.83/1.03  
% 3.83/1.03  --sat_mode                              false
% 3.83/1.03  --sat_fm_restart_options                ""
% 3.83/1.03  --sat_gr_def                            false
% 3.83/1.03  --sat_epr_types                         true
% 3.83/1.03  --sat_non_cyclic_types                  false
% 3.83/1.03  --sat_finite_models                     false
% 3.83/1.03  --sat_fm_lemmas                         false
% 3.83/1.03  --sat_fm_prep                           false
% 3.83/1.03  --sat_fm_uc_incr                        true
% 3.83/1.03  --sat_out_model                         small
% 3.83/1.03  --sat_out_clauses                       false
% 3.83/1.03  
% 3.83/1.03  ------ QBF Options
% 3.83/1.03  
% 3.83/1.03  --qbf_mode                              false
% 3.83/1.03  --qbf_elim_univ                         false
% 3.83/1.03  --qbf_dom_inst                          none
% 3.83/1.03  --qbf_dom_pre_inst                      false
% 3.83/1.03  --qbf_sk_in                             false
% 3.83/1.03  --qbf_pred_elim                         true
% 3.83/1.03  --qbf_split                             512
% 3.83/1.03  
% 3.83/1.03  ------ BMC1 Options
% 3.83/1.03  
% 3.83/1.03  --bmc1_incremental                      false
% 3.83/1.03  --bmc1_axioms                           reachable_all
% 3.83/1.03  --bmc1_min_bound                        0
% 3.83/1.03  --bmc1_max_bound                        -1
% 3.83/1.03  --bmc1_max_bound_default                -1
% 3.83/1.03  --bmc1_symbol_reachability              true
% 3.83/1.03  --bmc1_property_lemmas                  false
% 3.83/1.03  --bmc1_k_induction                      false
% 3.83/1.03  --bmc1_non_equiv_states                 false
% 3.83/1.03  --bmc1_deadlock                         false
% 3.83/1.03  --bmc1_ucm                              false
% 3.83/1.03  --bmc1_add_unsat_core                   none
% 3.83/1.03  --bmc1_unsat_core_children              false
% 3.83/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 3.83/1.03  --bmc1_out_stat                         full
% 3.83/1.03  --bmc1_ground_init                      false
% 3.83/1.03  --bmc1_pre_inst_next_state              false
% 3.83/1.03  --bmc1_pre_inst_state                   false
% 3.83/1.03  --bmc1_pre_inst_reach_state             false
% 3.83/1.03  --bmc1_out_unsat_core                   false
% 3.83/1.03  --bmc1_aig_witness_out                  false
% 3.83/1.03  --bmc1_verbose                          false
% 3.83/1.03  --bmc1_dump_clauses_tptp                false
% 3.83/1.03  --bmc1_dump_unsat_core_tptp             false
% 3.83/1.03  --bmc1_dump_file                        -
% 3.83/1.03  --bmc1_ucm_expand_uc_limit              128
% 3.83/1.03  --bmc1_ucm_n_expand_iterations          6
% 3.83/1.03  --bmc1_ucm_extend_mode                  1
% 3.83/1.03  --bmc1_ucm_init_mode                    2
% 3.83/1.03  --bmc1_ucm_cone_mode                    none
% 3.83/1.03  --bmc1_ucm_reduced_relation_type        0
% 3.83/1.03  --bmc1_ucm_relax_model                  4
% 3.83/1.03  --bmc1_ucm_full_tr_after_sat            true
% 3.83/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 3.83/1.03  --bmc1_ucm_layered_model                none
% 3.83/1.03  --bmc1_ucm_max_lemma_size               10
% 3.83/1.03  
% 3.83/1.03  ------ AIG Options
% 3.83/1.03  
% 3.83/1.03  --aig_mode                              false
% 3.83/1.03  
% 3.83/1.03  ------ Instantiation Options
% 3.83/1.03  
% 3.83/1.03  --instantiation_flag                    true
% 3.83/1.03  --inst_sos_flag                         true
% 3.83/1.03  --inst_sos_phase                        true
% 3.83/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.83/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.83/1.03  --inst_lit_sel_side                     num_symb
% 3.83/1.03  --inst_solver_per_active                1400
% 3.83/1.03  --inst_solver_calls_frac                1.
% 3.83/1.03  --inst_passive_queue_type               priority_queues
% 3.83/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.83/1.03  --inst_passive_queues_freq              [25;2]
% 3.83/1.03  --inst_dismatching                      true
% 3.83/1.03  --inst_eager_unprocessed_to_passive     true
% 3.83/1.03  --inst_prop_sim_given                   true
% 3.83/1.03  --inst_prop_sim_new                     false
% 3.83/1.03  --inst_subs_new                         false
% 3.83/1.03  --inst_eq_res_simp                      false
% 3.83/1.03  --inst_subs_given                       false
% 3.83/1.03  --inst_orphan_elimination               true
% 3.83/1.03  --inst_learning_loop_flag               true
% 3.83/1.03  --inst_learning_start                   3000
% 3.83/1.03  --inst_learning_factor                  2
% 3.83/1.03  --inst_start_prop_sim_after_learn       3
% 3.83/1.03  --inst_sel_renew                        solver
% 3.83/1.03  --inst_lit_activity_flag                true
% 3.83/1.03  --inst_restr_to_given                   false
% 3.83/1.03  --inst_activity_threshold               500
% 3.83/1.03  --inst_out_proof                        true
% 3.83/1.03  
% 3.83/1.03  ------ Resolution Options
% 3.83/1.03  
% 3.83/1.03  --resolution_flag                       true
% 3.83/1.03  --res_lit_sel                           adaptive
% 3.83/1.03  --res_lit_sel_side                      none
% 3.83/1.03  --res_ordering                          kbo
% 3.83/1.03  --res_to_prop_solver                    active
% 3.83/1.03  --res_prop_simpl_new                    false
% 3.83/1.03  --res_prop_simpl_given                  true
% 3.83/1.03  --res_passive_queue_type                priority_queues
% 3.83/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.83/1.03  --res_passive_queues_freq               [15;5]
% 3.83/1.03  --res_forward_subs                      full
% 3.83/1.03  --res_backward_subs                     full
% 3.83/1.03  --res_forward_subs_resolution           true
% 3.83/1.03  --res_backward_subs_resolution          true
% 3.83/1.03  --res_orphan_elimination                true
% 3.83/1.03  --res_time_limit                        2.
% 3.83/1.03  --res_out_proof                         true
% 3.83/1.03  
% 3.83/1.03  ------ Superposition Options
% 3.83/1.03  
% 3.83/1.03  --superposition_flag                    true
% 3.83/1.03  --sup_passive_queue_type                priority_queues
% 3.83/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.83/1.03  --sup_passive_queues_freq               [8;1;4]
% 3.83/1.03  --demod_completeness_check              fast
% 3.83/1.03  --demod_use_ground                      true
% 3.83/1.03  --sup_to_prop_solver                    passive
% 3.83/1.03  --sup_prop_simpl_new                    true
% 3.83/1.03  --sup_prop_simpl_given                  true
% 3.83/1.03  --sup_fun_splitting                     true
% 3.83/1.03  --sup_smt_interval                      50000
% 3.83/1.03  
% 3.83/1.03  ------ Superposition Simplification Setup
% 3.83/1.03  
% 3.83/1.03  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.83/1.03  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.83/1.03  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.83/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.83/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 3.83/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.83/1.03  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.83/1.03  --sup_immed_triv                        [TrivRules]
% 3.83/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.83/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.83/1.03  --sup_immed_bw_main                     []
% 3.83/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.83/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 3.83/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.83/1.03  --sup_input_bw                          []
% 3.83/1.03  
% 3.83/1.03  ------ Combination Options
% 3.83/1.03  
% 3.83/1.03  --comb_res_mult                         3
% 3.83/1.03  --comb_sup_mult                         2
% 3.83/1.03  --comb_inst_mult                        10
% 3.83/1.03  
% 3.83/1.03  ------ Debug Options
% 3.83/1.03  
% 3.83/1.03  --dbg_backtrace                         false
% 3.83/1.03  --dbg_dump_prop_clauses                 false
% 3.83/1.03  --dbg_dump_prop_clauses_file            -
% 3.83/1.03  --dbg_out_stat                          false
% 3.83/1.03  ------ Parsing...
% 3.83/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.83/1.03  
% 3.83/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.83/1.03  
% 3.83/1.03  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.83/1.03  
% 3.83/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.83/1.03  ------ Proving...
% 3.83/1.03  ------ Problem Properties 
% 3.83/1.03  
% 3.83/1.03  
% 3.83/1.03  clauses                                 27
% 3.83/1.03  conjectures                             6
% 3.83/1.03  EPR                                     6
% 3.83/1.03  Horn                                    27
% 3.83/1.03  unary                                   12
% 3.83/1.03  binary                                  5
% 3.83/1.03  lits                                    75
% 3.83/1.03  lits eq                                 12
% 3.83/1.03  fd_pure                                 0
% 3.83/1.03  fd_pseudo                               0
% 3.83/1.03  fd_cond                                 0
% 3.83/1.03  fd_pseudo_cond                          1
% 3.83/1.03  AC symbols                              0
% 3.83/1.03  
% 3.83/1.03  ------ Schedule dynamic 5 is on 
% 3.83/1.03  
% 3.83/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.83/1.03  
% 3.83/1.03  
% 3.83/1.03  ------ 
% 3.83/1.03  Current options:
% 3.83/1.03  ------ 
% 3.83/1.03  
% 3.83/1.03  ------ Input Options
% 3.83/1.03  
% 3.83/1.03  --out_options                           all
% 3.83/1.03  --tptp_safe_out                         true
% 3.83/1.03  --problem_path                          ""
% 3.83/1.03  --include_path                          ""
% 3.83/1.03  --clausifier                            res/vclausify_rel
% 3.83/1.03  --clausifier_options                    ""
% 3.83/1.03  --stdin                                 false
% 3.83/1.03  --stats_out                             all
% 3.83/1.03  
% 3.83/1.03  ------ General Options
% 3.83/1.03  
% 3.83/1.03  --fof                                   false
% 3.83/1.03  --time_out_real                         305.
% 3.83/1.03  --time_out_virtual                      -1.
% 3.83/1.03  --symbol_type_check                     false
% 3.83/1.03  --clausify_out                          false
% 3.83/1.03  --sig_cnt_out                           false
% 3.83/1.03  --trig_cnt_out                          false
% 3.83/1.03  --trig_cnt_out_tolerance                1.
% 3.83/1.03  --trig_cnt_out_sk_spl                   false
% 3.83/1.03  --abstr_cl_out                          false
% 3.83/1.03  
% 3.83/1.03  ------ Global Options
% 3.83/1.03  
% 3.83/1.03  --schedule                              default
% 3.83/1.03  --add_important_lit                     false
% 3.83/1.03  --prop_solver_per_cl                    1000
% 3.83/1.03  --min_unsat_core                        false
% 3.83/1.03  --soft_assumptions                      false
% 3.83/1.03  --soft_lemma_size                       3
% 3.83/1.03  --prop_impl_unit_size                   0
% 3.83/1.03  --prop_impl_unit                        []
% 3.83/1.03  --share_sel_clauses                     true
% 3.83/1.03  --reset_solvers                         false
% 3.83/1.03  --bc_imp_inh                            [conj_cone]
% 3.83/1.03  --conj_cone_tolerance                   3.
% 3.83/1.03  --extra_neg_conj                        none
% 3.83/1.03  --large_theory_mode                     true
% 3.83/1.03  --prolific_symb_bound                   200
% 3.83/1.03  --lt_threshold                          2000
% 3.83/1.03  --clause_weak_htbl                      true
% 3.83/1.03  --gc_record_bc_elim                     false
% 3.83/1.03  
% 3.83/1.03  ------ Preprocessing Options
% 3.83/1.03  
% 3.83/1.03  --preprocessing_flag                    true
% 3.83/1.03  --time_out_prep_mult                    0.1
% 3.83/1.03  --splitting_mode                        input
% 3.83/1.03  --splitting_grd                         true
% 3.83/1.03  --splitting_cvd                         false
% 3.83/1.03  --splitting_cvd_svl                     false
% 3.83/1.03  --splitting_nvd                         32
% 3.83/1.03  --sub_typing                            true
% 3.83/1.03  --prep_gs_sim                           true
% 3.83/1.03  --prep_unflatten                        true
% 3.83/1.03  --prep_res_sim                          true
% 3.83/1.03  --prep_upred                            true
% 3.83/1.03  --prep_sem_filter                       exhaustive
% 3.83/1.03  --prep_sem_filter_out                   false
% 3.83/1.03  --pred_elim                             true
% 3.83/1.03  --res_sim_input                         true
% 3.83/1.03  --eq_ax_congr_red                       true
% 3.83/1.03  --pure_diseq_elim                       true
% 3.83/1.03  --brand_transform                       false
% 3.83/1.03  --non_eq_to_eq                          false
% 3.83/1.03  --prep_def_merge                        true
% 3.83/1.03  --prep_def_merge_prop_impl              false
% 3.83/1.03  --prep_def_merge_mbd                    true
% 3.83/1.03  --prep_def_merge_tr_red                 false
% 3.83/1.03  --prep_def_merge_tr_cl                  false
% 3.83/1.03  --smt_preprocessing                     true
% 3.83/1.03  --smt_ac_axioms                         fast
% 3.83/1.03  --preprocessed_out                      false
% 3.83/1.03  --preprocessed_stats                    false
% 3.83/1.03  
% 3.83/1.03  ------ Abstraction refinement Options
% 3.83/1.03  
% 3.83/1.03  --abstr_ref                             []
% 3.83/1.03  --abstr_ref_prep                        false
% 3.83/1.03  --abstr_ref_until_sat                   false
% 3.83/1.03  --abstr_ref_sig_restrict                funpre
% 3.83/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 3.83/1.03  --abstr_ref_under                       []
% 3.83/1.03  
% 3.83/1.03  ------ SAT Options
% 3.83/1.03  
% 3.83/1.03  --sat_mode                              false
% 3.83/1.03  --sat_fm_restart_options                ""
% 3.83/1.03  --sat_gr_def                            false
% 3.83/1.03  --sat_epr_types                         true
% 3.83/1.03  --sat_non_cyclic_types                  false
% 3.83/1.03  --sat_finite_models                     false
% 3.83/1.03  --sat_fm_lemmas                         false
% 3.83/1.03  --sat_fm_prep                           false
% 3.83/1.03  --sat_fm_uc_incr                        true
% 3.83/1.03  --sat_out_model                         small
% 3.83/1.03  --sat_out_clauses                       false
% 3.83/1.03  
% 3.83/1.03  ------ QBF Options
% 3.83/1.03  
% 3.83/1.03  --qbf_mode                              false
% 3.83/1.03  --qbf_elim_univ                         false
% 3.83/1.03  --qbf_dom_inst                          none
% 3.83/1.03  --qbf_dom_pre_inst                      false
% 3.83/1.03  --qbf_sk_in                             false
% 3.83/1.03  --qbf_pred_elim                         true
% 3.83/1.03  --qbf_split                             512
% 3.83/1.03  
% 3.83/1.03  ------ BMC1 Options
% 3.83/1.03  
% 3.83/1.03  --bmc1_incremental                      false
% 3.83/1.03  --bmc1_axioms                           reachable_all
% 3.83/1.03  --bmc1_min_bound                        0
% 3.83/1.03  --bmc1_max_bound                        -1
% 3.83/1.03  --bmc1_max_bound_default                -1
% 3.83/1.03  --bmc1_symbol_reachability              true
% 3.83/1.03  --bmc1_property_lemmas                  false
% 3.83/1.03  --bmc1_k_induction                      false
% 3.83/1.03  --bmc1_non_equiv_states                 false
% 3.83/1.03  --bmc1_deadlock                         false
% 3.83/1.03  --bmc1_ucm                              false
% 3.83/1.03  --bmc1_add_unsat_core                   none
% 3.83/1.03  --bmc1_unsat_core_children              false
% 3.83/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 3.83/1.03  --bmc1_out_stat                         full
% 3.83/1.03  --bmc1_ground_init                      false
% 3.83/1.03  --bmc1_pre_inst_next_state              false
% 3.83/1.03  --bmc1_pre_inst_state                   false
% 3.83/1.03  --bmc1_pre_inst_reach_state             false
% 3.83/1.03  --bmc1_out_unsat_core                   false
% 3.83/1.03  --bmc1_aig_witness_out                  false
% 3.83/1.03  --bmc1_verbose                          false
% 3.83/1.03  --bmc1_dump_clauses_tptp                false
% 3.83/1.03  --bmc1_dump_unsat_core_tptp             false
% 3.83/1.03  --bmc1_dump_file                        -
% 3.83/1.03  --bmc1_ucm_expand_uc_limit              128
% 3.83/1.03  --bmc1_ucm_n_expand_iterations          6
% 3.83/1.03  --bmc1_ucm_extend_mode                  1
% 3.83/1.03  --bmc1_ucm_init_mode                    2
% 3.83/1.03  --bmc1_ucm_cone_mode                    none
% 3.83/1.03  --bmc1_ucm_reduced_relation_type        0
% 3.83/1.03  --bmc1_ucm_relax_model                  4
% 3.83/1.03  --bmc1_ucm_full_tr_after_sat            true
% 3.83/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 3.83/1.03  --bmc1_ucm_layered_model                none
% 3.83/1.03  --bmc1_ucm_max_lemma_size               10
% 3.83/1.03  
% 3.83/1.03  ------ AIG Options
% 3.83/1.03  
% 3.83/1.03  --aig_mode                              false
% 3.83/1.03  
% 3.83/1.03  ------ Instantiation Options
% 3.83/1.03  
% 3.83/1.03  --instantiation_flag                    true
% 3.83/1.03  --inst_sos_flag                         true
% 3.83/1.03  --inst_sos_phase                        true
% 3.83/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.83/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.83/1.03  --inst_lit_sel_side                     none
% 3.83/1.03  --inst_solver_per_active                1400
% 3.83/1.03  --inst_solver_calls_frac                1.
% 3.83/1.03  --inst_passive_queue_type               priority_queues
% 3.83/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.83/1.03  --inst_passive_queues_freq              [25;2]
% 3.83/1.03  --inst_dismatching                      true
% 3.83/1.03  --inst_eager_unprocessed_to_passive     true
% 3.83/1.03  --inst_prop_sim_given                   true
% 3.83/1.03  --inst_prop_sim_new                     false
% 3.83/1.03  --inst_subs_new                         false
% 3.83/1.03  --inst_eq_res_simp                      false
% 3.83/1.03  --inst_subs_given                       false
% 3.83/1.03  --inst_orphan_elimination               true
% 3.83/1.03  --inst_learning_loop_flag               true
% 3.83/1.03  --inst_learning_start                   3000
% 3.83/1.03  --inst_learning_factor                  2
% 3.83/1.03  --inst_start_prop_sim_after_learn       3
% 3.83/1.03  --inst_sel_renew                        solver
% 3.83/1.03  --inst_lit_activity_flag                true
% 3.83/1.03  --inst_restr_to_given                   false
% 3.83/1.03  --inst_activity_threshold               500
% 3.83/1.03  --inst_out_proof                        true
% 3.83/1.03  
% 3.83/1.03  ------ Resolution Options
% 3.83/1.03  
% 3.83/1.03  --resolution_flag                       false
% 3.83/1.03  --res_lit_sel                           adaptive
% 3.83/1.03  --res_lit_sel_side                      none
% 3.83/1.03  --res_ordering                          kbo
% 3.83/1.03  --res_to_prop_solver                    active
% 3.83/1.03  --res_prop_simpl_new                    false
% 3.83/1.03  --res_prop_simpl_given                  true
% 3.83/1.03  --res_passive_queue_type                priority_queues
% 3.83/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.83/1.03  --res_passive_queues_freq               [15;5]
% 3.83/1.03  --res_forward_subs                      full
% 3.83/1.03  --res_backward_subs                     full
% 3.83/1.03  --res_forward_subs_resolution           true
% 3.83/1.03  --res_backward_subs_resolution          true
% 3.83/1.03  --res_orphan_elimination                true
% 3.83/1.03  --res_time_limit                        2.
% 3.83/1.03  --res_out_proof                         true
% 3.83/1.03  
% 3.83/1.03  ------ Superposition Options
% 3.83/1.03  
% 3.83/1.03  --superposition_flag                    true
% 3.83/1.03  --sup_passive_queue_type                priority_queues
% 3.83/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.83/1.03  --sup_passive_queues_freq               [8;1;4]
% 3.83/1.03  --demod_completeness_check              fast
% 3.83/1.03  --demod_use_ground                      true
% 3.83/1.03  --sup_to_prop_solver                    passive
% 3.83/1.03  --sup_prop_simpl_new                    true
% 3.83/1.03  --sup_prop_simpl_given                  true
% 3.83/1.03  --sup_fun_splitting                     true
% 3.83/1.03  --sup_smt_interval                      50000
% 3.83/1.03  
% 3.83/1.03  ------ Superposition Simplification Setup
% 3.83/1.03  
% 3.83/1.03  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.83/1.03  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.83/1.03  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.83/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.83/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 3.83/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.83/1.03  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.83/1.03  --sup_immed_triv                        [TrivRules]
% 3.83/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.83/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.83/1.03  --sup_immed_bw_main                     []
% 3.83/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.83/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 3.83/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.83/1.03  --sup_input_bw                          []
% 3.83/1.03  
% 3.83/1.03  ------ Combination Options
% 3.83/1.03  
% 3.83/1.03  --comb_res_mult                         3
% 3.83/1.03  --comb_sup_mult                         2
% 3.83/1.03  --comb_inst_mult                        10
% 3.83/1.03  
% 3.83/1.03  ------ Debug Options
% 3.83/1.03  
% 3.83/1.03  --dbg_backtrace                         false
% 3.83/1.03  --dbg_dump_prop_clauses                 false
% 3.83/1.03  --dbg_dump_prop_clauses_file            -
% 3.83/1.03  --dbg_out_stat                          false
% 3.83/1.03  
% 3.83/1.03  
% 3.83/1.03  
% 3.83/1.03  
% 3.83/1.03  ------ Proving...
% 3.83/1.03  
% 3.83/1.03  
% 3.83/1.03  % SZS status Theorem for theBenchmark.p
% 3.83/1.03  
% 3.83/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 3.83/1.03  
% 3.83/1.03  fof(f18,conjecture,(
% 3.83/1.03    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 3.83/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/1.03  
% 3.83/1.03  fof(f19,negated_conjecture,(
% 3.83/1.03    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 3.83/1.03    inference(negated_conjecture,[],[f18])).
% 3.83/1.03  
% 3.83/1.03  fof(f39,plain,(
% 3.83/1.03    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.83/1.03    inference(ennf_transformation,[],[f19])).
% 3.83/1.03  
% 3.83/1.03  fof(f40,plain,(
% 3.83/1.03    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.83/1.03    inference(flattening,[],[f39])).
% 3.83/1.03  
% 3.83/1.03  fof(f47,plain,(
% 3.83/1.03    ( ! [X2,X0,X1] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((~v2_funct_2(sK3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 3.83/1.03    introduced(choice_axiom,[])).
% 3.83/1.03  
% 3.83/1.03  fof(f46,plain,(
% 3.83/1.03    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 3.83/1.03    introduced(choice_axiom,[])).
% 3.83/1.03  
% 3.83/1.03  fof(f48,plain,(
% 3.83/1.03    ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 3.83/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f40,f47,f46])).
% 3.83/1.03  
% 3.83/1.03  fof(f77,plain,(
% 3.83/1.03    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.83/1.03    inference(cnf_transformation,[],[f48])).
% 3.83/1.03  
% 3.83/1.03  fof(f80,plain,(
% 3.83/1.03    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 3.83/1.03    inference(cnf_transformation,[],[f48])).
% 3.83/1.03  
% 3.83/1.03  fof(f15,axiom,(
% 3.83/1.03    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.83/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/1.03  
% 3.83/1.03  fof(f35,plain,(
% 3.83/1.03    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.83/1.03    inference(ennf_transformation,[],[f15])).
% 3.83/1.03  
% 3.83/1.03  fof(f36,plain,(
% 3.83/1.03    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.83/1.03    inference(flattening,[],[f35])).
% 3.83/1.03  
% 3.83/1.03  fof(f72,plain,(
% 3.83/1.03    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.83/1.03    inference(cnf_transformation,[],[f36])).
% 3.83/1.03  
% 3.83/1.03  fof(f78,plain,(
% 3.83/1.03    v1_funct_1(sK3)),
% 3.83/1.03    inference(cnf_transformation,[],[f48])).
% 3.83/1.03  
% 3.83/1.03  fof(f11,axiom,(
% 3.83/1.03    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.83/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/1.03  
% 3.83/1.03  fof(f29,plain,(
% 3.83/1.03    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.83/1.03    inference(ennf_transformation,[],[f11])).
% 3.83/1.03  
% 3.83/1.03  fof(f30,plain,(
% 3.83/1.03    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.83/1.03    inference(flattening,[],[f29])).
% 3.83/1.03  
% 3.83/1.03  fof(f44,plain,(
% 3.83/1.03    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.83/1.03    inference(nnf_transformation,[],[f30])).
% 3.83/1.03  
% 3.83/1.03  fof(f65,plain,(
% 3.83/1.03    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.83/1.03    inference(cnf_transformation,[],[f44])).
% 3.83/1.03  
% 3.83/1.03  fof(f81,plain,(
% 3.83/1.03    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 3.83/1.03    inference(cnf_transformation,[],[f48])).
% 3.83/1.03  
% 3.83/1.03  fof(f12,axiom,(
% 3.83/1.03    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.83/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/1.03  
% 3.83/1.03  fof(f67,plain,(
% 3.83/1.03    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.83/1.03    inference(cnf_transformation,[],[f12])).
% 3.83/1.03  
% 3.83/1.03  fof(f16,axiom,(
% 3.83/1.03    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.83/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/1.03  
% 3.83/1.03  fof(f73,plain,(
% 3.83/1.03    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.83/1.03    inference(cnf_transformation,[],[f16])).
% 3.83/1.03  
% 3.83/1.03  fof(f87,plain,(
% 3.83/1.03    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.83/1.03    inference(definition_unfolding,[],[f67,f73])).
% 3.83/1.03  
% 3.83/1.03  fof(f75,plain,(
% 3.83/1.03    v1_funct_1(sK2)),
% 3.83/1.03    inference(cnf_transformation,[],[f48])).
% 3.83/1.03  
% 3.83/1.03  fof(f14,axiom,(
% 3.83/1.03    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 3.83/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/1.03  
% 3.83/1.03  fof(f33,plain,(
% 3.83/1.03    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.83/1.03    inference(ennf_transformation,[],[f14])).
% 3.83/1.03  
% 3.83/1.03  fof(f34,plain,(
% 3.83/1.03    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.83/1.03    inference(flattening,[],[f33])).
% 3.83/1.03  
% 3.83/1.03  fof(f71,plain,(
% 3.83/1.03    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.83/1.03    inference(cnf_transformation,[],[f34])).
% 3.83/1.03  
% 3.83/1.03  fof(f6,axiom,(
% 3.83/1.03    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X0)) => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)))))),
% 3.83/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/1.03  
% 3.83/1.03  fof(f22,plain,(
% 3.83/1.03    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.83/1.03    inference(ennf_transformation,[],[f6])).
% 3.83/1.03  
% 3.83/1.03  fof(f23,plain,(
% 3.83/1.03    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.83/1.03    inference(flattening,[],[f22])).
% 3.83/1.03  
% 3.83/1.03  fof(f59,plain,(
% 3.83/1.03    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.83/1.03    inference(cnf_transformation,[],[f23])).
% 3.83/1.03  
% 3.83/1.03  fof(f4,axiom,(
% 3.83/1.03    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.83/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/1.03  
% 3.83/1.03  fof(f55,plain,(
% 3.83/1.03    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 3.83/1.03    inference(cnf_transformation,[],[f4])).
% 3.83/1.03  
% 3.83/1.03  fof(f84,plain,(
% 3.83/1.03    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 3.83/1.03    inference(definition_unfolding,[],[f55,f73])).
% 3.83/1.03  
% 3.83/1.03  fof(f8,axiom,(
% 3.83/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.83/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/1.03  
% 3.83/1.03  fof(f26,plain,(
% 3.83/1.03    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.83/1.03    inference(ennf_transformation,[],[f8])).
% 3.83/1.03  
% 3.83/1.03  fof(f61,plain,(
% 3.83/1.03    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.83/1.03    inference(cnf_transformation,[],[f26])).
% 3.83/1.03  
% 3.83/1.03  fof(f9,axiom,(
% 3.83/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.83/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/1.03  
% 3.83/1.03  fof(f27,plain,(
% 3.83/1.03    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.83/1.03    inference(ennf_transformation,[],[f9])).
% 3.83/1.03  
% 3.83/1.03  fof(f62,plain,(
% 3.83/1.03    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.83/1.03    inference(cnf_transformation,[],[f27])).
% 3.83/1.03  
% 3.83/1.03  fof(f2,axiom,(
% 3.83/1.03    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.83/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/1.03  
% 3.83/1.03  fof(f20,plain,(
% 3.83/1.03    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.83/1.03    inference(ennf_transformation,[],[f2])).
% 3.83/1.03  
% 3.83/1.03  fof(f43,plain,(
% 3.83/1.03    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.83/1.03    inference(nnf_transformation,[],[f20])).
% 3.83/1.03  
% 3.83/1.03  fof(f52,plain,(
% 3.83/1.03    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.83/1.03    inference(cnf_transformation,[],[f43])).
% 3.83/1.03  
% 3.83/1.03  fof(f1,axiom,(
% 3.83/1.03    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.83/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/1.03  
% 3.83/1.03  fof(f41,plain,(
% 3.83/1.03    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.83/1.03    inference(nnf_transformation,[],[f1])).
% 3.83/1.03  
% 3.83/1.03  fof(f42,plain,(
% 3.83/1.03    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.83/1.03    inference(flattening,[],[f41])).
% 3.83/1.03  
% 3.83/1.03  fof(f51,plain,(
% 3.83/1.03    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.83/1.03    inference(cnf_transformation,[],[f42])).
% 3.83/1.03  
% 3.83/1.03  fof(f3,axiom,(
% 3.83/1.03    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 3.83/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/1.03  
% 3.83/1.03  fof(f21,plain,(
% 3.83/1.03    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.83/1.03    inference(ennf_transformation,[],[f3])).
% 3.83/1.03  
% 3.83/1.03  fof(f54,plain,(
% 3.83/1.03    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.83/1.03    inference(cnf_transformation,[],[f21])).
% 3.83/1.03  
% 3.83/1.03  fof(f7,axiom,(
% 3.83/1.03    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) & v2_funct_1(k5_relat_1(X1,X0))) => v2_funct_1(X1))))),
% 3.83/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/1.03  
% 3.83/1.03  fof(f24,plain,(
% 3.83/1.03    ! [X0] : (! [X1] : ((v2_funct_1(X1) | (~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.83/1.03    inference(ennf_transformation,[],[f7])).
% 3.83/1.03  
% 3.83/1.03  fof(f25,plain,(
% 3.83/1.03    ! [X0] : (! [X1] : (v2_funct_1(X1) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.83/1.03    inference(flattening,[],[f24])).
% 3.83/1.03  
% 3.83/1.03  fof(f60,plain,(
% 3.83/1.03    ( ! [X0,X1] : (v2_funct_1(X1) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.83/1.03    inference(cnf_transformation,[],[f25])).
% 3.83/1.03  
% 3.83/1.03  fof(f10,axiom,(
% 3.83/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.83/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/1.03  
% 3.83/1.03  fof(f28,plain,(
% 3.83/1.03    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.83/1.03    inference(ennf_transformation,[],[f10])).
% 3.83/1.03  
% 3.83/1.03  fof(f64,plain,(
% 3.83/1.03    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.83/1.03    inference(cnf_transformation,[],[f28])).
% 3.83/1.03  
% 3.83/1.03  fof(f17,axiom,(
% 3.83/1.03    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 3.83/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/1.03  
% 3.83/1.03  fof(f37,plain,(
% 3.83/1.03    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.83/1.03    inference(ennf_transformation,[],[f17])).
% 3.83/1.03  
% 3.83/1.03  fof(f38,plain,(
% 3.83/1.03    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.83/1.03    inference(flattening,[],[f37])).
% 3.83/1.03  
% 3.83/1.03  fof(f74,plain,(
% 3.83/1.03    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.83/1.03    inference(cnf_transformation,[],[f38])).
% 3.83/1.03  
% 3.83/1.03  fof(f76,plain,(
% 3.83/1.03    v1_funct_2(sK2,sK0,sK1)),
% 3.83/1.03    inference(cnf_transformation,[],[f48])).
% 3.83/1.03  
% 3.83/1.03  fof(f79,plain,(
% 3.83/1.03    v1_funct_2(sK3,sK1,sK0)),
% 3.83/1.03    inference(cnf_transformation,[],[f48])).
% 3.83/1.03  
% 3.83/1.03  fof(f63,plain,(
% 3.83/1.03    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.83/1.03    inference(cnf_transformation,[],[f27])).
% 3.83/1.03  
% 3.83/1.03  fof(f13,axiom,(
% 3.83/1.03    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 3.83/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/1.03  
% 3.83/1.03  fof(f31,plain,(
% 3.83/1.03    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.83/1.03    inference(ennf_transformation,[],[f13])).
% 3.83/1.03  
% 3.83/1.03  fof(f32,plain,(
% 3.83/1.03    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.83/1.03    inference(flattening,[],[f31])).
% 3.83/1.03  
% 3.83/1.03  fof(f45,plain,(
% 3.83/1.03    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.83/1.03    inference(nnf_transformation,[],[f32])).
% 3.83/1.03  
% 3.83/1.03  fof(f69,plain,(
% 3.83/1.03    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.83/1.03    inference(cnf_transformation,[],[f45])).
% 3.83/1.03  
% 3.83/1.03  fof(f91,plain,(
% 3.83/1.03    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.83/1.03    inference(equality_resolution,[],[f69])).
% 3.83/1.03  
% 3.83/1.03  fof(f82,plain,(
% 3.83/1.03    ~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)),
% 3.83/1.03    inference(cnf_transformation,[],[f48])).
% 3.83/1.03  
% 3.83/1.03  fof(f5,axiom,(
% 3.83/1.03    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 3.83/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.83/1.03  
% 3.83/1.03  fof(f58,plain,(
% 3.83/1.03    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 3.83/1.03    inference(cnf_transformation,[],[f5])).
% 3.83/1.03  
% 3.83/1.03  fof(f85,plain,(
% 3.83/1.03    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 3.83/1.03    inference(definition_unfolding,[],[f58,f73])).
% 3.83/1.03  
% 3.83/1.03  cnf(c_30,negated_conjecture,
% 3.83/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.83/1.03      inference(cnf_transformation,[],[f77]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_1165,plain,
% 3.83/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.83/1.03      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_27,negated_conjecture,
% 3.83/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 3.83/1.03      inference(cnf_transformation,[],[f80]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_1168,plain,
% 3.83/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.83/1.03      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_23,plain,
% 3.83/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.83/1.03      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.83/1.03      | ~ v1_funct_1(X0)
% 3.83/1.03      | ~ v1_funct_1(X3)
% 3.83/1.03      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.83/1.03      inference(cnf_transformation,[],[f72]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_1169,plain,
% 3.83/1.03      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 3.83/1.03      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 3.83/1.03      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.83/1.03      | v1_funct_1(X4) != iProver_top
% 3.83/1.03      | v1_funct_1(X5) != iProver_top ),
% 3.83/1.03      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_3348,plain,
% 3.83/1.03      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 3.83/1.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.83/1.03      | v1_funct_1(X2) != iProver_top
% 3.83/1.03      | v1_funct_1(sK3) != iProver_top ),
% 3.83/1.03      inference(superposition,[status(thm)],[c_1168,c_1169]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_29,negated_conjecture,
% 3.83/1.03      ( v1_funct_1(sK3) ),
% 3.83/1.03      inference(cnf_transformation,[],[f78]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_36,plain,
% 3.83/1.03      ( v1_funct_1(sK3) = iProver_top ),
% 3.83/1.03      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_3604,plain,
% 3.83/1.03      ( v1_funct_1(X2) != iProver_top
% 3.83/1.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.83/1.03      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 3.83/1.03      inference(global_propositional_subsumption,
% 3.83/1.03                [status(thm)],
% 3.83/1.03                [c_3348,c_36]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_3605,plain,
% 3.83/1.03      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 3.83/1.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.83/1.03      | v1_funct_1(X2) != iProver_top ),
% 3.83/1.03      inference(renaming,[status(thm)],[c_3604]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_3612,plain,
% 3.83/1.03      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 3.83/1.03      | v1_funct_1(sK2) != iProver_top ),
% 3.83/1.03      inference(superposition,[status(thm)],[c_1165,c_3605]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_17,plain,
% 3.83/1.03      ( ~ r2_relset_1(X0,X1,X2,X3)
% 3.83/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.83/1.03      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.83/1.03      | X3 = X2 ),
% 3.83/1.03      inference(cnf_transformation,[],[f65]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_26,negated_conjecture,
% 3.83/1.03      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 3.83/1.03      inference(cnf_transformation,[],[f81]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_469,plain,
% 3.83/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.83/1.03      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.83/1.03      | X3 = X0
% 3.83/1.03      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 3.83/1.03      | k6_partfun1(sK0) != X3
% 3.83/1.03      | sK0 != X2
% 3.83/1.03      | sK0 != X1 ),
% 3.83/1.03      inference(resolution_lifted,[status(thm)],[c_17,c_26]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_470,plain,
% 3.83/1.03      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.83/1.03      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.83/1.03      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.83/1.03      inference(unflattening,[status(thm)],[c_469]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_18,plain,
% 3.83/1.03      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.83/1.03      inference(cnf_transformation,[],[f87]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_60,plain,
% 3.83/1.03      ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.83/1.03      inference(instantiation,[status(thm)],[c_18]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_472,plain,
% 3.83/1.03      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.83/1.03      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.83/1.03      inference(global_propositional_subsumption,
% 3.83/1.03                [status(thm)],
% 3.83/1.03                [c_470,c_60]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_1158,plain,
% 3.83/1.03      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.83/1.03      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.83/1.03      inference(predicate_to_equality,[status(thm)],[c_472]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_32,negated_conjecture,
% 3.83/1.03      ( v1_funct_1(sK2) ),
% 3.83/1.03      inference(cnf_transformation,[],[f75]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_21,plain,
% 3.83/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.83/1.03      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.83/1.03      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.83/1.03      | ~ v1_funct_1(X0)
% 3.83/1.03      | ~ v1_funct_1(X3) ),
% 3.83/1.03      inference(cnf_transformation,[],[f71]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_1217,plain,
% 3.83/1.03      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.83/1.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.83/1.03      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.83/1.03      | ~ v1_funct_1(sK2)
% 3.83/1.03      | ~ v1_funct_1(sK3) ),
% 3.83/1.03      inference(instantiation,[status(thm)],[c_21]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_1808,plain,
% 3.83/1.03      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.83/1.03      inference(global_propositional_subsumption,
% 3.83/1.03                [status(thm)],
% 3.83/1.03                [c_1158,c_32,c_30,c_29,c_27,c_60,c_470,c_1217]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_3613,plain,
% 3.83/1.03      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 3.83/1.03      | v1_funct_1(sK2) != iProver_top ),
% 3.83/1.03      inference(light_normalisation,[status(thm)],[c_3612,c_1808]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_33,plain,
% 3.83/1.03      ( v1_funct_1(sK2) = iProver_top ),
% 3.83/1.03      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_3853,plain,
% 3.83/1.03      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 3.83/1.03      inference(global_propositional_subsumption,
% 3.83/1.03                [status(thm)],
% 3.83/1.03                [c_3613,c_33]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_10,plain,
% 3.83/1.03      ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
% 3.83/1.03      | ~ v1_funct_1(X0)
% 3.83/1.03      | ~ v1_funct_1(X1)
% 3.83/1.03      | ~ v1_relat_1(X0)
% 3.83/1.03      | ~ v1_relat_1(X1)
% 3.83/1.03      | k1_relat_1(k5_relat_1(X0,X1)) != k1_relat_1(X0) ),
% 3.83/1.03      inference(cnf_transformation,[],[f59]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_1176,plain,
% 3.83/1.03      ( k1_relat_1(k5_relat_1(X0,X1)) != k1_relat_1(X0)
% 3.83/1.03      | r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) = iProver_top
% 3.83/1.03      | v1_funct_1(X0) != iProver_top
% 3.83/1.03      | v1_funct_1(X1) != iProver_top
% 3.83/1.03      | v1_relat_1(X0) != iProver_top
% 3.83/1.03      | v1_relat_1(X1) != iProver_top ),
% 3.83/1.03      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_3855,plain,
% 3.83/1.03      ( k1_relat_1(k6_partfun1(sK0)) != k1_relat_1(sK2)
% 3.83/1.03      | r1_tarski(k2_relat_1(sK2),k1_relat_1(sK3)) = iProver_top
% 3.83/1.03      | v1_funct_1(sK2) != iProver_top
% 3.83/1.03      | v1_funct_1(sK3) != iProver_top
% 3.83/1.03      | v1_relat_1(sK2) != iProver_top
% 3.83/1.03      | v1_relat_1(sK3) != iProver_top ),
% 3.83/1.03      inference(superposition,[status(thm)],[c_3853,c_1176]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_7,plain,
% 3.83/1.03      ( k1_relat_1(k6_partfun1(X0)) = X0 ),
% 3.83/1.03      inference(cnf_transformation,[],[f84]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_3858,plain,
% 3.83/1.03      ( k1_relat_1(sK2) != sK0
% 3.83/1.03      | r1_tarski(k2_relat_1(sK2),k1_relat_1(sK3)) = iProver_top
% 3.83/1.03      | v1_funct_1(sK2) != iProver_top
% 3.83/1.03      | v1_funct_1(sK3) != iProver_top
% 3.83/1.03      | v1_relat_1(sK2) != iProver_top
% 3.83/1.03      | v1_relat_1(sK3) != iProver_top ),
% 3.83/1.03      inference(demodulation,[status(thm)],[c_3855,c_7]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_35,plain,
% 3.83/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.83/1.03      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_38,plain,
% 3.83/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.83/1.03      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_12,plain,
% 3.83/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.83/1.03      | v1_relat_1(X0) ),
% 3.83/1.03      inference(cnf_transformation,[],[f61]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_1268,plain,
% 3.83/1.03      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.83/1.03      | v1_relat_1(sK2) ),
% 3.83/1.03      inference(instantiation,[status(thm)],[c_12]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_1296,plain,
% 3.83/1.03      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.83/1.03      | v1_relat_1(sK2) ),
% 3.83/1.03      inference(instantiation,[status(thm)],[c_1268]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_1297,plain,
% 3.83/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.83/1.03      | v1_relat_1(sK2) = iProver_top ),
% 3.83/1.03      inference(predicate_to_equality,[status(thm)],[c_1296]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_1351,plain,
% 3.83/1.03      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.83/1.03      | v1_relat_1(sK3) ),
% 3.83/1.03      inference(instantiation,[status(thm)],[c_12]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_1352,plain,
% 3.83/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.83/1.03      | v1_relat_1(sK3) = iProver_top ),
% 3.83/1.03      inference(predicate_to_equality,[status(thm)],[c_1351]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_14,plain,
% 3.83/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.83/1.03      | v4_relat_1(X0,X1) ),
% 3.83/1.03      inference(cnf_transformation,[],[f62]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_4,plain,
% 3.83/1.03      ( ~ v4_relat_1(X0,X1)
% 3.83/1.03      | r1_tarski(k1_relat_1(X0),X1)
% 3.83/1.03      | ~ v1_relat_1(X0) ),
% 3.83/1.03      inference(cnf_transformation,[],[f52]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_347,plain,
% 3.83/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.83/1.03      | r1_tarski(k1_relat_1(X0),X1)
% 3.83/1.03      | ~ v1_relat_1(X0) ),
% 3.83/1.03      inference(resolution,[status(thm)],[c_14,c_4]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_351,plain,
% 3.83/1.03      ( r1_tarski(k1_relat_1(X0),X1)
% 3.83/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.83/1.03      inference(global_propositional_subsumption,
% 3.83/1.03                [status(thm)],
% 3.83/1.03                [c_347,c_12]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_352,plain,
% 3.83/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.83/1.03      | r1_tarski(k1_relat_1(X0),X1) ),
% 3.83/1.03      inference(renaming,[status(thm)],[c_351]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_1162,plain,
% 3.83/1.03      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.83/1.03      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 3.83/1.03      inference(predicate_to_equality,[status(thm)],[c_352]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_2154,plain,
% 3.83/1.03      ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
% 3.83/1.03      inference(superposition,[status(thm)],[c_1165,c_1162]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_0,plain,
% 3.83/1.03      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.83/1.03      inference(cnf_transformation,[],[f51]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_1181,plain,
% 3.83/1.03      ( X0 = X1
% 3.83/1.03      | r1_tarski(X0,X1) != iProver_top
% 3.83/1.03      | r1_tarski(X1,X0) != iProver_top ),
% 3.83/1.03      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_2647,plain,
% 3.83/1.03      ( k1_relat_1(sK2) = sK0
% 3.83/1.03      | r1_tarski(sK0,k1_relat_1(sK2)) != iProver_top ),
% 3.83/1.03      inference(superposition,[status(thm)],[c_2154,c_1181]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_5,plain,
% 3.83/1.03      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
% 3.83/1.03      | ~ v1_relat_1(X1)
% 3.83/1.03      | ~ v1_relat_1(X0) ),
% 3.83/1.03      inference(cnf_transformation,[],[f54]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_1179,plain,
% 3.83/1.03      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) = iProver_top
% 3.83/1.03      | v1_relat_1(X0) != iProver_top
% 3.83/1.03      | v1_relat_1(X1) != iProver_top ),
% 3.83/1.03      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_3856,plain,
% 3.83/1.03      ( r1_tarski(k1_relat_1(k6_partfun1(sK0)),k1_relat_1(sK2)) = iProver_top
% 3.83/1.03      | v1_relat_1(sK2) != iProver_top
% 3.83/1.03      | v1_relat_1(sK3) != iProver_top ),
% 3.83/1.03      inference(superposition,[status(thm)],[c_3853,c_1179]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_3857,plain,
% 3.83/1.03      ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top
% 3.83/1.03      | v1_relat_1(sK2) != iProver_top
% 3.83/1.03      | v1_relat_1(sK3) != iProver_top ),
% 3.83/1.03      inference(demodulation,[status(thm)],[c_3856,c_7]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_3970,plain,
% 3.83/1.03      ( r1_tarski(k2_relat_1(sK2),k1_relat_1(sK3)) = iProver_top ),
% 3.83/1.03      inference(global_propositional_subsumption,
% 3.83/1.03                [status(thm)],
% 3.83/1.03                [c_3858,c_33,c_35,c_36,c_38,c_1297,c_1352,c_2647,c_3857]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_11,plain,
% 3.83/1.03      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
% 3.83/1.03      | ~ v1_funct_1(X0)
% 3.83/1.03      | ~ v1_funct_1(X1)
% 3.83/1.03      | v2_funct_1(X0)
% 3.83/1.03      | ~ v2_funct_1(k5_relat_1(X0,X1))
% 3.83/1.03      | ~ v1_relat_1(X0)
% 3.83/1.03      | ~ v1_relat_1(X1) ),
% 3.83/1.03      inference(cnf_transformation,[],[f60]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_1175,plain,
% 3.83/1.03      ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) != iProver_top
% 3.83/1.03      | v1_funct_1(X0) != iProver_top
% 3.83/1.03      | v1_funct_1(X1) != iProver_top
% 3.83/1.03      | v2_funct_1(X0) = iProver_top
% 3.83/1.03      | v2_funct_1(k5_relat_1(X0,X1)) != iProver_top
% 3.83/1.03      | v1_relat_1(X0) != iProver_top
% 3.83/1.03      | v1_relat_1(X1) != iProver_top ),
% 3.83/1.03      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_3975,plain,
% 3.83/1.03      ( v1_funct_1(sK2) != iProver_top
% 3.83/1.03      | v1_funct_1(sK3) != iProver_top
% 3.83/1.03      | v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
% 3.83/1.03      | v2_funct_1(sK2) = iProver_top
% 3.83/1.03      | v1_relat_1(sK2) != iProver_top
% 3.83/1.03      | v1_relat_1(sK3) != iProver_top ),
% 3.83/1.03      inference(superposition,[status(thm)],[c_3970,c_1175]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_3976,plain,
% 3.83/1.03      ( v1_funct_1(sK2) != iProver_top
% 3.83/1.03      | v1_funct_1(sK3) != iProver_top
% 3.83/1.03      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 3.83/1.03      | v2_funct_1(sK2) = iProver_top
% 3.83/1.03      | v1_relat_1(sK2) != iProver_top
% 3.83/1.03      | v1_relat_1(sK3) != iProver_top ),
% 3.83/1.03      inference(light_normalisation,[status(thm)],[c_3975,c_3853]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_15,plain,
% 3.83/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.83/1.03      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.83/1.03      inference(cnf_transformation,[],[f64]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_1173,plain,
% 3.83/1.03      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.83/1.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.83/1.03      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_2362,plain,
% 3.83/1.03      ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 3.83/1.03      inference(superposition,[status(thm)],[c_1168,c_1173]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_24,plain,
% 3.83/1.03      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.83/1.03      | ~ v1_funct_2(X2,X0,X1)
% 3.83/1.03      | ~ v1_funct_2(X3,X1,X0)
% 3.83/1.03      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.83/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.83/1.03      | ~ v1_funct_1(X2)
% 3.83/1.03      | ~ v1_funct_1(X3)
% 3.83/1.03      | k2_relset_1(X1,X0,X3) = X0 ),
% 3.83/1.03      inference(cnf_transformation,[],[f74]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_483,plain,
% 3.83/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 3.83/1.03      | ~ v1_funct_2(X3,X2,X1)
% 3.83/1.03      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.83/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.83/1.03      | ~ v1_funct_1(X0)
% 3.83/1.03      | ~ v1_funct_1(X3)
% 3.83/1.03      | k1_partfun1(X2,X1,X1,X2,X3,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.83/1.03      | k2_relset_1(X1,X2,X0) = X2
% 3.83/1.03      | k6_partfun1(X2) != k6_partfun1(sK0)
% 3.83/1.03      | sK0 != X2 ),
% 3.83/1.03      inference(resolution_lifted,[status(thm)],[c_24,c_26]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_484,plain,
% 3.83/1.03      ( ~ v1_funct_2(X0,X1,sK0)
% 3.83/1.03      | ~ v1_funct_2(X2,sK0,X1)
% 3.83/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 3.83/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 3.83/1.03      | ~ v1_funct_1(X0)
% 3.83/1.03      | ~ v1_funct_1(X2)
% 3.83/1.03      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.83/1.03      | k2_relset_1(X1,sK0,X0) = sK0
% 3.83/1.03      | k6_partfun1(sK0) != k6_partfun1(sK0) ),
% 3.83/1.03      inference(unflattening,[status(thm)],[c_483]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_562,plain,
% 3.83/1.03      ( ~ v1_funct_2(X0,X1,sK0)
% 3.83/1.03      | ~ v1_funct_2(X2,sK0,X1)
% 3.83/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 3.83/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 3.83/1.03      | ~ v1_funct_1(X0)
% 3.83/1.03      | ~ v1_funct_1(X2)
% 3.83/1.03      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.83/1.03      | k2_relset_1(X1,sK0,X0) = sK0 ),
% 3.83/1.03      inference(equality_resolution_simp,[status(thm)],[c_484]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_1157,plain,
% 3.83/1.03      ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.83/1.03      | k2_relset_1(X0,sK0,X2) = sK0
% 3.83/1.03      | v1_funct_2(X2,X0,sK0) != iProver_top
% 3.83/1.03      | v1_funct_2(X1,sK0,X0) != iProver_top
% 3.83/1.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 3.83/1.03      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 3.83/1.03      | v1_funct_1(X1) != iProver_top
% 3.83/1.03      | v1_funct_1(X2) != iProver_top ),
% 3.83/1.03      inference(predicate_to_equality,[status(thm)],[c_562]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_1912,plain,
% 3.83/1.03      ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k6_partfun1(sK0)
% 3.83/1.03      | k2_relset_1(X0,sK0,X2) = sK0
% 3.83/1.03      | v1_funct_2(X2,X0,sK0) != iProver_top
% 3.83/1.03      | v1_funct_2(X1,sK0,X0) != iProver_top
% 3.83/1.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 3.83/1.03      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 3.83/1.03      | v1_funct_1(X2) != iProver_top
% 3.83/1.03      | v1_funct_1(X1) != iProver_top ),
% 3.83/1.03      inference(light_normalisation,[status(thm)],[c_1157,c_1808]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_1916,plain,
% 3.83/1.03      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 3.83/1.03      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 3.83/1.03      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 3.83/1.03      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.83/1.03      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.83/1.03      | v1_funct_1(sK2) != iProver_top
% 3.83/1.03      | v1_funct_1(sK3) != iProver_top ),
% 3.83/1.03      inference(superposition,[status(thm)],[c_1808,c_1912]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_31,negated_conjecture,
% 3.83/1.03      ( v1_funct_2(sK2,sK0,sK1) ),
% 3.83/1.03      inference(cnf_transformation,[],[f76]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_34,plain,
% 3.83/1.03      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 3.83/1.03      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_28,negated_conjecture,
% 3.83/1.03      ( v1_funct_2(sK3,sK1,sK0) ),
% 3.83/1.03      inference(cnf_transformation,[],[f79]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_37,plain,
% 3.83/1.03      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 3.83/1.03      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_1919,plain,
% 3.83/1.03      ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 3.83/1.03      inference(global_propositional_subsumption,
% 3.83/1.03                [status(thm)],
% 3.83/1.03                [c_1916,c_33,c_34,c_35,c_36,c_37,c_38]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_2364,plain,
% 3.83/1.03      ( k2_relat_1(sK3) = sK0 ),
% 3.83/1.03      inference(light_normalisation,[status(thm)],[c_2362,c_1919]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_13,plain,
% 3.83/1.03      ( v5_relat_1(X0,X1)
% 3.83/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.83/1.03      inference(cnf_transformation,[],[f63]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_19,plain,
% 3.83/1.03      ( v2_funct_2(X0,k2_relat_1(X0))
% 3.83/1.03      | ~ v5_relat_1(X0,k2_relat_1(X0))
% 3.83/1.03      | ~ v1_relat_1(X0) ),
% 3.83/1.03      inference(cnf_transformation,[],[f91]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_387,plain,
% 3.83/1.03      ( v2_funct_2(X0,k2_relat_1(X0))
% 3.83/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.83/1.03      | ~ v1_relat_1(X0)
% 3.83/1.03      | X0 != X1
% 3.83/1.03      | k2_relat_1(X0) != X3 ),
% 3.83/1.03      inference(resolution_lifted,[status(thm)],[c_13,c_19]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_388,plain,
% 3.83/1.03      ( v2_funct_2(X0,k2_relat_1(X0))
% 3.83/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
% 3.83/1.03      | ~ v1_relat_1(X0) ),
% 3.83/1.03      inference(unflattening,[status(thm)],[c_387]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_398,plain,
% 3.83/1.03      ( v2_funct_2(X0,k2_relat_1(X0))
% 3.83/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0)))) ),
% 3.83/1.03      inference(forward_subsumption_resolution,
% 3.83/1.03                [status(thm)],
% 3.83/1.03                [c_388,c_12]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_25,negated_conjecture,
% 3.83/1.03      ( ~ v2_funct_2(sK3,sK0) | ~ v2_funct_1(sK2) ),
% 3.83/1.03      inference(cnf_transformation,[],[f82]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_413,plain,
% 3.83/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
% 3.83/1.03      | ~ v2_funct_1(sK2)
% 3.83/1.03      | k2_relat_1(X0) != sK0
% 3.83/1.03      | sK3 != X0 ),
% 3.83/1.03      inference(resolution_lifted,[status(thm)],[c_398,c_25]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_414,plain,
% 3.83/1.03      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3))))
% 3.83/1.03      | ~ v2_funct_1(sK2)
% 3.83/1.03      | k2_relat_1(sK3) != sK0 ),
% 3.83/1.03      inference(unflattening,[status(thm)],[c_413]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_705,plain,
% 3.83/1.03      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3))))
% 3.83/1.03      | ~ sP0_iProver_split ),
% 3.83/1.03      inference(splitting,
% 3.83/1.03                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 3.83/1.03                [c_414]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_1161,plain,
% 3.83/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3)))) != iProver_top
% 3.83/1.03      | sP0_iProver_split != iProver_top ),
% 3.83/1.03      inference(predicate_to_equality,[status(thm)],[c_705]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_2692,plain,
% 3.83/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 3.83/1.03      | sP0_iProver_split != iProver_top ),
% 3.83/1.03      inference(demodulation,[status(thm)],[c_2364,c_1161]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_3035,plain,
% 3.83/1.03      ( sP0_iProver_split != iProver_top ),
% 3.83/1.03      inference(superposition,[status(thm)],[c_1168,c_2692]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_706,plain,
% 3.83/1.03      ( ~ v2_funct_1(sK2) | sP0_iProver_split | k2_relat_1(sK3) != sK0 ),
% 3.83/1.03      inference(splitting,
% 3.83/1.03                [splitting(split),new_symbols(definition,[])],
% 3.83/1.03                [c_414]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_1160,plain,
% 3.83/1.03      ( k2_relat_1(sK3) != sK0
% 3.83/1.03      | v2_funct_1(sK2) != iProver_top
% 3.83/1.03      | sP0_iProver_split = iProver_top ),
% 3.83/1.03      inference(predicate_to_equality,[status(thm)],[c_706]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_2693,plain,
% 3.83/1.03      ( sK0 != sK0
% 3.83/1.03      | v2_funct_1(sK2) != iProver_top
% 3.83/1.03      | sP0_iProver_split = iProver_top ),
% 3.83/1.03      inference(demodulation,[status(thm)],[c_2364,c_1160]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_2694,plain,
% 3.83/1.03      ( v2_funct_1(sK2) != iProver_top
% 3.83/1.03      | sP0_iProver_split = iProver_top ),
% 3.83/1.03      inference(equality_resolution_simp,[status(thm)],[c_2693]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_8,plain,
% 3.83/1.03      ( v2_funct_1(k6_partfun1(X0)) ),
% 3.83/1.03      inference(cnf_transformation,[],[f85]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_89,plain,
% 3.83/1.03      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 3.83/1.03      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(c_91,plain,
% 3.83/1.03      ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
% 3.83/1.03      inference(instantiation,[status(thm)],[c_89]) ).
% 3.83/1.03  
% 3.83/1.03  cnf(contradiction,plain,
% 3.83/1.03      ( $false ),
% 3.83/1.03      inference(minisat,
% 3.83/1.03                [status(thm)],
% 3.83/1.03                [c_3976,c_3035,c_2694,c_1352,c_1297,c_91,c_38,c_36,c_35,
% 3.83/1.03                 c_33]) ).
% 3.83/1.03  
% 3.83/1.03  
% 3.83/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 3.83/1.03  
% 3.83/1.03  ------                               Statistics
% 3.83/1.03  
% 3.83/1.03  ------ General
% 3.83/1.03  
% 3.83/1.03  abstr_ref_over_cycles:                  0
% 3.83/1.03  abstr_ref_under_cycles:                 0
% 3.83/1.03  gc_basic_clause_elim:                   0
% 3.83/1.03  forced_gc_time:                         0
% 3.83/1.03  parsing_time:                           0.007
% 3.83/1.03  unif_index_cands_time:                  0.
% 3.83/1.03  unif_index_add_time:                    0.
% 3.83/1.03  orderings_time:                         0.
% 3.83/1.03  out_proof_time:                         0.025
% 3.83/1.03  total_time:                             0.178
% 3.83/1.03  num_of_symbols:                         54
% 3.83/1.03  num_of_terms:                           6697
% 3.83/1.03  
% 3.83/1.03  ------ Preprocessing
% 3.83/1.03  
% 3.83/1.03  num_of_splits:                          1
% 3.83/1.03  num_of_split_atoms:                     1
% 3.83/1.03  num_of_reused_defs:                     0
% 3.83/1.03  num_eq_ax_congr_red:                    16
% 3.83/1.03  num_of_sem_filtered_clauses:            1
% 3.83/1.03  num_of_subtypes:                        0
% 3.83/1.03  monotx_restored_types:                  0
% 3.83/1.03  sat_num_of_epr_types:                   0
% 3.83/1.03  sat_num_of_non_cyclic_types:            0
% 3.83/1.03  sat_guarded_non_collapsed_types:        0
% 3.83/1.03  num_pure_diseq_elim:                    0
% 3.83/1.03  simp_replaced_by:                       0
% 3.83/1.03  res_preprocessed:                       143
% 3.83/1.03  prep_upred:                             0
% 3.83/1.03  prep_unflattend:                        17
% 3.83/1.03  smt_new_axioms:                         0
% 3.83/1.03  pred_elim_cands:                        6
% 3.83/1.03  pred_elim:                              4
% 3.83/1.03  pred_elim_cl:                           6
% 3.83/1.03  pred_elim_cycles:                       6
% 3.83/1.03  merged_defs:                            0
% 3.83/1.03  merged_defs_ncl:                        0
% 3.83/1.03  bin_hyper_res:                          0
% 3.83/1.03  prep_cycles:                            4
% 3.83/1.03  pred_elim_time:                         0.004
% 3.83/1.03  splitting_time:                         0.
% 3.83/1.03  sem_filter_time:                        0.
% 3.83/1.03  monotx_time:                            0.
% 3.83/1.03  subtype_inf_time:                       0.
% 3.83/1.03  
% 3.83/1.03  ------ Problem properties
% 3.83/1.03  
% 3.83/1.03  clauses:                                27
% 3.83/1.03  conjectures:                            6
% 3.83/1.03  epr:                                    6
% 3.83/1.03  horn:                                   27
% 3.83/1.03  ground:                                 8
% 3.83/1.03  unary:                                  12
% 3.83/1.03  binary:                                 5
% 3.83/1.03  lits:                                   75
% 3.83/1.03  lits_eq:                                12
% 3.83/1.03  fd_pure:                                0
% 3.83/1.03  fd_pseudo:                              0
% 3.83/1.03  fd_cond:                                0
% 3.83/1.03  fd_pseudo_cond:                         1
% 3.83/1.03  ac_symbols:                             0
% 3.83/1.03  
% 3.83/1.03  ------ Propositional Solver
% 3.83/1.03  
% 3.83/1.03  prop_solver_calls:                      29
% 3.83/1.03  prop_fast_solver_calls:                 991
% 3.83/1.03  smt_solver_calls:                       0
% 3.83/1.03  smt_fast_solver_calls:                  0
% 3.83/1.03  prop_num_of_clauses:                    1880
% 3.83/1.03  prop_preprocess_simplified:             6159
% 3.83/1.03  prop_fo_subsumed:                       23
% 3.83/1.03  prop_solver_time:                       0.
% 3.83/1.03  smt_solver_time:                        0.
% 3.83/1.03  smt_fast_solver_time:                   0.
% 3.83/1.03  prop_fast_solver_time:                  0.
% 3.83/1.03  prop_unsat_core_time:                   0.
% 3.83/1.03  
% 3.83/1.03  ------ QBF
% 3.83/1.03  
% 3.83/1.03  qbf_q_res:                              0
% 3.83/1.03  qbf_num_tautologies:                    0
% 3.83/1.03  qbf_prep_cycles:                        0
% 3.83/1.03  
% 3.83/1.03  ------ BMC1
% 3.83/1.03  
% 3.83/1.03  bmc1_current_bound:                     -1
% 3.83/1.03  bmc1_last_solved_bound:                 -1
% 3.83/1.03  bmc1_unsat_core_size:                   -1
% 3.83/1.03  bmc1_unsat_core_parents_size:           -1
% 3.83/1.03  bmc1_merge_next_fun:                    0
% 3.83/1.03  bmc1_unsat_core_clauses_time:           0.
% 3.83/1.03  
% 3.83/1.03  ------ Instantiation
% 3.83/1.03  
% 3.83/1.03  inst_num_of_clauses:                    486
% 3.83/1.03  inst_num_in_passive:                    187
% 3.83/1.03  inst_num_in_active:                     235
% 3.83/1.03  inst_num_in_unprocessed:                64
% 3.83/1.03  inst_num_of_loops:                      250
% 3.83/1.03  inst_num_of_learning_restarts:          0
% 3.83/1.03  inst_num_moves_active_passive:          12
% 3.83/1.03  inst_lit_activity:                      0
% 3.83/1.03  inst_lit_activity_moves:                0
% 3.83/1.03  inst_num_tautologies:                   0
% 3.83/1.03  inst_num_prop_implied:                  0
% 3.83/1.03  inst_num_existing_simplified:           0
% 3.83/1.03  inst_num_eq_res_simplified:             0
% 3.83/1.03  inst_num_child_elim:                    0
% 3.83/1.03  inst_num_of_dismatching_blockings:      77
% 3.83/1.03  inst_num_of_non_proper_insts:           453
% 3.83/1.03  inst_num_of_duplicates:                 0
% 3.83/1.03  inst_inst_num_from_inst_to_res:         0
% 3.83/1.03  inst_dismatching_checking_time:         0.
% 3.83/1.03  
% 3.83/1.03  ------ Resolution
% 3.83/1.03  
% 3.83/1.03  res_num_of_clauses:                     0
% 3.83/1.03  res_num_in_passive:                     0
% 3.83/1.03  res_num_in_active:                      0
% 3.83/1.03  res_num_of_loops:                       147
% 3.83/1.03  res_forward_subset_subsumed:            29
% 3.83/1.03  res_backward_subset_subsumed:           0
% 3.83/1.03  res_forward_subsumed:                   0
% 3.83/1.03  res_backward_subsumed:                  0
% 3.83/1.03  res_forward_subsumption_resolution:     3
% 3.83/1.03  res_backward_subsumption_resolution:    0
% 3.83/1.03  res_clause_to_clause_subsumption:       127
% 3.83/1.03  res_orphan_elimination:                 0
% 3.83/1.03  res_tautology_del:                      31
% 3.83/1.03  res_num_eq_res_simplified:              1
% 3.83/1.03  res_num_sel_changes:                    0
% 3.83/1.03  res_moves_from_active_to_pass:          0
% 3.83/1.03  
% 3.83/1.03  ------ Superposition
% 3.83/1.03  
% 3.83/1.03  sup_time_total:                         0.
% 3.83/1.03  sup_time_generating:                    0.
% 3.83/1.03  sup_time_sim_full:                      0.
% 3.83/1.03  sup_time_sim_immed:                     0.
% 3.83/1.03  
% 3.83/1.03  sup_num_of_clauses:                     69
% 3.83/1.03  sup_num_in_active:                      45
% 3.83/1.03  sup_num_in_passive:                     24
% 3.83/1.03  sup_num_of_loops:                       49
% 3.83/1.03  sup_fw_superposition:                   31
% 3.83/1.03  sup_bw_superposition:                   20
% 3.83/1.03  sup_immediate_simplified:               12
% 3.83/1.03  sup_given_eliminated:                   1
% 3.83/1.03  comparisons_done:                       0
% 3.83/1.03  comparisons_avoided:                    0
% 3.83/1.03  
% 3.83/1.03  ------ Simplifications
% 3.83/1.03  
% 3.83/1.03  
% 3.83/1.03  sim_fw_subset_subsumed:                 2
% 3.83/1.03  sim_bw_subset_subsumed:                 1
% 3.83/1.03  sim_fw_subsumed:                        2
% 3.83/1.03  sim_bw_subsumed:                        1
% 3.83/1.03  sim_fw_subsumption_res:                 0
% 3.83/1.03  sim_bw_subsumption_res:                 0
% 3.83/1.03  sim_tautology_del:                      0
% 3.83/1.03  sim_eq_tautology_del:                   0
% 3.83/1.03  sim_eq_res_simp:                        1
% 3.83/1.03  sim_fw_demodulated:                     3
% 3.83/1.03  sim_bw_demodulated:                     3
% 3.83/1.03  sim_light_normalised:                   6
% 3.83/1.03  sim_joinable_taut:                      0
% 3.83/1.03  sim_joinable_simp:                      0
% 3.83/1.03  sim_ac_normalised:                      0
% 3.83/1.03  sim_smt_subsumption:                    0
% 3.83/1.03  
%------------------------------------------------------------------------------
