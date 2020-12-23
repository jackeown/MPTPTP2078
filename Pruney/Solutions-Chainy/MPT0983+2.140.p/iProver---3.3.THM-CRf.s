%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:14 EST 2020

% Result     : Theorem 2.95s
% Output     : CNFRefutation 2.95s
% Verified   : 
% Statistics : Number of formulae       :  172 ( 868 expanded)
%              Number of clauses        :  106 ( 295 expanded)
%              Number of leaves         :   20 ( 203 expanded)
%              Depth                    :   18
%              Number of atoms          :  592 (5443 expanded)
%              Number of equality atoms :  180 ( 448 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f29])).

fof(f56,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f25])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f16,conjecture,(
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

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f40,plain,(
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

fof(f39,plain,
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

fof(f41,plain,
    ( ( ~ v2_funct_2(sK3,sK0)
      | ~ v2_funct_1(sK2) )
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f36,f40,f39])).

fof(f68,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f41])).

fof(f12,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f57,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f62,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f64,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f41])).

fof(f65,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f67,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f41])).

fof(f15,axiom,(
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

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f60,plain,(
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
    inference(cnf_transformation,[],[f34])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f14,axiom,(
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

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f63,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f66,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f73,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f54])).

fof(f69,plain,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f5,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f13,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f70,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f47,f58])).

cnf(c_679,plain,
    ( ~ v2_funct_1(X0_48)
    | v2_funct_1(X1_48)
    | X1_48 != X0_48 ),
    theory(equality)).

cnf(c_4285,plain,
    ( ~ v2_funct_1(X0_48)
    | v2_funct_1(sK2)
    | sK2 != X0_48 ),
    inference(instantiation,[status(thm)],[c_679])).

cnf(c_4287,plain,
    ( v2_funct_1(sK2)
    | ~ v2_funct_1(sK0)
    | sK2 != sK0 ),
    inference(instantiation,[status(thm)],[c_4285])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_658,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | ~ m1_subset_1(X3_48,k1_zfmisc_1(k2_zfmisc_1(X4_48,X5_48)))
    | m1_subset_1(k1_partfun1(X4_48,X5_48,X1_48,X2_48,X3_48,X0_48),k1_zfmisc_1(k2_zfmisc_1(X4_48,X2_48)))
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(X3_48) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1138,plain,
    ( m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48))) != iProver_top
    | m1_subset_1(X3_48,k1_zfmisc_1(k2_zfmisc_1(X4_48,X5_48))) != iProver_top
    | m1_subset_1(k1_partfun1(X4_48,X5_48,X1_48,X2_48,X3_48,X0_48),k1_zfmisc_1(k2_zfmisc_1(X4_48,X2_48))) = iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(X3_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_658])).

cnf(c_10,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_20,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_417,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_20])).

cnf(c_418,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_417])).

cnf(c_15,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_45,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_420,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_418,c_45])).

cnf(c_645,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_420])).

cnf(c_1152,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_645])).

cnf(c_2107,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1138,c_1152])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_27,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_29,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_30,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_32,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2359,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2107,c_27,c_29,c_30,c_32])).

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
    inference(cnf_transformation,[],[f60])).

cnf(c_654,plain,
    ( ~ v1_funct_2(X0_48,X1_48,X2_48)
    | ~ v1_funct_2(X3_48,X2_48,X4_48)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | ~ m1_subset_1(X3_48,k1_zfmisc_1(k2_zfmisc_1(X2_48,X4_48)))
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(X3_48)
    | v2_funct_1(X0_48)
    | ~ v2_funct_1(k1_partfun1(X1_48,X2_48,X2_48,X4_48,X0_48,X3_48))
    | k1_xboole_0 = X4_48 ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1142,plain,
    ( k1_xboole_0 = X0_48
    | v1_funct_2(X1_48,X2_48,X3_48) != iProver_top
    | v1_funct_2(X4_48,X3_48,X0_48) != iProver_top
    | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_48,X3_48))) != iProver_top
    | m1_subset_1(X4_48,k1_zfmisc_1(k2_zfmisc_1(X3_48,X0_48))) != iProver_top
    | v1_funct_1(X1_48) != iProver_top
    | v1_funct_1(X4_48) != iProver_top
    | v2_funct_1(X1_48) = iProver_top
    | v2_funct_1(k1_partfun1(X2_48,X3_48,X3_48,X0_48,X1_48,X4_48)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_654])).

cnf(c_2893,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2359,c_1142])).

cnf(c_653,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1143,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_653])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_659,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | k2_relset_1(X1_48,X2_48,X0_48) = k2_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1137,plain,
    ( k2_relset_1(X0_48,X1_48,X2_48) = k2_relat_1(X2_48)
    | m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_659])).

cnf(c_2069,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1143,c_1137])).

cnf(c_16,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_431,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k1_partfun1(X1,X2,X2,X1,X0,X3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X2,X1,X3) = X1
    | k6_partfun1(X1) != k6_partfun1(sK0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_20])).

cnf(c_432,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X0)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0
    | k6_partfun1(sK0) != k6_partfun1(sK0) ),
    inference(unflattening,[status(thm)],[c_431])).

cnf(c_509,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_432])).

cnf(c_644,plain,
    ( ~ v1_funct_2(X0_48,X1_48,sK0)
    | ~ v1_funct_2(X2_48,sK0,X1_48)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,sK0)))
    | ~ m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(sK0,X1_48)))
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(X2_48)
    | k1_partfun1(sK0,X1_48,X1_48,sK0,X2_48,X0_48) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1_48,sK0,X0_48) = sK0 ),
    inference(subtyping,[status(esa)],[c_509])).

cnf(c_1153,plain,
    ( k1_partfun1(sK0,X0_48,X0_48,sK0,X1_48,X2_48) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X0_48,sK0,X2_48) = sK0
    | v1_funct_2(X2_48,X0_48,sK0) != iProver_top
    | v1_funct_2(X1_48,sK0,X0_48) != iProver_top
    | m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,sK0))) != iProver_top
    | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_48))) != iProver_top
    | v1_funct_1(X2_48) != iProver_top
    | v1_funct_1(X1_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_644])).

cnf(c_1883,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1153])).

cnf(c_25,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_28,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_22,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_31,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1886,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1883,c_27,c_28,c_29,c_30,c_31,c_32])).

cnf(c_2077,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_2069,c_1886])).

cnf(c_6,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_11,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_19,negated_conjecture,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_336,plain,
    ( ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) != sK0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_19])).

cnf(c_337,plain,
    ( ~ v5_relat_1(sK3,k2_relat_1(sK3))
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) != sK0 ),
    inference(unflattening,[status(thm)],[c_336])).

cnf(c_357,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) != X2
    | k2_relat_1(sK3) != sK0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_337])).

cnf(c_358,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3))))
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) != sK0 ),
    inference(unflattening,[status(thm)],[c_357])).

cnf(c_647,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_48,k2_relat_1(sK3))))
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) != sK0 ),
    inference(subtyping,[status(esa)],[c_358])).

cnf(c_667,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_48,k2_relat_1(sK3))))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_647])).

cnf(c_1150,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_48,k2_relat_1(sK3)))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_667])).

cnf(c_2290,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_48,sK0))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(demodulation,[status(thm)],[c_2077,c_1150])).

cnf(c_2404,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_1143,c_2290])).

cnf(c_2405,plain,
    ( ~ sP0_iProver_split ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2404])).

cnf(c_668,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | sP0_iProver_split
    | k2_relat_1(sK3) != sK0 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_647])).

cnf(c_1149,plain,
    ( k2_relat_1(sK3) != sK0
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_668])).

cnf(c_723,plain,
    ( k2_relat_1(sK3) != sK0
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_668])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_664,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(X1_48))
    | ~ v1_relat_1(X1_48)
    | v1_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1132,plain,
    ( m1_subset_1(X0_48,k1_zfmisc_1(X1_48)) != iProver_top
    | v1_relat_1(X1_48) != iProver_top
    | v1_relat_1(X0_48) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_664])).

cnf(c_1592,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1143,c_1132])).

cnf(c_3,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_663,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_48,X1_48)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1133,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_48,X1_48)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_663])).

cnf(c_1749,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1592,c_1133])).

cnf(c_1829,plain,
    ( v2_funct_1(sK2) != iProver_top
    | k2_relat_1(sK3) != sK0
    | sP0_iProver_split = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1149,c_723,c_1749])).

cnf(c_1830,plain,
    ( k2_relat_1(sK3) != sK0
    | v2_funct_1(sK2) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(renaming,[status(thm)],[c_1829])).

cnf(c_2289,plain,
    ( sK0 != sK0
    | v2_funct_1(sK2) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_2077,c_1830])).

cnf(c_2295,plain,
    ( v2_funct_1(sK2) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2289])).

cnf(c_656,plain,
    ( m1_subset_1(k6_partfun1(X0_48),k1_zfmisc_1(k2_zfmisc_1(X0_48,X0_48))) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1140,plain,
    ( m1_subset_1(k6_partfun1(X0_48),k1_zfmisc_1(k2_zfmisc_1(X0_48,X0_48))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_656])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_660,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
    | ~ v1_xboole_0(X1_48)
    | v1_xboole_0(X0_48) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1136,plain,
    ( m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48))) != iProver_top
    | v1_xboole_0(X1_48) != iProver_top
    | v1_xboole_0(X0_48) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_660])).

cnf(c_1989,plain,
    ( v1_xboole_0(X0_48) != iProver_top
    | v1_xboole_0(k6_partfun1(X0_48)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1140,c_1136])).

cnf(c_2004,plain,
    ( ~ v1_xboole_0(X0_48)
    | v1_xboole_0(k6_partfun1(X0_48)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1989])).

cnf(c_2006,plain,
    ( v1_xboole_0(k6_partfun1(sK0))
    | ~ v1_xboole_0(sK0) ),
    inference(instantiation,[status(thm)],[c_2004])).

cnf(c_650,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1146,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_650])).

cnf(c_1988,plain,
    ( v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1146,c_1136])).

cnf(c_2003,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_xboole_0(sK0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1988])).

cnf(c_1831,plain,
    ( ~ v2_funct_1(sK2)
    | sP0_iProver_split
    | k2_relat_1(sK3) != sK0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1830])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_665,plain,
    ( ~ v1_xboole_0(X0_48)
    | ~ v1_xboole_0(X1_48)
    | X1_48 = X0_48 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1788,plain,
    ( ~ v1_xboole_0(X0_48)
    | ~ v1_xboole_0(k6_partfun1(X1_48))
    | X0_48 = k6_partfun1(X1_48) ),
    inference(instantiation,[status(thm)],[c_665])).

cnf(c_1790,plain,
    ( ~ v1_xboole_0(k6_partfun1(sK0))
    | ~ v1_xboole_0(sK0)
    | sK0 = k6_partfun1(sK0) ),
    inference(instantiation,[status(thm)],[c_1788])).

cnf(c_1759,plain,
    ( ~ v1_xboole_0(X0_48)
    | ~ v1_xboole_0(sK2)
    | sK2 = X0_48 ),
    inference(instantiation,[status(thm)],[c_665])).

cnf(c_1761,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ v1_xboole_0(sK0)
    | sK2 = sK0 ),
    inference(instantiation,[status(thm)],[c_1759])).

cnf(c_673,plain,
    ( ~ v1_xboole_0(X0_48)
    | v1_xboole_0(X1_48)
    | X1_48 != X0_48 ),
    theory(equality)).

cnf(c_1492,plain,
    ( v1_xboole_0(X0_48)
    | ~ v1_xboole_0(k1_xboole_0)
    | X0_48 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_673])).

cnf(c_1494,plain,
    ( v1_xboole_0(sK0)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1492])).

cnf(c_1378,plain,
    ( v2_funct_1(X0_48)
    | ~ v2_funct_1(k6_partfun1(X1_48))
    | X0_48 != k6_partfun1(X1_48) ),
    inference(instantiation,[status(thm)],[c_679])).

cnf(c_1380,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | v2_funct_1(sK0)
    | sK0 != k6_partfun1(sK0) ),
    inference(instantiation,[status(thm)],[c_1378])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_4,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_75,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_77,plain,
    ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_75])).

cnf(c_76,plain,
    ( v2_funct_1(k6_partfun1(sK0)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4287,c_2893,c_2405,c_2404,c_2295,c_2077,c_2006,c_2003,c_1831,c_1790,c_1761,c_1494,c_1380,c_0,c_77,c_76,c_32,c_31,c_30,c_29,c_28,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:19:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.95/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.95/0.99  
% 2.95/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.95/0.99  
% 2.95/0.99  ------  iProver source info
% 2.95/0.99  
% 2.95/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.95/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.95/0.99  git: non_committed_changes: false
% 2.95/0.99  git: last_make_outside_of_git: false
% 2.95/0.99  
% 2.95/0.99  ------ 
% 2.95/0.99  
% 2.95/0.99  ------ Input Options
% 2.95/0.99  
% 2.95/0.99  --out_options                           all
% 2.95/0.99  --tptp_safe_out                         true
% 2.95/0.99  --problem_path                          ""
% 2.95/0.99  --include_path                          ""
% 2.95/0.99  --clausifier                            res/vclausify_rel
% 2.95/0.99  --clausifier_options                    --mode clausify
% 2.95/0.99  --stdin                                 false
% 2.95/0.99  --stats_out                             all
% 2.95/0.99  
% 2.95/0.99  ------ General Options
% 2.95/0.99  
% 2.95/0.99  --fof                                   false
% 2.95/0.99  --time_out_real                         305.
% 2.95/0.99  --time_out_virtual                      -1.
% 2.95/0.99  --symbol_type_check                     false
% 2.95/0.99  --clausify_out                          false
% 2.95/0.99  --sig_cnt_out                           false
% 2.95/0.99  --trig_cnt_out                          false
% 2.95/0.99  --trig_cnt_out_tolerance                1.
% 2.95/0.99  --trig_cnt_out_sk_spl                   false
% 2.95/0.99  --abstr_cl_out                          false
% 2.95/0.99  
% 2.95/0.99  ------ Global Options
% 2.95/0.99  
% 2.95/0.99  --schedule                              default
% 2.95/0.99  --add_important_lit                     false
% 2.95/0.99  --prop_solver_per_cl                    1000
% 2.95/0.99  --min_unsat_core                        false
% 2.95/0.99  --soft_assumptions                      false
% 2.95/0.99  --soft_lemma_size                       3
% 2.95/0.99  --prop_impl_unit_size                   0
% 2.95/0.99  --prop_impl_unit                        []
% 2.95/0.99  --share_sel_clauses                     true
% 2.95/0.99  --reset_solvers                         false
% 2.95/0.99  --bc_imp_inh                            [conj_cone]
% 2.95/0.99  --conj_cone_tolerance                   3.
% 2.95/0.99  --extra_neg_conj                        none
% 2.95/0.99  --large_theory_mode                     true
% 2.95/0.99  --prolific_symb_bound                   200
% 2.95/0.99  --lt_threshold                          2000
% 2.95/0.99  --clause_weak_htbl                      true
% 2.95/0.99  --gc_record_bc_elim                     false
% 2.95/0.99  
% 2.95/0.99  ------ Preprocessing Options
% 2.95/0.99  
% 2.95/0.99  --preprocessing_flag                    true
% 2.95/0.99  --time_out_prep_mult                    0.1
% 2.95/0.99  --splitting_mode                        input
% 2.95/0.99  --splitting_grd                         true
% 2.95/0.99  --splitting_cvd                         false
% 2.95/0.99  --splitting_cvd_svl                     false
% 2.95/0.99  --splitting_nvd                         32
% 2.95/0.99  --sub_typing                            true
% 2.95/0.99  --prep_gs_sim                           true
% 2.95/0.99  --prep_unflatten                        true
% 2.95/0.99  --prep_res_sim                          true
% 2.95/0.99  --prep_upred                            true
% 2.95/0.99  --prep_sem_filter                       exhaustive
% 2.95/0.99  --prep_sem_filter_out                   false
% 2.95/0.99  --pred_elim                             true
% 2.95/0.99  --res_sim_input                         true
% 2.95/0.99  --eq_ax_congr_red                       true
% 2.95/0.99  --pure_diseq_elim                       true
% 2.95/0.99  --brand_transform                       false
% 2.95/0.99  --non_eq_to_eq                          false
% 2.95/0.99  --prep_def_merge                        true
% 2.95/0.99  --prep_def_merge_prop_impl              false
% 2.95/0.99  --prep_def_merge_mbd                    true
% 2.95/0.99  --prep_def_merge_tr_red                 false
% 2.95/0.99  --prep_def_merge_tr_cl                  false
% 2.95/0.99  --smt_preprocessing                     true
% 2.95/0.99  --smt_ac_axioms                         fast
% 2.95/0.99  --preprocessed_out                      false
% 2.95/0.99  --preprocessed_stats                    false
% 2.95/0.99  
% 2.95/0.99  ------ Abstraction refinement Options
% 2.95/0.99  
% 2.95/0.99  --abstr_ref                             []
% 2.95/0.99  --abstr_ref_prep                        false
% 2.95/0.99  --abstr_ref_until_sat                   false
% 2.95/0.99  --abstr_ref_sig_restrict                funpre
% 2.95/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.95/0.99  --abstr_ref_under                       []
% 2.95/0.99  
% 2.95/0.99  ------ SAT Options
% 2.95/0.99  
% 2.95/0.99  --sat_mode                              false
% 2.95/0.99  --sat_fm_restart_options                ""
% 2.95/0.99  --sat_gr_def                            false
% 2.95/0.99  --sat_epr_types                         true
% 2.95/0.99  --sat_non_cyclic_types                  false
% 2.95/0.99  --sat_finite_models                     false
% 2.95/0.99  --sat_fm_lemmas                         false
% 2.95/0.99  --sat_fm_prep                           false
% 2.95/0.99  --sat_fm_uc_incr                        true
% 2.95/0.99  --sat_out_model                         small
% 2.95/0.99  --sat_out_clauses                       false
% 2.95/0.99  
% 2.95/0.99  ------ QBF Options
% 2.95/0.99  
% 2.95/0.99  --qbf_mode                              false
% 2.95/0.99  --qbf_elim_univ                         false
% 2.95/0.99  --qbf_dom_inst                          none
% 2.95/0.99  --qbf_dom_pre_inst                      false
% 2.95/0.99  --qbf_sk_in                             false
% 2.95/0.99  --qbf_pred_elim                         true
% 2.95/0.99  --qbf_split                             512
% 2.95/0.99  
% 2.95/0.99  ------ BMC1 Options
% 2.95/0.99  
% 2.95/0.99  --bmc1_incremental                      false
% 2.95/0.99  --bmc1_axioms                           reachable_all
% 2.95/0.99  --bmc1_min_bound                        0
% 2.95/0.99  --bmc1_max_bound                        -1
% 2.95/0.99  --bmc1_max_bound_default                -1
% 2.95/0.99  --bmc1_symbol_reachability              true
% 2.95/0.99  --bmc1_property_lemmas                  false
% 2.95/0.99  --bmc1_k_induction                      false
% 2.95/0.99  --bmc1_non_equiv_states                 false
% 2.95/0.99  --bmc1_deadlock                         false
% 2.95/0.99  --bmc1_ucm                              false
% 2.95/0.99  --bmc1_add_unsat_core                   none
% 2.95/0.99  --bmc1_unsat_core_children              false
% 2.95/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.95/0.99  --bmc1_out_stat                         full
% 2.95/0.99  --bmc1_ground_init                      false
% 2.95/0.99  --bmc1_pre_inst_next_state              false
% 2.95/0.99  --bmc1_pre_inst_state                   false
% 2.95/0.99  --bmc1_pre_inst_reach_state             false
% 2.95/0.99  --bmc1_out_unsat_core                   false
% 2.95/0.99  --bmc1_aig_witness_out                  false
% 2.95/0.99  --bmc1_verbose                          false
% 2.95/0.99  --bmc1_dump_clauses_tptp                false
% 2.95/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.95/0.99  --bmc1_dump_file                        -
% 2.95/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.95/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.95/0.99  --bmc1_ucm_extend_mode                  1
% 2.95/0.99  --bmc1_ucm_init_mode                    2
% 2.95/0.99  --bmc1_ucm_cone_mode                    none
% 2.95/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.95/0.99  --bmc1_ucm_relax_model                  4
% 2.95/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.95/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.95/0.99  --bmc1_ucm_layered_model                none
% 2.95/0.99  --bmc1_ucm_max_lemma_size               10
% 2.95/0.99  
% 2.95/0.99  ------ AIG Options
% 2.95/0.99  
% 2.95/0.99  --aig_mode                              false
% 2.95/0.99  
% 2.95/0.99  ------ Instantiation Options
% 2.95/0.99  
% 2.95/0.99  --instantiation_flag                    true
% 2.95/0.99  --inst_sos_flag                         false
% 2.95/0.99  --inst_sos_phase                        true
% 2.95/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.95/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.95/0.99  --inst_lit_sel_side                     num_symb
% 2.95/0.99  --inst_solver_per_active                1400
% 2.95/0.99  --inst_solver_calls_frac                1.
% 2.95/0.99  --inst_passive_queue_type               priority_queues
% 2.95/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.95/0.99  --inst_passive_queues_freq              [25;2]
% 2.95/0.99  --inst_dismatching                      true
% 2.95/0.99  --inst_eager_unprocessed_to_passive     true
% 2.95/0.99  --inst_prop_sim_given                   true
% 2.95/0.99  --inst_prop_sim_new                     false
% 2.95/0.99  --inst_subs_new                         false
% 2.95/0.99  --inst_eq_res_simp                      false
% 2.95/0.99  --inst_subs_given                       false
% 2.95/0.99  --inst_orphan_elimination               true
% 2.95/0.99  --inst_learning_loop_flag               true
% 2.95/0.99  --inst_learning_start                   3000
% 2.95/0.99  --inst_learning_factor                  2
% 2.95/0.99  --inst_start_prop_sim_after_learn       3
% 2.95/0.99  --inst_sel_renew                        solver
% 2.95/0.99  --inst_lit_activity_flag                true
% 2.95/0.99  --inst_restr_to_given                   false
% 2.95/0.99  --inst_activity_threshold               500
% 2.95/0.99  --inst_out_proof                        true
% 2.95/0.99  
% 2.95/0.99  ------ Resolution Options
% 2.95/0.99  
% 2.95/0.99  --resolution_flag                       true
% 2.95/0.99  --res_lit_sel                           adaptive
% 2.95/0.99  --res_lit_sel_side                      none
% 2.95/0.99  --res_ordering                          kbo
% 2.95/0.99  --res_to_prop_solver                    active
% 2.95/0.99  --res_prop_simpl_new                    false
% 2.95/0.99  --res_prop_simpl_given                  true
% 2.95/0.99  --res_passive_queue_type                priority_queues
% 2.95/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.95/0.99  --res_passive_queues_freq               [15;5]
% 2.95/0.99  --res_forward_subs                      full
% 2.95/0.99  --res_backward_subs                     full
% 2.95/0.99  --res_forward_subs_resolution           true
% 2.95/0.99  --res_backward_subs_resolution          true
% 2.95/0.99  --res_orphan_elimination                true
% 2.95/0.99  --res_time_limit                        2.
% 2.95/0.99  --res_out_proof                         true
% 2.95/0.99  
% 2.95/0.99  ------ Superposition Options
% 2.95/0.99  
% 2.95/0.99  --superposition_flag                    true
% 2.95/0.99  --sup_passive_queue_type                priority_queues
% 2.95/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.95/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.95/0.99  --demod_completeness_check              fast
% 2.95/0.99  --demod_use_ground                      true
% 2.95/0.99  --sup_to_prop_solver                    passive
% 2.95/0.99  --sup_prop_simpl_new                    true
% 2.95/0.99  --sup_prop_simpl_given                  true
% 2.95/0.99  --sup_fun_splitting                     false
% 2.95/0.99  --sup_smt_interval                      50000
% 2.95/0.99  
% 2.95/0.99  ------ Superposition Simplification Setup
% 2.95/0.99  
% 2.95/0.99  --sup_indices_passive                   []
% 2.95/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.95/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.95/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.95/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.95/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.95/0.99  --sup_full_bw                           [BwDemod]
% 2.95/0.99  --sup_immed_triv                        [TrivRules]
% 2.95/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.95/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.95/0.99  --sup_immed_bw_main                     []
% 2.95/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.95/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.95/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.95/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.95/0.99  
% 2.95/0.99  ------ Combination Options
% 2.95/0.99  
% 2.95/0.99  --comb_res_mult                         3
% 2.95/0.99  --comb_sup_mult                         2
% 2.95/0.99  --comb_inst_mult                        10
% 2.95/0.99  
% 2.95/0.99  ------ Debug Options
% 2.95/0.99  
% 2.95/0.99  --dbg_backtrace                         false
% 2.95/0.99  --dbg_dump_prop_clauses                 false
% 2.95/0.99  --dbg_dump_prop_clauses_file            -
% 2.95/0.99  --dbg_out_stat                          false
% 2.95/0.99  ------ Parsing...
% 2.95/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.95/0.99  
% 2.95/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.95/0.99  
% 2.95/0.99  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.95/0.99  
% 2.95/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.95/0.99  ------ Proving...
% 2.95/0.99  ------ Problem Properties 
% 2.95/0.99  
% 2.95/0.99  
% 2.95/0.99  clauses                                 24
% 2.95/0.99  conjectures                             6
% 2.95/0.99  EPR                                     6
% 2.95/0.99  Horn                                    23
% 2.95/0.99  unary                                   11
% 2.95/0.99  binary                                  3
% 2.95/0.99  lits                                    73
% 2.95/0.99  lits eq                                 9
% 2.95/0.99  fd_pure                                 0
% 2.95/0.99  fd_pseudo                               0
% 2.95/0.99  fd_cond                                 1
% 2.95/0.99  fd_pseudo_cond                          1
% 2.95/0.99  AC symbols                              0
% 2.95/0.99  
% 2.95/0.99  ------ Schedule dynamic 5 is on 
% 2.95/0.99  
% 2.95/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.95/0.99  
% 2.95/0.99  
% 2.95/0.99  ------ 
% 2.95/0.99  Current options:
% 2.95/0.99  ------ 
% 2.95/0.99  
% 2.95/0.99  ------ Input Options
% 2.95/0.99  
% 2.95/0.99  --out_options                           all
% 2.95/0.99  --tptp_safe_out                         true
% 2.95/0.99  --problem_path                          ""
% 2.95/0.99  --include_path                          ""
% 2.95/0.99  --clausifier                            res/vclausify_rel
% 2.95/0.99  --clausifier_options                    --mode clausify
% 2.95/0.99  --stdin                                 false
% 2.95/0.99  --stats_out                             all
% 2.95/0.99  
% 2.95/0.99  ------ General Options
% 2.95/0.99  
% 2.95/0.99  --fof                                   false
% 2.95/0.99  --time_out_real                         305.
% 2.95/0.99  --time_out_virtual                      -1.
% 2.95/0.99  --symbol_type_check                     false
% 2.95/0.99  --clausify_out                          false
% 2.95/0.99  --sig_cnt_out                           false
% 2.95/0.99  --trig_cnt_out                          false
% 2.95/0.99  --trig_cnt_out_tolerance                1.
% 2.95/0.99  --trig_cnt_out_sk_spl                   false
% 2.95/0.99  --abstr_cl_out                          false
% 2.95/0.99  
% 2.95/0.99  ------ Global Options
% 2.95/0.99  
% 2.95/0.99  --schedule                              default
% 2.95/0.99  --add_important_lit                     false
% 2.95/0.99  --prop_solver_per_cl                    1000
% 2.95/0.99  --min_unsat_core                        false
% 2.95/0.99  --soft_assumptions                      false
% 2.95/0.99  --soft_lemma_size                       3
% 2.95/0.99  --prop_impl_unit_size                   0
% 2.95/0.99  --prop_impl_unit                        []
% 2.95/0.99  --share_sel_clauses                     true
% 2.95/0.99  --reset_solvers                         false
% 2.95/0.99  --bc_imp_inh                            [conj_cone]
% 2.95/0.99  --conj_cone_tolerance                   3.
% 2.95/0.99  --extra_neg_conj                        none
% 2.95/0.99  --large_theory_mode                     true
% 2.95/0.99  --prolific_symb_bound                   200
% 2.95/0.99  --lt_threshold                          2000
% 2.95/0.99  --clause_weak_htbl                      true
% 2.95/0.99  --gc_record_bc_elim                     false
% 2.95/0.99  
% 2.95/0.99  ------ Preprocessing Options
% 2.95/0.99  
% 2.95/0.99  --preprocessing_flag                    true
% 2.95/0.99  --time_out_prep_mult                    0.1
% 2.95/0.99  --splitting_mode                        input
% 2.95/0.99  --splitting_grd                         true
% 2.95/0.99  --splitting_cvd                         false
% 2.95/0.99  --splitting_cvd_svl                     false
% 2.95/0.99  --splitting_nvd                         32
% 2.95/0.99  --sub_typing                            true
% 2.95/0.99  --prep_gs_sim                           true
% 2.95/0.99  --prep_unflatten                        true
% 2.95/0.99  --prep_res_sim                          true
% 2.95/0.99  --prep_upred                            true
% 2.95/0.99  --prep_sem_filter                       exhaustive
% 2.95/0.99  --prep_sem_filter_out                   false
% 2.95/0.99  --pred_elim                             true
% 2.95/0.99  --res_sim_input                         true
% 2.95/0.99  --eq_ax_congr_red                       true
% 2.95/0.99  --pure_diseq_elim                       true
% 2.95/0.99  --brand_transform                       false
% 2.95/0.99  --non_eq_to_eq                          false
% 2.95/0.99  --prep_def_merge                        true
% 2.95/0.99  --prep_def_merge_prop_impl              false
% 2.95/0.99  --prep_def_merge_mbd                    true
% 2.95/0.99  --prep_def_merge_tr_red                 false
% 2.95/0.99  --prep_def_merge_tr_cl                  false
% 2.95/0.99  --smt_preprocessing                     true
% 2.95/0.99  --smt_ac_axioms                         fast
% 2.95/0.99  --preprocessed_out                      false
% 2.95/0.99  --preprocessed_stats                    false
% 2.95/0.99  
% 2.95/0.99  ------ Abstraction refinement Options
% 2.95/0.99  
% 2.95/0.99  --abstr_ref                             []
% 2.95/0.99  --abstr_ref_prep                        false
% 2.95/0.99  --abstr_ref_until_sat                   false
% 2.95/0.99  --abstr_ref_sig_restrict                funpre
% 2.95/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.95/0.99  --abstr_ref_under                       []
% 2.95/0.99  
% 2.95/0.99  ------ SAT Options
% 2.95/0.99  
% 2.95/0.99  --sat_mode                              false
% 2.95/0.99  --sat_fm_restart_options                ""
% 2.95/0.99  --sat_gr_def                            false
% 2.95/0.99  --sat_epr_types                         true
% 2.95/0.99  --sat_non_cyclic_types                  false
% 2.95/0.99  --sat_finite_models                     false
% 2.95/0.99  --sat_fm_lemmas                         false
% 2.95/0.99  --sat_fm_prep                           false
% 2.95/0.99  --sat_fm_uc_incr                        true
% 2.95/0.99  --sat_out_model                         small
% 2.95/0.99  --sat_out_clauses                       false
% 2.95/0.99  
% 2.95/0.99  ------ QBF Options
% 2.95/0.99  
% 2.95/0.99  --qbf_mode                              false
% 2.95/0.99  --qbf_elim_univ                         false
% 2.95/0.99  --qbf_dom_inst                          none
% 2.95/0.99  --qbf_dom_pre_inst                      false
% 2.95/0.99  --qbf_sk_in                             false
% 2.95/0.99  --qbf_pred_elim                         true
% 2.95/0.99  --qbf_split                             512
% 2.95/0.99  
% 2.95/0.99  ------ BMC1 Options
% 2.95/0.99  
% 2.95/0.99  --bmc1_incremental                      false
% 2.95/0.99  --bmc1_axioms                           reachable_all
% 2.95/0.99  --bmc1_min_bound                        0
% 2.95/0.99  --bmc1_max_bound                        -1
% 2.95/0.99  --bmc1_max_bound_default                -1
% 2.95/0.99  --bmc1_symbol_reachability              true
% 2.95/0.99  --bmc1_property_lemmas                  false
% 2.95/0.99  --bmc1_k_induction                      false
% 2.95/0.99  --bmc1_non_equiv_states                 false
% 2.95/0.99  --bmc1_deadlock                         false
% 2.95/0.99  --bmc1_ucm                              false
% 2.95/0.99  --bmc1_add_unsat_core                   none
% 2.95/0.99  --bmc1_unsat_core_children              false
% 2.95/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.95/0.99  --bmc1_out_stat                         full
% 2.95/0.99  --bmc1_ground_init                      false
% 2.95/0.99  --bmc1_pre_inst_next_state              false
% 2.95/0.99  --bmc1_pre_inst_state                   false
% 2.95/0.99  --bmc1_pre_inst_reach_state             false
% 2.95/0.99  --bmc1_out_unsat_core                   false
% 2.95/0.99  --bmc1_aig_witness_out                  false
% 2.95/0.99  --bmc1_verbose                          false
% 2.95/0.99  --bmc1_dump_clauses_tptp                false
% 2.95/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.95/0.99  --bmc1_dump_file                        -
% 2.95/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.95/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.95/0.99  --bmc1_ucm_extend_mode                  1
% 2.95/0.99  --bmc1_ucm_init_mode                    2
% 2.95/0.99  --bmc1_ucm_cone_mode                    none
% 2.95/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.95/0.99  --bmc1_ucm_relax_model                  4
% 2.95/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.95/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.95/0.99  --bmc1_ucm_layered_model                none
% 2.95/0.99  --bmc1_ucm_max_lemma_size               10
% 2.95/0.99  
% 2.95/0.99  ------ AIG Options
% 2.95/0.99  
% 2.95/0.99  --aig_mode                              false
% 2.95/0.99  
% 2.95/0.99  ------ Instantiation Options
% 2.95/0.99  
% 2.95/0.99  --instantiation_flag                    true
% 2.95/0.99  --inst_sos_flag                         false
% 2.95/0.99  --inst_sos_phase                        true
% 2.95/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.95/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.95/0.99  --inst_lit_sel_side                     none
% 2.95/0.99  --inst_solver_per_active                1400
% 2.95/0.99  --inst_solver_calls_frac                1.
% 2.95/0.99  --inst_passive_queue_type               priority_queues
% 2.95/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.95/0.99  --inst_passive_queues_freq              [25;2]
% 2.95/0.99  --inst_dismatching                      true
% 2.95/0.99  --inst_eager_unprocessed_to_passive     true
% 2.95/0.99  --inst_prop_sim_given                   true
% 2.95/0.99  --inst_prop_sim_new                     false
% 2.95/0.99  --inst_subs_new                         false
% 2.95/0.99  --inst_eq_res_simp                      false
% 2.95/0.99  --inst_subs_given                       false
% 2.95/0.99  --inst_orphan_elimination               true
% 2.95/0.99  --inst_learning_loop_flag               true
% 2.95/0.99  --inst_learning_start                   3000
% 2.95/0.99  --inst_learning_factor                  2
% 2.95/0.99  --inst_start_prop_sim_after_learn       3
% 2.95/0.99  --inst_sel_renew                        solver
% 2.95/0.99  --inst_lit_activity_flag                true
% 2.95/0.99  --inst_restr_to_given                   false
% 2.95/0.99  --inst_activity_threshold               500
% 2.95/0.99  --inst_out_proof                        true
% 2.95/0.99  
% 2.95/0.99  ------ Resolution Options
% 2.95/0.99  
% 2.95/0.99  --resolution_flag                       false
% 2.95/0.99  --res_lit_sel                           adaptive
% 2.95/0.99  --res_lit_sel_side                      none
% 2.95/0.99  --res_ordering                          kbo
% 2.95/0.99  --res_to_prop_solver                    active
% 2.95/0.99  --res_prop_simpl_new                    false
% 2.95/0.99  --res_prop_simpl_given                  true
% 2.95/0.99  --res_passive_queue_type                priority_queues
% 2.95/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.95/0.99  --res_passive_queues_freq               [15;5]
% 2.95/0.99  --res_forward_subs                      full
% 2.95/0.99  --res_backward_subs                     full
% 2.95/0.99  --res_forward_subs_resolution           true
% 2.95/0.99  --res_backward_subs_resolution          true
% 2.95/0.99  --res_orphan_elimination                true
% 2.95/0.99  --res_time_limit                        2.
% 2.95/0.99  --res_out_proof                         true
% 2.95/0.99  
% 2.95/0.99  ------ Superposition Options
% 2.95/0.99  
% 2.95/0.99  --superposition_flag                    true
% 2.95/0.99  --sup_passive_queue_type                priority_queues
% 2.95/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.95/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.95/0.99  --demod_completeness_check              fast
% 2.95/0.99  --demod_use_ground                      true
% 2.95/0.99  --sup_to_prop_solver                    passive
% 2.95/0.99  --sup_prop_simpl_new                    true
% 2.95/0.99  --sup_prop_simpl_given                  true
% 2.95/0.99  --sup_fun_splitting                     false
% 2.95/0.99  --sup_smt_interval                      50000
% 2.95/0.99  
% 2.95/0.99  ------ Superposition Simplification Setup
% 2.95/0.99  
% 2.95/0.99  --sup_indices_passive                   []
% 2.95/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.95/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.95/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.95/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.95/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.95/0.99  --sup_full_bw                           [BwDemod]
% 2.95/0.99  --sup_immed_triv                        [TrivRules]
% 2.95/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.95/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.95/0.99  --sup_immed_bw_main                     []
% 2.95/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.95/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.95/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.95/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.95/0.99  
% 2.95/0.99  ------ Combination Options
% 2.95/0.99  
% 2.95/0.99  --comb_res_mult                         3
% 2.95/0.99  --comb_sup_mult                         2
% 2.95/0.99  --comb_inst_mult                        10
% 2.95/0.99  
% 2.95/0.99  ------ Debug Options
% 2.95/0.99  
% 2.95/0.99  --dbg_backtrace                         false
% 2.95/0.99  --dbg_dump_prop_clauses                 false
% 2.95/0.99  --dbg_dump_prop_clauses_file            -
% 2.95/0.99  --dbg_out_stat                          false
% 2.95/0.99  
% 2.95/0.99  
% 2.95/0.99  
% 2.95/0.99  
% 2.95/0.99  ------ Proving...
% 2.95/0.99  
% 2.95/0.99  
% 2.95/0.99  % SZS status Theorem for theBenchmark.p
% 2.95/0.99  
% 2.95/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.95/0.99  
% 2.95/0.99  fof(f11,axiom,(
% 2.95/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 2.95/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.95/0.99  
% 2.95/0.99  fof(f29,plain,(
% 2.95/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.95/0.99    inference(ennf_transformation,[],[f11])).
% 2.95/0.99  
% 2.95/0.99  fof(f30,plain,(
% 2.95/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.95/0.99    inference(flattening,[],[f29])).
% 2.95/0.99  
% 2.95/0.99  fof(f56,plain,(
% 2.95/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.95/0.99    inference(cnf_transformation,[],[f30])).
% 2.95/0.99  
% 2.95/0.99  fof(f9,axiom,(
% 2.95/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.95/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.95/0.99  
% 2.95/0.99  fof(f25,plain,(
% 2.95/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.95/0.99    inference(ennf_transformation,[],[f9])).
% 2.95/0.99  
% 2.95/0.99  fof(f26,plain,(
% 2.95/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.95/0.99    inference(flattening,[],[f25])).
% 2.95/0.99  
% 2.95/0.99  fof(f37,plain,(
% 2.95/0.99    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.95/0.99    inference(nnf_transformation,[],[f26])).
% 2.95/0.99  
% 2.95/0.99  fof(f51,plain,(
% 2.95/0.99    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.95/0.99    inference(cnf_transformation,[],[f37])).
% 2.95/0.99  
% 2.95/0.99  fof(f16,conjecture,(
% 2.95/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 2.95/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.95/0.99  
% 2.95/0.99  fof(f17,negated_conjecture,(
% 2.95/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 2.95/0.99    inference(negated_conjecture,[],[f16])).
% 2.95/0.99  
% 2.95/0.99  fof(f35,plain,(
% 2.95/0.99    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.95/0.99    inference(ennf_transformation,[],[f17])).
% 2.95/0.99  
% 2.95/0.99  fof(f36,plain,(
% 2.95/0.99    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.95/0.99    inference(flattening,[],[f35])).
% 2.95/0.99  
% 2.95/0.99  fof(f40,plain,(
% 2.95/0.99    ( ! [X2,X0,X1] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((~v2_funct_2(sK3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 2.95/0.99    introduced(choice_axiom,[])).
% 2.95/0.99  
% 2.95/0.99  fof(f39,plain,(
% 2.95/0.99    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 2.95/0.99    introduced(choice_axiom,[])).
% 2.95/0.99  
% 2.95/0.99  fof(f41,plain,(
% 2.95/0.99    ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 2.95/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f36,f40,f39])).
% 2.95/0.99  
% 2.95/0.99  fof(f68,plain,(
% 2.95/0.99    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.95/0.99    inference(cnf_transformation,[],[f41])).
% 2.95/0.99  
% 2.95/0.99  fof(f12,axiom,(
% 2.95/0.99    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 2.95/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.95/0.99  
% 2.95/0.99  fof(f18,plain,(
% 2.95/0.99    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 2.95/0.99    inference(pure_predicate_removal,[],[f12])).
% 2.95/1.00  
% 2.95/1.00  fof(f57,plain,(
% 2.95/1.00    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.95/1.00    inference(cnf_transformation,[],[f18])).
% 2.95/1.00  
% 2.95/1.00  fof(f62,plain,(
% 2.95/1.00    v1_funct_1(sK2)),
% 2.95/1.00    inference(cnf_transformation,[],[f41])).
% 2.95/1.00  
% 2.95/1.00  fof(f64,plain,(
% 2.95/1.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.95/1.00    inference(cnf_transformation,[],[f41])).
% 2.95/1.00  
% 2.95/1.00  fof(f65,plain,(
% 2.95/1.00    v1_funct_1(sK3)),
% 2.95/1.00    inference(cnf_transformation,[],[f41])).
% 2.95/1.00  
% 2.95/1.00  fof(f67,plain,(
% 2.95/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.95/1.00    inference(cnf_transformation,[],[f41])).
% 2.95/1.00  
% 2.95/1.00  fof(f15,axiom,(
% 2.95/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 2.95/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.95/1.00  
% 2.95/1.00  fof(f33,plain,(
% 2.95/1.00    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.95/1.00    inference(ennf_transformation,[],[f15])).
% 2.95/1.00  
% 2.95/1.00  fof(f34,plain,(
% 2.95/1.00    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.95/1.00    inference(flattening,[],[f33])).
% 2.95/1.00  
% 2.95/1.00  fof(f60,plain,(
% 2.95/1.00    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X3) | k1_xboole_0 = X2 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.95/1.00    inference(cnf_transformation,[],[f34])).
% 2.95/1.00  
% 2.95/1.00  fof(f8,axiom,(
% 2.95/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 2.95/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.95/1.00  
% 2.95/1.00  fof(f24,plain,(
% 2.95/1.00    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.95/1.00    inference(ennf_transformation,[],[f8])).
% 2.95/1.00  
% 2.95/1.00  fof(f50,plain,(
% 2.95/1.00    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.95/1.00    inference(cnf_transformation,[],[f24])).
% 2.95/1.00  
% 2.95/1.00  fof(f14,axiom,(
% 2.95/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 2.95/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.95/1.00  
% 2.95/1.00  fof(f31,plain,(
% 2.95/1.00    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.95/1.00    inference(ennf_transformation,[],[f14])).
% 2.95/1.00  
% 2.95/1.00  fof(f32,plain,(
% 2.95/1.00    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.95/1.00    inference(flattening,[],[f31])).
% 2.95/1.00  
% 2.95/1.00  fof(f59,plain,(
% 2.95/1.00    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.95/1.00    inference(cnf_transformation,[],[f32])).
% 2.95/1.00  
% 2.95/1.00  fof(f63,plain,(
% 2.95/1.00    v1_funct_2(sK2,sK0,sK1)),
% 2.95/1.00    inference(cnf_transformation,[],[f41])).
% 2.95/1.00  
% 2.95/1.00  fof(f66,plain,(
% 2.95/1.00    v1_funct_2(sK3,sK1,sK0)),
% 2.95/1.00    inference(cnf_transformation,[],[f41])).
% 2.95/1.00  
% 2.95/1.00  fof(f6,axiom,(
% 2.95/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.95/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.95/1.00  
% 2.95/1.00  fof(f19,plain,(
% 2.95/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 2.95/1.00    inference(pure_predicate_removal,[],[f6])).
% 2.95/1.00  
% 2.95/1.00  fof(f22,plain,(
% 2.95/1.00    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.95/1.00    inference(ennf_transformation,[],[f19])).
% 2.95/1.00  
% 2.95/1.00  fof(f48,plain,(
% 2.95/1.00    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.95/1.00    inference(cnf_transformation,[],[f22])).
% 2.95/1.00  
% 2.95/1.00  fof(f10,axiom,(
% 2.95/1.00    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 2.95/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.95/1.00  
% 2.95/1.00  fof(f27,plain,(
% 2.95/1.00    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.95/1.00    inference(ennf_transformation,[],[f10])).
% 2.95/1.00  
% 2.95/1.00  fof(f28,plain,(
% 2.95/1.00    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.95/1.00    inference(flattening,[],[f27])).
% 2.95/1.00  
% 2.95/1.00  fof(f38,plain,(
% 2.95/1.00    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.95/1.00    inference(nnf_transformation,[],[f28])).
% 2.95/1.00  
% 2.95/1.00  fof(f54,plain,(
% 2.95/1.00    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.95/1.00    inference(cnf_transformation,[],[f38])).
% 2.95/1.00  
% 2.95/1.00  fof(f73,plain,(
% 2.95/1.00    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.95/1.00    inference(equality_resolution,[],[f54])).
% 2.95/1.00  
% 2.95/1.00  fof(f69,plain,(
% 2.95/1.00    ~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)),
% 2.95/1.00    inference(cnf_transformation,[],[f41])).
% 2.95/1.00  
% 2.95/1.00  fof(f3,axiom,(
% 2.95/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.95/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.95/1.00  
% 2.95/1.00  fof(f21,plain,(
% 2.95/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.95/1.00    inference(ennf_transformation,[],[f3])).
% 2.95/1.00  
% 2.95/1.00  fof(f44,plain,(
% 2.95/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.95/1.00    inference(cnf_transformation,[],[f21])).
% 2.95/1.00  
% 2.95/1.00  fof(f4,axiom,(
% 2.95/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.95/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.95/1.00  
% 2.95/1.00  fof(f45,plain,(
% 2.95/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.95/1.00    inference(cnf_transformation,[],[f4])).
% 2.95/1.00  
% 2.95/1.00  fof(f7,axiom,(
% 2.95/1.00    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 2.95/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.95/1.00  
% 2.95/1.00  fof(f23,plain,(
% 2.95/1.00    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 2.95/1.00    inference(ennf_transformation,[],[f7])).
% 2.95/1.00  
% 2.95/1.00  fof(f49,plain,(
% 2.95/1.00    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 2.95/1.00    inference(cnf_transformation,[],[f23])).
% 2.95/1.00  
% 2.95/1.00  fof(f2,axiom,(
% 2.95/1.00    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 2.95/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.95/1.00  
% 2.95/1.00  fof(f20,plain,(
% 2.95/1.00    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 2.95/1.00    inference(ennf_transformation,[],[f2])).
% 2.95/1.00  
% 2.95/1.00  fof(f43,plain,(
% 2.95/1.00    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 2.95/1.00    inference(cnf_transformation,[],[f20])).
% 2.95/1.00  
% 2.95/1.00  fof(f1,axiom,(
% 2.95/1.00    v1_xboole_0(k1_xboole_0)),
% 2.95/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.95/1.00  
% 2.95/1.00  fof(f42,plain,(
% 2.95/1.00    v1_xboole_0(k1_xboole_0)),
% 2.95/1.00    inference(cnf_transformation,[],[f1])).
% 2.95/1.00  
% 2.95/1.00  fof(f5,axiom,(
% 2.95/1.00    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.95/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.95/1.00  
% 2.95/1.00  fof(f47,plain,(
% 2.95/1.00    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 2.95/1.00    inference(cnf_transformation,[],[f5])).
% 2.95/1.00  
% 2.95/1.00  fof(f13,axiom,(
% 2.95/1.00    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.95/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.95/1.00  
% 2.95/1.00  fof(f58,plain,(
% 2.95/1.00    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.95/1.00    inference(cnf_transformation,[],[f13])).
% 2.95/1.00  
% 2.95/1.00  fof(f70,plain,(
% 2.95/1.00    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 2.95/1.00    inference(definition_unfolding,[],[f47,f58])).
% 2.95/1.00  
% 2.95/1.00  cnf(c_679,plain,
% 2.95/1.00      ( ~ v2_funct_1(X0_48) | v2_funct_1(X1_48) | X1_48 != X0_48 ),
% 2.95/1.00      theory(equality) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_4285,plain,
% 2.95/1.00      ( ~ v2_funct_1(X0_48) | v2_funct_1(sK2) | sK2 != X0_48 ),
% 2.95/1.00      inference(instantiation,[status(thm)],[c_679]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_4287,plain,
% 2.95/1.00      ( v2_funct_1(sK2) | ~ v2_funct_1(sK0) | sK2 != sK0 ),
% 2.95/1.00      inference(instantiation,[status(thm)],[c_4285]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_13,plain,
% 2.95/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.95/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 2.95/1.00      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 2.95/1.00      | ~ v1_funct_1(X0)
% 2.95/1.00      | ~ v1_funct_1(X3) ),
% 2.95/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_658,plain,
% 2.95/1.00      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
% 2.95/1.00      | ~ m1_subset_1(X3_48,k1_zfmisc_1(k2_zfmisc_1(X4_48,X5_48)))
% 2.95/1.00      | m1_subset_1(k1_partfun1(X4_48,X5_48,X1_48,X2_48,X3_48,X0_48),k1_zfmisc_1(k2_zfmisc_1(X4_48,X2_48)))
% 2.95/1.00      | ~ v1_funct_1(X0_48)
% 2.95/1.00      | ~ v1_funct_1(X3_48) ),
% 2.95/1.00      inference(subtyping,[status(esa)],[c_13]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_1138,plain,
% 2.95/1.00      ( m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48))) != iProver_top
% 2.95/1.00      | m1_subset_1(X3_48,k1_zfmisc_1(k2_zfmisc_1(X4_48,X5_48))) != iProver_top
% 2.95/1.00      | m1_subset_1(k1_partfun1(X4_48,X5_48,X1_48,X2_48,X3_48,X0_48),k1_zfmisc_1(k2_zfmisc_1(X4_48,X2_48))) = iProver_top
% 2.95/1.00      | v1_funct_1(X0_48) != iProver_top
% 2.95/1.00      | v1_funct_1(X3_48) != iProver_top ),
% 2.95/1.00      inference(predicate_to_equality,[status(thm)],[c_658]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_10,plain,
% 2.95/1.00      ( ~ r2_relset_1(X0,X1,X2,X3)
% 2.95/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.95/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.95/1.00      | X3 = X2 ),
% 2.95/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_20,negated_conjecture,
% 2.95/1.00      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 2.95/1.00      inference(cnf_transformation,[],[f68]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_417,plain,
% 2.95/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.95/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.95/1.00      | X3 = X0
% 2.95/1.00      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 2.95/1.00      | k6_partfun1(sK0) != X3
% 2.95/1.00      | sK0 != X2
% 2.95/1.00      | sK0 != X1 ),
% 2.95/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_20]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_418,plain,
% 2.95/1.00      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.95/1.00      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.95/1.00      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 2.95/1.00      inference(unflattening,[status(thm)],[c_417]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_15,plain,
% 2.95/1.00      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 2.95/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_45,plain,
% 2.95/1.00      ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 2.95/1.00      inference(instantiation,[status(thm)],[c_15]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_420,plain,
% 2.95/1.00      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.95/1.00      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 2.95/1.00      inference(global_propositional_subsumption,
% 2.95/1.00                [status(thm)],
% 2.95/1.00                [c_418,c_45]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_645,plain,
% 2.95/1.00      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.95/1.00      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 2.95/1.00      inference(subtyping,[status(esa)],[c_420]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_1152,plain,
% 2.95/1.00      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 2.95/1.00      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 2.95/1.00      inference(predicate_to_equality,[status(thm)],[c_645]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_2107,plain,
% 2.95/1.00      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
% 2.95/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.95/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.95/1.00      | v1_funct_1(sK2) != iProver_top
% 2.95/1.00      | v1_funct_1(sK3) != iProver_top ),
% 2.95/1.00      inference(superposition,[status(thm)],[c_1138,c_1152]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_26,negated_conjecture,
% 2.95/1.00      ( v1_funct_1(sK2) ),
% 2.95/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_27,plain,
% 2.95/1.00      ( v1_funct_1(sK2) = iProver_top ),
% 2.95/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_24,negated_conjecture,
% 2.95/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.95/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_29,plain,
% 2.95/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.95/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_23,negated_conjecture,
% 2.95/1.00      ( v1_funct_1(sK3) ),
% 2.95/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_30,plain,
% 2.95/1.00      ( v1_funct_1(sK3) = iProver_top ),
% 2.95/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_21,negated_conjecture,
% 2.95/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 2.95/1.00      inference(cnf_transformation,[],[f67]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_32,plain,
% 2.95/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 2.95/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_2359,plain,
% 2.95/1.00      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
% 2.95/1.00      inference(global_propositional_subsumption,
% 2.95/1.00                [status(thm)],
% 2.95/1.00                [c_2107,c_27,c_29,c_30,c_32]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_18,plain,
% 2.95/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.95/1.00      | ~ v1_funct_2(X3,X2,X4)
% 2.95/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.95/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
% 2.95/1.00      | ~ v1_funct_1(X3)
% 2.95/1.00      | ~ v1_funct_1(X0)
% 2.95/1.00      | v2_funct_1(X0)
% 2.95/1.00      | ~ v2_funct_1(k1_partfun1(X1,X2,X2,X4,X0,X3))
% 2.95/1.00      | k1_xboole_0 = X4 ),
% 2.95/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_654,plain,
% 2.95/1.00      ( ~ v1_funct_2(X0_48,X1_48,X2_48)
% 2.95/1.00      | ~ v1_funct_2(X3_48,X2_48,X4_48)
% 2.95/1.00      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
% 2.95/1.00      | ~ m1_subset_1(X3_48,k1_zfmisc_1(k2_zfmisc_1(X2_48,X4_48)))
% 2.95/1.00      | ~ v1_funct_1(X0_48)
% 2.95/1.00      | ~ v1_funct_1(X3_48)
% 2.95/1.00      | v2_funct_1(X0_48)
% 2.95/1.00      | ~ v2_funct_1(k1_partfun1(X1_48,X2_48,X2_48,X4_48,X0_48,X3_48))
% 2.95/1.00      | k1_xboole_0 = X4_48 ),
% 2.95/1.00      inference(subtyping,[status(esa)],[c_18]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_1142,plain,
% 2.95/1.00      ( k1_xboole_0 = X0_48
% 2.95/1.00      | v1_funct_2(X1_48,X2_48,X3_48) != iProver_top
% 2.95/1.00      | v1_funct_2(X4_48,X3_48,X0_48) != iProver_top
% 2.95/1.00      | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_48,X3_48))) != iProver_top
% 2.95/1.00      | m1_subset_1(X4_48,k1_zfmisc_1(k2_zfmisc_1(X3_48,X0_48))) != iProver_top
% 2.95/1.00      | v1_funct_1(X1_48) != iProver_top
% 2.95/1.00      | v1_funct_1(X4_48) != iProver_top
% 2.95/1.00      | v2_funct_1(X1_48) = iProver_top
% 2.95/1.00      | v2_funct_1(k1_partfun1(X2_48,X3_48,X3_48,X0_48,X1_48,X4_48)) != iProver_top ),
% 2.95/1.00      inference(predicate_to_equality,[status(thm)],[c_654]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_2893,plain,
% 2.95/1.00      ( sK0 = k1_xboole_0
% 2.95/1.00      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 2.95/1.00      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 2.95/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.95/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.95/1.00      | v1_funct_1(sK2) != iProver_top
% 2.95/1.00      | v1_funct_1(sK3) != iProver_top
% 2.95/1.00      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 2.95/1.00      | v2_funct_1(sK2) = iProver_top ),
% 2.95/1.00      inference(superposition,[status(thm)],[c_2359,c_1142]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_653,negated_conjecture,
% 2.95/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 2.95/1.00      inference(subtyping,[status(esa)],[c_21]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_1143,plain,
% 2.95/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 2.95/1.00      inference(predicate_to_equality,[status(thm)],[c_653]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_8,plain,
% 2.95/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.95/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.95/1.00      inference(cnf_transformation,[],[f50]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_659,plain,
% 2.95/1.00      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
% 2.95/1.00      | k2_relset_1(X1_48,X2_48,X0_48) = k2_relat_1(X0_48) ),
% 2.95/1.00      inference(subtyping,[status(esa)],[c_8]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_1137,plain,
% 2.95/1.00      ( k2_relset_1(X0_48,X1_48,X2_48) = k2_relat_1(X2_48)
% 2.95/1.00      | m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top ),
% 2.95/1.00      inference(predicate_to_equality,[status(thm)],[c_659]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_2069,plain,
% 2.95/1.00      ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 2.95/1.00      inference(superposition,[status(thm)],[c_1143,c_1137]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_16,plain,
% 2.95/1.00      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 2.95/1.00      | ~ v1_funct_2(X2,X0,X1)
% 2.95/1.00      | ~ v1_funct_2(X3,X1,X0)
% 2.95/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.95/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.95/1.00      | ~ v1_funct_1(X2)
% 2.95/1.00      | ~ v1_funct_1(X3)
% 2.95/1.00      | k2_relset_1(X1,X0,X3) = X0 ),
% 2.95/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_431,plain,
% 2.95/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.95/1.00      | ~ v1_funct_2(X3,X2,X1)
% 2.95/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.95/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.95/1.00      | ~ v1_funct_1(X3)
% 2.95/1.00      | ~ v1_funct_1(X0)
% 2.95/1.00      | k1_partfun1(X1,X2,X2,X1,X0,X3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 2.95/1.00      | k2_relset_1(X2,X1,X3) = X1
% 2.95/1.00      | k6_partfun1(X1) != k6_partfun1(sK0)
% 2.95/1.00      | sK0 != X1 ),
% 2.95/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_20]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_432,plain,
% 2.95/1.00      ( ~ v1_funct_2(X0,X1,sK0)
% 2.95/1.00      | ~ v1_funct_2(X2,sK0,X1)
% 2.95/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 2.95/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 2.95/1.00      | ~ v1_funct_1(X2)
% 2.95/1.00      | ~ v1_funct_1(X0)
% 2.95/1.00      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 2.95/1.00      | k2_relset_1(X1,sK0,X0) = sK0
% 2.95/1.00      | k6_partfun1(sK0) != k6_partfun1(sK0) ),
% 2.95/1.00      inference(unflattening,[status(thm)],[c_431]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_509,plain,
% 2.95/1.00      ( ~ v1_funct_2(X0,X1,sK0)
% 2.95/1.00      | ~ v1_funct_2(X2,sK0,X1)
% 2.95/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 2.95/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 2.95/1.00      | ~ v1_funct_1(X0)
% 2.95/1.00      | ~ v1_funct_1(X2)
% 2.95/1.00      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 2.95/1.00      | k2_relset_1(X1,sK0,X0) = sK0 ),
% 2.95/1.00      inference(equality_resolution_simp,[status(thm)],[c_432]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_644,plain,
% 2.95/1.00      ( ~ v1_funct_2(X0_48,X1_48,sK0)
% 2.95/1.00      | ~ v1_funct_2(X2_48,sK0,X1_48)
% 2.95/1.00      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,sK0)))
% 2.95/1.00      | ~ m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(sK0,X1_48)))
% 2.95/1.00      | ~ v1_funct_1(X0_48)
% 2.95/1.00      | ~ v1_funct_1(X2_48)
% 2.95/1.00      | k1_partfun1(sK0,X1_48,X1_48,sK0,X2_48,X0_48) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 2.95/1.00      | k2_relset_1(X1_48,sK0,X0_48) = sK0 ),
% 2.95/1.00      inference(subtyping,[status(esa)],[c_509]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_1153,plain,
% 2.95/1.00      ( k1_partfun1(sK0,X0_48,X0_48,sK0,X1_48,X2_48) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 2.95/1.00      | k2_relset_1(X0_48,sK0,X2_48) = sK0
% 2.95/1.00      | v1_funct_2(X2_48,X0_48,sK0) != iProver_top
% 2.95/1.00      | v1_funct_2(X1_48,sK0,X0_48) != iProver_top
% 2.95/1.00      | m1_subset_1(X2_48,k1_zfmisc_1(k2_zfmisc_1(X0_48,sK0))) != iProver_top
% 2.95/1.00      | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_48))) != iProver_top
% 2.95/1.00      | v1_funct_1(X2_48) != iProver_top
% 2.95/1.00      | v1_funct_1(X1_48) != iProver_top ),
% 2.95/1.00      inference(predicate_to_equality,[status(thm)],[c_644]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_1883,plain,
% 2.95/1.00      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 2.95/1.00      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 2.95/1.00      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 2.95/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.95/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.95/1.00      | v1_funct_1(sK2) != iProver_top
% 2.95/1.00      | v1_funct_1(sK3) != iProver_top ),
% 2.95/1.00      inference(equality_resolution,[status(thm)],[c_1153]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_25,negated_conjecture,
% 2.95/1.00      ( v1_funct_2(sK2,sK0,sK1) ),
% 2.95/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_28,plain,
% 2.95/1.00      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 2.95/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_22,negated_conjecture,
% 2.95/1.00      ( v1_funct_2(sK3,sK1,sK0) ),
% 2.95/1.00      inference(cnf_transformation,[],[f66]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_31,plain,
% 2.95/1.00      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 2.95/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_1886,plain,
% 2.95/1.00      ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 2.95/1.00      inference(global_propositional_subsumption,
% 2.95/1.00                [status(thm)],
% 2.95/1.00                [c_1883,c_27,c_28,c_29,c_30,c_31,c_32]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_2077,plain,
% 2.95/1.00      ( k2_relat_1(sK3) = sK0 ),
% 2.95/1.00      inference(light_normalisation,[status(thm)],[c_2069,c_1886]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_6,plain,
% 2.95/1.00      ( v5_relat_1(X0,X1)
% 2.95/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.95/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_11,plain,
% 2.95/1.00      ( v2_funct_2(X0,k2_relat_1(X0))
% 2.95/1.00      | ~ v5_relat_1(X0,k2_relat_1(X0))
% 2.95/1.00      | ~ v1_relat_1(X0) ),
% 2.95/1.00      inference(cnf_transformation,[],[f73]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_19,negated_conjecture,
% 2.95/1.00      ( ~ v2_funct_2(sK3,sK0) | ~ v2_funct_1(sK2) ),
% 2.95/1.00      inference(cnf_transformation,[],[f69]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_336,plain,
% 2.95/1.00      ( ~ v5_relat_1(X0,k2_relat_1(X0))
% 2.95/1.00      | ~ v2_funct_1(sK2)
% 2.95/1.00      | ~ v1_relat_1(X0)
% 2.95/1.00      | k2_relat_1(X0) != sK0
% 2.95/1.00      | sK3 != X0 ),
% 2.95/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_19]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_337,plain,
% 2.95/1.00      ( ~ v5_relat_1(sK3,k2_relat_1(sK3))
% 2.95/1.00      | ~ v2_funct_1(sK2)
% 2.95/1.00      | ~ v1_relat_1(sK3)
% 2.95/1.00      | k2_relat_1(sK3) != sK0 ),
% 2.95/1.00      inference(unflattening,[status(thm)],[c_336]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_357,plain,
% 2.95/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.95/1.00      | ~ v2_funct_1(sK2)
% 2.95/1.00      | ~ v1_relat_1(sK3)
% 2.95/1.00      | k2_relat_1(sK3) != X2
% 2.95/1.00      | k2_relat_1(sK3) != sK0
% 2.95/1.00      | sK3 != X0 ),
% 2.95/1.00      inference(resolution_lifted,[status(thm)],[c_6,c_337]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_358,plain,
% 2.95/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3))))
% 2.95/1.00      | ~ v2_funct_1(sK2)
% 2.95/1.00      | ~ v1_relat_1(sK3)
% 2.95/1.00      | k2_relat_1(sK3) != sK0 ),
% 2.95/1.00      inference(unflattening,[status(thm)],[c_357]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_647,plain,
% 2.95/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_48,k2_relat_1(sK3))))
% 2.95/1.00      | ~ v2_funct_1(sK2)
% 2.95/1.00      | ~ v1_relat_1(sK3)
% 2.95/1.00      | k2_relat_1(sK3) != sK0 ),
% 2.95/1.00      inference(subtyping,[status(esa)],[c_358]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_667,plain,
% 2.95/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_48,k2_relat_1(sK3))))
% 2.95/1.00      | ~ sP0_iProver_split ),
% 2.95/1.00      inference(splitting,
% 2.95/1.00                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.95/1.00                [c_647]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_1150,plain,
% 2.95/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_48,k2_relat_1(sK3)))) != iProver_top
% 2.95/1.00      | sP0_iProver_split != iProver_top ),
% 2.95/1.00      inference(predicate_to_equality,[status(thm)],[c_667]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_2290,plain,
% 2.95/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_48,sK0))) != iProver_top
% 2.95/1.00      | sP0_iProver_split != iProver_top ),
% 2.95/1.00      inference(demodulation,[status(thm)],[c_2077,c_1150]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_2404,plain,
% 2.95/1.00      ( sP0_iProver_split != iProver_top ),
% 2.95/1.00      inference(superposition,[status(thm)],[c_1143,c_2290]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_2405,plain,
% 2.95/1.00      ( ~ sP0_iProver_split ),
% 2.95/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_2404]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_668,plain,
% 2.95/1.00      ( ~ v2_funct_1(sK2)
% 2.95/1.00      | ~ v1_relat_1(sK3)
% 2.95/1.00      | sP0_iProver_split
% 2.95/1.00      | k2_relat_1(sK3) != sK0 ),
% 2.95/1.00      inference(splitting,
% 2.95/1.00                [splitting(split),new_symbols(definition,[])],
% 2.95/1.00                [c_647]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_1149,plain,
% 2.95/1.00      ( k2_relat_1(sK3) != sK0
% 2.95/1.00      | v2_funct_1(sK2) != iProver_top
% 2.95/1.00      | v1_relat_1(sK3) != iProver_top
% 2.95/1.00      | sP0_iProver_split = iProver_top ),
% 2.95/1.00      inference(predicate_to_equality,[status(thm)],[c_668]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_723,plain,
% 2.95/1.00      ( k2_relat_1(sK3) != sK0
% 2.95/1.00      | v2_funct_1(sK2) != iProver_top
% 2.95/1.00      | v1_relat_1(sK3) != iProver_top
% 2.95/1.00      | sP0_iProver_split = iProver_top ),
% 2.95/1.00      inference(predicate_to_equality,[status(thm)],[c_668]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_2,plain,
% 2.95/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.95/1.00      | ~ v1_relat_1(X1)
% 2.95/1.00      | v1_relat_1(X0) ),
% 2.95/1.00      inference(cnf_transformation,[],[f44]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_664,plain,
% 2.95/1.00      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(X1_48))
% 2.95/1.00      | ~ v1_relat_1(X1_48)
% 2.95/1.00      | v1_relat_1(X0_48) ),
% 2.95/1.00      inference(subtyping,[status(esa)],[c_2]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_1132,plain,
% 2.95/1.00      ( m1_subset_1(X0_48,k1_zfmisc_1(X1_48)) != iProver_top
% 2.95/1.00      | v1_relat_1(X1_48) != iProver_top
% 2.95/1.00      | v1_relat_1(X0_48) = iProver_top ),
% 2.95/1.00      inference(predicate_to_equality,[status(thm)],[c_664]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_1592,plain,
% 2.95/1.00      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 2.95/1.00      | v1_relat_1(sK3) = iProver_top ),
% 2.95/1.00      inference(superposition,[status(thm)],[c_1143,c_1132]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_3,plain,
% 2.95/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.95/1.00      inference(cnf_transformation,[],[f45]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_663,plain,
% 2.95/1.00      ( v1_relat_1(k2_zfmisc_1(X0_48,X1_48)) ),
% 2.95/1.00      inference(subtyping,[status(esa)],[c_3]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_1133,plain,
% 2.95/1.00      ( v1_relat_1(k2_zfmisc_1(X0_48,X1_48)) = iProver_top ),
% 2.95/1.00      inference(predicate_to_equality,[status(thm)],[c_663]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_1749,plain,
% 2.95/1.00      ( v1_relat_1(sK3) = iProver_top ),
% 2.95/1.00      inference(forward_subsumption_resolution,
% 2.95/1.00                [status(thm)],
% 2.95/1.00                [c_1592,c_1133]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_1829,plain,
% 2.95/1.00      ( v2_funct_1(sK2) != iProver_top
% 2.95/1.00      | k2_relat_1(sK3) != sK0
% 2.95/1.00      | sP0_iProver_split = iProver_top ),
% 2.95/1.00      inference(global_propositional_subsumption,
% 2.95/1.00                [status(thm)],
% 2.95/1.00                [c_1149,c_723,c_1749]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_1830,plain,
% 2.95/1.00      ( k2_relat_1(sK3) != sK0
% 2.95/1.00      | v2_funct_1(sK2) != iProver_top
% 2.95/1.00      | sP0_iProver_split = iProver_top ),
% 2.95/1.00      inference(renaming,[status(thm)],[c_1829]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_2289,plain,
% 2.95/1.00      ( sK0 != sK0
% 2.95/1.00      | v2_funct_1(sK2) != iProver_top
% 2.95/1.00      | sP0_iProver_split = iProver_top ),
% 2.95/1.00      inference(demodulation,[status(thm)],[c_2077,c_1830]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_2295,plain,
% 2.95/1.00      ( v2_funct_1(sK2) != iProver_top
% 2.95/1.00      | sP0_iProver_split = iProver_top ),
% 2.95/1.00      inference(equality_resolution_simp,[status(thm)],[c_2289]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_656,plain,
% 2.95/1.00      ( m1_subset_1(k6_partfun1(X0_48),k1_zfmisc_1(k2_zfmisc_1(X0_48,X0_48))) ),
% 2.95/1.00      inference(subtyping,[status(esa)],[c_15]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_1140,plain,
% 2.95/1.00      ( m1_subset_1(k6_partfun1(X0_48),k1_zfmisc_1(k2_zfmisc_1(X0_48,X0_48))) = iProver_top ),
% 2.95/1.00      inference(predicate_to_equality,[status(thm)],[c_656]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_7,plain,
% 2.95/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.95/1.00      | ~ v1_xboole_0(X1)
% 2.95/1.00      | v1_xboole_0(X0) ),
% 2.95/1.00      inference(cnf_transformation,[],[f49]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_660,plain,
% 2.95/1.00      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48)))
% 2.95/1.00      | ~ v1_xboole_0(X1_48)
% 2.95/1.00      | v1_xboole_0(X0_48) ),
% 2.95/1.00      inference(subtyping,[status(esa)],[c_7]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_1136,plain,
% 2.95/1.00      ( m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X1_48,X2_48))) != iProver_top
% 2.95/1.00      | v1_xboole_0(X1_48) != iProver_top
% 2.95/1.00      | v1_xboole_0(X0_48) = iProver_top ),
% 2.95/1.00      inference(predicate_to_equality,[status(thm)],[c_660]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_1989,plain,
% 2.95/1.00      ( v1_xboole_0(X0_48) != iProver_top
% 2.95/1.00      | v1_xboole_0(k6_partfun1(X0_48)) = iProver_top ),
% 2.95/1.00      inference(superposition,[status(thm)],[c_1140,c_1136]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_2004,plain,
% 2.95/1.00      ( ~ v1_xboole_0(X0_48) | v1_xboole_0(k6_partfun1(X0_48)) ),
% 2.95/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1989]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_2006,plain,
% 2.95/1.00      ( v1_xboole_0(k6_partfun1(sK0)) | ~ v1_xboole_0(sK0) ),
% 2.95/1.00      inference(instantiation,[status(thm)],[c_2004]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_650,negated_conjecture,
% 2.95/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.95/1.00      inference(subtyping,[status(esa)],[c_24]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_1146,plain,
% 2.95/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.95/1.00      inference(predicate_to_equality,[status(thm)],[c_650]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_1988,plain,
% 2.95/1.00      ( v1_xboole_0(sK2) = iProver_top
% 2.95/1.00      | v1_xboole_0(sK0) != iProver_top ),
% 2.95/1.00      inference(superposition,[status(thm)],[c_1146,c_1136]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_2003,plain,
% 2.95/1.00      ( v1_xboole_0(sK2) | ~ v1_xboole_0(sK0) ),
% 2.95/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1988]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_1831,plain,
% 2.95/1.00      ( ~ v2_funct_1(sK2) | sP0_iProver_split | k2_relat_1(sK3) != sK0 ),
% 2.95/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1830]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_1,plain,
% 2.95/1.00      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X1 = X0 ),
% 2.95/1.00      inference(cnf_transformation,[],[f43]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_665,plain,
% 2.95/1.00      ( ~ v1_xboole_0(X0_48) | ~ v1_xboole_0(X1_48) | X1_48 = X0_48 ),
% 2.95/1.00      inference(subtyping,[status(esa)],[c_1]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_1788,plain,
% 2.95/1.00      ( ~ v1_xboole_0(X0_48)
% 2.95/1.00      | ~ v1_xboole_0(k6_partfun1(X1_48))
% 2.95/1.00      | X0_48 = k6_partfun1(X1_48) ),
% 2.95/1.00      inference(instantiation,[status(thm)],[c_665]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_1790,plain,
% 2.95/1.00      ( ~ v1_xboole_0(k6_partfun1(sK0))
% 2.95/1.00      | ~ v1_xboole_0(sK0)
% 2.95/1.00      | sK0 = k6_partfun1(sK0) ),
% 2.95/1.00      inference(instantiation,[status(thm)],[c_1788]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_1759,plain,
% 2.95/1.00      ( ~ v1_xboole_0(X0_48) | ~ v1_xboole_0(sK2) | sK2 = X0_48 ),
% 2.95/1.00      inference(instantiation,[status(thm)],[c_665]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_1761,plain,
% 2.95/1.00      ( ~ v1_xboole_0(sK2) | ~ v1_xboole_0(sK0) | sK2 = sK0 ),
% 2.95/1.00      inference(instantiation,[status(thm)],[c_1759]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_673,plain,
% 2.95/1.00      ( ~ v1_xboole_0(X0_48) | v1_xboole_0(X1_48) | X1_48 != X0_48 ),
% 2.95/1.00      theory(equality) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_1492,plain,
% 2.95/1.00      ( v1_xboole_0(X0_48)
% 2.95/1.00      | ~ v1_xboole_0(k1_xboole_0)
% 2.95/1.00      | X0_48 != k1_xboole_0 ),
% 2.95/1.00      inference(instantiation,[status(thm)],[c_673]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_1494,plain,
% 2.95/1.00      ( v1_xboole_0(sK0)
% 2.95/1.00      | ~ v1_xboole_0(k1_xboole_0)
% 2.95/1.00      | sK0 != k1_xboole_0 ),
% 2.95/1.00      inference(instantiation,[status(thm)],[c_1492]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_1378,plain,
% 2.95/1.00      ( v2_funct_1(X0_48)
% 2.95/1.00      | ~ v2_funct_1(k6_partfun1(X1_48))
% 2.95/1.00      | X0_48 != k6_partfun1(X1_48) ),
% 2.95/1.00      inference(instantiation,[status(thm)],[c_679]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_1380,plain,
% 2.95/1.00      ( ~ v2_funct_1(k6_partfun1(sK0))
% 2.95/1.00      | v2_funct_1(sK0)
% 2.95/1.00      | sK0 != k6_partfun1(sK0) ),
% 2.95/1.00      inference(instantiation,[status(thm)],[c_1378]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_0,plain,
% 2.95/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 2.95/1.00      inference(cnf_transformation,[],[f42]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_4,plain,
% 2.95/1.00      ( v2_funct_1(k6_partfun1(X0)) ),
% 2.95/1.00      inference(cnf_transformation,[],[f70]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_75,plain,
% 2.95/1.00      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 2.95/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_77,plain,
% 2.95/1.00      ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
% 2.95/1.00      inference(instantiation,[status(thm)],[c_75]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(c_76,plain,
% 2.95/1.00      ( v2_funct_1(k6_partfun1(sK0)) ),
% 2.95/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 2.95/1.00  
% 2.95/1.00  cnf(contradiction,plain,
% 2.95/1.00      ( $false ),
% 2.95/1.00      inference(minisat,
% 2.95/1.00                [status(thm)],
% 2.95/1.00                [c_4287,c_2893,c_2405,c_2404,c_2295,c_2077,c_2006,c_2003,
% 2.95/1.00                 c_1831,c_1790,c_1761,c_1494,c_1380,c_0,c_77,c_76,c_32,
% 2.95/1.00                 c_31,c_30,c_29,c_28,c_27]) ).
% 2.95/1.00  
% 2.95/1.00  
% 2.95/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.95/1.00  
% 2.95/1.00  ------                               Statistics
% 2.95/1.00  
% 2.95/1.00  ------ General
% 2.95/1.00  
% 2.95/1.00  abstr_ref_over_cycles:                  0
% 2.95/1.00  abstr_ref_under_cycles:                 0
% 2.95/1.00  gc_basic_clause_elim:                   0
% 2.95/1.00  forced_gc_time:                         0
% 2.95/1.00  parsing_time:                           0.018
% 2.95/1.00  unif_index_cands_time:                  0.
% 2.95/1.00  unif_index_add_time:                    0.
% 2.95/1.00  orderings_time:                         0.
% 2.95/1.00  out_proof_time:                         0.012
% 2.95/1.00  total_time:                             0.189
% 2.95/1.00  num_of_symbols:                         54
% 2.95/1.00  num_of_terms:                           6390
% 2.95/1.00  
% 2.95/1.00  ------ Preprocessing
% 2.95/1.00  
% 2.95/1.00  num_of_splits:                          1
% 2.95/1.00  num_of_split_atoms:                     1
% 2.95/1.00  num_of_reused_defs:                     0
% 2.95/1.00  num_eq_ax_congr_red:                    9
% 2.95/1.00  num_of_sem_filtered_clauses:            1
% 2.95/1.00  num_of_subtypes:                        2
% 2.95/1.00  monotx_restored_types:                  1
% 2.95/1.00  sat_num_of_epr_types:                   0
% 2.95/1.00  sat_num_of_non_cyclic_types:            0
% 2.95/1.00  sat_guarded_non_collapsed_types:        1
% 2.95/1.00  num_pure_diseq_elim:                    0
% 2.95/1.00  simp_replaced_by:                       0
% 2.95/1.00  res_preprocessed:                       129
% 2.95/1.00  prep_upred:                             0
% 2.95/1.00  prep_unflattend:                        19
% 2.95/1.00  smt_new_axioms:                         0
% 2.95/1.00  pred_elim_cands:                        6
% 2.95/1.00  pred_elim:                              3
% 2.95/1.00  pred_elim_cl:                           4
% 2.95/1.00  pred_elim_cycles:                       6
% 2.95/1.00  merged_defs:                            0
% 2.95/1.00  merged_defs_ncl:                        0
% 2.95/1.00  bin_hyper_res:                          0
% 2.95/1.00  prep_cycles:                            4
% 2.95/1.00  pred_elim_time:                         0.006
% 2.95/1.00  splitting_time:                         0.
% 2.95/1.00  sem_filter_time:                        0.
% 2.95/1.00  monotx_time:                            0.001
% 2.95/1.00  subtype_inf_time:                       0.001
% 2.95/1.00  
% 2.95/1.00  ------ Problem properties
% 2.95/1.00  
% 2.95/1.00  clauses:                                24
% 2.95/1.00  conjectures:                            6
% 2.95/1.00  epr:                                    6
% 2.95/1.00  horn:                                   23
% 2.95/1.00  ground:                                 9
% 2.95/1.00  unary:                                  11
% 2.95/1.00  binary:                                 3
% 2.95/1.00  lits:                                   73
% 2.95/1.00  lits_eq:                                9
% 2.95/1.00  fd_pure:                                0
% 2.95/1.00  fd_pseudo:                              0
% 2.95/1.00  fd_cond:                                1
% 2.95/1.00  fd_pseudo_cond:                         1
% 2.95/1.00  ac_symbols:                             0
% 2.95/1.00  
% 2.95/1.00  ------ Propositional Solver
% 2.95/1.00  
% 2.95/1.00  prop_solver_calls:                      28
% 2.95/1.00  prop_fast_solver_calls:                 1002
% 2.95/1.00  smt_solver_calls:                       0
% 2.95/1.00  smt_fast_solver_calls:                  0
% 2.95/1.00  prop_num_of_clauses:                    1668
% 2.95/1.00  prop_preprocess_simplified:             5185
% 2.95/1.00  prop_fo_subsumed:                       31
% 2.95/1.00  prop_solver_time:                       0.
% 2.95/1.00  smt_solver_time:                        0.
% 2.95/1.00  smt_fast_solver_time:                   0.
% 2.95/1.00  prop_fast_solver_time:                  0.
% 2.95/1.00  prop_unsat_core_time:                   0.
% 2.95/1.00  
% 2.95/1.00  ------ QBF
% 2.95/1.00  
% 2.95/1.00  qbf_q_res:                              0
% 2.95/1.00  qbf_num_tautologies:                    0
% 2.95/1.00  qbf_prep_cycles:                        0
% 2.95/1.00  
% 2.95/1.00  ------ BMC1
% 2.95/1.00  
% 2.95/1.00  bmc1_current_bound:                     -1
% 2.95/1.00  bmc1_last_solved_bound:                 -1
% 2.95/1.00  bmc1_unsat_core_size:                   -1
% 2.95/1.00  bmc1_unsat_core_parents_size:           -1
% 2.95/1.00  bmc1_merge_next_fun:                    0
% 2.95/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.95/1.00  
% 2.95/1.00  ------ Instantiation
% 2.95/1.00  
% 2.95/1.00  inst_num_of_clauses:                    449
% 2.95/1.00  inst_num_in_passive:                    79
% 2.95/1.00  inst_num_in_active:                     254
% 2.95/1.00  inst_num_in_unprocessed:                115
% 2.95/1.00  inst_num_of_loops:                      299
% 2.95/1.00  inst_num_of_learning_restarts:          0
% 2.95/1.00  inst_num_moves_active_passive:          39
% 2.95/1.00  inst_lit_activity:                      0
% 2.95/1.00  inst_lit_activity_moves:                0
% 2.95/1.00  inst_num_tautologies:                   0
% 2.95/1.00  inst_num_prop_implied:                  0
% 2.95/1.00  inst_num_existing_simplified:           0
% 2.95/1.00  inst_num_eq_res_simplified:             0
% 2.95/1.00  inst_num_child_elim:                    0
% 2.95/1.00  inst_num_of_dismatching_blockings:      67
% 2.95/1.00  inst_num_of_non_proper_insts:           321
% 2.95/1.00  inst_num_of_duplicates:                 0
% 2.95/1.00  inst_inst_num_from_inst_to_res:         0
% 2.95/1.00  inst_dismatching_checking_time:         0.
% 2.95/1.00  
% 2.95/1.00  ------ Resolution
% 2.95/1.00  
% 2.95/1.00  res_num_of_clauses:                     0
% 2.95/1.00  res_num_in_passive:                     0
% 2.95/1.00  res_num_in_active:                      0
% 2.95/1.00  res_num_of_loops:                       133
% 2.95/1.00  res_forward_subset_subsumed:            38
% 2.95/1.00  res_backward_subset_subsumed:           4
% 2.95/1.00  res_forward_subsumed:                   0
% 2.95/1.00  res_backward_subsumed:                  0
% 2.95/1.00  res_forward_subsumption_resolution:     1
% 2.95/1.00  res_backward_subsumption_resolution:    0
% 2.95/1.00  res_clause_to_clause_subsumption:       161
% 2.95/1.00  res_orphan_elimination:                 0
% 2.95/1.00  res_tautology_del:                      21
% 2.95/1.00  res_num_eq_res_simplified:              1
% 2.95/1.00  res_num_sel_changes:                    0
% 2.95/1.00  res_moves_from_active_to_pass:          0
% 2.95/1.00  
% 2.95/1.00  ------ Superposition
% 2.95/1.00  
% 2.95/1.00  sup_time_total:                         0.
% 2.95/1.00  sup_time_generating:                    0.
% 2.95/1.00  sup_time_sim_full:                      0.
% 2.95/1.00  sup_time_sim_immed:                     0.
% 2.95/1.00  
% 2.95/1.00  sup_num_of_clauses:                     65
% 2.95/1.00  sup_num_in_active:                      41
% 2.95/1.00  sup_num_in_passive:                     24
% 2.95/1.00  sup_num_of_loops:                       58
% 2.95/1.00  sup_fw_superposition:                   31
% 2.95/1.00  sup_bw_superposition:                   21
% 2.95/1.00  sup_immediate_simplified:               6
% 2.95/1.00  sup_given_eliminated:                   1
% 2.95/1.00  comparisons_done:                       0
% 2.95/1.00  comparisons_avoided:                    0
% 2.95/1.00  
% 2.95/1.00  ------ Simplifications
% 2.95/1.00  
% 2.95/1.00  
% 2.95/1.00  sim_fw_subset_subsumed:                 4
% 2.95/1.00  sim_bw_subset_subsumed:                 0
% 2.95/1.00  sim_fw_subsumed:                        1
% 2.95/1.00  sim_bw_subsumed:                        0
% 2.95/1.00  sim_fw_subsumption_res:                 3
% 2.95/1.00  sim_bw_subsumption_res:                 0
% 2.95/1.00  sim_tautology_del:                      0
% 2.95/1.00  sim_eq_tautology_del:                   2
% 2.95/1.00  sim_eq_res_simp:                        1
% 2.95/1.00  sim_fw_demodulated:                     0
% 2.95/1.00  sim_bw_demodulated:                     17
% 2.95/1.00  sim_light_normalised:                   1
% 2.95/1.00  sim_joinable_taut:                      0
% 2.95/1.00  sim_joinable_simp:                      0
% 2.95/1.00  sim_ac_normalised:                      0
% 2.95/1.00  sim_smt_subsumption:                    0
% 2.95/1.00  
%------------------------------------------------------------------------------
