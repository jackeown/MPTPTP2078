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
% DateTime   : Thu Dec  3 12:01:58 EST 2020

% Result     : Theorem 4.10s
% Output     : CNFRefutation 4.10s
% Verified   : 
% Statistics : Number of formulae       :  191 (1986 expanded)
%              Number of clauses        :  112 ( 573 expanded)
%              Number of leaves         :   20 ( 498 expanded)
%              Depth                    :   28
%              Number of atoms          :  668 (13129 expanded)
%              Number of equality atoms :  239 ( 939 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f15,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f86,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f60,f74])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f28])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

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

fof(f49,plain,(
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

fof(f48,plain,
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

fof(f50,plain,
    ( ( ~ v2_funct_2(sK3,sK0)
      | ~ v2_funct_1(sK2) )
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f41,f49,f48])).

fof(f84,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f50])).

fof(f13,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f72,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f78,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f80,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f50])).

fof(f81,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f83,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f50])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f32])).

fof(f71,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f33])).

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

fof(f76,plain,(
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

fof(f79,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f82,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

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

fof(f75,plain,(
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

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f91,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f69])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f85,plain,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f50])).

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

fof(f73,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f42])).

fof(f53,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f45,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f57,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f6,axiom,(
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

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_funct_1(X1)
          | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

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
    inference(flattening,[],[f23])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f58,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_8,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1257,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_16,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_27,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_494,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_27])).

cnf(c_495,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_494])).

cnf(c_21,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_503,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_495,c_21])).

cnf(c_1236,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_503])).

cnf(c_33,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1316,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_1780,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1236,c_33,c_31,c_30,c_28,c_503,c_1316])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v2_funct_1(X3)
    | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1247,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | v1_funct_2(X3,X4,X2) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v2_funct_1(X3) = iProver_top
    | v2_funct_1(k1_partfun1(X4,X2,X2,X0,X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2576,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1780,c_1247])).

cnf(c_34,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_35,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_36,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_37,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_38,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_39,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_1246,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1253,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2268,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1246,c_1253])).

cnf(c_23,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_507,plain,
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
    inference(resolution_lifted,[status(thm)],[c_23,c_27])).

cnf(c_508,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0
    | k6_partfun1(sK0) != k6_partfun1(sK0) ),
    inference(unflattening,[status(thm)],[c_507])).

cnf(c_589,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_508])).

cnf(c_1235,plain,
    ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X0,sK0,X2) = sK0
    | v1_funct_2(X2,X0,sK0) != iProver_top
    | v1_funct_2(X1,sK0,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_589])).

cnf(c_1667,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1235])).

cnf(c_1839,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1667,c_34,c_35,c_36,c_37,c_38,c_39])).

cnf(c_2270,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_2268,c_1839])).

cnf(c_12,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_17,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_412,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X0)
    | X0 != X1
    | k2_relat_1(X0) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_17])).

cnf(c_413,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_412])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_423,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0)))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_413,c_11])).

cnf(c_26,negated_conjecture,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_438,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
    | ~ v2_funct_1(sK2)
    | k2_relat_1(X0) != sK0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_423,c_26])).

cnf(c_439,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3))))
    | ~ v2_funct_1(sK2)
    | k2_relat_1(sK3) != sK0 ),
    inference(unflattening,[status(thm)],[c_438])).

cnf(c_747,plain,
    ( ~ v2_funct_1(sK2)
    | sP0_iProver_split
    | k2_relat_1(sK3) != sK0 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_439])).

cnf(c_1238,plain,
    ( k2_relat_1(sK3) != sK0
    | v2_funct_1(sK2) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_747])).

cnf(c_2425,plain,
    ( sK0 != sK0
    | v2_funct_1(sK2) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_2270,c_1238])).

cnf(c_2426,plain,
    ( v2_funct_1(sK2) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2425])).

cnf(c_746,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3))))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_439])).

cnf(c_1239,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3)))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_746])).

cnf(c_2424,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(demodulation,[status(thm)],[c_2270,c_1239])).

cnf(c_2521,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_1246,c_2424])).

cnf(c_5848,plain,
    ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2576,c_34,c_35,c_36,c_37,c_38,c_39,c_2426,c_2521])).

cnf(c_5849,plain,
    ( sK0 = k1_xboole_0
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5848])).

cnf(c_5852,plain,
    ( sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1257,c_5849])).

cnf(c_1243,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1249,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2633,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1246,c_1249])).

cnf(c_2768,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2633,c_37])).

cnf(c_2769,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_2768])).

cnf(c_2777,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1243,c_2769])).

cnf(c_2778,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2777,c_1780])).

cnf(c_3088,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2778,c_34])).

cnf(c_5872,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_5852,c_3088])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v4_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_5,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_372,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_13,c_5])).

cnf(c_376,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_372,c_11])).

cnf(c_377,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_376])).

cnf(c_1240,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_377])).

cnf(c_2082,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1243,c_1240])).

cnf(c_5881,plain,
    ( r1_tarski(k1_relat_1(sK2),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5852,c_2082])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1260,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1262,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2274,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1260,c_1262])).

cnf(c_6408,plain,
    ( k1_relat_1(sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5881,c_2274])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) = k1_xboole_0
    | k1_relat_1(X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1258,plain,
    ( k2_relat_1(X0) = k1_xboole_0
    | k1_relat_1(X0) != k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_6867,plain,
    ( k2_relat_1(sK2) = k1_xboole_0
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_6408,c_1258])).

cnf(c_1363,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1631,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1363])).

cnf(c_1632,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1631])).

cnf(c_6970,plain,
    ( k2_relat_1(sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6867,c_36,c_1632])).

cnf(c_10,plain,
    ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | v2_funct_1(X0)
    | ~ v2_funct_1(k5_relat_1(X0,X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1255,plain,
    ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v2_funct_1(X0) = iProver_top
    | v2_funct_1(k5_relat_1(X0,X1)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_6974,plain,
    ( r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k5_relat_1(sK2,X0)) != iProver_top
    | v2_funct_1(sK2) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_6970,c_1255])).

cnf(c_11738,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v2_funct_1(k5_relat_1(sK2,X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6974,c_34,c_36,c_1632,c_2426,c_2521])).

cnf(c_11739,plain,
    ( r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(k5_relat_1(sK2,X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_11738])).

cnf(c_11744,plain,
    ( r1_tarski(k1_xboole_0,k1_relat_1(sK3)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5872,c_11739])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_relat_1(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1259,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_relat_1(X0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2431,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | sK0 != k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2270,c_1259])).

cnf(c_1503,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1734,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1503])).

cnf(c_1735,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1734])).

cnf(c_4994,plain,
    ( sK0 != k1_xboole_0
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2431,c_39,c_1735])).

cnf(c_4995,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_4994])).

cnf(c_5858,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5852,c_4995])).

cnf(c_5889,plain,
    ( k1_relat_1(sK3) = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_5858])).

cnf(c_11745,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11744,c_5889])).

cnf(c_108,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_110,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_108])).

cnf(c_93,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_95,plain,
    ( v2_funct_1(k6_partfun1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_93])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11745,c_1735,c_110,c_95,c_39,c_37])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:39:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 4.10/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.10/1.01  
% 4.10/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.10/1.01  
% 4.10/1.01  ------  iProver source info
% 4.10/1.01  
% 4.10/1.01  git: date: 2020-06-30 10:37:57 +0100
% 4.10/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.10/1.01  git: non_committed_changes: false
% 4.10/1.01  git: last_make_outside_of_git: false
% 4.10/1.01  
% 4.10/1.01  ------ 
% 4.10/1.01  
% 4.10/1.01  ------ Input Options
% 4.10/1.01  
% 4.10/1.01  --out_options                           all
% 4.10/1.01  --tptp_safe_out                         true
% 4.10/1.01  --problem_path                          ""
% 4.10/1.01  --include_path                          ""
% 4.10/1.01  --clausifier                            res/vclausify_rel
% 4.10/1.01  --clausifier_options                    ""
% 4.10/1.01  --stdin                                 false
% 4.10/1.01  --stats_out                             all
% 4.10/1.01  
% 4.10/1.01  ------ General Options
% 4.10/1.01  
% 4.10/1.01  --fof                                   false
% 4.10/1.01  --time_out_real                         305.
% 4.10/1.01  --time_out_virtual                      -1.
% 4.10/1.01  --symbol_type_check                     false
% 4.10/1.01  --clausify_out                          false
% 4.10/1.01  --sig_cnt_out                           false
% 4.10/1.01  --trig_cnt_out                          false
% 4.10/1.01  --trig_cnt_out_tolerance                1.
% 4.10/1.01  --trig_cnt_out_sk_spl                   false
% 4.10/1.01  --abstr_cl_out                          false
% 4.10/1.01  
% 4.10/1.01  ------ Global Options
% 4.10/1.01  
% 4.10/1.01  --schedule                              default
% 4.10/1.01  --add_important_lit                     false
% 4.10/1.01  --prop_solver_per_cl                    1000
% 4.10/1.01  --min_unsat_core                        false
% 4.10/1.01  --soft_assumptions                      false
% 4.10/1.01  --soft_lemma_size                       3
% 4.10/1.01  --prop_impl_unit_size                   0
% 4.10/1.01  --prop_impl_unit                        []
% 4.10/1.01  --share_sel_clauses                     true
% 4.10/1.01  --reset_solvers                         false
% 4.10/1.01  --bc_imp_inh                            [conj_cone]
% 4.10/1.01  --conj_cone_tolerance                   3.
% 4.10/1.01  --extra_neg_conj                        none
% 4.10/1.01  --large_theory_mode                     true
% 4.10/1.01  --prolific_symb_bound                   200
% 4.10/1.01  --lt_threshold                          2000
% 4.10/1.01  --clause_weak_htbl                      true
% 4.10/1.01  --gc_record_bc_elim                     false
% 4.10/1.01  
% 4.10/1.01  ------ Preprocessing Options
% 4.10/1.01  
% 4.10/1.01  --preprocessing_flag                    true
% 4.10/1.01  --time_out_prep_mult                    0.1
% 4.10/1.01  --splitting_mode                        input
% 4.10/1.01  --splitting_grd                         true
% 4.10/1.01  --splitting_cvd                         false
% 4.10/1.01  --splitting_cvd_svl                     false
% 4.10/1.01  --splitting_nvd                         32
% 4.10/1.01  --sub_typing                            true
% 4.10/1.01  --prep_gs_sim                           true
% 4.10/1.01  --prep_unflatten                        true
% 4.10/1.01  --prep_res_sim                          true
% 4.10/1.01  --prep_upred                            true
% 4.10/1.01  --prep_sem_filter                       exhaustive
% 4.10/1.01  --prep_sem_filter_out                   false
% 4.10/1.01  --pred_elim                             true
% 4.10/1.01  --res_sim_input                         true
% 4.10/1.01  --eq_ax_congr_red                       true
% 4.10/1.01  --pure_diseq_elim                       true
% 4.10/1.01  --brand_transform                       false
% 4.10/1.01  --non_eq_to_eq                          false
% 4.10/1.01  --prep_def_merge                        true
% 4.10/1.01  --prep_def_merge_prop_impl              false
% 4.10/1.01  --prep_def_merge_mbd                    true
% 4.10/1.01  --prep_def_merge_tr_red                 false
% 4.10/1.01  --prep_def_merge_tr_cl                  false
% 4.10/1.01  --smt_preprocessing                     true
% 4.10/1.01  --smt_ac_axioms                         fast
% 4.10/1.01  --preprocessed_out                      false
% 4.10/1.01  --preprocessed_stats                    false
% 4.10/1.01  
% 4.10/1.01  ------ Abstraction refinement Options
% 4.10/1.01  
% 4.10/1.01  --abstr_ref                             []
% 4.10/1.01  --abstr_ref_prep                        false
% 4.10/1.01  --abstr_ref_until_sat                   false
% 4.10/1.01  --abstr_ref_sig_restrict                funpre
% 4.10/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 4.10/1.01  --abstr_ref_under                       []
% 4.10/1.01  
% 4.10/1.01  ------ SAT Options
% 4.10/1.01  
% 4.10/1.01  --sat_mode                              false
% 4.10/1.01  --sat_fm_restart_options                ""
% 4.10/1.01  --sat_gr_def                            false
% 4.10/1.01  --sat_epr_types                         true
% 4.10/1.01  --sat_non_cyclic_types                  false
% 4.10/1.01  --sat_finite_models                     false
% 4.10/1.01  --sat_fm_lemmas                         false
% 4.10/1.01  --sat_fm_prep                           false
% 4.10/1.01  --sat_fm_uc_incr                        true
% 4.10/1.01  --sat_out_model                         small
% 4.10/1.01  --sat_out_clauses                       false
% 4.10/1.01  
% 4.10/1.01  ------ QBF Options
% 4.10/1.01  
% 4.10/1.01  --qbf_mode                              false
% 4.10/1.01  --qbf_elim_univ                         false
% 4.10/1.01  --qbf_dom_inst                          none
% 4.10/1.01  --qbf_dom_pre_inst                      false
% 4.10/1.01  --qbf_sk_in                             false
% 4.10/1.01  --qbf_pred_elim                         true
% 4.10/1.01  --qbf_split                             512
% 4.10/1.01  
% 4.10/1.01  ------ BMC1 Options
% 4.10/1.01  
% 4.10/1.01  --bmc1_incremental                      false
% 4.10/1.01  --bmc1_axioms                           reachable_all
% 4.10/1.01  --bmc1_min_bound                        0
% 4.10/1.01  --bmc1_max_bound                        -1
% 4.10/1.01  --bmc1_max_bound_default                -1
% 4.10/1.01  --bmc1_symbol_reachability              true
% 4.10/1.01  --bmc1_property_lemmas                  false
% 4.10/1.01  --bmc1_k_induction                      false
% 4.10/1.01  --bmc1_non_equiv_states                 false
% 4.10/1.01  --bmc1_deadlock                         false
% 4.10/1.01  --bmc1_ucm                              false
% 4.10/1.01  --bmc1_add_unsat_core                   none
% 4.10/1.01  --bmc1_unsat_core_children              false
% 4.10/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 4.10/1.01  --bmc1_out_stat                         full
% 4.10/1.01  --bmc1_ground_init                      false
% 4.10/1.01  --bmc1_pre_inst_next_state              false
% 4.10/1.01  --bmc1_pre_inst_state                   false
% 4.10/1.01  --bmc1_pre_inst_reach_state             false
% 4.10/1.01  --bmc1_out_unsat_core                   false
% 4.10/1.01  --bmc1_aig_witness_out                  false
% 4.10/1.01  --bmc1_verbose                          false
% 4.10/1.01  --bmc1_dump_clauses_tptp                false
% 4.10/1.01  --bmc1_dump_unsat_core_tptp             false
% 4.10/1.01  --bmc1_dump_file                        -
% 4.10/1.01  --bmc1_ucm_expand_uc_limit              128
% 4.10/1.01  --bmc1_ucm_n_expand_iterations          6
% 4.10/1.01  --bmc1_ucm_extend_mode                  1
% 4.10/1.01  --bmc1_ucm_init_mode                    2
% 4.10/1.01  --bmc1_ucm_cone_mode                    none
% 4.10/1.01  --bmc1_ucm_reduced_relation_type        0
% 4.10/1.01  --bmc1_ucm_relax_model                  4
% 4.10/1.01  --bmc1_ucm_full_tr_after_sat            true
% 4.10/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 4.10/1.01  --bmc1_ucm_layered_model                none
% 4.10/1.01  --bmc1_ucm_max_lemma_size               10
% 4.10/1.01  
% 4.10/1.01  ------ AIG Options
% 4.10/1.01  
% 4.10/1.01  --aig_mode                              false
% 4.10/1.01  
% 4.10/1.01  ------ Instantiation Options
% 4.10/1.01  
% 4.10/1.01  --instantiation_flag                    true
% 4.10/1.01  --inst_sos_flag                         true
% 4.10/1.01  --inst_sos_phase                        true
% 4.10/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.10/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.10/1.01  --inst_lit_sel_side                     num_symb
% 4.10/1.01  --inst_solver_per_active                1400
% 4.10/1.01  --inst_solver_calls_frac                1.
% 4.10/1.01  --inst_passive_queue_type               priority_queues
% 4.10/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.10/1.01  --inst_passive_queues_freq              [25;2]
% 4.10/1.01  --inst_dismatching                      true
% 4.10/1.01  --inst_eager_unprocessed_to_passive     true
% 4.10/1.01  --inst_prop_sim_given                   true
% 4.10/1.01  --inst_prop_sim_new                     false
% 4.10/1.01  --inst_subs_new                         false
% 4.10/1.01  --inst_eq_res_simp                      false
% 4.10/1.01  --inst_subs_given                       false
% 4.10/1.01  --inst_orphan_elimination               true
% 4.10/1.01  --inst_learning_loop_flag               true
% 4.10/1.01  --inst_learning_start                   3000
% 4.10/1.01  --inst_learning_factor                  2
% 4.10/1.01  --inst_start_prop_sim_after_learn       3
% 4.10/1.01  --inst_sel_renew                        solver
% 4.10/1.01  --inst_lit_activity_flag                true
% 4.10/1.01  --inst_restr_to_given                   false
% 4.10/1.01  --inst_activity_threshold               500
% 4.10/1.01  --inst_out_proof                        true
% 4.10/1.01  
% 4.10/1.01  ------ Resolution Options
% 4.10/1.01  
% 4.10/1.01  --resolution_flag                       true
% 4.10/1.01  --res_lit_sel                           adaptive
% 4.10/1.01  --res_lit_sel_side                      none
% 4.10/1.01  --res_ordering                          kbo
% 4.10/1.01  --res_to_prop_solver                    active
% 4.10/1.01  --res_prop_simpl_new                    false
% 4.10/1.01  --res_prop_simpl_given                  true
% 4.10/1.01  --res_passive_queue_type                priority_queues
% 4.10/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.10/1.01  --res_passive_queues_freq               [15;5]
% 4.10/1.01  --res_forward_subs                      full
% 4.10/1.01  --res_backward_subs                     full
% 4.10/1.01  --res_forward_subs_resolution           true
% 4.10/1.01  --res_backward_subs_resolution          true
% 4.10/1.01  --res_orphan_elimination                true
% 4.10/1.01  --res_time_limit                        2.
% 4.10/1.01  --res_out_proof                         true
% 4.10/1.01  
% 4.10/1.01  ------ Superposition Options
% 4.10/1.01  
% 4.10/1.01  --superposition_flag                    true
% 4.10/1.01  --sup_passive_queue_type                priority_queues
% 4.10/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.10/1.01  --sup_passive_queues_freq               [8;1;4]
% 4.10/1.01  --demod_completeness_check              fast
% 4.10/1.01  --demod_use_ground                      true
% 4.10/1.01  --sup_to_prop_solver                    passive
% 4.10/1.01  --sup_prop_simpl_new                    true
% 4.10/1.01  --sup_prop_simpl_given                  true
% 4.10/1.01  --sup_fun_splitting                     true
% 4.10/1.01  --sup_smt_interval                      50000
% 4.10/1.01  
% 4.10/1.01  ------ Superposition Simplification Setup
% 4.10/1.01  
% 4.10/1.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.10/1.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.10/1.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.10/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.10/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 4.10/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.10/1.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.10/1.01  --sup_immed_triv                        [TrivRules]
% 4.10/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.10/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.10/1.01  --sup_immed_bw_main                     []
% 4.10/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.10/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 4.10/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.10/1.01  --sup_input_bw                          []
% 4.10/1.01  
% 4.10/1.01  ------ Combination Options
% 4.10/1.01  
% 4.10/1.01  --comb_res_mult                         3
% 4.10/1.01  --comb_sup_mult                         2
% 4.10/1.01  --comb_inst_mult                        10
% 4.10/1.01  
% 4.10/1.01  ------ Debug Options
% 4.10/1.01  
% 4.10/1.01  --dbg_backtrace                         false
% 4.10/1.01  --dbg_dump_prop_clauses                 false
% 4.10/1.01  --dbg_dump_prop_clauses_file            -
% 4.10/1.01  --dbg_out_stat                          false
% 4.10/1.01  ------ Parsing...
% 4.10/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.10/1.01  
% 4.10/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 4.10/1.01  
% 4.10/1.01  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.10/1.01  
% 4.10/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.10/1.01  ------ Proving...
% 4.10/1.01  ------ Problem Properties 
% 4.10/1.01  
% 4.10/1.01  
% 4.10/1.01  clauses                                 28
% 4.10/1.01  conjectures                             6
% 4.10/1.01  EPR                                     7
% 4.10/1.01  Horn                                    27
% 4.10/1.01  unary                                   11
% 4.10/1.01  binary                                  5
% 4.10/1.01  lits                                    88
% 4.10/1.01  lits eq                                 14
% 4.10/1.01  fd_pure                                 0
% 4.10/1.01  fd_pseudo                               0
% 4.10/1.01  fd_cond                                 1
% 4.10/1.01  fd_pseudo_cond                          1
% 4.10/1.01  AC symbols                              0
% 4.10/1.01  
% 4.10/1.01  ------ Schedule dynamic 5 is on 
% 4.10/1.01  
% 4.10/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 4.10/1.01  
% 4.10/1.01  
% 4.10/1.01  ------ 
% 4.10/1.01  Current options:
% 4.10/1.01  ------ 
% 4.10/1.01  
% 4.10/1.01  ------ Input Options
% 4.10/1.01  
% 4.10/1.01  --out_options                           all
% 4.10/1.01  --tptp_safe_out                         true
% 4.10/1.01  --problem_path                          ""
% 4.10/1.01  --include_path                          ""
% 4.10/1.01  --clausifier                            res/vclausify_rel
% 4.10/1.01  --clausifier_options                    ""
% 4.10/1.01  --stdin                                 false
% 4.10/1.01  --stats_out                             all
% 4.10/1.01  
% 4.10/1.01  ------ General Options
% 4.10/1.01  
% 4.10/1.01  --fof                                   false
% 4.10/1.01  --time_out_real                         305.
% 4.10/1.01  --time_out_virtual                      -1.
% 4.10/1.01  --symbol_type_check                     false
% 4.10/1.01  --clausify_out                          false
% 4.10/1.01  --sig_cnt_out                           false
% 4.10/1.01  --trig_cnt_out                          false
% 4.10/1.01  --trig_cnt_out_tolerance                1.
% 4.10/1.01  --trig_cnt_out_sk_spl                   false
% 4.10/1.01  --abstr_cl_out                          false
% 4.10/1.01  
% 4.10/1.01  ------ Global Options
% 4.10/1.01  
% 4.10/1.01  --schedule                              default
% 4.10/1.01  --add_important_lit                     false
% 4.10/1.01  --prop_solver_per_cl                    1000
% 4.10/1.01  --min_unsat_core                        false
% 4.10/1.01  --soft_assumptions                      false
% 4.10/1.01  --soft_lemma_size                       3
% 4.10/1.01  --prop_impl_unit_size                   0
% 4.10/1.01  --prop_impl_unit                        []
% 4.10/1.01  --share_sel_clauses                     true
% 4.10/1.01  --reset_solvers                         false
% 4.10/1.01  --bc_imp_inh                            [conj_cone]
% 4.10/1.01  --conj_cone_tolerance                   3.
% 4.10/1.01  --extra_neg_conj                        none
% 4.10/1.01  --large_theory_mode                     true
% 4.10/1.01  --prolific_symb_bound                   200
% 4.10/1.01  --lt_threshold                          2000
% 4.10/1.01  --clause_weak_htbl                      true
% 4.10/1.01  --gc_record_bc_elim                     false
% 4.10/1.01  
% 4.10/1.01  ------ Preprocessing Options
% 4.10/1.01  
% 4.10/1.01  --preprocessing_flag                    true
% 4.10/1.01  --time_out_prep_mult                    0.1
% 4.10/1.01  --splitting_mode                        input
% 4.10/1.01  --splitting_grd                         true
% 4.10/1.01  --splitting_cvd                         false
% 4.10/1.01  --splitting_cvd_svl                     false
% 4.10/1.01  --splitting_nvd                         32
% 4.10/1.01  --sub_typing                            true
% 4.10/1.01  --prep_gs_sim                           true
% 4.10/1.01  --prep_unflatten                        true
% 4.10/1.01  --prep_res_sim                          true
% 4.10/1.01  --prep_upred                            true
% 4.10/1.01  --prep_sem_filter                       exhaustive
% 4.10/1.01  --prep_sem_filter_out                   false
% 4.10/1.01  --pred_elim                             true
% 4.10/1.01  --res_sim_input                         true
% 4.10/1.01  --eq_ax_congr_red                       true
% 4.10/1.01  --pure_diseq_elim                       true
% 4.10/1.01  --brand_transform                       false
% 4.10/1.01  --non_eq_to_eq                          false
% 4.10/1.01  --prep_def_merge                        true
% 4.10/1.01  --prep_def_merge_prop_impl              false
% 4.10/1.01  --prep_def_merge_mbd                    true
% 4.10/1.01  --prep_def_merge_tr_red                 false
% 4.10/1.01  --prep_def_merge_tr_cl                  false
% 4.10/1.01  --smt_preprocessing                     true
% 4.10/1.01  --smt_ac_axioms                         fast
% 4.10/1.01  --preprocessed_out                      false
% 4.10/1.01  --preprocessed_stats                    false
% 4.10/1.01  
% 4.10/1.01  ------ Abstraction refinement Options
% 4.10/1.01  
% 4.10/1.01  --abstr_ref                             []
% 4.10/1.01  --abstr_ref_prep                        false
% 4.10/1.01  --abstr_ref_until_sat                   false
% 4.10/1.01  --abstr_ref_sig_restrict                funpre
% 4.10/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 4.10/1.01  --abstr_ref_under                       []
% 4.10/1.01  
% 4.10/1.01  ------ SAT Options
% 4.10/1.01  
% 4.10/1.01  --sat_mode                              false
% 4.10/1.01  --sat_fm_restart_options                ""
% 4.10/1.01  --sat_gr_def                            false
% 4.10/1.01  --sat_epr_types                         true
% 4.10/1.01  --sat_non_cyclic_types                  false
% 4.10/1.01  --sat_finite_models                     false
% 4.10/1.01  --sat_fm_lemmas                         false
% 4.10/1.01  --sat_fm_prep                           false
% 4.10/1.01  --sat_fm_uc_incr                        true
% 4.10/1.01  --sat_out_model                         small
% 4.10/1.01  --sat_out_clauses                       false
% 4.10/1.01  
% 4.10/1.01  ------ QBF Options
% 4.10/1.01  
% 4.10/1.01  --qbf_mode                              false
% 4.10/1.01  --qbf_elim_univ                         false
% 4.10/1.01  --qbf_dom_inst                          none
% 4.10/1.01  --qbf_dom_pre_inst                      false
% 4.10/1.01  --qbf_sk_in                             false
% 4.10/1.01  --qbf_pred_elim                         true
% 4.10/1.01  --qbf_split                             512
% 4.10/1.01  
% 4.10/1.01  ------ BMC1 Options
% 4.10/1.01  
% 4.10/1.01  --bmc1_incremental                      false
% 4.10/1.01  --bmc1_axioms                           reachable_all
% 4.10/1.01  --bmc1_min_bound                        0
% 4.10/1.01  --bmc1_max_bound                        -1
% 4.10/1.01  --bmc1_max_bound_default                -1
% 4.10/1.01  --bmc1_symbol_reachability              true
% 4.10/1.01  --bmc1_property_lemmas                  false
% 4.10/1.01  --bmc1_k_induction                      false
% 4.10/1.01  --bmc1_non_equiv_states                 false
% 4.10/1.01  --bmc1_deadlock                         false
% 4.10/1.01  --bmc1_ucm                              false
% 4.10/1.01  --bmc1_add_unsat_core                   none
% 4.10/1.01  --bmc1_unsat_core_children              false
% 4.10/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 4.10/1.01  --bmc1_out_stat                         full
% 4.10/1.01  --bmc1_ground_init                      false
% 4.10/1.01  --bmc1_pre_inst_next_state              false
% 4.10/1.01  --bmc1_pre_inst_state                   false
% 4.10/1.01  --bmc1_pre_inst_reach_state             false
% 4.10/1.01  --bmc1_out_unsat_core                   false
% 4.10/1.01  --bmc1_aig_witness_out                  false
% 4.10/1.01  --bmc1_verbose                          false
% 4.10/1.01  --bmc1_dump_clauses_tptp                false
% 4.10/1.01  --bmc1_dump_unsat_core_tptp             false
% 4.10/1.01  --bmc1_dump_file                        -
% 4.10/1.01  --bmc1_ucm_expand_uc_limit              128
% 4.10/1.01  --bmc1_ucm_n_expand_iterations          6
% 4.10/1.01  --bmc1_ucm_extend_mode                  1
% 4.10/1.01  --bmc1_ucm_init_mode                    2
% 4.10/1.01  --bmc1_ucm_cone_mode                    none
% 4.10/1.01  --bmc1_ucm_reduced_relation_type        0
% 4.10/1.01  --bmc1_ucm_relax_model                  4
% 4.10/1.01  --bmc1_ucm_full_tr_after_sat            true
% 4.10/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 4.10/1.01  --bmc1_ucm_layered_model                none
% 4.10/1.01  --bmc1_ucm_max_lemma_size               10
% 4.10/1.01  
% 4.10/1.01  ------ AIG Options
% 4.10/1.01  
% 4.10/1.01  --aig_mode                              false
% 4.10/1.01  
% 4.10/1.01  ------ Instantiation Options
% 4.10/1.01  
% 4.10/1.01  --instantiation_flag                    true
% 4.10/1.01  --inst_sos_flag                         true
% 4.10/1.01  --inst_sos_phase                        true
% 4.10/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.10/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.10/1.01  --inst_lit_sel_side                     none
% 4.10/1.01  --inst_solver_per_active                1400
% 4.10/1.01  --inst_solver_calls_frac                1.
% 4.10/1.01  --inst_passive_queue_type               priority_queues
% 4.10/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.10/1.01  --inst_passive_queues_freq              [25;2]
% 4.10/1.01  --inst_dismatching                      true
% 4.10/1.01  --inst_eager_unprocessed_to_passive     true
% 4.10/1.01  --inst_prop_sim_given                   true
% 4.10/1.01  --inst_prop_sim_new                     false
% 4.10/1.01  --inst_subs_new                         false
% 4.10/1.01  --inst_eq_res_simp                      false
% 4.10/1.01  --inst_subs_given                       false
% 4.10/1.01  --inst_orphan_elimination               true
% 4.10/1.01  --inst_learning_loop_flag               true
% 4.10/1.01  --inst_learning_start                   3000
% 4.10/1.01  --inst_learning_factor                  2
% 4.10/1.01  --inst_start_prop_sim_after_learn       3
% 4.10/1.01  --inst_sel_renew                        solver
% 4.10/1.01  --inst_lit_activity_flag                true
% 4.10/1.01  --inst_restr_to_given                   false
% 4.10/1.01  --inst_activity_threshold               500
% 4.10/1.01  --inst_out_proof                        true
% 4.10/1.01  
% 4.10/1.01  ------ Resolution Options
% 4.10/1.01  
% 4.10/1.01  --resolution_flag                       false
% 4.10/1.01  --res_lit_sel                           adaptive
% 4.10/1.01  --res_lit_sel_side                      none
% 4.10/1.01  --res_ordering                          kbo
% 4.10/1.01  --res_to_prop_solver                    active
% 4.10/1.01  --res_prop_simpl_new                    false
% 4.10/1.01  --res_prop_simpl_given                  true
% 4.10/1.01  --res_passive_queue_type                priority_queues
% 4.10/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.10/1.01  --res_passive_queues_freq               [15;5]
% 4.10/1.01  --res_forward_subs                      full
% 4.10/1.01  --res_backward_subs                     full
% 4.10/1.01  --res_forward_subs_resolution           true
% 4.10/1.01  --res_backward_subs_resolution          true
% 4.10/1.01  --res_orphan_elimination                true
% 4.10/1.01  --res_time_limit                        2.
% 4.10/1.01  --res_out_proof                         true
% 4.10/1.01  
% 4.10/1.01  ------ Superposition Options
% 4.10/1.01  
% 4.10/1.01  --superposition_flag                    true
% 4.10/1.01  --sup_passive_queue_type                priority_queues
% 4.10/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.10/1.01  --sup_passive_queues_freq               [8;1;4]
% 4.10/1.01  --demod_completeness_check              fast
% 4.10/1.01  --demod_use_ground                      true
% 4.10/1.01  --sup_to_prop_solver                    passive
% 4.10/1.01  --sup_prop_simpl_new                    true
% 4.10/1.01  --sup_prop_simpl_given                  true
% 4.10/1.01  --sup_fun_splitting                     true
% 4.10/1.01  --sup_smt_interval                      50000
% 4.10/1.01  
% 4.10/1.01  ------ Superposition Simplification Setup
% 4.10/1.01  
% 4.10/1.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.10/1.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.10/1.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.10/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.10/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 4.10/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.10/1.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.10/1.01  --sup_immed_triv                        [TrivRules]
% 4.10/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.10/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.10/1.01  --sup_immed_bw_main                     []
% 4.10/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.10/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 4.10/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.10/1.01  --sup_input_bw                          []
% 4.10/1.01  
% 4.10/1.01  ------ Combination Options
% 4.10/1.01  
% 4.10/1.01  --comb_res_mult                         3
% 4.10/1.01  --comb_sup_mult                         2
% 4.10/1.01  --comb_inst_mult                        10
% 4.10/1.01  
% 4.10/1.01  ------ Debug Options
% 4.10/1.01  
% 4.10/1.01  --dbg_backtrace                         false
% 4.10/1.01  --dbg_dump_prop_clauses                 false
% 4.10/1.01  --dbg_dump_prop_clauses_file            -
% 4.10/1.01  --dbg_out_stat                          false
% 4.10/1.01  
% 4.10/1.01  
% 4.10/1.01  
% 4.10/1.01  
% 4.10/1.01  ------ Proving...
% 4.10/1.01  
% 4.10/1.01  
% 4.10/1.01  % SZS status Theorem for theBenchmark.p
% 4.10/1.01  
% 4.10/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 4.10/1.01  
% 4.10/1.01  fof(f5,axiom,(
% 4.10/1.01    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 4.10/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.10/1.01  
% 4.10/1.01  fof(f60,plain,(
% 4.10/1.01    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 4.10/1.01    inference(cnf_transformation,[],[f5])).
% 4.10/1.01  
% 4.10/1.01  fof(f15,axiom,(
% 4.10/1.01    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 4.10/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.10/1.01  
% 4.10/1.01  fof(f74,plain,(
% 4.10/1.01    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 4.10/1.01    inference(cnf_transformation,[],[f15])).
% 4.10/1.01  
% 4.10/1.01  fof(f86,plain,(
% 4.10/1.01    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 4.10/1.01    inference(definition_unfolding,[],[f60,f74])).
% 4.10/1.01  
% 4.10/1.01  fof(f10,axiom,(
% 4.10/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 4.10/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.10/1.01  
% 4.10/1.01  fof(f28,plain,(
% 4.10/1.01    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 4.10/1.01    inference(ennf_transformation,[],[f10])).
% 4.10/1.01  
% 4.10/1.01  fof(f29,plain,(
% 4.10/1.01    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.10/1.01    inference(flattening,[],[f28])).
% 4.10/1.01  
% 4.10/1.01  fof(f46,plain,(
% 4.10/1.01    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.10/1.01    inference(nnf_transformation,[],[f29])).
% 4.10/1.01  
% 4.10/1.01  fof(f66,plain,(
% 4.10/1.01    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.10/1.01    inference(cnf_transformation,[],[f46])).
% 4.10/1.01  
% 4.10/1.01  fof(f18,conjecture,(
% 4.10/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 4.10/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.10/1.01  
% 4.10/1.01  fof(f19,negated_conjecture,(
% 4.10/1.01    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 4.10/1.01    inference(negated_conjecture,[],[f18])).
% 4.10/1.01  
% 4.10/1.01  fof(f40,plain,(
% 4.10/1.01    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 4.10/1.01    inference(ennf_transformation,[],[f19])).
% 4.10/1.01  
% 4.10/1.01  fof(f41,plain,(
% 4.10/1.01    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 4.10/1.01    inference(flattening,[],[f40])).
% 4.10/1.01  
% 4.10/1.01  fof(f49,plain,(
% 4.10/1.01    ( ! [X2,X0,X1] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((~v2_funct_2(sK3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 4.10/1.01    introduced(choice_axiom,[])).
% 4.10/1.01  
% 4.10/1.01  fof(f48,plain,(
% 4.10/1.01    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 4.10/1.01    introduced(choice_axiom,[])).
% 4.10/1.01  
% 4.10/1.01  fof(f50,plain,(
% 4.10/1.01    ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 4.10/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f41,f49,f48])).
% 4.10/1.01  
% 4.10/1.01  fof(f84,plain,(
% 4.10/1.01    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 4.10/1.01    inference(cnf_transformation,[],[f50])).
% 4.10/1.01  
% 4.10/1.01  fof(f13,axiom,(
% 4.10/1.01    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 4.10/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.10/1.01  
% 4.10/1.01  fof(f20,plain,(
% 4.10/1.01    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 4.10/1.01    inference(pure_predicate_removal,[],[f13])).
% 4.10/1.01  
% 4.10/1.01  fof(f72,plain,(
% 4.10/1.01    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 4.10/1.01    inference(cnf_transformation,[],[f20])).
% 4.10/1.01  
% 4.10/1.01  fof(f78,plain,(
% 4.10/1.01    v1_funct_1(sK2)),
% 4.10/1.01    inference(cnf_transformation,[],[f50])).
% 4.10/1.01  
% 4.10/1.01  fof(f80,plain,(
% 4.10/1.01    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 4.10/1.01    inference(cnf_transformation,[],[f50])).
% 4.10/1.01  
% 4.10/1.01  fof(f81,plain,(
% 4.10/1.01    v1_funct_1(sK3)),
% 4.10/1.01    inference(cnf_transformation,[],[f50])).
% 4.10/1.01  
% 4.10/1.01  fof(f83,plain,(
% 4.10/1.01    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 4.10/1.01    inference(cnf_transformation,[],[f50])).
% 4.10/1.01  
% 4.10/1.01  fof(f12,axiom,(
% 4.10/1.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 4.10/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.10/1.01  
% 4.10/1.01  fof(f32,plain,(
% 4.10/1.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 4.10/1.01    inference(ennf_transformation,[],[f12])).
% 4.10/1.01  
% 4.10/1.01  fof(f33,plain,(
% 4.10/1.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 4.10/1.01    inference(flattening,[],[f32])).
% 4.10/1.01  
% 4.10/1.01  fof(f71,plain,(
% 4.10/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 4.10/1.01    inference(cnf_transformation,[],[f33])).
% 4.10/1.01  
% 4.10/1.01  fof(f17,axiom,(
% 4.10/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 4.10/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.10/1.01  
% 4.10/1.01  fof(f38,plain,(
% 4.10/1.01    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 4.10/1.01    inference(ennf_transformation,[],[f17])).
% 4.10/1.01  
% 4.10/1.01  fof(f39,plain,(
% 4.10/1.01    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 4.10/1.01    inference(flattening,[],[f38])).
% 4.10/1.01  
% 4.10/1.01  fof(f76,plain,(
% 4.10/1.01    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X3) | k1_xboole_0 = X2 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 4.10/1.01    inference(cnf_transformation,[],[f39])).
% 4.10/1.01  
% 4.10/1.01  fof(f79,plain,(
% 4.10/1.01    v1_funct_2(sK2,sK0,sK1)),
% 4.10/1.01    inference(cnf_transformation,[],[f50])).
% 4.10/1.01  
% 4.10/1.01  fof(f82,plain,(
% 4.10/1.01    v1_funct_2(sK3,sK1,sK0)),
% 4.10/1.01    inference(cnf_transformation,[],[f50])).
% 4.10/1.01  
% 4.10/1.01  fof(f9,axiom,(
% 4.10/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 4.10/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.10/1.01  
% 4.10/1.01  fof(f27,plain,(
% 4.10/1.01    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.10/1.01    inference(ennf_transformation,[],[f9])).
% 4.10/1.01  
% 4.10/1.01  fof(f65,plain,(
% 4.10/1.01    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.10/1.01    inference(cnf_transformation,[],[f27])).
% 4.10/1.01  
% 4.10/1.01  fof(f16,axiom,(
% 4.10/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 4.10/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.10/1.01  
% 4.10/1.01  fof(f36,plain,(
% 4.10/1.01    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 4.10/1.01    inference(ennf_transformation,[],[f16])).
% 4.10/1.01  
% 4.10/1.01  fof(f37,plain,(
% 4.10/1.01    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 4.10/1.01    inference(flattening,[],[f36])).
% 4.10/1.01  
% 4.10/1.01  fof(f75,plain,(
% 4.10/1.01    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 4.10/1.01    inference(cnf_transformation,[],[f37])).
% 4.10/1.01  
% 4.10/1.01  fof(f8,axiom,(
% 4.10/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 4.10/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.10/1.01  
% 4.10/1.01  fof(f26,plain,(
% 4.10/1.01    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.10/1.01    inference(ennf_transformation,[],[f8])).
% 4.10/1.01  
% 4.10/1.01  fof(f64,plain,(
% 4.10/1.01    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.10/1.01    inference(cnf_transformation,[],[f26])).
% 4.10/1.01  
% 4.10/1.01  fof(f11,axiom,(
% 4.10/1.01    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 4.10/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.10/1.01  
% 4.10/1.01  fof(f30,plain,(
% 4.10/1.01    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 4.10/1.01    inference(ennf_transformation,[],[f11])).
% 4.10/1.01  
% 4.10/1.01  fof(f31,plain,(
% 4.10/1.01    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 4.10/1.01    inference(flattening,[],[f30])).
% 4.10/1.01  
% 4.10/1.01  fof(f47,plain,(
% 4.10/1.01    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 4.10/1.01    inference(nnf_transformation,[],[f31])).
% 4.10/1.01  
% 4.10/1.01  fof(f69,plain,(
% 4.10/1.01    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 4.10/1.01    inference(cnf_transformation,[],[f47])).
% 4.10/1.01  
% 4.10/1.01  fof(f91,plain,(
% 4.10/1.01    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 4.10/1.01    inference(equality_resolution,[],[f69])).
% 4.10/1.01  
% 4.10/1.01  fof(f7,axiom,(
% 4.10/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 4.10/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.10/1.01  
% 4.10/1.01  fof(f25,plain,(
% 4.10/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.10/1.01    inference(ennf_transformation,[],[f7])).
% 4.10/1.01  
% 4.10/1.01  fof(f62,plain,(
% 4.10/1.01    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.10/1.01    inference(cnf_transformation,[],[f25])).
% 4.10/1.01  
% 4.10/1.01  fof(f85,plain,(
% 4.10/1.01    ~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)),
% 4.10/1.01    inference(cnf_transformation,[],[f50])).
% 4.10/1.01  
% 4.10/1.01  fof(f14,axiom,(
% 4.10/1.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 4.10/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.10/1.01  
% 4.10/1.01  fof(f34,plain,(
% 4.10/1.01    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 4.10/1.01    inference(ennf_transformation,[],[f14])).
% 4.10/1.01  
% 4.10/1.01  fof(f35,plain,(
% 4.10/1.01    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 4.10/1.01    inference(flattening,[],[f34])).
% 4.10/1.01  
% 4.10/1.01  fof(f73,plain,(
% 4.10/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 4.10/1.01    inference(cnf_transformation,[],[f35])).
% 4.10/1.01  
% 4.10/1.01  fof(f63,plain,(
% 4.10/1.01    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.10/1.01    inference(cnf_transformation,[],[f26])).
% 4.10/1.01  
% 4.10/1.01  fof(f3,axiom,(
% 4.10/1.01    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 4.10/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.10/1.01  
% 4.10/1.01  fof(f21,plain,(
% 4.10/1.01    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 4.10/1.01    inference(ennf_transformation,[],[f3])).
% 4.10/1.01  
% 4.10/1.01  fof(f44,plain,(
% 4.10/1.01    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 4.10/1.01    inference(nnf_transformation,[],[f21])).
% 4.10/1.01  
% 4.10/1.01  fof(f55,plain,(
% 4.10/1.01    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 4.10/1.01    inference(cnf_transformation,[],[f44])).
% 4.10/1.01  
% 4.10/1.01  fof(f2,axiom,(
% 4.10/1.01    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 4.10/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.10/1.01  
% 4.10/1.01  fof(f54,plain,(
% 4.10/1.01    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 4.10/1.01    inference(cnf_transformation,[],[f2])).
% 4.10/1.01  
% 4.10/1.01  fof(f1,axiom,(
% 4.10/1.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 4.10/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.10/1.01  
% 4.10/1.01  fof(f42,plain,(
% 4.10/1.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.10/1.01    inference(nnf_transformation,[],[f1])).
% 4.10/1.01  
% 4.10/1.01  fof(f43,plain,(
% 4.10/1.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.10/1.01    inference(flattening,[],[f42])).
% 4.10/1.01  
% 4.10/1.01  fof(f53,plain,(
% 4.10/1.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 4.10/1.01    inference(cnf_transformation,[],[f43])).
% 4.10/1.01  
% 4.10/1.01  fof(f4,axiom,(
% 4.10/1.01    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 4.10/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.10/1.01  
% 4.10/1.01  fof(f22,plain,(
% 4.10/1.01    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 4.10/1.01    inference(ennf_transformation,[],[f4])).
% 4.10/1.01  
% 4.10/1.01  fof(f45,plain,(
% 4.10/1.01    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 4.10/1.01    inference(nnf_transformation,[],[f22])).
% 4.10/1.01  
% 4.10/1.01  fof(f57,plain,(
% 4.10/1.01    ( ! [X0] : (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 4.10/1.01    inference(cnf_transformation,[],[f45])).
% 4.10/1.01  
% 4.10/1.01  fof(f6,axiom,(
% 4.10/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) & v2_funct_1(k5_relat_1(X1,X0))) => v2_funct_1(X1))))),
% 4.10/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.10/1.01  
% 4.10/1.01  fof(f23,plain,(
% 4.10/1.01    ! [X0] : (! [X1] : ((v2_funct_1(X1) | (~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 4.10/1.01    inference(ennf_transformation,[],[f6])).
% 4.10/1.01  
% 4.10/1.01  fof(f24,plain,(
% 4.10/1.01    ! [X0] : (! [X1] : (v2_funct_1(X1) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.10/1.01    inference(flattening,[],[f23])).
% 4.10/1.01  
% 4.10/1.01  fof(f61,plain,(
% 4.10/1.01    ( ! [X0,X1] : (v2_funct_1(X1) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.10/1.01    inference(cnf_transformation,[],[f24])).
% 4.10/1.01  
% 4.10/1.01  fof(f58,plain,(
% 4.10/1.01    ( ! [X0] : (k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 4.10/1.01    inference(cnf_transformation,[],[f45])).
% 4.10/1.01  
% 4.10/1.01  cnf(c_8,plain,
% 4.10/1.01      ( v2_funct_1(k6_partfun1(X0)) ),
% 4.10/1.01      inference(cnf_transformation,[],[f86]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_1257,plain,
% 4.10/1.01      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 4.10/1.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_16,plain,
% 4.10/1.01      ( ~ r2_relset_1(X0,X1,X2,X3)
% 4.10/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 4.10/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 4.10/1.01      | X3 = X2 ),
% 4.10/1.01      inference(cnf_transformation,[],[f66]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_27,negated_conjecture,
% 4.10/1.01      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 4.10/1.01      inference(cnf_transformation,[],[f84]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_494,plain,
% 4.10/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.10/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.10/1.01      | X3 = X0
% 4.10/1.01      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 4.10/1.01      | k6_partfun1(sK0) != X3
% 4.10/1.01      | sK0 != X2
% 4.10/1.01      | sK0 != X1 ),
% 4.10/1.01      inference(resolution_lifted,[status(thm)],[c_16,c_27]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_495,plain,
% 4.10/1.01      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 4.10/1.01      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 4.10/1.01      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 4.10/1.01      inference(unflattening,[status(thm)],[c_494]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_21,plain,
% 4.10/1.01      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 4.10/1.01      inference(cnf_transformation,[],[f72]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_503,plain,
% 4.10/1.01      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 4.10/1.01      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 4.10/1.01      inference(forward_subsumption_resolution,
% 4.10/1.01                [status(thm)],
% 4.10/1.01                [c_495,c_21]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_1236,plain,
% 4.10/1.01      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 4.10/1.01      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 4.10/1.01      inference(predicate_to_equality,[status(thm)],[c_503]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_33,negated_conjecture,
% 4.10/1.01      ( v1_funct_1(sK2) ),
% 4.10/1.01      inference(cnf_transformation,[],[f78]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_31,negated_conjecture,
% 4.10/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 4.10/1.01      inference(cnf_transformation,[],[f80]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_30,negated_conjecture,
% 4.10/1.01      ( v1_funct_1(sK3) ),
% 4.10/1.01      inference(cnf_transformation,[],[f81]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_28,negated_conjecture,
% 4.10/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 4.10/1.01      inference(cnf_transformation,[],[f83]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_19,plain,
% 4.10/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.10/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 4.10/1.01      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 4.10/1.01      | ~ v1_funct_1(X0)
% 4.10/1.01      | ~ v1_funct_1(X3) ),
% 4.10/1.01      inference(cnf_transformation,[],[f71]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_1316,plain,
% 4.10/1.01      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 4.10/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 4.10/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 4.10/1.01      | ~ v1_funct_1(sK2)
% 4.10/1.01      | ~ v1_funct_1(sK3) ),
% 4.10/1.01      inference(instantiation,[status(thm)],[c_19]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_1780,plain,
% 4.10/1.01      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 4.10/1.01      inference(global_propositional_subsumption,
% 4.10/1.01                [status(thm)],
% 4.10/1.01                [c_1236,c_33,c_31,c_30,c_28,c_503,c_1316]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_25,plain,
% 4.10/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 4.10/1.01      | ~ v1_funct_2(X3,X4,X1)
% 4.10/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 4.10/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.10/1.01      | ~ v1_funct_1(X0)
% 4.10/1.01      | ~ v1_funct_1(X3)
% 4.10/1.01      | v2_funct_1(X3)
% 4.10/1.01      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 4.10/1.01      | k1_xboole_0 = X2 ),
% 4.10/1.01      inference(cnf_transformation,[],[f76]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_1247,plain,
% 4.10/1.01      ( k1_xboole_0 = X0
% 4.10/1.01      | v1_funct_2(X1,X2,X0) != iProver_top
% 4.10/1.01      | v1_funct_2(X3,X4,X2) != iProver_top
% 4.10/1.01      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
% 4.10/1.01      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 4.10/1.01      | v1_funct_1(X1) != iProver_top
% 4.10/1.01      | v1_funct_1(X3) != iProver_top
% 4.10/1.01      | v2_funct_1(X3) = iProver_top
% 4.10/1.01      | v2_funct_1(k1_partfun1(X4,X2,X2,X0,X3,X1)) != iProver_top ),
% 4.10/1.01      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_2576,plain,
% 4.10/1.01      ( sK0 = k1_xboole_0
% 4.10/1.01      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 4.10/1.01      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 4.10/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 4.10/1.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 4.10/1.01      | v1_funct_1(sK2) != iProver_top
% 4.10/1.01      | v1_funct_1(sK3) != iProver_top
% 4.10/1.01      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 4.10/1.01      | v2_funct_1(sK2) = iProver_top ),
% 4.10/1.01      inference(superposition,[status(thm)],[c_1780,c_1247]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_34,plain,
% 4.10/1.01      ( v1_funct_1(sK2) = iProver_top ),
% 4.10/1.01      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_32,negated_conjecture,
% 4.10/1.01      ( v1_funct_2(sK2,sK0,sK1) ),
% 4.10/1.01      inference(cnf_transformation,[],[f79]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_35,plain,
% 4.10/1.01      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 4.10/1.01      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_36,plain,
% 4.10/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 4.10/1.01      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_37,plain,
% 4.10/1.01      ( v1_funct_1(sK3) = iProver_top ),
% 4.10/1.01      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_29,negated_conjecture,
% 4.10/1.01      ( v1_funct_2(sK3,sK1,sK0) ),
% 4.10/1.01      inference(cnf_transformation,[],[f82]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_38,plain,
% 4.10/1.01      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 4.10/1.01      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_39,plain,
% 4.10/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 4.10/1.01      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_1246,plain,
% 4.10/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 4.10/1.01      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_14,plain,
% 4.10/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.10/1.01      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 4.10/1.01      inference(cnf_transformation,[],[f65]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_1253,plain,
% 4.10/1.01      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 4.10/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 4.10/1.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_2268,plain,
% 4.10/1.01      ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 4.10/1.01      inference(superposition,[status(thm)],[c_1246,c_1253]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_23,plain,
% 4.10/1.01      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 4.10/1.01      | ~ v1_funct_2(X2,X0,X1)
% 4.10/1.01      | ~ v1_funct_2(X3,X1,X0)
% 4.10/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 4.10/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 4.10/1.01      | ~ v1_funct_1(X2)
% 4.10/1.01      | ~ v1_funct_1(X3)
% 4.10/1.01      | k2_relset_1(X1,X0,X3) = X0 ),
% 4.10/1.01      inference(cnf_transformation,[],[f75]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_507,plain,
% 4.10/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 4.10/1.01      | ~ v1_funct_2(X3,X2,X1)
% 4.10/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 4.10/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.10/1.01      | ~ v1_funct_1(X0)
% 4.10/1.01      | ~ v1_funct_1(X3)
% 4.10/1.01      | k1_partfun1(X2,X1,X1,X2,X3,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 4.10/1.01      | k2_relset_1(X1,X2,X0) = X2
% 4.10/1.01      | k6_partfun1(X2) != k6_partfun1(sK0)
% 4.10/1.01      | sK0 != X2 ),
% 4.10/1.01      inference(resolution_lifted,[status(thm)],[c_23,c_27]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_508,plain,
% 4.10/1.01      ( ~ v1_funct_2(X0,X1,sK0)
% 4.10/1.01      | ~ v1_funct_2(X2,sK0,X1)
% 4.10/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 4.10/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 4.10/1.01      | ~ v1_funct_1(X0)
% 4.10/1.01      | ~ v1_funct_1(X2)
% 4.10/1.01      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 4.10/1.01      | k2_relset_1(X1,sK0,X0) = sK0
% 4.10/1.01      | k6_partfun1(sK0) != k6_partfun1(sK0) ),
% 4.10/1.01      inference(unflattening,[status(thm)],[c_507]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_589,plain,
% 4.10/1.01      ( ~ v1_funct_2(X0,X1,sK0)
% 4.10/1.01      | ~ v1_funct_2(X2,sK0,X1)
% 4.10/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 4.10/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 4.10/1.01      | ~ v1_funct_1(X0)
% 4.10/1.01      | ~ v1_funct_1(X2)
% 4.10/1.01      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 4.10/1.01      | k2_relset_1(X1,sK0,X0) = sK0 ),
% 4.10/1.01      inference(equality_resolution_simp,[status(thm)],[c_508]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_1235,plain,
% 4.10/1.01      ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 4.10/1.01      | k2_relset_1(X0,sK0,X2) = sK0
% 4.10/1.01      | v1_funct_2(X2,X0,sK0) != iProver_top
% 4.10/1.01      | v1_funct_2(X1,sK0,X0) != iProver_top
% 4.10/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 4.10/1.01      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 4.10/1.01      | v1_funct_1(X2) != iProver_top
% 4.10/1.01      | v1_funct_1(X1) != iProver_top ),
% 4.10/1.01      inference(predicate_to_equality,[status(thm)],[c_589]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_1667,plain,
% 4.10/1.01      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 4.10/1.01      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 4.10/1.01      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 4.10/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 4.10/1.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 4.10/1.01      | v1_funct_1(sK2) != iProver_top
% 4.10/1.01      | v1_funct_1(sK3) != iProver_top ),
% 4.10/1.01      inference(equality_resolution,[status(thm)],[c_1235]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_1839,plain,
% 4.10/1.01      ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 4.10/1.01      inference(global_propositional_subsumption,
% 4.10/1.01                [status(thm)],
% 4.10/1.01                [c_1667,c_34,c_35,c_36,c_37,c_38,c_39]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_2270,plain,
% 4.10/1.01      ( k2_relat_1(sK3) = sK0 ),
% 4.10/1.01      inference(light_normalisation,[status(thm)],[c_2268,c_1839]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_12,plain,
% 4.10/1.01      ( v5_relat_1(X0,X1)
% 4.10/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 4.10/1.01      inference(cnf_transformation,[],[f64]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_17,plain,
% 4.10/1.01      ( v2_funct_2(X0,k2_relat_1(X0))
% 4.10/1.01      | ~ v5_relat_1(X0,k2_relat_1(X0))
% 4.10/1.01      | ~ v1_relat_1(X0) ),
% 4.10/1.01      inference(cnf_transformation,[],[f91]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_412,plain,
% 4.10/1.01      ( v2_funct_2(X0,k2_relat_1(X0))
% 4.10/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 4.10/1.01      | ~ v1_relat_1(X0)
% 4.10/1.01      | X0 != X1
% 4.10/1.01      | k2_relat_1(X0) != X3 ),
% 4.10/1.01      inference(resolution_lifted,[status(thm)],[c_12,c_17]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_413,plain,
% 4.10/1.01      ( v2_funct_2(X0,k2_relat_1(X0))
% 4.10/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
% 4.10/1.01      | ~ v1_relat_1(X0) ),
% 4.10/1.01      inference(unflattening,[status(thm)],[c_412]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_11,plain,
% 4.10/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.10/1.01      | v1_relat_1(X0) ),
% 4.10/1.01      inference(cnf_transformation,[],[f62]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_423,plain,
% 4.10/1.01      ( v2_funct_2(X0,k2_relat_1(X0))
% 4.10/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0)))) ),
% 4.10/1.01      inference(forward_subsumption_resolution,
% 4.10/1.01                [status(thm)],
% 4.10/1.01                [c_413,c_11]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_26,negated_conjecture,
% 4.10/1.01      ( ~ v2_funct_2(sK3,sK0) | ~ v2_funct_1(sK2) ),
% 4.10/1.01      inference(cnf_transformation,[],[f85]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_438,plain,
% 4.10/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))
% 4.10/1.01      | ~ v2_funct_1(sK2)
% 4.10/1.01      | k2_relat_1(X0) != sK0
% 4.10/1.01      | sK3 != X0 ),
% 4.10/1.01      inference(resolution_lifted,[status(thm)],[c_423,c_26]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_439,plain,
% 4.10/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3))))
% 4.10/1.01      | ~ v2_funct_1(sK2)
% 4.10/1.01      | k2_relat_1(sK3) != sK0 ),
% 4.10/1.01      inference(unflattening,[status(thm)],[c_438]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_747,plain,
% 4.10/1.01      ( ~ v2_funct_1(sK2) | sP0_iProver_split | k2_relat_1(sK3) != sK0 ),
% 4.10/1.01      inference(splitting,
% 4.10/1.01                [splitting(split),new_symbols(definition,[])],
% 4.10/1.01                [c_439]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_1238,plain,
% 4.10/1.01      ( k2_relat_1(sK3) != sK0
% 4.10/1.01      | v2_funct_1(sK2) != iProver_top
% 4.10/1.01      | sP0_iProver_split = iProver_top ),
% 4.10/1.01      inference(predicate_to_equality,[status(thm)],[c_747]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_2425,plain,
% 4.10/1.01      ( sK0 != sK0
% 4.10/1.01      | v2_funct_1(sK2) != iProver_top
% 4.10/1.01      | sP0_iProver_split = iProver_top ),
% 4.10/1.01      inference(demodulation,[status(thm)],[c_2270,c_1238]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_2426,plain,
% 4.10/1.01      ( v2_funct_1(sK2) != iProver_top
% 4.10/1.01      | sP0_iProver_split = iProver_top ),
% 4.10/1.01      inference(equality_resolution_simp,[status(thm)],[c_2425]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_746,plain,
% 4.10/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3))))
% 4.10/1.01      | ~ sP0_iProver_split ),
% 4.10/1.01      inference(splitting,
% 4.10/1.01                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 4.10/1.01                [c_439]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_1239,plain,
% 4.10/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK3)))) != iProver_top
% 4.10/1.01      | sP0_iProver_split != iProver_top ),
% 4.10/1.01      inference(predicate_to_equality,[status(thm)],[c_746]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_2424,plain,
% 4.10/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 4.10/1.01      | sP0_iProver_split != iProver_top ),
% 4.10/1.01      inference(demodulation,[status(thm)],[c_2270,c_1239]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_2521,plain,
% 4.10/1.01      ( sP0_iProver_split != iProver_top ),
% 4.10/1.01      inference(superposition,[status(thm)],[c_1246,c_2424]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_5848,plain,
% 4.10/1.01      ( v2_funct_1(k6_partfun1(sK0)) != iProver_top | sK0 = k1_xboole_0 ),
% 4.10/1.01      inference(global_propositional_subsumption,
% 4.10/1.01                [status(thm)],
% 4.10/1.01                [c_2576,c_34,c_35,c_36,c_37,c_38,c_39,c_2426,c_2521]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_5849,plain,
% 4.10/1.01      ( sK0 = k1_xboole_0 | v2_funct_1(k6_partfun1(sK0)) != iProver_top ),
% 4.10/1.01      inference(renaming,[status(thm)],[c_5848]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_5852,plain,
% 4.10/1.01      ( sK0 = k1_xboole_0 ),
% 4.10/1.01      inference(superposition,[status(thm)],[c_1257,c_5849]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_1243,plain,
% 4.10/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 4.10/1.01      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_22,plain,
% 4.10/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.10/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 4.10/1.01      | ~ v1_funct_1(X0)
% 4.10/1.01      | ~ v1_funct_1(X3)
% 4.10/1.01      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 4.10/1.01      inference(cnf_transformation,[],[f73]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_1249,plain,
% 4.10/1.01      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 4.10/1.01      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 4.10/1.01      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 4.10/1.01      | v1_funct_1(X5) != iProver_top
% 4.10/1.01      | v1_funct_1(X4) != iProver_top ),
% 4.10/1.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_2633,plain,
% 4.10/1.01      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 4.10/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 4.10/1.01      | v1_funct_1(X2) != iProver_top
% 4.10/1.01      | v1_funct_1(sK3) != iProver_top ),
% 4.10/1.01      inference(superposition,[status(thm)],[c_1246,c_1249]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_2768,plain,
% 4.10/1.01      ( v1_funct_1(X2) != iProver_top
% 4.10/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 4.10/1.01      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 4.10/1.01      inference(global_propositional_subsumption,
% 4.10/1.01                [status(thm)],
% 4.10/1.01                [c_2633,c_37]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_2769,plain,
% 4.10/1.01      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 4.10/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 4.10/1.01      | v1_funct_1(X2) != iProver_top ),
% 4.10/1.01      inference(renaming,[status(thm)],[c_2768]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_2777,plain,
% 4.10/1.01      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 4.10/1.01      | v1_funct_1(sK2) != iProver_top ),
% 4.10/1.01      inference(superposition,[status(thm)],[c_1243,c_2769]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_2778,plain,
% 4.10/1.01      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 4.10/1.01      | v1_funct_1(sK2) != iProver_top ),
% 4.10/1.01      inference(light_normalisation,[status(thm)],[c_2777,c_1780]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_3088,plain,
% 4.10/1.01      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 4.10/1.01      inference(global_propositional_subsumption,
% 4.10/1.01                [status(thm)],
% 4.10/1.01                [c_2778,c_34]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_5872,plain,
% 4.10/1.01      ( k5_relat_1(sK2,sK3) = k6_partfun1(k1_xboole_0) ),
% 4.10/1.01      inference(demodulation,[status(thm)],[c_5852,c_3088]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_13,plain,
% 4.10/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.10/1.01      | v4_relat_1(X0,X1) ),
% 4.10/1.01      inference(cnf_transformation,[],[f63]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_5,plain,
% 4.10/1.01      ( ~ v4_relat_1(X0,X1)
% 4.10/1.01      | r1_tarski(k1_relat_1(X0),X1)
% 4.10/1.01      | ~ v1_relat_1(X0) ),
% 4.10/1.01      inference(cnf_transformation,[],[f55]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_372,plain,
% 4.10/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.10/1.01      | r1_tarski(k1_relat_1(X0),X1)
% 4.10/1.01      | ~ v1_relat_1(X0) ),
% 4.10/1.01      inference(resolution,[status(thm)],[c_13,c_5]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_376,plain,
% 4.10/1.01      ( r1_tarski(k1_relat_1(X0),X1)
% 4.10/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 4.10/1.01      inference(global_propositional_subsumption,
% 4.10/1.01                [status(thm)],
% 4.10/1.01                [c_372,c_11]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_377,plain,
% 4.10/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.10/1.01      | r1_tarski(k1_relat_1(X0),X1) ),
% 4.10/1.01      inference(renaming,[status(thm)],[c_376]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_1240,plain,
% 4.10/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 4.10/1.01      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 4.10/1.01      inference(predicate_to_equality,[status(thm)],[c_377]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_2082,plain,
% 4.10/1.01      ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
% 4.10/1.01      inference(superposition,[status(thm)],[c_1243,c_1240]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_5881,plain,
% 4.10/1.01      ( r1_tarski(k1_relat_1(sK2),k1_xboole_0) = iProver_top ),
% 4.10/1.01      inference(demodulation,[status(thm)],[c_5852,c_2082]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_3,plain,
% 4.10/1.01      ( r1_tarski(k1_xboole_0,X0) ),
% 4.10/1.01      inference(cnf_transformation,[],[f54]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_1260,plain,
% 4.10/1.01      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 4.10/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_0,plain,
% 4.10/1.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 4.10/1.01      inference(cnf_transformation,[],[f53]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_1262,plain,
% 4.10/1.01      ( X0 = X1
% 4.10/1.01      | r1_tarski(X0,X1) != iProver_top
% 4.10/1.01      | r1_tarski(X1,X0) != iProver_top ),
% 4.10/1.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_2274,plain,
% 4.10/1.01      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 4.10/1.01      inference(superposition,[status(thm)],[c_1260,c_1262]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_6408,plain,
% 4.10/1.01      ( k1_relat_1(sK2) = k1_xboole_0 ),
% 4.10/1.01      inference(superposition,[status(thm)],[c_5881,c_2274]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_7,plain,
% 4.10/1.01      ( ~ v1_relat_1(X0)
% 4.10/1.01      | k2_relat_1(X0) = k1_xboole_0
% 4.10/1.01      | k1_relat_1(X0) != k1_xboole_0 ),
% 4.10/1.01      inference(cnf_transformation,[],[f57]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_1258,plain,
% 4.10/1.01      ( k2_relat_1(X0) = k1_xboole_0
% 4.10/1.01      | k1_relat_1(X0) != k1_xboole_0
% 4.10/1.01      | v1_relat_1(X0) != iProver_top ),
% 4.10/1.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_6867,plain,
% 4.10/1.01      ( k2_relat_1(sK2) = k1_xboole_0 | v1_relat_1(sK2) != iProver_top ),
% 4.10/1.01      inference(superposition,[status(thm)],[c_6408,c_1258]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_1363,plain,
% 4.10/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 4.10/1.01      | v1_relat_1(sK2) ),
% 4.10/1.01      inference(instantiation,[status(thm)],[c_11]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_1631,plain,
% 4.10/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 4.10/1.01      | v1_relat_1(sK2) ),
% 4.10/1.01      inference(instantiation,[status(thm)],[c_1363]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_1632,plain,
% 4.10/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 4.10/1.01      | v1_relat_1(sK2) = iProver_top ),
% 4.10/1.01      inference(predicate_to_equality,[status(thm)],[c_1631]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_6970,plain,
% 4.10/1.01      ( k2_relat_1(sK2) = k1_xboole_0 ),
% 4.10/1.01      inference(global_propositional_subsumption,
% 4.10/1.01                [status(thm)],
% 4.10/1.01                [c_6867,c_36,c_1632]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_10,plain,
% 4.10/1.01      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
% 4.10/1.01      | ~ v1_funct_1(X0)
% 4.10/1.01      | ~ v1_funct_1(X1)
% 4.10/1.01      | v2_funct_1(X0)
% 4.10/1.01      | ~ v2_funct_1(k5_relat_1(X0,X1))
% 4.10/1.01      | ~ v1_relat_1(X0)
% 4.10/1.01      | ~ v1_relat_1(X1) ),
% 4.10/1.01      inference(cnf_transformation,[],[f61]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_1255,plain,
% 4.10/1.01      ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) != iProver_top
% 4.10/1.01      | v1_funct_1(X0) != iProver_top
% 4.10/1.01      | v1_funct_1(X1) != iProver_top
% 4.10/1.01      | v2_funct_1(X0) = iProver_top
% 4.10/1.01      | v2_funct_1(k5_relat_1(X0,X1)) != iProver_top
% 4.10/1.01      | v1_relat_1(X0) != iProver_top
% 4.10/1.01      | v1_relat_1(X1) != iProver_top ),
% 4.10/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_6974,plain,
% 4.10/1.01      ( r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 4.10/1.01      | v1_funct_1(X0) != iProver_top
% 4.10/1.01      | v1_funct_1(sK2) != iProver_top
% 4.10/1.01      | v2_funct_1(k5_relat_1(sK2,X0)) != iProver_top
% 4.10/1.01      | v2_funct_1(sK2) = iProver_top
% 4.10/1.01      | v1_relat_1(X0) != iProver_top
% 4.10/1.01      | v1_relat_1(sK2) != iProver_top ),
% 4.10/1.01      inference(superposition,[status(thm)],[c_6970,c_1255]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_11738,plain,
% 4.10/1.01      ( v1_relat_1(X0) != iProver_top
% 4.10/1.01      | v1_funct_1(X0) != iProver_top
% 4.10/1.01      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 4.10/1.01      | v2_funct_1(k5_relat_1(sK2,X0)) != iProver_top ),
% 4.10/1.01      inference(global_propositional_subsumption,
% 4.10/1.01                [status(thm)],
% 4.10/1.01                [c_6974,c_34,c_36,c_1632,c_2426,c_2521]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_11739,plain,
% 4.10/1.01      ( r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 4.10/1.01      | v1_funct_1(X0) != iProver_top
% 4.10/1.01      | v2_funct_1(k5_relat_1(sK2,X0)) != iProver_top
% 4.10/1.01      | v1_relat_1(X0) != iProver_top ),
% 4.10/1.01      inference(renaming,[status(thm)],[c_11738]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_11744,plain,
% 4.10/1.01      ( r1_tarski(k1_xboole_0,k1_relat_1(sK3)) != iProver_top
% 4.10/1.01      | v1_funct_1(sK3) != iProver_top
% 4.10/1.01      | v2_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top
% 4.10/1.01      | v1_relat_1(sK3) != iProver_top ),
% 4.10/1.01      inference(superposition,[status(thm)],[c_5872,c_11739]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_6,plain,
% 4.10/1.01      ( ~ v1_relat_1(X0)
% 4.10/1.01      | k2_relat_1(X0) != k1_xboole_0
% 4.10/1.01      | k1_relat_1(X0) = k1_xboole_0 ),
% 4.10/1.01      inference(cnf_transformation,[],[f58]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_1259,plain,
% 4.10/1.01      ( k2_relat_1(X0) != k1_xboole_0
% 4.10/1.01      | k1_relat_1(X0) = k1_xboole_0
% 4.10/1.01      | v1_relat_1(X0) != iProver_top ),
% 4.10/1.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_2431,plain,
% 4.10/1.01      ( k1_relat_1(sK3) = k1_xboole_0
% 4.10/1.01      | sK0 != k1_xboole_0
% 4.10/1.01      | v1_relat_1(sK3) != iProver_top ),
% 4.10/1.01      inference(superposition,[status(thm)],[c_2270,c_1259]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_1503,plain,
% 4.10/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 4.10/1.01      | v1_relat_1(sK3) ),
% 4.10/1.01      inference(instantiation,[status(thm)],[c_11]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_1734,plain,
% 4.10/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 4.10/1.01      | v1_relat_1(sK3) ),
% 4.10/1.01      inference(instantiation,[status(thm)],[c_1503]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_1735,plain,
% 4.10/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 4.10/1.01      | v1_relat_1(sK3) = iProver_top ),
% 4.10/1.01      inference(predicate_to_equality,[status(thm)],[c_1734]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_4994,plain,
% 4.10/1.01      ( sK0 != k1_xboole_0 | k1_relat_1(sK3) = k1_xboole_0 ),
% 4.10/1.01      inference(global_propositional_subsumption,
% 4.10/1.01                [status(thm)],
% 4.10/1.01                [c_2431,c_39,c_1735]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_4995,plain,
% 4.10/1.01      ( k1_relat_1(sK3) = k1_xboole_0 | sK0 != k1_xboole_0 ),
% 4.10/1.01      inference(renaming,[status(thm)],[c_4994]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_5858,plain,
% 4.10/1.01      ( k1_relat_1(sK3) = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 4.10/1.01      inference(demodulation,[status(thm)],[c_5852,c_4995]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_5889,plain,
% 4.10/1.01      ( k1_relat_1(sK3) = k1_xboole_0 ),
% 4.10/1.01      inference(equality_resolution_simp,[status(thm)],[c_5858]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_11745,plain,
% 4.10/1.01      ( r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 4.10/1.01      | v1_funct_1(sK3) != iProver_top
% 4.10/1.01      | v2_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top
% 4.10/1.01      | v1_relat_1(sK3) != iProver_top ),
% 4.10/1.01      inference(light_normalisation,[status(thm)],[c_11744,c_5889]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_108,plain,
% 4.10/1.01      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 4.10/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_110,plain,
% 4.10/1.01      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 4.10/1.01      inference(instantiation,[status(thm)],[c_108]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_93,plain,
% 4.10/1.01      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 4.10/1.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(c_95,plain,
% 4.10/1.01      ( v2_funct_1(k6_partfun1(k1_xboole_0)) = iProver_top ),
% 4.10/1.01      inference(instantiation,[status(thm)],[c_93]) ).
% 4.10/1.01  
% 4.10/1.01  cnf(contradiction,plain,
% 4.10/1.01      ( $false ),
% 4.10/1.01      inference(minisat,
% 4.10/1.01                [status(thm)],
% 4.10/1.01                [c_11745,c_1735,c_110,c_95,c_39,c_37]) ).
% 4.10/1.01  
% 4.10/1.01  
% 4.10/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 4.10/1.01  
% 4.10/1.01  ------                               Statistics
% 4.10/1.01  
% 4.10/1.01  ------ General
% 4.10/1.01  
% 4.10/1.01  abstr_ref_over_cycles:                  0
% 4.10/1.01  abstr_ref_under_cycles:                 0
% 4.10/1.01  gc_basic_clause_elim:                   0
% 4.10/1.01  forced_gc_time:                         0
% 4.10/1.01  parsing_time:                           0.008
% 4.10/1.01  unif_index_cands_time:                  0.
% 4.10/1.01  unif_index_add_time:                    0.
% 4.10/1.01  orderings_time:                         0.
% 4.10/1.01  out_proof_time:                         0.014
% 4.10/1.01  total_time:                             0.413
% 4.10/1.01  num_of_symbols:                         55
% 4.10/1.01  num_of_terms:                           17852
% 4.10/1.01  
% 4.10/1.01  ------ Preprocessing
% 4.10/1.01  
% 4.10/1.01  num_of_splits:                          1
% 4.10/1.01  num_of_split_atoms:                     1
% 4.10/1.01  num_of_reused_defs:                     0
% 4.10/1.01  num_eq_ax_congr_red:                    20
% 4.10/1.01  num_of_sem_filtered_clauses:            1
% 4.10/1.01  num_of_subtypes:                        0
% 4.10/1.01  monotx_restored_types:                  0
% 4.10/1.01  sat_num_of_epr_types:                   0
% 4.10/1.01  sat_num_of_non_cyclic_types:            0
% 4.10/1.01  sat_guarded_non_collapsed_types:        0
% 4.10/1.01  num_pure_diseq_elim:                    0
% 4.10/1.01  simp_replaced_by:                       0
% 4.10/1.01  res_preprocessed:                       145
% 4.10/1.01  prep_upred:                             0
% 4.10/1.01  prep_unflattend:                        17
% 4.10/1.01  smt_new_axioms:                         0
% 4.10/1.01  pred_elim_cands:                        6
% 4.10/1.01  pred_elim:                              4
% 4.10/1.01  pred_elim_cl:                           6
% 4.10/1.01  pred_elim_cycles:                       6
% 4.10/1.01  merged_defs:                            0
% 4.10/1.01  merged_defs_ncl:                        0
% 4.10/1.01  bin_hyper_res:                          0
% 4.10/1.01  prep_cycles:                            4
% 4.10/1.01  pred_elim_time:                         0.004
% 4.10/1.01  splitting_time:                         0.
% 4.10/1.01  sem_filter_time:                        0.
% 4.10/1.01  monotx_time:                            0.
% 4.10/1.01  subtype_inf_time:                       0.
% 4.10/1.01  
% 4.10/1.01  ------ Problem properties
% 4.10/1.01  
% 4.10/1.01  clauses:                                28
% 4.10/1.01  conjectures:                            6
% 4.10/1.01  epr:                                    7
% 4.10/1.01  horn:                                   27
% 4.10/1.01  ground:                                 8
% 4.10/1.01  unary:                                  11
% 4.10/1.01  binary:                                 5
% 4.10/1.01  lits:                                   88
% 4.10/1.01  lits_eq:                                14
% 4.10/1.01  fd_pure:                                0
% 4.10/1.01  fd_pseudo:                              0
% 4.10/1.01  fd_cond:                                1
% 4.10/1.01  fd_pseudo_cond:                         1
% 4.10/1.01  ac_symbols:                             0
% 4.10/1.01  
% 4.10/1.01  ------ Propositional Solver
% 4.10/1.01  
% 4.10/1.01  prop_solver_calls:                      33
% 4.10/1.01  prop_fast_solver_calls:                 1572
% 4.10/1.01  smt_solver_calls:                       0
% 4.10/1.01  smt_fast_solver_calls:                  0
% 4.10/1.01  prop_num_of_clauses:                    6161
% 4.10/1.01  prop_preprocess_simplified:             10795
% 4.10/1.01  prop_fo_subsumed:                       161
% 4.10/1.01  prop_solver_time:                       0.
% 4.10/1.01  smt_solver_time:                        0.
% 4.10/1.01  smt_fast_solver_time:                   0.
% 4.10/1.01  prop_fast_solver_time:                  0.
% 4.10/1.01  prop_unsat_core_time:                   0.
% 4.10/1.01  
% 4.10/1.01  ------ QBF
% 4.10/1.01  
% 4.10/1.01  qbf_q_res:                              0
% 4.10/1.01  qbf_num_tautologies:                    0
% 4.10/1.01  qbf_prep_cycles:                        0
% 4.10/1.01  
% 4.10/1.01  ------ BMC1
% 4.10/1.01  
% 4.10/1.01  bmc1_current_bound:                     -1
% 4.10/1.01  bmc1_last_solved_bound:                 -1
% 4.10/1.01  bmc1_unsat_core_size:                   -1
% 4.10/1.01  bmc1_unsat_core_parents_size:           -1
% 4.10/1.01  bmc1_merge_next_fun:                    0
% 4.10/1.01  bmc1_unsat_core_clauses_time:           0.
% 4.10/1.01  
% 4.10/1.01  ------ Instantiation
% 4.10/1.01  
% 4.10/1.01  inst_num_of_clauses:                    1654
% 4.10/1.01  inst_num_in_passive:                    47
% 4.10/1.01  inst_num_in_active:                     828
% 4.10/1.01  inst_num_in_unprocessed:                779
% 4.10/1.01  inst_num_of_loops:                      890
% 4.10/1.01  inst_num_of_learning_restarts:          0
% 4.10/1.01  inst_num_moves_active_passive:          56
% 4.10/1.01  inst_lit_activity:                      0
% 4.10/1.01  inst_lit_activity_moves:                0
% 4.10/1.01  inst_num_tautologies:                   0
% 4.10/1.01  inst_num_prop_implied:                  0
% 4.10/1.01  inst_num_existing_simplified:           0
% 4.10/1.01  inst_num_eq_res_simplified:             0
% 4.10/1.01  inst_num_child_elim:                    0
% 4.10/1.01  inst_num_of_dismatching_blockings:      526
% 4.10/1.01  inst_num_of_non_proper_insts:           2016
% 4.10/1.01  inst_num_of_duplicates:                 0
% 4.10/1.01  inst_inst_num_from_inst_to_res:         0
% 4.10/1.01  inst_dismatching_checking_time:         0.
% 4.10/1.01  
% 4.10/1.01  ------ Resolution
% 4.10/1.01  
% 4.10/1.01  res_num_of_clauses:                     0
% 4.10/1.02  res_num_in_passive:                     0
% 4.10/1.02  res_num_in_active:                      0
% 4.10/1.02  res_num_of_loops:                       149
% 4.10/1.02  res_forward_subset_subsumed:            147
% 4.10/1.02  res_backward_subset_subsumed:           0
% 4.10/1.02  res_forward_subsumed:                   0
% 4.10/1.02  res_backward_subsumed:                  0
% 4.10/1.02  res_forward_subsumption_resolution:     4
% 4.10/1.02  res_backward_subsumption_resolution:    0
% 4.10/1.02  res_clause_to_clause_subsumption:       777
% 4.10/1.02  res_orphan_elimination:                 0
% 4.10/1.02  res_tautology_del:                      146
% 4.10/1.02  res_num_eq_res_simplified:              1
% 4.10/1.02  res_num_sel_changes:                    0
% 4.10/1.02  res_moves_from_active_to_pass:          0
% 4.10/1.02  
% 4.10/1.02  ------ Superposition
% 4.10/1.02  
% 4.10/1.02  sup_time_total:                         0.
% 4.10/1.02  sup_time_generating:                    0.
% 4.10/1.02  sup_time_sim_full:                      0.
% 4.10/1.02  sup_time_sim_immed:                     0.
% 4.10/1.02  
% 4.10/1.02  sup_num_of_clauses:                     304
% 4.10/1.02  sup_num_in_active:                      130
% 4.10/1.02  sup_num_in_passive:                     174
% 4.10/1.02  sup_num_of_loops:                       177
% 4.10/1.02  sup_fw_superposition:                   186
% 4.10/1.02  sup_bw_superposition:                   195
% 4.10/1.02  sup_immediate_simplified:               112
% 4.10/1.02  sup_given_eliminated:                   1
% 4.10/1.02  comparisons_done:                       0
% 4.10/1.02  comparisons_avoided:                    0
% 4.10/1.02  
% 4.10/1.02  ------ Simplifications
% 4.10/1.02  
% 4.10/1.02  
% 4.10/1.02  sim_fw_subset_subsumed:                 34
% 4.10/1.02  sim_bw_subset_subsumed:                 16
% 4.10/1.02  sim_fw_subsumed:                        15
% 4.10/1.02  sim_bw_subsumed:                        3
% 4.10/1.02  sim_fw_subsumption_res:                 0
% 4.10/1.02  sim_bw_subsumption_res:                 0
% 4.10/1.02  sim_tautology_del:                      0
% 4.10/1.02  sim_eq_tautology_del:                   21
% 4.10/1.02  sim_eq_res_simp:                        2
% 4.10/1.02  sim_fw_demodulated:                     8
% 4.10/1.02  sim_bw_demodulated:                     42
% 4.10/1.02  sim_light_normalised:                   66
% 4.10/1.02  sim_joinable_taut:                      0
% 4.10/1.02  sim_joinable_simp:                      0
% 4.10/1.02  sim_ac_normalised:                      0
% 4.10/1.02  sim_smt_subsumption:                    0
% 4.10/1.02  
%------------------------------------------------------------------------------
