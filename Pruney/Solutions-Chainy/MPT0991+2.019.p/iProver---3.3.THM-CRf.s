%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:43 EST 2020

% Result     : Theorem 2.28s
% Output     : CNFRefutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 249 expanded)
%              Number of clauses        :   60 (  72 expanded)
%              Number of leaves         :   19 (  65 expanded)
%              Depth                    :   18
%              Number of atoms          :  383 (1437 expanded)
%              Number of equality atoms :  115 ( 231 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f23])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ~ ( ~ v2_funct_1(X2)
          & ? [X3] :
              ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ~ ( ~ v2_funct_1(X2)
            & ? [X3] :
                ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
                & v1_funct_2(X3,X1,X0)
                & v1_funct_1(X3) )
            & k1_xboole_0 != X1 ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( ~ v2_funct_1(X2)
      & ? [X3] :
          ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f30,plain,(
    ? [X0,X1,X2] :
      ( ~ v2_funct_1(X2)
      & ? [X3] :
          ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
     => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0))
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(sK3,X1,X0)
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X0,X1,X2] :
        ( ~ v2_funct_1(X2)
        & ? [X3] :
            ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ~ v2_funct_1(sK2)
      & ? [X3] :
          ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & k1_xboole_0 != sK1
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ~ v2_funct_1(sK2)
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & k1_xboole_0 != sK1
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f30,f35,f34])).

fof(f65,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f36])).

fof(f10,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f10])).

fof(f12,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f69,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f52,f55])).

fof(f58,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f60,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f36])).

fof(f62,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f64,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f36])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f25])).

fof(f54,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f13,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f56,plain,(
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
    inference(cnf_transformation,[],[f28])).

fof(f59,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f63,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f66,plain,(
    ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f8,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f67,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f49,f55])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f31])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f71,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f40])).

fof(f2,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f38,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f4])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f43,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f44,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0)
        & v1_xboole_0(X0) )
     => ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f47,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_14,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X2 = X3 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_21,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_309,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_21])).

cnf(c_310,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_309])).

cnf(c_15,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_318,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_310,c_15])).

cnf(c_755,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_318])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_971,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_partfun1(X1,X2,sK1,sK0,X0,sK3),k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1081,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_971])).

cnf(c_1118,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_755,c_28,c_26,c_24,c_22,c_318,c_1081])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v2_funct_1(X3)
    | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_766,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | v1_funct_2(X3,X4,X2) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | v2_funct_1(X3) = iProver_top
    | v2_funct_1(k1_partfun1(X4,X2,X2,X0,X3,X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1763,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK2) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1118,c_766])).

cnf(c_29,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_30,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_31,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_32,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_33,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_34,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_20,negated_conjecture,
    ( ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_36,plain,
    ( v2_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2329,plain,
    ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1763,c_29,c_30,c_31,c_32,c_33,c_34,c_36])).

cnf(c_2330,plain,
    ( sK0 = k1_xboole_0
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2329])).

cnf(c_11,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_771,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2335,plain,
    ( sK0 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2330,c_771])).

cnf(c_761,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2339,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2335,c_761])).

cnf(c_3,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2347,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2339,c_3])).

cnf(c_442,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_990,plain,
    ( X0 != X1
    | sK2 != X1
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_442])).

cnf(c_1242,plain,
    ( X0 != sK2
    | sK2 = X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_990])).

cnf(c_1243,plain,
    ( sK2 != sK2
    | sK2 = k1_xboole_0
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_1242])).

cnf(c_441,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1018,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_441])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_292,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X0 != X2
    | k1_xboole_0 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_5])).

cnf(c_293,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_292])).

cnf(c_1012,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_293])).

cnf(c_1015,plain,
    ( k1_xboole_0 = sK2
    | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1012])).

cnf(c_447,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_918,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(sK2)
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_447])).

cnf(c_920,plain,
    ( v2_funct_1(sK2)
    | ~ v2_funct_1(k1_xboole_0)
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_918])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_6,plain,
    ( v1_relat_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_73,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_7,plain,
    ( v1_funct_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_70,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_8,plain,
    ( v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_67,plain,
    ( v2_funct_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2347,c_1243,c_1018,c_1015,c_920,c_0,c_73,c_70,c_67,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:48:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.28/0.97  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/0.97  
% 2.28/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.28/0.97  
% 2.28/0.97  ------  iProver source info
% 2.28/0.97  
% 2.28/0.97  git: date: 2020-06-30 10:37:57 +0100
% 2.28/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.28/0.97  git: non_committed_changes: false
% 2.28/0.97  git: last_make_outside_of_git: false
% 2.28/0.97  
% 2.28/0.97  ------ 
% 2.28/0.97  
% 2.28/0.97  ------ Input Options
% 2.28/0.97  
% 2.28/0.97  --out_options                           all
% 2.28/0.97  --tptp_safe_out                         true
% 2.28/0.97  --problem_path                          ""
% 2.28/0.97  --include_path                          ""
% 2.28/0.97  --clausifier                            res/vclausify_rel
% 2.28/0.97  --clausifier_options                    --mode clausify
% 2.28/0.97  --stdin                                 false
% 2.28/0.97  --stats_out                             all
% 2.28/0.97  
% 2.28/0.97  ------ General Options
% 2.28/0.97  
% 2.28/0.97  --fof                                   false
% 2.28/0.97  --time_out_real                         305.
% 2.28/0.97  --time_out_virtual                      -1.
% 2.28/0.97  --symbol_type_check                     false
% 2.28/0.97  --clausify_out                          false
% 2.28/0.97  --sig_cnt_out                           false
% 2.28/0.97  --trig_cnt_out                          false
% 2.28/0.97  --trig_cnt_out_tolerance                1.
% 2.28/0.97  --trig_cnt_out_sk_spl                   false
% 2.28/0.97  --abstr_cl_out                          false
% 2.28/0.97  
% 2.28/0.97  ------ Global Options
% 2.28/0.97  
% 2.28/0.97  --schedule                              default
% 2.28/0.97  --add_important_lit                     false
% 2.28/0.97  --prop_solver_per_cl                    1000
% 2.28/0.97  --min_unsat_core                        false
% 2.28/0.97  --soft_assumptions                      false
% 2.28/0.97  --soft_lemma_size                       3
% 2.28/0.97  --prop_impl_unit_size                   0
% 2.28/0.97  --prop_impl_unit                        []
% 2.28/0.97  --share_sel_clauses                     true
% 2.28/0.97  --reset_solvers                         false
% 2.28/0.97  --bc_imp_inh                            [conj_cone]
% 2.28/0.97  --conj_cone_tolerance                   3.
% 2.28/0.97  --extra_neg_conj                        none
% 2.28/0.97  --large_theory_mode                     true
% 2.28/0.97  --prolific_symb_bound                   200
% 2.28/0.97  --lt_threshold                          2000
% 2.28/0.97  --clause_weak_htbl                      true
% 2.28/0.97  --gc_record_bc_elim                     false
% 2.28/0.97  
% 2.28/0.97  ------ Preprocessing Options
% 2.28/0.97  
% 2.28/0.97  --preprocessing_flag                    true
% 2.28/0.97  --time_out_prep_mult                    0.1
% 2.28/0.97  --splitting_mode                        input
% 2.28/0.97  --splitting_grd                         true
% 2.28/0.97  --splitting_cvd                         false
% 2.28/0.97  --splitting_cvd_svl                     false
% 2.28/0.97  --splitting_nvd                         32
% 2.28/0.97  --sub_typing                            true
% 2.28/0.97  --prep_gs_sim                           true
% 2.28/0.97  --prep_unflatten                        true
% 2.28/0.97  --prep_res_sim                          true
% 2.28/0.97  --prep_upred                            true
% 2.28/0.97  --prep_sem_filter                       exhaustive
% 2.28/0.97  --prep_sem_filter_out                   false
% 2.28/0.97  --pred_elim                             true
% 2.28/0.97  --res_sim_input                         true
% 2.28/0.97  --eq_ax_congr_red                       true
% 2.28/0.97  --pure_diseq_elim                       true
% 2.28/0.97  --brand_transform                       false
% 2.28/0.97  --non_eq_to_eq                          false
% 2.28/0.97  --prep_def_merge                        true
% 2.28/0.97  --prep_def_merge_prop_impl              false
% 2.28/0.97  --prep_def_merge_mbd                    true
% 2.28/0.97  --prep_def_merge_tr_red                 false
% 2.28/0.97  --prep_def_merge_tr_cl                  false
% 2.28/0.97  --smt_preprocessing                     true
% 2.28/0.97  --smt_ac_axioms                         fast
% 2.28/0.97  --preprocessed_out                      false
% 2.28/0.97  --preprocessed_stats                    false
% 2.28/0.97  
% 2.28/0.97  ------ Abstraction refinement Options
% 2.28/0.97  
% 2.28/0.97  --abstr_ref                             []
% 2.28/0.97  --abstr_ref_prep                        false
% 2.28/0.97  --abstr_ref_until_sat                   false
% 2.28/0.97  --abstr_ref_sig_restrict                funpre
% 2.28/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.28/0.97  --abstr_ref_under                       []
% 2.28/0.97  
% 2.28/0.97  ------ SAT Options
% 2.28/0.97  
% 2.28/0.97  --sat_mode                              false
% 2.28/0.97  --sat_fm_restart_options                ""
% 2.28/0.97  --sat_gr_def                            false
% 2.28/0.97  --sat_epr_types                         true
% 2.28/0.97  --sat_non_cyclic_types                  false
% 2.28/0.97  --sat_finite_models                     false
% 2.28/0.97  --sat_fm_lemmas                         false
% 2.28/0.97  --sat_fm_prep                           false
% 2.28/0.98  --sat_fm_uc_incr                        true
% 2.28/0.98  --sat_out_model                         small
% 2.28/0.98  --sat_out_clauses                       false
% 2.28/0.98  
% 2.28/0.98  ------ QBF Options
% 2.28/0.98  
% 2.28/0.98  --qbf_mode                              false
% 2.28/0.98  --qbf_elim_univ                         false
% 2.28/0.98  --qbf_dom_inst                          none
% 2.28/0.98  --qbf_dom_pre_inst                      false
% 2.28/0.98  --qbf_sk_in                             false
% 2.28/0.98  --qbf_pred_elim                         true
% 2.28/0.98  --qbf_split                             512
% 2.28/0.98  
% 2.28/0.98  ------ BMC1 Options
% 2.28/0.98  
% 2.28/0.98  --bmc1_incremental                      false
% 2.28/0.98  --bmc1_axioms                           reachable_all
% 2.28/0.98  --bmc1_min_bound                        0
% 2.28/0.98  --bmc1_max_bound                        -1
% 2.28/0.98  --bmc1_max_bound_default                -1
% 2.28/0.98  --bmc1_symbol_reachability              true
% 2.28/0.98  --bmc1_property_lemmas                  false
% 2.28/0.98  --bmc1_k_induction                      false
% 2.28/0.98  --bmc1_non_equiv_states                 false
% 2.28/0.98  --bmc1_deadlock                         false
% 2.28/0.98  --bmc1_ucm                              false
% 2.28/0.98  --bmc1_add_unsat_core                   none
% 2.28/0.98  --bmc1_unsat_core_children              false
% 2.28/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.28/0.98  --bmc1_out_stat                         full
% 2.28/0.98  --bmc1_ground_init                      false
% 2.28/0.98  --bmc1_pre_inst_next_state              false
% 2.28/0.98  --bmc1_pre_inst_state                   false
% 2.28/0.98  --bmc1_pre_inst_reach_state             false
% 2.28/0.98  --bmc1_out_unsat_core                   false
% 2.28/0.98  --bmc1_aig_witness_out                  false
% 2.28/0.98  --bmc1_verbose                          false
% 2.28/0.98  --bmc1_dump_clauses_tptp                false
% 2.28/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.28/0.98  --bmc1_dump_file                        -
% 2.28/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.28/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.28/0.98  --bmc1_ucm_extend_mode                  1
% 2.28/0.98  --bmc1_ucm_init_mode                    2
% 2.28/0.98  --bmc1_ucm_cone_mode                    none
% 2.28/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.28/0.98  --bmc1_ucm_relax_model                  4
% 2.28/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.28/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.28/0.98  --bmc1_ucm_layered_model                none
% 2.28/0.98  --bmc1_ucm_max_lemma_size               10
% 2.28/0.98  
% 2.28/0.98  ------ AIG Options
% 2.28/0.98  
% 2.28/0.98  --aig_mode                              false
% 2.28/0.98  
% 2.28/0.98  ------ Instantiation Options
% 2.28/0.98  
% 2.28/0.98  --instantiation_flag                    true
% 2.28/0.98  --inst_sos_flag                         false
% 2.28/0.98  --inst_sos_phase                        true
% 2.28/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.28/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.28/0.98  --inst_lit_sel_side                     num_symb
% 2.28/0.98  --inst_solver_per_active                1400
% 2.28/0.98  --inst_solver_calls_frac                1.
% 2.28/0.98  --inst_passive_queue_type               priority_queues
% 2.28/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.28/0.98  --inst_passive_queues_freq              [25;2]
% 2.28/0.98  --inst_dismatching                      true
% 2.28/0.98  --inst_eager_unprocessed_to_passive     true
% 2.28/0.98  --inst_prop_sim_given                   true
% 2.28/0.98  --inst_prop_sim_new                     false
% 2.28/0.98  --inst_subs_new                         false
% 2.28/0.98  --inst_eq_res_simp                      false
% 2.28/0.98  --inst_subs_given                       false
% 2.28/0.98  --inst_orphan_elimination               true
% 2.28/0.98  --inst_learning_loop_flag               true
% 2.28/0.98  --inst_learning_start                   3000
% 2.28/0.98  --inst_learning_factor                  2
% 2.28/0.98  --inst_start_prop_sim_after_learn       3
% 2.28/0.98  --inst_sel_renew                        solver
% 2.28/0.98  --inst_lit_activity_flag                true
% 2.28/0.98  --inst_restr_to_given                   false
% 2.28/0.98  --inst_activity_threshold               500
% 2.28/0.98  --inst_out_proof                        true
% 2.28/0.98  
% 2.28/0.98  ------ Resolution Options
% 2.28/0.98  
% 2.28/0.98  --resolution_flag                       true
% 2.28/0.98  --res_lit_sel                           adaptive
% 2.28/0.98  --res_lit_sel_side                      none
% 2.28/0.98  --res_ordering                          kbo
% 2.28/0.98  --res_to_prop_solver                    active
% 2.28/0.98  --res_prop_simpl_new                    false
% 2.28/0.98  --res_prop_simpl_given                  true
% 2.28/0.98  --res_passive_queue_type                priority_queues
% 2.28/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.28/0.98  --res_passive_queues_freq               [15;5]
% 2.28/0.98  --res_forward_subs                      full
% 2.28/0.98  --res_backward_subs                     full
% 2.28/0.98  --res_forward_subs_resolution           true
% 2.28/0.98  --res_backward_subs_resolution          true
% 2.28/0.98  --res_orphan_elimination                true
% 2.28/0.98  --res_time_limit                        2.
% 2.28/0.98  --res_out_proof                         true
% 2.28/0.98  
% 2.28/0.98  ------ Superposition Options
% 2.28/0.98  
% 2.28/0.98  --superposition_flag                    true
% 2.28/0.98  --sup_passive_queue_type                priority_queues
% 2.28/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.28/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.28/0.98  --demod_completeness_check              fast
% 2.28/0.98  --demod_use_ground                      true
% 2.28/0.98  --sup_to_prop_solver                    passive
% 2.28/0.98  --sup_prop_simpl_new                    true
% 2.28/0.98  --sup_prop_simpl_given                  true
% 2.28/0.98  --sup_fun_splitting                     false
% 2.28/0.98  --sup_smt_interval                      50000
% 2.28/0.98  
% 2.28/0.98  ------ Superposition Simplification Setup
% 2.28/0.98  
% 2.28/0.98  --sup_indices_passive                   []
% 2.28/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.28/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.28/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.28/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.28/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.28/0.98  --sup_full_bw                           [BwDemod]
% 2.28/0.98  --sup_immed_triv                        [TrivRules]
% 2.28/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.28/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.28/0.98  --sup_immed_bw_main                     []
% 2.28/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.28/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.28/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.28/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.28/0.98  
% 2.28/0.98  ------ Combination Options
% 2.28/0.98  
% 2.28/0.98  --comb_res_mult                         3
% 2.28/0.98  --comb_sup_mult                         2
% 2.28/0.98  --comb_inst_mult                        10
% 2.28/0.98  
% 2.28/0.98  ------ Debug Options
% 2.28/0.98  
% 2.28/0.98  --dbg_backtrace                         false
% 2.28/0.98  --dbg_dump_prop_clauses                 false
% 2.28/0.98  --dbg_dump_prop_clauses_file            -
% 2.28/0.98  --dbg_out_stat                          false
% 2.28/0.98  ------ Parsing...
% 2.28/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.28/0.98  
% 2.28/0.98  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 2.28/0.98  
% 2.28/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.28/0.98  
% 2.28/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.28/0.98  ------ Proving...
% 2.28/0.98  ------ Problem Properties 
% 2.28/0.98  
% 2.28/0.98  
% 2.28/0.98  clauses                                 21
% 2.28/0.98  conjectures                             8
% 2.28/0.98  EPR                                     8
% 2.28/0.98  Horn                                    19
% 2.28/0.98  unary                                   14
% 2.28/0.98  binary                                  2
% 2.28/0.98  lits                                    48
% 2.28/0.98  lits eq                                 9
% 2.28/0.98  fd_pure                                 0
% 2.28/0.98  fd_pseudo                               0
% 2.28/0.98  fd_cond                                 3
% 2.28/0.98  fd_pseudo_cond                          0
% 2.28/0.98  AC symbols                              0
% 2.28/0.98  
% 2.28/0.98  ------ Schedule dynamic 5 is on 
% 2.28/0.98  
% 2.28/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.28/0.98  
% 2.28/0.98  
% 2.28/0.98  ------ 
% 2.28/0.98  Current options:
% 2.28/0.98  ------ 
% 2.28/0.98  
% 2.28/0.98  ------ Input Options
% 2.28/0.98  
% 2.28/0.98  --out_options                           all
% 2.28/0.98  --tptp_safe_out                         true
% 2.28/0.98  --problem_path                          ""
% 2.28/0.98  --include_path                          ""
% 2.28/0.98  --clausifier                            res/vclausify_rel
% 2.28/0.98  --clausifier_options                    --mode clausify
% 2.28/0.98  --stdin                                 false
% 2.28/0.98  --stats_out                             all
% 2.28/0.98  
% 2.28/0.98  ------ General Options
% 2.28/0.98  
% 2.28/0.98  --fof                                   false
% 2.28/0.98  --time_out_real                         305.
% 2.28/0.98  --time_out_virtual                      -1.
% 2.28/0.98  --symbol_type_check                     false
% 2.28/0.98  --clausify_out                          false
% 2.28/0.98  --sig_cnt_out                           false
% 2.28/0.98  --trig_cnt_out                          false
% 2.28/0.98  --trig_cnt_out_tolerance                1.
% 2.28/0.98  --trig_cnt_out_sk_spl                   false
% 2.28/0.98  --abstr_cl_out                          false
% 2.28/0.98  
% 2.28/0.98  ------ Global Options
% 2.28/0.98  
% 2.28/0.98  --schedule                              default
% 2.28/0.98  --add_important_lit                     false
% 2.28/0.98  --prop_solver_per_cl                    1000
% 2.28/0.98  --min_unsat_core                        false
% 2.28/0.98  --soft_assumptions                      false
% 2.28/0.98  --soft_lemma_size                       3
% 2.28/0.98  --prop_impl_unit_size                   0
% 2.28/0.98  --prop_impl_unit                        []
% 2.28/0.98  --share_sel_clauses                     true
% 2.28/0.98  --reset_solvers                         false
% 2.28/0.98  --bc_imp_inh                            [conj_cone]
% 2.28/0.98  --conj_cone_tolerance                   3.
% 2.28/0.98  --extra_neg_conj                        none
% 2.28/0.98  --large_theory_mode                     true
% 2.28/0.98  --prolific_symb_bound                   200
% 2.28/0.98  --lt_threshold                          2000
% 2.28/0.98  --clause_weak_htbl                      true
% 2.28/0.98  --gc_record_bc_elim                     false
% 2.28/0.98  
% 2.28/0.98  ------ Preprocessing Options
% 2.28/0.98  
% 2.28/0.98  --preprocessing_flag                    true
% 2.28/0.98  --time_out_prep_mult                    0.1
% 2.28/0.98  --splitting_mode                        input
% 2.28/0.98  --splitting_grd                         true
% 2.28/0.98  --splitting_cvd                         false
% 2.28/0.98  --splitting_cvd_svl                     false
% 2.28/0.98  --splitting_nvd                         32
% 2.28/0.98  --sub_typing                            true
% 2.28/0.98  --prep_gs_sim                           true
% 2.28/0.98  --prep_unflatten                        true
% 2.28/0.98  --prep_res_sim                          true
% 2.28/0.98  --prep_upred                            true
% 2.28/0.98  --prep_sem_filter                       exhaustive
% 2.28/0.98  --prep_sem_filter_out                   false
% 2.28/0.98  --pred_elim                             true
% 2.28/0.98  --res_sim_input                         true
% 2.28/0.98  --eq_ax_congr_red                       true
% 2.28/0.98  --pure_diseq_elim                       true
% 2.28/0.98  --brand_transform                       false
% 2.28/0.98  --non_eq_to_eq                          false
% 2.28/0.98  --prep_def_merge                        true
% 2.28/0.98  --prep_def_merge_prop_impl              false
% 2.28/0.98  --prep_def_merge_mbd                    true
% 2.28/0.98  --prep_def_merge_tr_red                 false
% 2.28/0.98  --prep_def_merge_tr_cl                  false
% 2.28/0.98  --smt_preprocessing                     true
% 2.28/0.98  --smt_ac_axioms                         fast
% 2.28/0.98  --preprocessed_out                      false
% 2.28/0.98  --preprocessed_stats                    false
% 2.28/0.98  
% 2.28/0.98  ------ Abstraction refinement Options
% 2.28/0.98  
% 2.28/0.98  --abstr_ref                             []
% 2.28/0.98  --abstr_ref_prep                        false
% 2.28/0.98  --abstr_ref_until_sat                   false
% 2.28/0.98  --abstr_ref_sig_restrict                funpre
% 2.28/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.28/0.98  --abstr_ref_under                       []
% 2.28/0.98  
% 2.28/0.98  ------ SAT Options
% 2.28/0.98  
% 2.28/0.98  --sat_mode                              false
% 2.28/0.98  --sat_fm_restart_options                ""
% 2.28/0.98  --sat_gr_def                            false
% 2.28/0.98  --sat_epr_types                         true
% 2.28/0.98  --sat_non_cyclic_types                  false
% 2.28/0.98  --sat_finite_models                     false
% 2.28/0.98  --sat_fm_lemmas                         false
% 2.28/0.98  --sat_fm_prep                           false
% 2.28/0.98  --sat_fm_uc_incr                        true
% 2.28/0.98  --sat_out_model                         small
% 2.28/0.98  --sat_out_clauses                       false
% 2.28/0.98  
% 2.28/0.98  ------ QBF Options
% 2.28/0.98  
% 2.28/0.98  --qbf_mode                              false
% 2.28/0.98  --qbf_elim_univ                         false
% 2.28/0.98  --qbf_dom_inst                          none
% 2.28/0.98  --qbf_dom_pre_inst                      false
% 2.28/0.98  --qbf_sk_in                             false
% 2.28/0.98  --qbf_pred_elim                         true
% 2.28/0.98  --qbf_split                             512
% 2.28/0.98  
% 2.28/0.98  ------ BMC1 Options
% 2.28/0.98  
% 2.28/0.98  --bmc1_incremental                      false
% 2.28/0.98  --bmc1_axioms                           reachable_all
% 2.28/0.98  --bmc1_min_bound                        0
% 2.28/0.98  --bmc1_max_bound                        -1
% 2.28/0.98  --bmc1_max_bound_default                -1
% 2.28/0.98  --bmc1_symbol_reachability              true
% 2.28/0.98  --bmc1_property_lemmas                  false
% 2.28/0.98  --bmc1_k_induction                      false
% 2.28/0.98  --bmc1_non_equiv_states                 false
% 2.28/0.98  --bmc1_deadlock                         false
% 2.28/0.98  --bmc1_ucm                              false
% 2.28/0.98  --bmc1_add_unsat_core                   none
% 2.28/0.98  --bmc1_unsat_core_children              false
% 2.28/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.28/0.98  --bmc1_out_stat                         full
% 2.28/0.98  --bmc1_ground_init                      false
% 2.28/0.98  --bmc1_pre_inst_next_state              false
% 2.28/0.98  --bmc1_pre_inst_state                   false
% 2.28/0.98  --bmc1_pre_inst_reach_state             false
% 2.28/0.98  --bmc1_out_unsat_core                   false
% 2.28/0.98  --bmc1_aig_witness_out                  false
% 2.28/0.98  --bmc1_verbose                          false
% 2.28/0.98  --bmc1_dump_clauses_tptp                false
% 2.28/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.28/0.98  --bmc1_dump_file                        -
% 2.28/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.28/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.28/0.98  --bmc1_ucm_extend_mode                  1
% 2.28/0.98  --bmc1_ucm_init_mode                    2
% 2.28/0.98  --bmc1_ucm_cone_mode                    none
% 2.28/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.28/0.98  --bmc1_ucm_relax_model                  4
% 2.28/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.28/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.28/0.98  --bmc1_ucm_layered_model                none
% 2.28/0.98  --bmc1_ucm_max_lemma_size               10
% 2.28/0.98  
% 2.28/0.98  ------ AIG Options
% 2.28/0.98  
% 2.28/0.98  --aig_mode                              false
% 2.28/0.98  
% 2.28/0.98  ------ Instantiation Options
% 2.28/0.98  
% 2.28/0.98  --instantiation_flag                    true
% 2.28/0.98  --inst_sos_flag                         false
% 2.28/0.98  --inst_sos_phase                        true
% 2.28/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.28/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.28/0.98  --inst_lit_sel_side                     none
% 2.28/0.98  --inst_solver_per_active                1400
% 2.28/0.98  --inst_solver_calls_frac                1.
% 2.28/0.98  --inst_passive_queue_type               priority_queues
% 2.28/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.28/0.98  --inst_passive_queues_freq              [25;2]
% 2.28/0.98  --inst_dismatching                      true
% 2.28/0.98  --inst_eager_unprocessed_to_passive     true
% 2.28/0.98  --inst_prop_sim_given                   true
% 2.28/0.98  --inst_prop_sim_new                     false
% 2.28/0.98  --inst_subs_new                         false
% 2.28/0.98  --inst_eq_res_simp                      false
% 2.28/0.98  --inst_subs_given                       false
% 2.28/0.98  --inst_orphan_elimination               true
% 2.28/0.98  --inst_learning_loop_flag               true
% 2.28/0.98  --inst_learning_start                   3000
% 2.28/0.98  --inst_learning_factor                  2
% 2.28/0.98  --inst_start_prop_sim_after_learn       3
% 2.28/0.98  --inst_sel_renew                        solver
% 2.28/0.98  --inst_lit_activity_flag                true
% 2.28/0.98  --inst_restr_to_given                   false
% 2.28/0.98  --inst_activity_threshold               500
% 2.28/0.98  --inst_out_proof                        true
% 2.28/0.98  
% 2.28/0.98  ------ Resolution Options
% 2.28/0.98  
% 2.28/0.98  --resolution_flag                       false
% 2.28/0.98  --res_lit_sel                           adaptive
% 2.28/0.98  --res_lit_sel_side                      none
% 2.28/0.98  --res_ordering                          kbo
% 2.28/0.98  --res_to_prop_solver                    active
% 2.28/0.98  --res_prop_simpl_new                    false
% 2.28/0.98  --res_prop_simpl_given                  true
% 2.28/0.98  --res_passive_queue_type                priority_queues
% 2.28/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.28/0.98  --res_passive_queues_freq               [15;5]
% 2.28/0.98  --res_forward_subs                      full
% 2.28/0.98  --res_backward_subs                     full
% 2.28/0.98  --res_forward_subs_resolution           true
% 2.28/0.98  --res_backward_subs_resolution          true
% 2.28/0.98  --res_orphan_elimination                true
% 2.28/0.98  --res_time_limit                        2.
% 2.28/0.98  --res_out_proof                         true
% 2.28/0.98  
% 2.28/0.98  ------ Superposition Options
% 2.28/0.98  
% 2.28/0.98  --superposition_flag                    true
% 2.28/0.98  --sup_passive_queue_type                priority_queues
% 2.28/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.28/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.28/0.98  --demod_completeness_check              fast
% 2.28/0.98  --demod_use_ground                      true
% 2.28/0.98  --sup_to_prop_solver                    passive
% 2.28/0.98  --sup_prop_simpl_new                    true
% 2.28/0.98  --sup_prop_simpl_given                  true
% 2.28/0.98  --sup_fun_splitting                     false
% 2.28/0.98  --sup_smt_interval                      50000
% 2.28/0.98  
% 2.28/0.98  ------ Superposition Simplification Setup
% 2.28/0.98  
% 2.28/0.98  --sup_indices_passive                   []
% 2.28/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.28/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.28/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.28/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.28/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.28/0.98  --sup_full_bw                           [BwDemod]
% 2.28/0.98  --sup_immed_triv                        [TrivRules]
% 2.28/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.28/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.28/0.98  --sup_immed_bw_main                     []
% 2.28/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.28/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.28/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.28/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.28/0.98  
% 2.28/0.98  ------ Combination Options
% 2.28/0.98  
% 2.28/0.98  --comb_res_mult                         3
% 2.28/0.98  --comb_sup_mult                         2
% 2.28/0.98  --comb_inst_mult                        10
% 2.28/0.98  
% 2.28/0.98  ------ Debug Options
% 2.28/0.98  
% 2.28/0.98  --dbg_backtrace                         false
% 2.28/0.98  --dbg_dump_prop_clauses                 false
% 2.28/0.98  --dbg_dump_prop_clauses_file            -
% 2.28/0.98  --dbg_out_stat                          false
% 2.28/0.98  
% 2.28/0.98  
% 2.28/0.98  
% 2.28/0.98  
% 2.28/0.98  ------ Proving...
% 2.28/0.98  
% 2.28/0.98  
% 2.28/0.98  % SZS status Theorem for theBenchmark.p
% 2.28/0.98  
% 2.28/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.28/0.98  
% 2.28/0.98  fof(f9,axiom,(
% 2.28/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.28/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.28/0.98  
% 2.28/0.98  fof(f23,plain,(
% 2.28/0.98    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.28/0.98    inference(ennf_transformation,[],[f9])).
% 2.28/0.98  
% 2.28/0.98  fof(f24,plain,(
% 2.28/0.98    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.28/0.98    inference(flattening,[],[f23])).
% 2.28/0.98  
% 2.28/0.98  fof(f33,plain,(
% 2.28/0.98    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.28/0.98    inference(nnf_transformation,[],[f24])).
% 2.28/0.98  
% 2.28/0.98  fof(f50,plain,(
% 2.28/0.98    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.28/0.98    inference(cnf_transformation,[],[f33])).
% 2.28/0.98  
% 2.28/0.98  fof(f14,conjecture,(
% 2.28/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ~(~v2_funct_1(X2) & ? [X3] : (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & k1_xboole_0 != X1))),
% 2.28/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.28/0.98  
% 2.28/0.98  fof(f15,negated_conjecture,(
% 2.28/0.98    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ~(~v2_funct_1(X2) & ? [X3] : (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & k1_xboole_0 != X1))),
% 2.28/0.98    inference(negated_conjecture,[],[f14])).
% 2.28/0.98  
% 2.28/0.98  fof(f29,plain,(
% 2.28/0.98    ? [X0,X1,X2] : ((~v2_funct_1(X2) & ? [X3] : (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.28/0.98    inference(ennf_transformation,[],[f15])).
% 2.28/0.98  
% 2.28/0.98  fof(f30,plain,(
% 2.28/0.98    ? [X0,X1,X2] : (~v2_funct_1(X2) & ? [X3] : (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.28/0.98    inference(flattening,[],[f29])).
% 2.28/0.98  
% 2.28/0.98  fof(f35,plain,(
% 2.28/0.98    ( ! [X2,X0,X1] : (? [X3] : (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 2.28/0.98    introduced(choice_axiom,[])).
% 2.28/0.98  
% 2.28/0.98  fof(f34,plain,(
% 2.28/0.98    ? [X0,X1,X2] : (~v2_funct_1(X2) & ? [X3] : (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (~v2_funct_1(sK2) & ? [X3] : (r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 2.28/0.98    introduced(choice_axiom,[])).
% 2.28/0.98  
% 2.28/0.98  fof(f36,plain,(
% 2.28/0.98    ~v2_funct_1(sK2) & (r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 2.28/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f30,f35,f34])).
% 2.28/0.98  
% 2.28/0.98  fof(f65,plain,(
% 2.28/0.98    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.28/0.98    inference(cnf_transformation,[],[f36])).
% 2.28/0.98  
% 2.28/0.98  fof(f10,axiom,(
% 2.28/0.98    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 2.28/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.28/0.98  
% 2.28/0.98  fof(f52,plain,(
% 2.28/0.98    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.28/0.98    inference(cnf_transformation,[],[f10])).
% 2.28/0.98  
% 2.28/0.98  fof(f12,axiom,(
% 2.28/0.98    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.28/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.28/0.98  
% 2.28/0.98  fof(f55,plain,(
% 2.28/0.98    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.28/0.98    inference(cnf_transformation,[],[f12])).
% 2.28/0.98  
% 2.28/0.98  fof(f69,plain,(
% 2.28/0.98    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.28/0.98    inference(definition_unfolding,[],[f52,f55])).
% 2.28/0.98  
% 2.28/0.98  fof(f58,plain,(
% 2.28/0.98    v1_funct_1(sK2)),
% 2.28/0.98    inference(cnf_transformation,[],[f36])).
% 2.28/0.98  
% 2.28/0.98  fof(f60,plain,(
% 2.28/0.98    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.28/0.98    inference(cnf_transformation,[],[f36])).
% 2.28/0.98  
% 2.28/0.98  fof(f62,plain,(
% 2.28/0.98    v1_funct_1(sK3)),
% 2.28/0.98    inference(cnf_transformation,[],[f36])).
% 2.28/0.98  
% 2.28/0.98  fof(f64,plain,(
% 2.28/0.98    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.28/0.98    inference(cnf_transformation,[],[f36])).
% 2.28/0.98  
% 2.28/0.98  fof(f11,axiom,(
% 2.28/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 2.28/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.28/0.98  
% 2.28/0.98  fof(f25,plain,(
% 2.28/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.28/0.98    inference(ennf_transformation,[],[f11])).
% 2.28/0.98  
% 2.28/0.98  fof(f26,plain,(
% 2.28/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.28/0.98    inference(flattening,[],[f25])).
% 2.28/0.98  
% 2.28/0.98  fof(f54,plain,(
% 2.28/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.28/0.98    inference(cnf_transformation,[],[f26])).
% 2.28/0.98  
% 2.28/0.98  fof(f13,axiom,(
% 2.28/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 2.28/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.28/0.98  
% 2.28/0.98  fof(f27,plain,(
% 2.28/0.98    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.28/0.98    inference(ennf_transformation,[],[f13])).
% 2.28/0.98  
% 2.28/0.98  fof(f28,plain,(
% 2.28/0.98    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.28/0.98    inference(flattening,[],[f27])).
% 2.28/0.98  
% 2.28/0.98  fof(f56,plain,(
% 2.28/0.98    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X3) | k1_xboole_0 = X2 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.28/0.98    inference(cnf_transformation,[],[f28])).
% 2.28/0.98  
% 2.28/0.98  fof(f59,plain,(
% 2.28/0.98    v1_funct_2(sK2,sK0,sK1)),
% 2.28/0.98    inference(cnf_transformation,[],[f36])).
% 2.28/0.98  
% 2.28/0.98  fof(f63,plain,(
% 2.28/0.98    v1_funct_2(sK3,sK1,sK0)),
% 2.28/0.98    inference(cnf_transformation,[],[f36])).
% 2.28/0.98  
% 2.28/0.98  fof(f66,plain,(
% 2.28/0.98    ~v2_funct_1(sK2)),
% 2.28/0.98    inference(cnf_transformation,[],[f36])).
% 2.28/0.98  
% 2.28/0.98  fof(f8,axiom,(
% 2.28/0.98    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.28/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.28/0.98  
% 2.28/0.98  fof(f49,plain,(
% 2.28/0.98    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 2.28/0.98    inference(cnf_transformation,[],[f8])).
% 2.28/0.98  
% 2.28/0.98  fof(f67,plain,(
% 2.28/0.98    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 2.28/0.98    inference(definition_unfolding,[],[f49,f55])).
% 2.28/0.98  
% 2.28/0.98  fof(f3,axiom,(
% 2.28/0.98    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.28/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.28/0.98  
% 2.28/0.98  fof(f31,plain,(
% 2.28/0.98    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.28/0.98    inference(nnf_transformation,[],[f3])).
% 2.28/0.98  
% 2.28/0.98  fof(f32,plain,(
% 2.28/0.98    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.28/0.98    inference(flattening,[],[f31])).
% 2.28/0.98  
% 2.28/0.98  fof(f40,plain,(
% 2.28/0.98    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.28/0.98    inference(cnf_transformation,[],[f32])).
% 2.28/0.98  
% 2.28/0.98  fof(f71,plain,(
% 2.28/0.98    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.28/0.98    inference(equality_resolution,[],[f40])).
% 2.28/0.98  
% 2.28/0.98  fof(f2,axiom,(
% 2.28/0.98    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 2.28/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.28/0.98  
% 2.28/0.98  fof(f17,plain,(
% 2.28/0.98    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 2.28/0.98    inference(ennf_transformation,[],[f2])).
% 2.28/0.98  
% 2.28/0.98  fof(f38,plain,(
% 2.28/0.98    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 2.28/0.98    inference(cnf_transformation,[],[f17])).
% 2.28/0.98  
% 2.28/0.98  fof(f4,axiom,(
% 2.28/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.28/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.28/0.98  
% 2.28/0.98  fof(f16,plain,(
% 2.28/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 2.28/0.98    inference(unused_predicate_definition_removal,[],[f4])).
% 2.28/0.98  
% 2.28/0.98  fof(f18,plain,(
% 2.28/0.98    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 2.28/0.98    inference(ennf_transformation,[],[f16])).
% 2.28/0.98  
% 2.28/0.98  fof(f42,plain,(
% 2.28/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.28/0.98    inference(cnf_transformation,[],[f18])).
% 2.28/0.98  
% 2.28/0.98  fof(f1,axiom,(
% 2.28/0.98    v1_xboole_0(k1_xboole_0)),
% 2.28/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.28/0.98  
% 2.28/0.98  fof(f37,plain,(
% 2.28/0.98    v1_xboole_0(k1_xboole_0)),
% 2.28/0.98    inference(cnf_transformation,[],[f1])).
% 2.28/0.98  
% 2.28/0.98  fof(f5,axiom,(
% 2.28/0.98    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 2.28/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.28/0.98  
% 2.28/0.98  fof(f19,plain,(
% 2.28/0.98    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 2.28/0.98    inference(ennf_transformation,[],[f5])).
% 2.28/0.98  
% 2.28/0.98  fof(f43,plain,(
% 2.28/0.98    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 2.28/0.98    inference(cnf_transformation,[],[f19])).
% 2.28/0.98  
% 2.28/0.98  fof(f6,axiom,(
% 2.28/0.98    ! [X0] : (v1_xboole_0(X0) => v1_funct_1(X0))),
% 2.28/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.28/0.98  
% 2.28/0.98  fof(f20,plain,(
% 2.28/0.98    ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 2.28/0.98    inference(ennf_transformation,[],[f6])).
% 2.28/0.98  
% 2.28/0.98  fof(f44,plain,(
% 2.28/0.98    ( ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0)) )),
% 2.28/0.98    inference(cnf_transformation,[],[f20])).
% 2.28/0.98  
% 2.28/0.98  fof(f7,axiom,(
% 2.28/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0) & v1_xboole_0(X0)) => (v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)))),
% 2.28/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.28/0.98  
% 2.28/0.98  fof(f21,plain,(
% 2.28/0.98    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_xboole_0(X0)))),
% 2.28/0.98    inference(ennf_transformation,[],[f7])).
% 2.28/0.98  
% 2.28/0.98  fof(f22,plain,(
% 2.28/0.98    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 2.28/0.98    inference(flattening,[],[f21])).
% 2.28/0.98  
% 2.28/0.98  fof(f47,plain,(
% 2.28/0.98    ( ! [X0] : (v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 2.28/0.98    inference(cnf_transformation,[],[f22])).
% 2.28/0.98  
% 2.28/0.98  cnf(c_14,plain,
% 2.28/0.98      ( ~ r2_relset_1(X0,X1,X2,X3)
% 2.28/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.28/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.28/0.98      | X2 = X3 ),
% 2.28/0.98      inference(cnf_transformation,[],[f50]) ).
% 2.28/0.98  
% 2.28/0.98  cnf(c_21,negated_conjecture,
% 2.28/0.98      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 2.28/0.98      inference(cnf_transformation,[],[f65]) ).
% 2.28/0.98  
% 2.28/0.98  cnf(c_309,plain,
% 2.28/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.28/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.28/0.98      | X3 = X0
% 2.28/0.98      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 2.28/0.98      | k6_partfun1(sK0) != X3
% 2.28/0.98      | sK0 != X2
% 2.28/0.98      | sK0 != X1 ),
% 2.28/0.98      inference(resolution_lifted,[status(thm)],[c_14,c_21]) ).
% 2.28/0.98  
% 2.28/0.98  cnf(c_310,plain,
% 2.28/0.98      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.28/0.98      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.28/0.98      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 2.28/0.98      inference(unflattening,[status(thm)],[c_309]) ).
% 2.28/0.98  
% 2.28/0.98  cnf(c_15,plain,
% 2.28/0.98      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 2.28/0.98      inference(cnf_transformation,[],[f69]) ).
% 2.28/0.98  
% 2.28/0.98  cnf(c_318,plain,
% 2.28/0.98      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.28/0.98      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 2.28/0.98      inference(forward_subsumption_resolution,
% 2.28/0.98                [status(thm)],
% 2.28/0.98                [c_310,c_15]) ).
% 2.28/0.98  
% 2.28/0.98  cnf(c_755,plain,
% 2.28/0.98      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 2.28/0.98      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 2.28/0.98      inference(predicate_to_equality,[status(thm)],[c_318]) ).
% 2.28/0.98  
% 2.28/0.98  cnf(c_28,negated_conjecture,
% 2.28/0.98      ( v1_funct_1(sK2) ),
% 2.28/0.98      inference(cnf_transformation,[],[f58]) ).
% 2.28/0.98  
% 2.28/0.98  cnf(c_26,negated_conjecture,
% 2.28/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.28/0.98      inference(cnf_transformation,[],[f60]) ).
% 2.28/0.98  
% 2.28/0.98  cnf(c_24,negated_conjecture,
% 2.28/0.98      ( v1_funct_1(sK3) ),
% 2.28/0.98      inference(cnf_transformation,[],[f62]) ).
% 2.28/0.98  
% 2.28/0.98  cnf(c_22,negated_conjecture,
% 2.28/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 2.28/0.98      inference(cnf_transformation,[],[f64]) ).
% 2.28/0.98  
% 2.28/0.98  cnf(c_16,plain,
% 2.28/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.28/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 2.28/0.98      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 2.28/0.98      | ~ v1_funct_1(X0)
% 2.28/0.98      | ~ v1_funct_1(X3) ),
% 2.28/0.98      inference(cnf_transformation,[],[f54]) ).
% 2.28/0.98  
% 2.28/0.98  cnf(c_971,plain,
% 2.28/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.28/0.98      | m1_subset_1(k1_partfun1(X1,X2,sK1,sK0,X0,sK3),k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 2.28/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.28/0.98      | ~ v1_funct_1(X0)
% 2.28/0.98      | ~ v1_funct_1(sK3) ),
% 2.28/0.98      inference(instantiation,[status(thm)],[c_16]) ).
% 2.28/0.98  
% 2.28/0.98  cnf(c_1081,plain,
% 2.28/0.98      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.28/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.28/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.28/0.98      | ~ v1_funct_1(sK3)
% 2.28/0.98      | ~ v1_funct_1(sK2) ),
% 2.28/0.98      inference(instantiation,[status(thm)],[c_971]) ).
% 2.28/0.98  
% 2.28/0.98  cnf(c_1118,plain,
% 2.28/0.98      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 2.28/0.98      inference(global_propositional_subsumption,
% 2.28/0.98                [status(thm)],
% 2.28/0.98                [c_755,c_28,c_26,c_24,c_22,c_318,c_1081]) ).
% 2.28/0.98  
% 2.28/0.98  cnf(c_19,plain,
% 2.28/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.28/0.98      | ~ v1_funct_2(X3,X4,X1)
% 2.28/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 2.28/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.28/0.98      | v2_funct_1(X3)
% 2.28/0.98      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 2.28/0.98      | ~ v1_funct_1(X0)
% 2.28/0.98      | ~ v1_funct_1(X3)
% 2.28/0.98      | k1_xboole_0 = X2 ),
% 2.28/0.98      inference(cnf_transformation,[],[f56]) ).
% 2.28/0.98  
% 2.28/0.98  cnf(c_766,plain,
% 2.28/0.98      ( k1_xboole_0 = X0
% 2.28/0.98      | v1_funct_2(X1,X2,X0) != iProver_top
% 2.28/0.98      | v1_funct_2(X3,X4,X2) != iProver_top
% 2.28/0.98      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
% 2.28/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 2.28/0.98      | v2_funct_1(X3) = iProver_top
% 2.28/0.98      | v2_funct_1(k1_partfun1(X4,X2,X2,X0,X3,X1)) != iProver_top
% 2.28/0.98      | v1_funct_1(X1) != iProver_top
% 2.28/0.98      | v1_funct_1(X3) != iProver_top ),
% 2.28/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.28/0.98  
% 2.28/0.98  cnf(c_1763,plain,
% 2.28/0.98      ( sK0 = k1_xboole_0
% 2.28/0.98      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 2.28/0.98      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 2.28/0.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.28/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.28/0.98      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 2.28/0.98      | v2_funct_1(sK2) = iProver_top
% 2.28/0.98      | v1_funct_1(sK3) != iProver_top
% 2.28/0.98      | v1_funct_1(sK2) != iProver_top ),
% 2.28/0.98      inference(superposition,[status(thm)],[c_1118,c_766]) ).
% 2.28/0.98  
% 2.28/0.98  cnf(c_29,plain,
% 2.28/0.98      ( v1_funct_1(sK2) = iProver_top ),
% 2.28/0.98      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.28/0.98  
% 2.28/0.98  cnf(c_27,negated_conjecture,
% 2.28/0.98      ( v1_funct_2(sK2,sK0,sK1) ),
% 2.28/0.98      inference(cnf_transformation,[],[f59]) ).
% 2.28/0.98  
% 2.28/0.98  cnf(c_30,plain,
% 2.28/0.98      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 2.28/0.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.28/0.98  
% 2.28/0.98  cnf(c_31,plain,
% 2.28/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.28/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.28/0.98  
% 2.28/0.98  cnf(c_32,plain,
% 2.28/0.98      ( v1_funct_1(sK3) = iProver_top ),
% 2.28/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.28/0.98  
% 2.28/0.98  cnf(c_23,negated_conjecture,
% 2.28/0.98      ( v1_funct_2(sK3,sK1,sK0) ),
% 2.28/0.98      inference(cnf_transformation,[],[f63]) ).
% 2.28/0.98  
% 2.28/0.98  cnf(c_33,plain,
% 2.28/0.98      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 2.28/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.28/0.98  
% 2.28/0.98  cnf(c_34,plain,
% 2.28/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 2.28/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.28/0.98  
% 2.28/0.98  cnf(c_20,negated_conjecture,
% 2.28/0.98      ( ~ v2_funct_1(sK2) ),
% 2.28/0.98      inference(cnf_transformation,[],[f66]) ).
% 2.28/0.98  
% 2.28/0.98  cnf(c_36,plain,
% 2.28/0.98      ( v2_funct_1(sK2) != iProver_top ),
% 2.28/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.28/0.98  
% 2.28/0.98  cnf(c_2329,plain,
% 2.28/0.98      ( v2_funct_1(k6_partfun1(sK0)) != iProver_top | sK0 = k1_xboole_0 ),
% 2.28/0.98      inference(global_propositional_subsumption,
% 2.28/0.98                [status(thm)],
% 2.28/0.98                [c_1763,c_29,c_30,c_31,c_32,c_33,c_34,c_36]) ).
% 2.28/0.98  
% 2.28/0.98  cnf(c_2330,plain,
% 2.28/0.98      ( sK0 = k1_xboole_0 | v2_funct_1(k6_partfun1(sK0)) != iProver_top ),
% 2.28/0.98      inference(renaming,[status(thm)],[c_2329]) ).
% 2.28/0.98  
% 2.28/0.98  cnf(c_11,plain,
% 2.28/0.98      ( v2_funct_1(k6_partfun1(X0)) ),
% 2.28/0.98      inference(cnf_transformation,[],[f67]) ).
% 2.28/0.98  
% 2.28/0.98  cnf(c_771,plain,
% 2.28/0.98      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 2.28/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.28/0.98  
% 2.28/0.98  cnf(c_2335,plain,
% 2.28/0.98      ( sK0 = k1_xboole_0 ),
% 2.28/0.98      inference(forward_subsumption_resolution,
% 2.28/0.98                [status(thm)],
% 2.28/0.98                [c_2330,c_771]) ).
% 2.28/0.98  
% 2.28/0.98  cnf(c_761,plain,
% 2.28/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.28/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.28/0.98  
% 2.28/0.98  cnf(c_2339,plain,
% 2.28/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) = iProver_top ),
% 2.28/0.98      inference(demodulation,[status(thm)],[c_2335,c_761]) ).
% 2.28/0.98  
% 2.28/0.98  cnf(c_3,plain,
% 2.28/0.98      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.28/0.98      inference(cnf_transformation,[],[f71]) ).
% 2.28/0.98  
% 2.28/0.98  cnf(c_2347,plain,
% 2.28/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.28/0.98      inference(demodulation,[status(thm)],[c_2339,c_3]) ).
% 2.28/0.98  
% 2.28/0.98  cnf(c_442,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.28/0.98  
% 2.28/0.98  cnf(c_990,plain,
% 2.28/0.98      ( X0 != X1 | sK2 != X1 | sK2 = X0 ),
% 2.28/0.98      inference(instantiation,[status(thm)],[c_442]) ).
% 2.28/0.98  
% 2.28/0.98  cnf(c_1242,plain,
% 2.28/0.98      ( X0 != sK2 | sK2 = X0 | sK2 != sK2 ),
% 2.28/0.98      inference(instantiation,[status(thm)],[c_990]) ).
% 2.28/0.98  
% 2.28/0.98  cnf(c_1243,plain,
% 2.28/0.98      ( sK2 != sK2 | sK2 = k1_xboole_0 | k1_xboole_0 != sK2 ),
% 2.28/0.98      inference(instantiation,[status(thm)],[c_1242]) ).
% 2.28/0.98  
% 2.28/0.98  cnf(c_441,plain,( X0 = X0 ),theory(equality) ).
% 2.28/0.98  
% 2.28/0.98  cnf(c_1018,plain,
% 2.28/0.98      ( sK2 = sK2 ),
% 2.28/0.98      inference(instantiation,[status(thm)],[c_441]) ).
% 2.28/0.98  
% 2.28/0.98  cnf(c_1,plain,
% 2.28/0.98      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 2.28/0.98      inference(cnf_transformation,[],[f38]) ).
% 2.28/0.98  
% 2.28/0.98  cnf(c_5,plain,
% 2.28/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.28/0.98      inference(cnf_transformation,[],[f42]) ).
% 2.28/0.98  
% 2.28/0.98  cnf(c_292,plain,
% 2.28/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.28/0.98      | X0 != X2
% 2.28/0.98      | k1_xboole_0 != X1
% 2.28/0.98      | k1_xboole_0 = X2 ),
% 2.28/0.98      inference(resolution_lifted,[status(thm)],[c_1,c_5]) ).
% 2.28/0.98  
% 2.28/0.98  cnf(c_293,plain,
% 2.28/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0 ),
% 2.28/0.98      inference(unflattening,[status(thm)],[c_292]) ).
% 2.28/0.98  
% 2.28/0.98  cnf(c_1012,plain,
% 2.28/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK2 ),
% 2.28/0.98      inference(instantiation,[status(thm)],[c_293]) ).
% 2.28/0.98  
% 2.28/0.98  cnf(c_1015,plain,
% 2.28/0.98      ( k1_xboole_0 = sK2
% 2.28/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.28/0.98      inference(predicate_to_equality,[status(thm)],[c_1012]) ).
% 2.28/0.98  
% 2.28/0.98  cnf(c_447,plain,
% 2.28/0.98      ( ~ v2_funct_1(X0) | v2_funct_1(X1) | X1 != X0 ),
% 2.28/0.98      theory(equality) ).
% 2.28/0.98  
% 2.28/0.98  cnf(c_918,plain,
% 2.28/0.98      ( ~ v2_funct_1(X0) | v2_funct_1(sK2) | sK2 != X0 ),
% 2.28/0.98      inference(instantiation,[status(thm)],[c_447]) ).
% 2.28/0.98  
% 2.28/0.98  cnf(c_920,plain,
% 2.28/0.98      ( v2_funct_1(sK2)
% 2.28/0.98      | ~ v2_funct_1(k1_xboole_0)
% 2.28/0.98      | sK2 != k1_xboole_0 ),
% 2.28/0.98      inference(instantiation,[status(thm)],[c_918]) ).
% 2.28/0.98  
% 2.28/0.98  cnf(c_0,plain,
% 2.28/0.98      ( v1_xboole_0(k1_xboole_0) ),
% 2.28/0.98      inference(cnf_transformation,[],[f37]) ).
% 2.28/0.98  
% 2.28/0.98  cnf(c_6,plain,
% 2.28/0.98      ( v1_relat_1(X0) | ~ v1_xboole_0(X0) ),
% 2.28/0.98      inference(cnf_transformation,[],[f43]) ).
% 2.28/0.98  
% 2.28/0.98  cnf(c_73,plain,
% 2.28/0.98      ( v1_relat_1(k1_xboole_0) | ~ v1_xboole_0(k1_xboole_0) ),
% 2.28/0.98      inference(instantiation,[status(thm)],[c_6]) ).
% 2.28/0.98  
% 2.28/0.98  cnf(c_7,plain,
% 2.28/0.98      ( v1_funct_1(X0) | ~ v1_xboole_0(X0) ),
% 2.28/0.98      inference(cnf_transformation,[],[f44]) ).
% 2.28/0.98  
% 2.28/0.98  cnf(c_70,plain,
% 2.28/0.98      ( v1_funct_1(k1_xboole_0) | ~ v1_xboole_0(k1_xboole_0) ),
% 2.28/0.98      inference(instantiation,[status(thm)],[c_7]) ).
% 2.28/0.98  
% 2.28/0.98  cnf(c_8,plain,
% 2.28/0.98      ( v2_funct_1(X0)
% 2.28/0.98      | ~ v1_funct_1(X0)
% 2.28/0.98      | ~ v1_relat_1(X0)
% 2.28/0.98      | ~ v1_xboole_0(X0) ),
% 2.28/0.98      inference(cnf_transformation,[],[f47]) ).
% 2.28/0.98  
% 2.28/0.98  cnf(c_67,plain,
% 2.28/0.98      ( v2_funct_1(k1_xboole_0)
% 2.28/0.98      | ~ v1_funct_1(k1_xboole_0)
% 2.28/0.98      | ~ v1_relat_1(k1_xboole_0)
% 2.28/0.98      | ~ v1_xboole_0(k1_xboole_0) ),
% 2.28/0.98      inference(instantiation,[status(thm)],[c_8]) ).
% 2.28/0.98  
% 2.28/0.98  cnf(contradiction,plain,
% 2.28/0.98      ( $false ),
% 2.28/0.98      inference(minisat,
% 2.28/0.98                [status(thm)],
% 2.28/0.98                [c_2347,c_1243,c_1018,c_1015,c_920,c_0,c_73,c_70,c_67,
% 2.28/0.98                 c_20]) ).
% 2.28/0.98  
% 2.28/0.98  
% 2.28/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.28/0.98  
% 2.28/0.98  ------                               Statistics
% 2.28/0.98  
% 2.28/0.98  ------ General
% 2.28/0.98  
% 2.28/0.98  abstr_ref_over_cycles:                  0
% 2.28/0.98  abstr_ref_under_cycles:                 0
% 2.28/0.98  gc_basic_clause_elim:                   0
% 2.28/0.98  forced_gc_time:                         0
% 2.28/0.98  parsing_time:                           0.009
% 2.28/0.98  unif_index_cands_time:                  0.
% 2.28/0.98  unif_index_add_time:                    0.
% 2.28/0.98  orderings_time:                         0.
% 2.28/0.98  out_proof_time:                         0.01
% 2.28/0.98  total_time:                             0.123
% 2.28/0.98  num_of_symbols:                         48
% 2.28/0.98  num_of_terms:                           2677
% 2.28/0.98  
% 2.28/0.98  ------ Preprocessing
% 2.28/0.98  
% 2.28/0.98  num_of_splits:                          0
% 2.28/0.98  num_of_split_atoms:                     0
% 2.28/0.98  num_of_reused_defs:                     0
% 2.28/0.98  num_eq_ax_congr_red:                    1
% 2.28/0.98  num_of_sem_filtered_clauses:            3
% 2.28/0.98  num_of_subtypes:                        0
% 2.28/0.98  monotx_restored_types:                  0
% 2.28/0.98  sat_num_of_epr_types:                   0
% 2.28/0.98  sat_num_of_non_cyclic_types:            0
% 2.28/0.98  sat_guarded_non_collapsed_types:        0
% 2.28/0.98  num_pure_diseq_elim:                    0
% 2.28/0.98  simp_replaced_by:                       0
% 2.28/0.98  res_preprocessed:                       111
% 2.28/0.98  prep_upred:                             0
% 2.28/0.98  prep_unflattend:                        12
% 2.28/0.98  smt_new_axioms:                         0
% 2.28/0.98  pred_elim_cands:                        4
% 2.28/0.98  pred_elim:                              3
% 2.28/0.98  pred_elim_cl:                           4
% 2.28/0.98  pred_elim_cycles:                       5
% 2.28/0.98  merged_defs:                            0
% 2.28/0.98  merged_defs_ncl:                        0
% 2.28/0.98  bin_hyper_res:                          0
% 2.28/0.98  prep_cycles:                            4
% 2.28/0.98  pred_elim_time:                         0.001
% 2.28/0.98  splitting_time:                         0.
% 2.28/0.98  sem_filter_time:                        0.
% 2.28/0.98  monotx_time:                            0.001
% 2.28/0.98  subtype_inf_time:                       0.
% 2.28/0.98  
% 2.28/0.98  ------ Problem properties
% 2.28/0.98  
% 2.28/0.98  clauses:                                21
% 2.28/0.98  conjectures:                            8
% 2.28/0.98  epr:                                    8
% 2.28/0.98  horn:                                   19
% 2.28/0.98  ground:                                 11
% 2.28/0.98  unary:                                  14
% 2.28/0.98  binary:                                 2
% 2.28/0.98  lits:                                   48
% 2.28/0.98  lits_eq:                                9
% 2.28/0.98  fd_pure:                                0
% 2.28/0.98  fd_pseudo:                              0
% 2.28/0.98  fd_cond:                                3
% 2.28/0.98  fd_pseudo_cond:                         0
% 2.28/0.98  ac_symbols:                             0
% 2.28/0.98  
% 2.28/0.98  ------ Propositional Solver
% 2.28/0.98  
% 2.28/0.98  prop_solver_calls:                      27
% 2.28/0.98  prop_fast_solver_calls:                 622
% 2.28/0.98  smt_solver_calls:                       0
% 2.28/0.98  smt_fast_solver_calls:                  0
% 2.28/0.98  prop_num_of_clauses:                    927
% 2.28/0.98  prop_preprocess_simplified:             3653
% 2.28/0.98  prop_fo_subsumed:                       14
% 2.28/0.98  prop_solver_time:                       0.
% 2.28/0.98  smt_solver_time:                        0.
% 2.28/0.98  smt_fast_solver_time:                   0.
% 2.28/0.98  prop_fast_solver_time:                  0.
% 2.28/0.98  prop_unsat_core_time:                   0.
% 2.28/0.98  
% 2.28/0.98  ------ QBF
% 2.28/0.98  
% 2.28/0.98  qbf_q_res:                              0
% 2.28/0.98  qbf_num_tautologies:                    0
% 2.28/0.98  qbf_prep_cycles:                        0
% 2.28/0.98  
% 2.28/0.98  ------ BMC1
% 2.28/0.98  
% 2.28/0.98  bmc1_current_bound:                     -1
% 2.28/0.98  bmc1_last_solved_bound:                 -1
% 2.28/0.98  bmc1_unsat_core_size:                   -1
% 2.28/0.98  bmc1_unsat_core_parents_size:           -1
% 2.28/0.98  bmc1_merge_next_fun:                    0
% 2.28/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.28/0.98  
% 2.28/0.98  ------ Instantiation
% 2.28/0.98  
% 2.28/0.98  inst_num_of_clauses:                    363
% 2.28/0.98  inst_num_in_passive:                    150
% 2.28/0.98  inst_num_in_active:                     125
% 2.28/0.98  inst_num_in_unprocessed:                88
% 2.28/0.98  inst_num_of_loops:                      130
% 2.28/0.98  inst_num_of_learning_restarts:          0
% 2.28/0.98  inst_num_moves_active_passive:          3
% 2.28/0.98  inst_lit_activity:                      0
% 2.28/0.98  inst_lit_activity_moves:                0
% 2.28/0.98  inst_num_tautologies:                   0
% 2.28/0.98  inst_num_prop_implied:                  0
% 2.28/0.98  inst_num_existing_simplified:           0
% 2.28/0.98  inst_num_eq_res_simplified:             0
% 2.28/0.98  inst_num_child_elim:                    0
% 2.28/0.98  inst_num_of_dismatching_blockings:      6
% 2.28/0.98  inst_num_of_non_proper_insts:           185
% 2.28/0.98  inst_num_of_duplicates:                 0
% 2.28/0.98  inst_inst_num_from_inst_to_res:         0
% 2.28/0.98  inst_dismatching_checking_time:         0.
% 2.28/0.98  
% 2.28/0.98  ------ Resolution
% 2.28/0.98  
% 2.28/0.98  res_num_of_clauses:                     0
% 2.28/0.98  res_num_in_passive:                     0
% 2.28/0.98  res_num_in_active:                      0
% 2.28/0.98  res_num_of_loops:                       115
% 2.28/0.98  res_forward_subset_subsumed:            9
% 2.28/0.98  res_backward_subset_subsumed:           0
% 2.28/0.98  res_forward_subsumed:                   0
% 2.28/0.98  res_backward_subsumed:                  0
% 2.28/0.98  res_forward_subsumption_resolution:     1
% 2.28/0.98  res_backward_subsumption_resolution:    0
% 2.28/0.98  res_clause_to_clause_subsumption:       42
% 2.28/0.98  res_orphan_elimination:                 0
% 2.28/0.98  res_tautology_del:                      13
% 2.28/0.98  res_num_eq_res_simplified:              0
% 2.28/0.98  res_num_sel_changes:                    0
% 2.28/0.98  res_moves_from_active_to_pass:          0
% 2.28/0.98  
% 2.28/0.98  ------ Superposition
% 2.28/0.98  
% 2.28/0.98  sup_time_total:                         0.
% 2.28/0.98  sup_time_generating:                    0.
% 2.28/0.98  sup_time_sim_full:                      0.
% 2.28/0.98  sup_time_sim_immed:                     0.
% 2.28/0.98  
% 2.28/0.98  sup_num_of_clauses:                     27
% 2.28/0.98  sup_num_in_active:                      18
% 2.28/0.98  sup_num_in_passive:                     9
% 2.28/0.98  sup_num_of_loops:                       25
% 2.28/0.98  sup_fw_superposition:                   10
% 2.28/0.98  sup_bw_superposition:                   4
% 2.28/0.98  sup_immediate_simplified:               8
% 2.28/0.98  sup_given_eliminated:                   0
% 2.28/0.98  comparisons_done:                       0
% 2.28/0.98  comparisons_avoided:                    0
% 2.28/0.98  
% 2.28/0.98  ------ Simplifications
% 2.28/0.98  
% 2.28/0.98  
% 2.28/0.98  sim_fw_subset_subsumed:                 0
% 2.28/0.98  sim_bw_subset_subsumed:                 0
% 2.28/0.98  sim_fw_subsumed:                        1
% 2.28/0.98  sim_bw_subsumed:                        0
% 2.28/0.98  sim_fw_subsumption_res:                 1
% 2.28/0.98  sim_bw_subsumption_res:                 0
% 2.28/0.98  sim_tautology_del:                      0
% 2.28/0.98  sim_eq_tautology_del:                   2
% 2.28/0.98  sim_eq_res_simp:                        0
% 2.28/0.98  sim_fw_demodulated:                     6
% 2.28/0.98  sim_bw_demodulated:                     7
% 2.28/0.98  sim_light_normalised:                   2
% 2.28/0.98  sim_joinable_taut:                      0
% 2.28/0.98  sim_joinable_simp:                      0
% 2.28/0.98  sim_ac_normalised:                      0
% 2.28/0.98  sim_smt_subsumption:                    0
% 2.28/0.98  
%------------------------------------------------------------------------------
