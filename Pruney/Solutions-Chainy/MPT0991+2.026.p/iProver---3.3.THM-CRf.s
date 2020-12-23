%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:44 EST 2020

% Result     : Theorem 35.75s
% Output     : CNFRefutation 35.75s
% Verified   : 
% Statistics : Number of formulae       :  201 ( 643 expanded)
%              Number of clauses        :  127 ( 212 expanded)
%              Number of leaves         :   22 ( 152 expanded)
%              Depth                    :   20
%              Number of atoms          :  618 (3531 expanded)
%              Number of equality atoms :  278 ( 639 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f30])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f17,conjecture,(
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

fof(f18,negated_conjecture,(
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
    inference(negated_conjecture,[],[f17])).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f45,plain,(
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

fof(f44,plain,
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

fof(f46,plain,
    ( ~ v2_funct_1(sK2)
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & k1_xboole_0 != sK1
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f37,f45,f44])).

fof(f79,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f80,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f46])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f74,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f76,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f46])).

fof(f82,plain,(
    ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f57,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f78,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f34])).

fof(f72,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f11,axiom,(
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
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f28])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f81,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f46])).

fof(f14,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f71,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f32])).

fof(f70,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f8,axiom,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f16,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f83,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f58,f73])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f38])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f85,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f49])).

fof(f1,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f47,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f84,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f50])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_694,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X0
    | sK1 != X1
    | sK0 != X2
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_29])).

cnf(c_695,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k1_relset_1(sK1,sK0,sK3) = sK1
    | k1_xboole_0 = sK0 ),
    inference(unflattening,[status(thm)],[c_694])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_697,plain,
    ( k1_relset_1(sK1,sK0,sK3) = sK1
    | k1_xboole_0 = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_695,c_28])).

cnf(c_185719,plain,
    ( ~ iProver_ARSWP_582
    | arAF4_k1_relset_1_0_1(sK1) = sK1
    | k1_xboole_0 = sK0 ),
    inference(arg_filter_abstr,[status(unp)],[c_697])).

cnf(c_186278,plain,
    ( arAF4_k1_relset_1_0_1(sK1) = sK1
    | k1_xboole_0 = sK0
    | iProver_ARSWP_582 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_185719])).

cnf(c_186296,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_185712,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ iProver_ARSWP_575
    | arAF4_k1_relset_1_0_1(X1) = k1_relat_1(X0) ),
    inference(arg_filter_abstr,[status(unp)],[c_13])).

cnf(c_186284,plain,
    ( arAF4_k1_relset_1_0_1(X0) = k1_relat_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) != iProver_top
    | iProver_ARSWP_575 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_185712])).

cnf(c_188774,plain,
    ( arAF4_k1_relset_1_0_1(sK1) = k1_relat_1(sK3)
    | iProver_ARSWP_575 != iProver_top ),
    inference(superposition,[status(thm)],[c_186296,c_186284])).

cnf(c_188994,plain,
    ( k1_relat_1(sK3) = sK1
    | sK0 = k1_xboole_0
    | iProver_ARSWP_582 != iProver_top
    | iProver_ARSWP_575 != iProver_top ),
    inference(superposition,[status(thm)],[c_186278,c_188774])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_26,negated_conjecture,
    ( ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_7663,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_4,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_244,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_4])).

cnf(c_245,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_244])).

cnf(c_309,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_6,c_245])).

cnf(c_36316,plain,
    ( ~ r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_309])).

cnf(c_9,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_38503,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_148128,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_12,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_8,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_418,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_12,c_8])).

cnf(c_148124,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_418])).

cnf(c_148329,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_148128,c_148124])).

cnf(c_37,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_7664,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7663])).

cnf(c_32992,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_32989,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_418])).

cnf(c_33145,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_32992,c_32989])).

cnf(c_36318,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36316])).

cnf(c_38504,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38503])).

cnf(c_148432,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_148329,c_37,c_7664,c_33145,c_36318,c_38504])).

cnf(c_148130,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_148136,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_148555,plain,
    ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_148130,c_148136])).

cnf(c_148623,plain,
    ( k1_relat_1(sK3) = sK1
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_697,c_148555])).

cnf(c_10,plain,
    ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | v2_funct_1(X0)
    | ~ v2_funct_1(k5_relat_1(X0,X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_148138,plain,
    ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v2_funct_1(X0) = iProver_top
    | v2_funct_1(k5_relat_1(X0,X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_148993,plain,
    ( sK0 = k1_xboole_0
    | r1_tarski(k2_relat_1(X0),sK1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(X0) = iProver_top
    | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_148623,c_148138])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_38,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_40,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_7656,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | r1_tarski(sK3,k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_7657,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | r1_tarski(sK3,k2_zfmisc_1(sK1,sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7656])).

cnf(c_36121,plain,
    ( ~ r1_tarski(sK3,k2_zfmisc_1(sK1,sK0))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_309])).

cnf(c_36123,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36121])).

cnf(c_37307,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_37308,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37307])).

cnf(c_163774,plain,
    ( v1_relat_1(X0) != iProver_top
    | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
    | v2_funct_1(X0) = iProver_top
    | sK0 = k1_xboole_0
    | r1_tarski(k2_relat_1(X0),sK1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_148993,c_38,c_40,c_7657,c_36123,c_37308])).

cnf(c_163775,plain,
    ( sK0 = k1_xboole_0
    | r1_tarski(k2_relat_1(X0),sK1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) = iProver_top
    | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_163774])).

cnf(c_163785,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
    | v2_funct_1(sK2) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_148432,c_163775])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_148132,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_149061,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_148130,c_148132])).

cnf(c_32994,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_32996,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_33565,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_32994,c_32996])).

cnf(c_149528,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_149061,c_38,c_33565])).

cnf(c_149529,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_149528])).

cnf(c_149539,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_148128,c_149529])).

cnf(c_15,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_27,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_439,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_27])).

cnf(c_440,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_439])).

cnf(c_24,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_448,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_440,c_24])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_33107,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_partfun1(X1,X2,X3,X4,X0,sK3),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_33167,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_partfun1(X1,X2,sK1,sK0,X0,sK3),k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_33107])).

cnf(c_33223,plain,
    ( m1_subset_1(k1_partfun1(X0,X1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_33167])).

cnf(c_33292,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_33223])).

cnf(c_147988,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_448,c_34,c_32,c_30,c_28,c_33292])).

cnf(c_149556,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_149539,c_147988])).

cnf(c_35,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_34016,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_33565,c_38])).

cnf(c_34017,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_34016])).

cnf(c_34029,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_32992,c_34017])).

cnf(c_33003,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_32988,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_448])).

cnf(c_33379,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | r1_tarski(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k2_zfmisc_1(sK0,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_33003,c_32988])).

cnf(c_32998,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_33305,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_32998,c_32988])).

cnf(c_33495,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_33379,c_35,c_37,c_38,c_40,c_33305])).

cnf(c_34046,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_34029,c_33495])).

cnf(c_149729,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_149556,c_35,c_34046])).

cnf(c_163855,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK2) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_163785,c_149729])).

cnf(c_163881,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(k6_partfun1(sK0))
    | v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | sK0 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_163855])).

cnf(c_11,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_192892,plain,
    ( v2_funct_1(k6_partfun1(sK0)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_219044,plain,
    ( sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_188994,c_34,c_32,c_26,c_7663,c_36316,c_38503,c_163881,c_192892])).

cnf(c_186294,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_219253,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_219044,c_186294])).

cnf(c_2,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_219255,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_219253,c_2])).

cnf(c_105195,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | r1_tarski(sK2,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_105198,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(sK2,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_105195])).

cnf(c_1098,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_88468,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1098])).

cnf(c_1099,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_50687,plain,
    ( sK2 != X0
    | sK2 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1099])).

cnf(c_82045,plain,
    ( sK2 != sK2
    | sK2 = k1_xboole_0
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_50687])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_63388,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_63392,plain,
    ( k1_xboole_0 = sK2
    | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_63388])).

cnf(c_1105,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_20440,plain,
    ( v2_funct_1(X0)
    | ~ v2_funct_1(k1_xboole_0)
    | X0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1105])).

cnf(c_20898,plain,
    ( v2_funct_1(sK2)
    | ~ v2_funct_1(k1_xboole_0)
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_20440])).

cnf(c_1,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_18391,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_18615,plain,
    ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_18391])).

cnf(c_18393,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_18646,plain,
    ( r1_tarski(k6_partfun1(k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_18615,c_18393])).

cnf(c_18395,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_18776,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_18646,c_18395])).

cnf(c_18392,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_18808,plain,
    ( v2_funct_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_18776,c_18392])).

cnf(c_18813,plain,
    ( v2_funct_1(k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_18808])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_219255,c_105198,c_88468,c_82045,c_63392,c_20898,c_18813,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:32:45 EST 2020
% 0.19/0.33  % CPUTime    : 
% 0.19/0.34  % Running in FOF mode
% 35.75/5.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 35.75/5.00  
% 35.75/5.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 35.75/5.00  
% 35.75/5.00  ------  iProver source info
% 35.75/5.00  
% 35.75/5.00  git: date: 2020-06-30 10:37:57 +0100
% 35.75/5.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 35.75/5.00  git: non_committed_changes: false
% 35.75/5.00  git: last_make_outside_of_git: false
% 35.75/5.00  
% 35.75/5.00  ------ 
% 35.75/5.00  ------ Parsing...
% 35.75/5.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 35.75/5.00  
% 35.75/5.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 35.75/5.00  
% 35.75/5.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 35.75/5.00  
% 35.75/5.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.75/5.00  ------ Proving...
% 35.75/5.00  ------ Problem Properties 
% 35.75/5.00  
% 35.75/5.00  
% 35.75/5.00  clauses                                 29
% 35.75/5.00  conjectures                             6
% 35.75/5.00  EPR                                     6
% 35.75/5.00  Horn                                    26
% 35.75/5.00  unary                                   12
% 35.75/5.00  binary                                  6
% 35.75/5.00  lits                                    68
% 35.75/5.00  lits eq                                 22
% 35.75/5.00  fd_pure                                 0
% 35.75/5.00  fd_pseudo                               0
% 35.75/5.00  fd_cond                                 2
% 35.75/5.00  fd_pseudo_cond                          0
% 35.75/5.00  AC symbols                              0
% 35.75/5.00  
% 35.75/5.00  ------ Input Options Time Limit: Unbounded
% 35.75/5.00  
% 35.75/5.00  
% 35.75/5.00  
% 35.75/5.00  
% 35.75/5.00  ------ Preprocessing...
% 35.75/5.00  
% 35.75/5.00  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 35.75/5.00  Current options:
% 35.75/5.00  ------ 
% 35.75/5.00  
% 35.75/5.00  
% 35.75/5.00  
% 35.75/5.00  
% 35.75/5.00  ------ Proving...
% 35.75/5.00  
% 35.75/5.00  
% 35.75/5.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.75/5.00  
% 35.75/5.00  ------ Proving...
% 35.75/5.00  
% 35.75/5.00  
% 35.75/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.75/5.00  
% 35.75/5.00  ------ Proving...
% 35.75/5.00  
% 35.75/5.00  
% 35.75/5.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.75/5.00  
% 35.75/5.00  ------ Proving...
% 35.75/5.00  
% 35.75/5.00  
% 35.75/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.75/5.00  
% 35.75/5.00  ------ Proving...
% 35.75/5.00  
% 35.75/5.00  
% 35.75/5.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.75/5.00  
% 35.75/5.00  ------ Proving...
% 35.75/5.00  
% 35.75/5.00  
% 35.75/5.00  ------ Preprocessing...
% 35.75/5.00  
% 35.75/5.00  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.75/5.00  
% 35.75/5.00  ------ Proving...
% 35.75/5.00  
% 35.75/5.00  
% 35.75/5.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.75/5.00  
% 35.75/5.00  ------ Proving...
% 35.75/5.00  
% 35.75/5.00  
% 35.75/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.75/5.00  
% 35.75/5.00  ------ Proving...
% 35.75/5.00  
% 35.75/5.00  
% 35.75/5.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.75/5.00  
% 35.75/5.00  ------ Proving...
% 35.75/5.00  
% 35.75/5.00  
% 35.75/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.75/5.00  
% 35.75/5.00  ------ Proving...
% 35.75/5.00  
% 35.75/5.00  
% 35.75/5.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.75/5.00  
% 35.75/5.00  ------ Proving...
% 35.75/5.00  
% 35.75/5.00  
% 35.75/5.00  ------ Preprocessing...
% 35.75/5.00  
% 35.75/5.00  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.75/5.00  
% 35.75/5.00  ------ Proving...
% 35.75/5.00  
% 35.75/5.00  
% 35.75/5.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.75/5.00  
% 35.75/5.00  ------ Proving...
% 35.75/5.00  
% 35.75/5.00  
% 35.75/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.75/5.00  
% 35.75/5.00  ------ Proving...
% 35.75/5.00  
% 35.75/5.00  
% 35.75/5.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.75/5.00  
% 35.75/5.00  ------ Proving...
% 35.75/5.00  
% 35.75/5.00  
% 35.75/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.75/5.00  
% 35.75/5.00  ------ Proving...
% 35.75/5.00  
% 35.75/5.00  
% 35.75/5.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.75/5.00  
% 35.75/5.00  ------ Proving...
% 35.75/5.00  
% 35.75/5.00  
% 35.75/5.00  ------ Preprocessing...
% 35.75/5.00  
% 35.75/5.00  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.75/5.00  
% 35.75/5.00  ------ Proving...
% 35.75/5.00  
% 35.75/5.00  
% 35.75/5.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.75/5.00  
% 35.75/5.00  ------ Proving...
% 35.75/5.00  
% 35.75/5.00  
% 35.75/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.75/5.00  
% 35.75/5.00  ------ Proving...
% 35.75/5.00  
% 35.75/5.00  
% 35.75/5.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.75/5.00  
% 35.75/5.00  ------ Proving...
% 35.75/5.00  
% 35.75/5.00  
% 35.75/5.00  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.75/5.00  
% 35.75/5.00  ------ Proving...
% 35.75/5.00  
% 35.75/5.00  
% 35.75/5.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.75/5.00  
% 35.75/5.00  ------ Proving...
% 35.75/5.00  
% 35.75/5.00  
% 35.75/5.00  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.75/5.00  
% 35.75/5.00  ------ Proving...
% 35.75/5.00  
% 35.75/5.00  
% 35.75/5.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.75/5.00  
% 35.75/5.00  ------ Proving...
% 35.75/5.00  
% 35.75/5.00  
% 35.75/5.00  ------ Preprocessing... sf_s  rm: 8 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.75/5.00  
% 35.75/5.00  ------ Proving...
% 35.75/5.00  
% 35.75/5.00  
% 35.75/5.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.75/5.00  
% 35.75/5.00  ------ Proving...
% 35.75/5.00  
% 35.75/5.00  
% 35.75/5.00  ------ Preprocessing... sf_s  rm: 7 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.75/5.00  
% 35.75/5.00  ------ Proving...
% 35.75/5.00  
% 35.75/5.00  
% 35.75/5.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.75/5.00  
% 35.75/5.00  ------ Proving...
% 35.75/5.00  
% 35.75/5.00  
% 35.75/5.00  ------ Preprocessing...
% 35.75/5.00  
% 35.75/5.00  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.75/5.00  
% 35.75/5.00  ------ Proving...
% 35.75/5.00  
% 35.75/5.00  
% 35.75/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.75/5.00  
% 35.75/5.00  ------ Proving...
% 35.75/5.00  
% 35.75/5.00  
% 35.75/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.75/5.00  
% 35.75/5.00  ------ Proving...
% 35.75/5.00  
% 35.75/5.00  
% 35.75/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.75/5.00  
% 35.75/5.00  ------ Proving...
% 35.75/5.00  
% 35.75/5.00  
% 35.75/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.75/5.00  
% 35.75/5.00  ------ Proving...
% 35.75/5.00  
% 35.75/5.00  
% 35.75/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.75/5.00  
% 35.75/5.00  ------ Proving...
% 35.75/5.00  
% 35.75/5.00  
% 35.75/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.75/5.00  
% 35.75/5.00  ------ Proving...
% 35.75/5.00  
% 35.75/5.00  
% 35.75/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.75/5.00  
% 35.75/5.00  ------ Proving...
% 35.75/5.00  
% 35.75/5.00  
% 35.75/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.75/5.00  
% 35.75/5.00  ------ Proving...
% 35.75/5.00  
% 35.75/5.00  
% 35.75/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.75/5.00  
% 35.75/5.00  ------ Proving...
% 35.75/5.00  
% 35.75/5.00  
% 35.75/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.75/5.00  
% 35.75/5.00  ------ Proving...
% 35.75/5.00  
% 35.75/5.00  
% 35.75/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.75/5.00  
% 35.75/5.00  ------ Proving...
% 35.75/5.00  
% 35.75/5.00  
% 35.75/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.75/5.00  
% 35.75/5.00  ------ Proving...
% 35.75/5.00  
% 35.75/5.00  
% 35.75/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.75/5.00  
% 35.75/5.00  ------ Proving...
% 35.75/5.00  
% 35.75/5.00  
% 35.75/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.75/5.00  
% 35.75/5.00  ------ Proving...
% 35.75/5.00  
% 35.75/5.00  
% 35.75/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.75/5.00  
% 35.75/5.00  ------ Proving...
% 35.75/5.00  
% 35.75/5.00  
% 35.75/5.00  % SZS status Theorem for theBenchmark.p
% 35.75/5.00  
% 35.75/5.00  % SZS output start CNFRefutation for theBenchmark.p
% 35.75/5.00  
% 35.75/5.00  fof(f12,axiom,(
% 35.75/5.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 35.75/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.75/5.00  
% 35.75/5.00  fof(f30,plain,(
% 35.75/5.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 35.75/5.00    inference(ennf_transformation,[],[f12])).
% 35.75/5.00  
% 35.75/5.00  fof(f31,plain,(
% 35.75/5.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 35.75/5.00    inference(flattening,[],[f30])).
% 35.75/5.00  
% 35.75/5.00  fof(f43,plain,(
% 35.75/5.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 35.75/5.00    inference(nnf_transformation,[],[f31])).
% 35.75/5.00  
% 35.75/5.00  fof(f63,plain,(
% 35.75/5.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 35.75/5.00    inference(cnf_transformation,[],[f43])).
% 35.75/5.00  
% 35.75/5.00  fof(f17,conjecture,(
% 35.75/5.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ~(~v2_funct_1(X2) & ? [X3] : (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & k1_xboole_0 != X1))),
% 35.75/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.75/5.00  
% 35.75/5.00  fof(f18,negated_conjecture,(
% 35.75/5.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ~(~v2_funct_1(X2) & ? [X3] : (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & k1_xboole_0 != X1))),
% 35.75/5.00    inference(negated_conjecture,[],[f17])).
% 35.75/5.00  
% 35.75/5.00  fof(f36,plain,(
% 35.75/5.00    ? [X0,X1,X2] : ((~v2_funct_1(X2) & ? [X3] : (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 35.75/5.00    inference(ennf_transformation,[],[f18])).
% 35.75/5.00  
% 35.75/5.00  fof(f37,plain,(
% 35.75/5.00    ? [X0,X1,X2] : (~v2_funct_1(X2) & ? [X3] : (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 35.75/5.00    inference(flattening,[],[f36])).
% 35.75/5.00  
% 35.75/5.00  fof(f45,plain,(
% 35.75/5.00    ( ! [X2,X0,X1] : (? [X3] : (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 35.75/5.00    introduced(choice_axiom,[])).
% 35.75/5.00  
% 35.75/5.00  fof(f44,plain,(
% 35.75/5.00    ? [X0,X1,X2] : (~v2_funct_1(X2) & ? [X3] : (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (~v2_funct_1(sK2) & ? [X3] : (r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 35.75/5.00    introduced(choice_axiom,[])).
% 35.75/5.00  
% 35.75/5.00  fof(f46,plain,(
% 35.75/5.00    ~v2_funct_1(sK2) & (r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 35.75/5.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f37,f45,f44])).
% 35.75/5.00  
% 35.75/5.00  fof(f79,plain,(
% 35.75/5.00    v1_funct_2(sK3,sK1,sK0)),
% 35.75/5.00    inference(cnf_transformation,[],[f46])).
% 35.75/5.00  
% 35.75/5.00  fof(f80,plain,(
% 35.75/5.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 35.75/5.00    inference(cnf_transformation,[],[f46])).
% 35.75/5.00  
% 35.75/5.00  fof(f10,axiom,(
% 35.75/5.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 35.75/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.75/5.00  
% 35.75/5.00  fof(f27,plain,(
% 35.75/5.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 35.75/5.00    inference(ennf_transformation,[],[f10])).
% 35.75/5.00  
% 35.75/5.00  fof(f60,plain,(
% 35.75/5.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 35.75/5.00    inference(cnf_transformation,[],[f27])).
% 35.75/5.00  
% 35.75/5.00  fof(f74,plain,(
% 35.75/5.00    v1_funct_1(sK2)),
% 35.75/5.00    inference(cnf_transformation,[],[f46])).
% 35.75/5.00  
% 35.75/5.00  fof(f76,plain,(
% 35.75/5.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 35.75/5.00    inference(cnf_transformation,[],[f46])).
% 35.75/5.00  
% 35.75/5.00  fof(f82,plain,(
% 35.75/5.00    ~v2_funct_1(sK2)),
% 35.75/5.00    inference(cnf_transformation,[],[f46])).
% 35.75/5.00  
% 35.75/5.00  fof(f3,axiom,(
% 35.75/5.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 35.75/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.75/5.00  
% 35.75/5.00  fof(f40,plain,(
% 35.75/5.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 35.75/5.00    inference(nnf_transformation,[],[f3])).
% 35.75/5.00  
% 35.75/5.00  fof(f51,plain,(
% 35.75/5.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 35.75/5.00    inference(cnf_transformation,[],[f40])).
% 35.75/5.00  
% 35.75/5.00  fof(f4,axiom,(
% 35.75/5.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 35.75/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.75/5.00  
% 35.75/5.00  fof(f22,plain,(
% 35.75/5.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 35.75/5.00    inference(ennf_transformation,[],[f4])).
% 35.75/5.00  
% 35.75/5.00  fof(f53,plain,(
% 35.75/5.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 35.75/5.00    inference(cnf_transformation,[],[f22])).
% 35.75/5.00  
% 35.75/5.00  fof(f52,plain,(
% 35.75/5.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 35.75/5.00    inference(cnf_transformation,[],[f40])).
% 35.75/5.00  
% 35.75/5.00  fof(f6,axiom,(
% 35.75/5.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 35.75/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.75/5.00  
% 35.75/5.00  fof(f56,plain,(
% 35.75/5.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 35.75/5.00    inference(cnf_transformation,[],[f6])).
% 35.75/5.00  
% 35.75/5.00  fof(f9,axiom,(
% 35.75/5.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 35.75/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.75/5.00  
% 35.75/5.00  fof(f20,plain,(
% 35.75/5.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 35.75/5.00    inference(pure_predicate_removal,[],[f9])).
% 35.75/5.00  
% 35.75/5.00  fof(f26,plain,(
% 35.75/5.00    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 35.75/5.00    inference(ennf_transformation,[],[f20])).
% 35.75/5.00  
% 35.75/5.00  fof(f59,plain,(
% 35.75/5.00    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 35.75/5.00    inference(cnf_transformation,[],[f26])).
% 35.75/5.00  
% 35.75/5.00  fof(f5,axiom,(
% 35.75/5.00    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 35.75/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.75/5.00  
% 35.75/5.00  fof(f23,plain,(
% 35.75/5.00    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 35.75/5.00    inference(ennf_transformation,[],[f5])).
% 35.75/5.00  
% 35.75/5.00  fof(f41,plain,(
% 35.75/5.00    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 35.75/5.00    inference(nnf_transformation,[],[f23])).
% 35.75/5.00  
% 35.75/5.00  fof(f54,plain,(
% 35.75/5.00    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 35.75/5.00    inference(cnf_transformation,[],[f41])).
% 35.75/5.00  
% 35.75/5.00  fof(f7,axiom,(
% 35.75/5.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) & v2_funct_1(k5_relat_1(X1,X0))) => v2_funct_1(X1))))),
% 35.75/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.75/5.00  
% 35.75/5.00  fof(f24,plain,(
% 35.75/5.00    ! [X0] : (! [X1] : ((v2_funct_1(X1) | (~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 35.75/5.00    inference(ennf_transformation,[],[f7])).
% 35.75/5.00  
% 35.75/5.00  fof(f25,plain,(
% 35.75/5.00    ! [X0] : (! [X1] : (v2_funct_1(X1) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 35.75/5.00    inference(flattening,[],[f24])).
% 35.75/5.00  
% 35.75/5.00  fof(f57,plain,(
% 35.75/5.00    ( ! [X0,X1] : (v2_funct_1(X1) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 35.75/5.00    inference(cnf_transformation,[],[f25])).
% 35.75/5.00  
% 35.75/5.00  fof(f78,plain,(
% 35.75/5.00    v1_funct_1(sK3)),
% 35.75/5.00    inference(cnf_transformation,[],[f46])).
% 35.75/5.00  
% 35.75/5.00  fof(f15,axiom,(
% 35.75/5.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 35.75/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.75/5.00  
% 35.75/5.00  fof(f34,plain,(
% 35.75/5.00    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 35.75/5.00    inference(ennf_transformation,[],[f15])).
% 35.75/5.00  
% 35.75/5.00  fof(f35,plain,(
% 35.75/5.00    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 35.75/5.00    inference(flattening,[],[f34])).
% 35.75/5.00  
% 35.75/5.00  fof(f72,plain,(
% 35.75/5.00    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 35.75/5.00    inference(cnf_transformation,[],[f35])).
% 35.75/5.00  
% 35.75/5.00  fof(f11,axiom,(
% 35.75/5.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 35.75/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.75/5.00  
% 35.75/5.00  fof(f28,plain,(
% 35.75/5.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 35.75/5.00    inference(ennf_transformation,[],[f11])).
% 35.75/5.00  
% 35.75/5.00  fof(f29,plain,(
% 35.75/5.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 35.75/5.00    inference(flattening,[],[f28])).
% 35.75/5.00  
% 35.75/5.00  fof(f42,plain,(
% 35.75/5.00    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 35.75/5.00    inference(nnf_transformation,[],[f29])).
% 35.75/5.00  
% 35.75/5.00  fof(f61,plain,(
% 35.75/5.00    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 35.75/5.00    inference(cnf_transformation,[],[f42])).
% 35.75/5.00  
% 35.75/5.00  fof(f81,plain,(
% 35.75/5.00    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 35.75/5.00    inference(cnf_transformation,[],[f46])).
% 35.75/5.00  
% 35.75/5.00  fof(f14,axiom,(
% 35.75/5.00    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 35.75/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.75/5.00  
% 35.75/5.00  fof(f19,plain,(
% 35.75/5.00    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 35.75/5.00    inference(pure_predicate_removal,[],[f14])).
% 35.75/5.00  
% 35.75/5.00  fof(f71,plain,(
% 35.75/5.00    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 35.75/5.00    inference(cnf_transformation,[],[f19])).
% 35.75/5.00  
% 35.75/5.00  fof(f13,axiom,(
% 35.75/5.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 35.75/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.75/5.00  
% 35.75/5.00  fof(f32,plain,(
% 35.75/5.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 35.75/5.00    inference(ennf_transformation,[],[f13])).
% 35.75/5.00  
% 35.75/5.00  fof(f33,plain,(
% 35.75/5.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 35.75/5.00    inference(flattening,[],[f32])).
% 35.75/5.00  
% 35.75/5.00  fof(f70,plain,(
% 35.75/5.00    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 35.75/5.00    inference(cnf_transformation,[],[f33])).
% 35.75/5.00  
% 35.75/5.00  fof(f8,axiom,(
% 35.75/5.00    ! [X0] : v2_funct_1(k6_relat_1(X0))),
% 35.75/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.75/5.00  
% 35.75/5.00  fof(f58,plain,(
% 35.75/5.00    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 35.75/5.00    inference(cnf_transformation,[],[f8])).
% 35.75/5.00  
% 35.75/5.00  fof(f16,axiom,(
% 35.75/5.00    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 35.75/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.75/5.00  
% 35.75/5.00  fof(f73,plain,(
% 35.75/5.00    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 35.75/5.00    inference(cnf_transformation,[],[f16])).
% 35.75/5.00  
% 35.75/5.00  fof(f83,plain,(
% 35.75/5.00    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 35.75/5.00    inference(definition_unfolding,[],[f58,f73])).
% 35.75/5.00  
% 35.75/5.00  fof(f2,axiom,(
% 35.75/5.00    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 35.75/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.75/5.00  
% 35.75/5.00  fof(f38,plain,(
% 35.75/5.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 35.75/5.00    inference(nnf_transformation,[],[f2])).
% 35.75/5.00  
% 35.75/5.00  fof(f39,plain,(
% 35.75/5.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 35.75/5.00    inference(flattening,[],[f38])).
% 35.75/5.00  
% 35.75/5.00  fof(f49,plain,(
% 35.75/5.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 35.75/5.00    inference(cnf_transformation,[],[f39])).
% 35.75/5.00  
% 35.75/5.00  fof(f85,plain,(
% 35.75/5.00    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 35.75/5.00    inference(equality_resolution,[],[f49])).
% 35.75/5.00  
% 35.75/5.00  fof(f1,axiom,(
% 35.75/5.00    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 35.75/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.75/5.00  
% 35.75/5.00  fof(f21,plain,(
% 35.75/5.00    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 35.75/5.00    inference(ennf_transformation,[],[f1])).
% 35.75/5.00  
% 35.75/5.00  fof(f47,plain,(
% 35.75/5.00    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 35.75/5.00    inference(cnf_transformation,[],[f21])).
% 35.75/5.00  
% 35.75/5.00  fof(f50,plain,(
% 35.75/5.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 35.75/5.00    inference(cnf_transformation,[],[f39])).
% 35.75/5.00  
% 35.75/5.00  fof(f84,plain,(
% 35.75/5.00    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 35.75/5.00    inference(equality_resolution,[],[f50])).
% 35.75/5.00  
% 35.75/5.00  cnf(c_21,plain,
% 35.75/5.00      ( ~ v1_funct_2(X0,X1,X2)
% 35.75/5.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.75/5.00      | k1_relset_1(X1,X2,X0) = X1
% 35.75/5.00      | k1_xboole_0 = X2 ),
% 35.75/5.00      inference(cnf_transformation,[],[f63]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_29,negated_conjecture,
% 35.75/5.00      ( v1_funct_2(sK3,sK1,sK0) ),
% 35.75/5.00      inference(cnf_transformation,[],[f79]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_694,plain,
% 35.75/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.75/5.00      | k1_relset_1(X1,X2,X0) = X1
% 35.75/5.00      | sK3 != X0
% 35.75/5.00      | sK1 != X1
% 35.75/5.00      | sK0 != X2
% 35.75/5.00      | k1_xboole_0 = X2 ),
% 35.75/5.00      inference(resolution_lifted,[status(thm)],[c_21,c_29]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_695,plain,
% 35.75/5.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 35.75/5.00      | k1_relset_1(sK1,sK0,sK3) = sK1
% 35.75/5.00      | k1_xboole_0 = sK0 ),
% 35.75/5.00      inference(unflattening,[status(thm)],[c_694]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_28,negated_conjecture,
% 35.75/5.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 35.75/5.00      inference(cnf_transformation,[],[f80]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_697,plain,
% 35.75/5.00      ( k1_relset_1(sK1,sK0,sK3) = sK1 | k1_xboole_0 = sK0 ),
% 35.75/5.00      inference(global_propositional_subsumption,
% 35.75/5.00                [status(thm)],
% 35.75/5.00                [c_695,c_28]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_185719,plain,
% 35.75/5.00      ( ~ iProver_ARSWP_582
% 35.75/5.00      | arAF4_k1_relset_1_0_1(sK1) = sK1
% 35.75/5.00      | k1_xboole_0 = sK0 ),
% 35.75/5.00      inference(arg_filter_abstr,[status(unp)],[c_697]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_186278,plain,
% 35.75/5.00      ( arAF4_k1_relset_1_0_1(sK1) = sK1
% 35.75/5.00      | k1_xboole_0 = sK0
% 35.75/5.00      | iProver_ARSWP_582 != iProver_top ),
% 35.75/5.00      inference(predicate_to_equality,[status(thm)],[c_185719]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_186296,plain,
% 35.75/5.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 35.75/5.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_13,plain,
% 35.75/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.75/5.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 35.75/5.00      inference(cnf_transformation,[],[f60]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_185712,plain,
% 35.75/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.75/5.00      | ~ iProver_ARSWP_575
% 35.75/5.00      | arAF4_k1_relset_1_0_1(X1) = k1_relat_1(X0) ),
% 35.75/5.00      inference(arg_filter_abstr,[status(unp)],[c_13]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_186284,plain,
% 35.75/5.00      ( arAF4_k1_relset_1_0_1(X0) = k1_relat_1(X1)
% 35.75/5.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) != iProver_top
% 35.75/5.00      | iProver_ARSWP_575 != iProver_top ),
% 35.75/5.00      inference(predicate_to_equality,[status(thm)],[c_185712]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_188774,plain,
% 35.75/5.00      ( arAF4_k1_relset_1_0_1(sK1) = k1_relat_1(sK3)
% 35.75/5.00      | iProver_ARSWP_575 != iProver_top ),
% 35.75/5.00      inference(superposition,[status(thm)],[c_186296,c_186284]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_188994,plain,
% 35.75/5.00      ( k1_relat_1(sK3) = sK1
% 35.75/5.00      | sK0 = k1_xboole_0
% 35.75/5.00      | iProver_ARSWP_582 != iProver_top
% 35.75/5.00      | iProver_ARSWP_575 != iProver_top ),
% 35.75/5.00      inference(superposition,[status(thm)],[c_186278,c_188774]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_34,negated_conjecture,
% 35.75/5.00      ( v1_funct_1(sK2) ),
% 35.75/5.00      inference(cnf_transformation,[],[f74]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_32,negated_conjecture,
% 35.75/5.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 35.75/5.00      inference(cnf_transformation,[],[f76]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_26,negated_conjecture,
% 35.75/5.00      ( ~ v2_funct_1(sK2) ),
% 35.75/5.00      inference(cnf_transformation,[],[f82]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_5,plain,
% 35.75/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 35.75/5.00      inference(cnf_transformation,[],[f51]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_7663,plain,
% 35.75/5.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 35.75/5.00      | r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
% 35.75/5.00      inference(instantiation,[status(thm)],[c_5]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_6,plain,
% 35.75/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 35.75/5.00      | ~ v1_relat_1(X1)
% 35.75/5.00      | v1_relat_1(X0) ),
% 35.75/5.00      inference(cnf_transformation,[],[f53]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_4,plain,
% 35.75/5.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 35.75/5.00      inference(cnf_transformation,[],[f52]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_244,plain,
% 35.75/5.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 35.75/5.00      inference(prop_impl,[status(thm)],[c_4]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_245,plain,
% 35.75/5.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 35.75/5.00      inference(renaming,[status(thm)],[c_244]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_309,plain,
% 35.75/5.00      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 35.75/5.00      inference(bin_hyper_res,[status(thm)],[c_6,c_245]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_36316,plain,
% 35.75/5.00      ( ~ r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
% 35.75/5.00      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
% 35.75/5.00      | v1_relat_1(sK2) ),
% 35.75/5.00      inference(instantiation,[status(thm)],[c_309]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_9,plain,
% 35.75/5.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 35.75/5.00      inference(cnf_transformation,[],[f56]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_38503,plain,
% 35.75/5.00      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 35.75/5.00      inference(instantiation,[status(thm)],[c_9]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_148128,plain,
% 35.75/5.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 35.75/5.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_12,plain,
% 35.75/5.00      ( v5_relat_1(X0,X1)
% 35.75/5.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 35.75/5.00      inference(cnf_transformation,[],[f59]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_8,plain,
% 35.75/5.00      ( ~ v5_relat_1(X0,X1)
% 35.75/5.00      | r1_tarski(k2_relat_1(X0),X1)
% 35.75/5.00      | ~ v1_relat_1(X0) ),
% 35.75/5.00      inference(cnf_transformation,[],[f54]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_418,plain,
% 35.75/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.75/5.00      | r1_tarski(k2_relat_1(X0),X2)
% 35.75/5.00      | ~ v1_relat_1(X0) ),
% 35.75/5.00      inference(resolution,[status(thm)],[c_12,c_8]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_148124,plain,
% 35.75/5.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 35.75/5.00      | r1_tarski(k2_relat_1(X0),X2) = iProver_top
% 35.75/5.00      | v1_relat_1(X0) != iProver_top ),
% 35.75/5.00      inference(predicate_to_equality,[status(thm)],[c_418]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_148329,plain,
% 35.75/5.00      ( r1_tarski(k2_relat_1(sK2),sK1) = iProver_top
% 35.75/5.00      | v1_relat_1(sK2) != iProver_top ),
% 35.75/5.00      inference(superposition,[status(thm)],[c_148128,c_148124]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_37,plain,
% 35.75/5.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 35.75/5.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_7664,plain,
% 35.75/5.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 35.75/5.00      | r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 35.75/5.00      inference(predicate_to_equality,[status(thm)],[c_7663]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_32992,plain,
% 35.75/5.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 35.75/5.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_32989,plain,
% 35.75/5.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 35.75/5.00      | r1_tarski(k2_relat_1(X0),X2) = iProver_top
% 35.75/5.00      | v1_relat_1(X0) != iProver_top ),
% 35.75/5.00      inference(predicate_to_equality,[status(thm)],[c_418]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_33145,plain,
% 35.75/5.00      ( r1_tarski(k2_relat_1(sK2),sK1) = iProver_top
% 35.75/5.00      | v1_relat_1(sK2) != iProver_top ),
% 35.75/5.00      inference(superposition,[status(thm)],[c_32992,c_32989]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_36318,plain,
% 35.75/5.00      ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) != iProver_top
% 35.75/5.00      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 35.75/5.00      | v1_relat_1(sK2) = iProver_top ),
% 35.75/5.00      inference(predicate_to_equality,[status(thm)],[c_36316]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_38504,plain,
% 35.75/5.00      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 35.75/5.00      inference(predicate_to_equality,[status(thm)],[c_38503]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_148432,plain,
% 35.75/5.00      ( r1_tarski(k2_relat_1(sK2),sK1) = iProver_top ),
% 35.75/5.00      inference(global_propositional_subsumption,
% 35.75/5.00                [status(thm)],
% 35.75/5.00                [c_148329,c_37,c_7664,c_33145,c_36318,c_38504]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_148130,plain,
% 35.75/5.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 35.75/5.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_148136,plain,
% 35.75/5.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 35.75/5.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 35.75/5.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_148555,plain,
% 35.75/5.00      ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
% 35.75/5.00      inference(superposition,[status(thm)],[c_148130,c_148136]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_148623,plain,
% 35.75/5.00      ( k1_relat_1(sK3) = sK1 | sK0 = k1_xboole_0 ),
% 35.75/5.00      inference(superposition,[status(thm)],[c_697,c_148555]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_10,plain,
% 35.75/5.00      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
% 35.75/5.00      | ~ v1_funct_1(X0)
% 35.75/5.00      | ~ v1_funct_1(X1)
% 35.75/5.00      | v2_funct_1(X0)
% 35.75/5.00      | ~ v2_funct_1(k5_relat_1(X0,X1))
% 35.75/5.00      | ~ v1_relat_1(X1)
% 35.75/5.00      | ~ v1_relat_1(X0) ),
% 35.75/5.00      inference(cnf_transformation,[],[f57]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_148138,plain,
% 35.75/5.00      ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) != iProver_top
% 35.75/5.00      | v1_funct_1(X0) != iProver_top
% 35.75/5.00      | v1_funct_1(X1) != iProver_top
% 35.75/5.00      | v2_funct_1(X0) = iProver_top
% 35.75/5.00      | v2_funct_1(k5_relat_1(X0,X1)) != iProver_top
% 35.75/5.00      | v1_relat_1(X1) != iProver_top
% 35.75/5.00      | v1_relat_1(X0) != iProver_top ),
% 35.75/5.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_148993,plain,
% 35.75/5.00      ( sK0 = k1_xboole_0
% 35.75/5.00      | r1_tarski(k2_relat_1(X0),sK1) != iProver_top
% 35.75/5.00      | v1_funct_1(X0) != iProver_top
% 35.75/5.00      | v1_funct_1(sK3) != iProver_top
% 35.75/5.00      | v2_funct_1(X0) = iProver_top
% 35.75/5.00      | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
% 35.75/5.00      | v1_relat_1(X0) != iProver_top
% 35.75/5.00      | v1_relat_1(sK3) != iProver_top ),
% 35.75/5.00      inference(superposition,[status(thm)],[c_148623,c_148138]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_30,negated_conjecture,
% 35.75/5.00      ( v1_funct_1(sK3) ),
% 35.75/5.00      inference(cnf_transformation,[],[f78]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_38,plain,
% 35.75/5.00      ( v1_funct_1(sK3) = iProver_top ),
% 35.75/5.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_40,plain,
% 35.75/5.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 35.75/5.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_7656,plain,
% 35.75/5.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 35.75/5.00      | r1_tarski(sK3,k2_zfmisc_1(sK1,sK0)) ),
% 35.75/5.00      inference(instantiation,[status(thm)],[c_5]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_7657,plain,
% 35.75/5.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 35.75/5.00      | r1_tarski(sK3,k2_zfmisc_1(sK1,sK0)) = iProver_top ),
% 35.75/5.00      inference(predicate_to_equality,[status(thm)],[c_7656]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_36121,plain,
% 35.75/5.00      ( ~ r1_tarski(sK3,k2_zfmisc_1(sK1,sK0))
% 35.75/5.00      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
% 35.75/5.00      | v1_relat_1(sK3) ),
% 35.75/5.00      inference(instantiation,[status(thm)],[c_309]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_36123,plain,
% 35.75/5.00      ( r1_tarski(sK3,k2_zfmisc_1(sK1,sK0)) != iProver_top
% 35.75/5.00      | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 35.75/5.00      | v1_relat_1(sK3) = iProver_top ),
% 35.75/5.00      inference(predicate_to_equality,[status(thm)],[c_36121]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_37307,plain,
% 35.75/5.00      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
% 35.75/5.00      inference(instantiation,[status(thm)],[c_9]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_37308,plain,
% 35.75/5.00      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
% 35.75/5.00      inference(predicate_to_equality,[status(thm)],[c_37307]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_163774,plain,
% 35.75/5.00      ( v1_relat_1(X0) != iProver_top
% 35.75/5.00      | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
% 35.75/5.00      | v2_funct_1(X0) = iProver_top
% 35.75/5.00      | sK0 = k1_xboole_0
% 35.75/5.00      | r1_tarski(k2_relat_1(X0),sK1) != iProver_top
% 35.75/5.00      | v1_funct_1(X0) != iProver_top ),
% 35.75/5.00      inference(global_propositional_subsumption,
% 35.75/5.00                [status(thm)],
% 35.75/5.00                [c_148993,c_38,c_40,c_7657,c_36123,c_37308]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_163775,plain,
% 35.75/5.00      ( sK0 = k1_xboole_0
% 35.75/5.00      | r1_tarski(k2_relat_1(X0),sK1) != iProver_top
% 35.75/5.00      | v1_funct_1(X0) != iProver_top
% 35.75/5.00      | v2_funct_1(X0) = iProver_top
% 35.75/5.00      | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
% 35.75/5.00      | v1_relat_1(X0) != iProver_top ),
% 35.75/5.00      inference(renaming,[status(thm)],[c_163774]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_163785,plain,
% 35.75/5.00      ( sK0 = k1_xboole_0
% 35.75/5.00      | v1_funct_1(sK2) != iProver_top
% 35.75/5.00      | v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
% 35.75/5.00      | v2_funct_1(sK2) = iProver_top
% 35.75/5.00      | v1_relat_1(sK2) != iProver_top ),
% 35.75/5.00      inference(superposition,[status(thm)],[c_148432,c_163775]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_25,plain,
% 35.75/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.75/5.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 35.75/5.00      | ~ v1_funct_1(X0)
% 35.75/5.00      | ~ v1_funct_1(X3)
% 35.75/5.00      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 35.75/5.00      inference(cnf_transformation,[],[f72]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_148132,plain,
% 35.75/5.00      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 35.75/5.00      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 35.75/5.00      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 35.75/5.00      | v1_funct_1(X5) != iProver_top
% 35.75/5.00      | v1_funct_1(X4) != iProver_top ),
% 35.75/5.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_149061,plain,
% 35.75/5.00      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 35.75/5.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 35.75/5.00      | v1_funct_1(X2) != iProver_top
% 35.75/5.00      | v1_funct_1(sK3) != iProver_top ),
% 35.75/5.00      inference(superposition,[status(thm)],[c_148130,c_148132]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_32994,plain,
% 35.75/5.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 35.75/5.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_32996,plain,
% 35.75/5.00      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 35.75/5.00      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 35.75/5.00      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 35.75/5.00      | v1_funct_1(X5) != iProver_top
% 35.75/5.00      | v1_funct_1(X4) != iProver_top ),
% 35.75/5.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_33565,plain,
% 35.75/5.00      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 35.75/5.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 35.75/5.00      | v1_funct_1(X2) != iProver_top
% 35.75/5.00      | v1_funct_1(sK3) != iProver_top ),
% 35.75/5.00      inference(superposition,[status(thm)],[c_32994,c_32996]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_149528,plain,
% 35.75/5.00      ( v1_funct_1(X2) != iProver_top
% 35.75/5.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 35.75/5.00      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 35.75/5.00      inference(global_propositional_subsumption,
% 35.75/5.00                [status(thm)],
% 35.75/5.00                [c_149061,c_38,c_33565]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_149529,plain,
% 35.75/5.00      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 35.75/5.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 35.75/5.00      | v1_funct_1(X2) != iProver_top ),
% 35.75/5.00      inference(renaming,[status(thm)],[c_149528]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_149539,plain,
% 35.75/5.00      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 35.75/5.00      | v1_funct_1(sK2) != iProver_top ),
% 35.75/5.00      inference(superposition,[status(thm)],[c_148128,c_149529]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_15,plain,
% 35.75/5.00      ( ~ r2_relset_1(X0,X1,X2,X3)
% 35.75/5.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 35.75/5.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 35.75/5.00      | X3 = X2 ),
% 35.75/5.00      inference(cnf_transformation,[],[f61]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_27,negated_conjecture,
% 35.75/5.00      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 35.75/5.00      inference(cnf_transformation,[],[f81]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_439,plain,
% 35.75/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.75/5.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.75/5.00      | X3 = X0
% 35.75/5.00      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 35.75/5.00      | k6_partfun1(sK0) != X3
% 35.75/5.00      | sK0 != X2
% 35.75/5.00      | sK0 != X1 ),
% 35.75/5.00      inference(resolution_lifted,[status(thm)],[c_15,c_27]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_440,plain,
% 35.75/5.00      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 35.75/5.00      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 35.75/5.00      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 35.75/5.00      inference(unflattening,[status(thm)],[c_439]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_24,plain,
% 35.75/5.00      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 35.75/5.00      inference(cnf_transformation,[],[f71]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_448,plain,
% 35.75/5.00      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 35.75/5.00      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 35.75/5.00      inference(forward_subsumption_resolution,
% 35.75/5.00                [status(thm)],
% 35.75/5.00                [c_440,c_24]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_22,plain,
% 35.75/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.75/5.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 35.75/5.00      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 35.75/5.00      | ~ v1_funct_1(X0)
% 35.75/5.00      | ~ v1_funct_1(X3) ),
% 35.75/5.00      inference(cnf_transformation,[],[f70]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_33107,plain,
% 35.75/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.75/5.00      | m1_subset_1(k1_partfun1(X1,X2,X3,X4,X0,sK3),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
% 35.75/5.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 35.75/5.00      | ~ v1_funct_1(X0)
% 35.75/5.00      | ~ v1_funct_1(sK3) ),
% 35.75/5.00      inference(instantiation,[status(thm)],[c_22]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_33167,plain,
% 35.75/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.75/5.00      | m1_subset_1(k1_partfun1(X1,X2,sK1,sK0,X0,sK3),k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 35.75/5.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 35.75/5.00      | ~ v1_funct_1(X0)
% 35.75/5.00      | ~ v1_funct_1(sK3) ),
% 35.75/5.00      inference(instantiation,[status(thm)],[c_33107]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_33223,plain,
% 35.75/5.00      ( m1_subset_1(k1_partfun1(X0,X1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
% 35.75/5.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 35.75/5.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 35.75/5.00      | ~ v1_funct_1(sK3)
% 35.75/5.00      | ~ v1_funct_1(sK2) ),
% 35.75/5.00      inference(instantiation,[status(thm)],[c_33167]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_33292,plain,
% 35.75/5.00      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 35.75/5.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 35.75/5.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 35.75/5.00      | ~ v1_funct_1(sK3)
% 35.75/5.00      | ~ v1_funct_1(sK2) ),
% 35.75/5.00      inference(instantiation,[status(thm)],[c_33223]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_147988,plain,
% 35.75/5.00      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 35.75/5.00      inference(global_propositional_subsumption,
% 35.75/5.00                [status(thm)],
% 35.75/5.00                [c_448,c_34,c_32,c_30,c_28,c_33292]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_149556,plain,
% 35.75/5.00      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 35.75/5.00      | v1_funct_1(sK2) != iProver_top ),
% 35.75/5.00      inference(light_normalisation,[status(thm)],[c_149539,c_147988]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_35,plain,
% 35.75/5.00      ( v1_funct_1(sK2) = iProver_top ),
% 35.75/5.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_34016,plain,
% 35.75/5.00      ( v1_funct_1(X2) != iProver_top
% 35.75/5.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 35.75/5.00      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 35.75/5.00      inference(global_propositional_subsumption,
% 35.75/5.00                [status(thm)],
% 35.75/5.00                [c_33565,c_38]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_34017,plain,
% 35.75/5.00      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 35.75/5.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 35.75/5.00      | v1_funct_1(X2) != iProver_top ),
% 35.75/5.00      inference(renaming,[status(thm)],[c_34016]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_34029,plain,
% 35.75/5.00      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 35.75/5.00      | v1_funct_1(sK2) != iProver_top ),
% 35.75/5.00      inference(superposition,[status(thm)],[c_32992,c_34017]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_33003,plain,
% 35.75/5.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 35.75/5.00      | r1_tarski(X0,X1) != iProver_top ),
% 35.75/5.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_32988,plain,
% 35.75/5.00      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 35.75/5.00      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 35.75/5.00      inference(predicate_to_equality,[status(thm)],[c_448]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_33379,plain,
% 35.75/5.00      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
% 35.75/5.00      | r1_tarski(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k2_zfmisc_1(sK0,sK0)) != iProver_top ),
% 35.75/5.00      inference(superposition,[status(thm)],[c_33003,c_32988]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_32998,plain,
% 35.75/5.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 35.75/5.00      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 35.75/5.00      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 35.75/5.00      | v1_funct_1(X0) != iProver_top
% 35.75/5.00      | v1_funct_1(X3) != iProver_top ),
% 35.75/5.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_33305,plain,
% 35.75/5.00      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
% 35.75/5.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 35.75/5.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 35.75/5.00      | v1_funct_1(sK3) != iProver_top
% 35.75/5.00      | v1_funct_1(sK2) != iProver_top ),
% 35.75/5.00      inference(superposition,[status(thm)],[c_32998,c_32988]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_33495,plain,
% 35.75/5.00      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
% 35.75/5.00      inference(global_propositional_subsumption,
% 35.75/5.00                [status(thm)],
% 35.75/5.00                [c_33379,c_35,c_37,c_38,c_40,c_33305]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_34046,plain,
% 35.75/5.00      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 35.75/5.00      | v1_funct_1(sK2) != iProver_top ),
% 35.75/5.00      inference(light_normalisation,[status(thm)],[c_34029,c_33495]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_149729,plain,
% 35.75/5.00      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 35.75/5.00      inference(global_propositional_subsumption,
% 35.75/5.00                [status(thm)],
% 35.75/5.00                [c_149556,c_35,c_34046]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_163855,plain,
% 35.75/5.00      ( sK0 = k1_xboole_0
% 35.75/5.00      | v1_funct_1(sK2) != iProver_top
% 35.75/5.00      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 35.75/5.00      | v2_funct_1(sK2) = iProver_top
% 35.75/5.00      | v1_relat_1(sK2) != iProver_top ),
% 35.75/5.00      inference(light_normalisation,[status(thm)],[c_163785,c_149729]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_163881,plain,
% 35.75/5.00      ( ~ v1_funct_1(sK2)
% 35.75/5.00      | ~ v2_funct_1(k6_partfun1(sK0))
% 35.75/5.00      | v2_funct_1(sK2)
% 35.75/5.00      | ~ v1_relat_1(sK2)
% 35.75/5.00      | sK0 = k1_xboole_0 ),
% 35.75/5.00      inference(predicate_to_equality_rev,[status(thm)],[c_163855]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_11,plain,
% 35.75/5.00      ( v2_funct_1(k6_partfun1(X0)) ),
% 35.75/5.00      inference(cnf_transformation,[],[f83]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_192892,plain,
% 35.75/5.00      ( v2_funct_1(k6_partfun1(sK0)) ),
% 35.75/5.00      inference(instantiation,[status(thm)],[c_11]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_219044,plain,
% 35.75/5.00      ( sK0 = k1_xboole_0 ),
% 35.75/5.00      inference(global_propositional_subsumption,
% 35.75/5.00                [status(thm)],
% 35.75/5.00                [c_188994,c_34,c_32,c_26,c_7663,c_36316,c_38503,c_163881,
% 35.75/5.00                 c_192892]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_186294,plain,
% 35.75/5.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 35.75/5.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_219253,plain,
% 35.75/5.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) = iProver_top ),
% 35.75/5.00      inference(demodulation,[status(thm)],[c_219044,c_186294]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_2,plain,
% 35.75/5.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 35.75/5.00      inference(cnf_transformation,[],[f85]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_219255,plain,
% 35.75/5.00      ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 35.75/5.00      inference(demodulation,[status(thm)],[c_219253,c_2]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_105195,plain,
% 35.75/5.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
% 35.75/5.00      | r1_tarski(sK2,k1_xboole_0) ),
% 35.75/5.00      inference(instantiation,[status(thm)],[c_5]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_105198,plain,
% 35.75/5.00      ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 35.75/5.00      | r1_tarski(sK2,k1_xboole_0) = iProver_top ),
% 35.75/5.00      inference(predicate_to_equality,[status(thm)],[c_105195]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_1098,plain,( X0 = X0 ),theory(equality) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_88468,plain,
% 35.75/5.00      ( sK2 = sK2 ),
% 35.75/5.00      inference(instantiation,[status(thm)],[c_1098]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_1099,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_50687,plain,
% 35.75/5.00      ( sK2 != X0 | sK2 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 35.75/5.00      inference(instantiation,[status(thm)],[c_1099]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_82045,plain,
% 35.75/5.00      ( sK2 != sK2 | sK2 = k1_xboole_0 | k1_xboole_0 != sK2 ),
% 35.75/5.00      inference(instantiation,[status(thm)],[c_50687]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_0,plain,
% 35.75/5.00      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 35.75/5.00      inference(cnf_transformation,[],[f47]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_63388,plain,
% 35.75/5.00      ( ~ r1_tarski(sK2,k1_xboole_0) | k1_xboole_0 = sK2 ),
% 35.75/5.00      inference(instantiation,[status(thm)],[c_0]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_63392,plain,
% 35.75/5.00      ( k1_xboole_0 = sK2 | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
% 35.75/5.00      inference(predicate_to_equality,[status(thm)],[c_63388]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_1105,plain,
% 35.75/5.00      ( ~ v2_funct_1(X0) | v2_funct_1(X1) | X1 != X0 ),
% 35.75/5.00      theory(equality) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_20440,plain,
% 35.75/5.00      ( v2_funct_1(X0) | ~ v2_funct_1(k1_xboole_0) | X0 != k1_xboole_0 ),
% 35.75/5.00      inference(instantiation,[status(thm)],[c_1105]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_20898,plain,
% 35.75/5.00      ( v2_funct_1(sK2)
% 35.75/5.00      | ~ v2_funct_1(k1_xboole_0)
% 35.75/5.00      | sK2 != k1_xboole_0 ),
% 35.75/5.00      inference(instantiation,[status(thm)],[c_20440]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_1,plain,
% 35.75/5.00      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 35.75/5.00      inference(cnf_transformation,[],[f84]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_18391,plain,
% 35.75/5.00      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 35.75/5.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_18615,plain,
% 35.75/5.00      ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 35.75/5.00      inference(superposition,[status(thm)],[c_1,c_18391]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_18393,plain,
% 35.75/5.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 35.75/5.00      | r1_tarski(X0,X1) = iProver_top ),
% 35.75/5.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_18646,plain,
% 35.75/5.00      ( r1_tarski(k6_partfun1(k1_xboole_0),k1_xboole_0) = iProver_top ),
% 35.75/5.00      inference(superposition,[status(thm)],[c_18615,c_18393]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_18395,plain,
% 35.75/5.00      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 35.75/5.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_18776,plain,
% 35.75/5.00      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 35.75/5.00      inference(superposition,[status(thm)],[c_18646,c_18395]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_18392,plain,
% 35.75/5.00      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 35.75/5.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_18808,plain,
% 35.75/5.00      ( v2_funct_1(k1_xboole_0) = iProver_top ),
% 35.75/5.00      inference(superposition,[status(thm)],[c_18776,c_18392]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(c_18813,plain,
% 35.75/5.00      ( v2_funct_1(k1_xboole_0) ),
% 35.75/5.00      inference(predicate_to_equality_rev,[status(thm)],[c_18808]) ).
% 35.75/5.00  
% 35.75/5.00  cnf(contradiction,plain,
% 35.75/5.00      ( $false ),
% 35.75/5.00      inference(minisat,
% 35.75/5.00                [status(thm)],
% 35.75/5.00                [c_219255,c_105198,c_88468,c_82045,c_63392,c_20898,
% 35.75/5.00                 c_18813,c_26]) ).
% 35.75/5.00  
% 35.75/5.00  
% 35.75/5.00  % SZS output end CNFRefutation for theBenchmark.p
% 35.75/5.00  
% 35.75/5.00  ------                               Statistics
% 35.75/5.00  
% 35.75/5.00  ------ Selected
% 35.75/5.00  
% 35.75/5.00  total_time:                             4.497
% 35.75/5.00  
%------------------------------------------------------------------------------
