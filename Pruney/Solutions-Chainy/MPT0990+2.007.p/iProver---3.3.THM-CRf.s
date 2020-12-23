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
% DateTime   : Thu Dec  3 12:02:57 EST 2020

% Result     : Theorem 11.50s
% Output     : CNFRefutation 11.50s
% Verified   : 
% Statistics : Number of formulae       :  194 ( 952 expanded)
%              Number of clauses        :  105 ( 293 expanded)
%              Number of leaves         :   23 ( 230 expanded)
%              Depth                    :   18
%              Number of atoms          :  587 (6831 expanded)
%              Number of equality atoms :  256 (2419 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   24 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f26,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( ( v2_funct_1(X2)
              & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
              & k2_relset_1(X0,X1,X2) = X1 )
           => ( k2_funct_1(X2) = X3
              | k1_xboole_0 = X1
              | k1_xboole_0 = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( ( v2_funct_1(X2)
                & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
                & k2_relset_1(X0,X1,X2) = X1 )
             => ( k2_funct_1(X2) = X3
                | k1_xboole_0 = X1
                | k1_xboole_0 = X0 ) ) ) ) ),
    inference(negated_conjecture,[],[f26])).

fof(f61,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f62,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f61])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
     => ( k2_funct_1(X2) != sK3
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & v2_funct_1(X2)
        & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0))
        & k2_relset_1(X0,X1,X2) = X1
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(sK3,X1,X0)
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( k2_funct_1(X2) != X3
            & k1_xboole_0 != X1
            & k1_xboole_0 != X0
            & v2_funct_1(X2)
            & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & k2_relset_1(X0,X1,X2) = X1
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k2_funct_1(sK2) != X3
          & k1_xboole_0 != sK1
          & k1_xboole_0 != sK0
          & v2_funct_1(sK2)
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & k2_relset_1(sK0,sK1,sK2) = sK1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,
    ( k2_funct_1(sK2) != sK3
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & v2_funct_1(sK2)
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & k2_relset_1(sK0,sK1,sK2) = sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f62,f68,f67])).

fof(f111,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f69])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f108,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f69])).

fof(f106,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f69])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f38])).

fof(f83,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f114,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f69])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f47,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f46])).

fof(f93,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f24,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f104,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f24])).

fof(f124,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f93,f104])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f112,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f69])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f45,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f44])).

fof(f91,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f121,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_partfun1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f82,f104])).

fof(f23,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f58,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f57])).

fof(f103,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f109,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f69])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f54,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f53])).

fof(f66,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f54])).

fof(f98,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f113,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f69])).

fof(f21,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f100,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f126,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f100,f104])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f56,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f55])).

fof(f102,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f40])).

fof(f87,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f7,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f119,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f79,f104])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f81,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f120,plain,(
    ! [X0] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f81,f104])).

fof(f117,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_41,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_1524,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1531,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2419,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1524,c_1531])).

cnf(c_44,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1521,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_2420,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1521,c_1531])).

cnf(c_46,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_1519,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_14,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1542,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k5_relat_1(k5_relat_1(X1,X0),X2) = k5_relat_1(X1,k5_relat_1(X0,X2)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1546,plain,
    ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_7868,plain,
    ( k5_relat_1(k2_funct_1(X0),k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(k2_funct_1(X0),X1),X2)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1542,c_1546])).

cnf(c_32453,plain,
    ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1519,c_7868])).

cnf(c_33301,plain,
    ( v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_32453,c_2420])).

cnf(c_33302,plain,
    ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_33301])).

cnf(c_33310,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2420,c_33302])).

cnf(c_38,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_1525,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_22,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_1534,plain,
    ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_6855,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1525,c_1534])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1530,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3325,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1521,c_1530])).

cnf(c_40,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f112])).

cnf(c_3326,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_3325,c_40])).

cnf(c_6856,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6855,c_3326])).

cnf(c_47,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_7480,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6856,c_47,c_2420])).

cnf(c_33315,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k6_partfun1(sK1),X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_33310,c_7480])).

cnf(c_35531,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
    inference(superposition,[status(thm)],[c_2419,c_33315])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v4_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_4,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_479,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_26,c_4])).

cnf(c_483,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_479,c_25])).

cnf(c_484,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_483])).

cnf(c_1517,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_484])).

cnf(c_3318,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1521,c_1517])).

cnf(c_20,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1536,plain,
    ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_7386,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1525,c_1536])).

cnf(c_7453,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7386,c_47,c_2420])).

cnf(c_12,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_partfun1(X1)) = X0 ),
    inference(cnf_transformation,[],[f121])).

cnf(c_1544,plain,
    ( k5_relat_1(X0,k6_partfun1(X1)) = X0
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_7456,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0)) = k2_funct_1(sK2)
    | r1_tarski(k1_relat_1(sK2),X0) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7453,c_1544])).

cnf(c_6817,plain,
    ( ~ v1_funct_1(sK2)
    | v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_6818,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6817])).

cnf(c_7517,plain,
    ( r1_tarski(k1_relat_1(sK2),X0) != iProver_top
    | k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0)) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7456,c_47,c_2420,c_6818])).

cnf(c_7518,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0)) = k2_funct_1(sK2)
    | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_7517])).

cnf(c_7524,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k2_funct_1(sK2) ),
    inference(superposition,[status(thm)],[c_3318,c_7518])).

cnf(c_33,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1526,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_8216,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1524,c_1526])).

cnf(c_43,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_50,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_8324,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8216,c_50])).

cnf(c_8325,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_8324])).

cnf(c_8333,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1521,c_8325])).

cnf(c_29,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_39,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_558,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_39])).

cnf(c_559,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_558])).

cnf(c_30,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_68,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_561,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_559,c_68])).

cnf(c_1514,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_561])).

cnf(c_31,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1611,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_2259,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1514,c_46,c_44,c_43,c_41,c_68,c_559,c_1611])).

cnf(c_8334,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8333,c_2259])).

cnf(c_8458,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8334,c_47])).

cnf(c_3317,plain,
    ( r1_tarski(k1_relat_1(sK3),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1524,c_1517])).

cnf(c_17,plain,
    ( ~ r1_tarski(X0,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1539,plain,
    ( k9_relat_1(X0,k10_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_7427,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
    | r1_tarski(X0,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3326,c_1539])).

cnf(c_7483,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7427,c_47,c_2420])).

cnf(c_7490,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(sK3))) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_3317,c_7483])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X1,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1547,plain,
    ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4841,plain,
    ( k10_relat_1(sK2,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(sK2,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2420,c_1547])).

cnf(c_5440,plain,
    ( k10_relat_1(sK2,k1_relat_1(sK3)) = k1_relat_1(k5_relat_1(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_2419,c_4841])).

cnf(c_7491,plain,
    ( k9_relat_1(sK2,k1_relat_1(k5_relat_1(sK2,sK3))) = k1_relat_1(sK3) ),
    inference(light_normalisation,[status(thm)],[c_7490,c_5440])).

cnf(c_19933,plain,
    ( k9_relat_1(sK2,k1_relat_1(k6_partfun1(sK0))) = k1_relat_1(sK3) ),
    inference(light_normalisation,[status(thm)],[c_7491,c_7491,c_8458])).

cnf(c_10,plain,
    ( k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f119])).

cnf(c_7,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_462,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_26,c_7])).

cnf(c_466,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_462,c_26,c_25,c_7])).

cnf(c_1518,plain,
    ( k7_relat_1(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_466])).

cnf(c_3113,plain,
    ( k7_relat_1(sK2,sK0) = sK2 ),
    inference(superposition,[status(thm)],[c_1521,c_1518])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1548,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2629,plain,
    ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_2420,c_1548])).

cnf(c_3639,plain,
    ( k9_relat_1(sK2,sK0) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_3113,c_2629])).

cnf(c_3640,plain,
    ( k9_relat_1(sK2,sK0) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_3639,c_3326])).

cnf(c_19934,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(demodulation,[status(thm)],[c_19933,c_10,c_3640])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 ),
    inference(cnf_transformation,[],[f120])).

cnf(c_1545,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2626,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1(sK3)),sK3) = sK3 ),
    inference(superposition,[status(thm)],[c_2419,c_1545])).

cnf(c_19950,plain,
    ( k5_relat_1(k6_partfun1(sK1),sK3) = sK3 ),
    inference(demodulation,[status(thm)],[c_19934,c_2626])).

cnf(c_35539,plain,
    ( k2_funct_1(sK2) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_35531,c_7524,c_8458,c_19950])).

cnf(c_35,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f117])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_35539,c_35])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:20:00 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 11.50/1.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.50/1.97  
% 11.50/1.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.50/1.97  
% 11.50/1.97  ------  iProver source info
% 11.50/1.97  
% 11.50/1.97  git: date: 2020-06-30 10:37:57 +0100
% 11.50/1.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.50/1.97  git: non_committed_changes: false
% 11.50/1.97  git: last_make_outside_of_git: false
% 11.50/1.97  
% 11.50/1.97  ------ 
% 11.50/1.97  
% 11.50/1.97  ------ Input Options
% 11.50/1.97  
% 11.50/1.97  --out_options                           all
% 11.50/1.97  --tptp_safe_out                         true
% 11.50/1.97  --problem_path                          ""
% 11.50/1.97  --include_path                          ""
% 11.50/1.97  --clausifier                            res/vclausify_rel
% 11.50/1.97  --clausifier_options                    ""
% 11.50/1.97  --stdin                                 false
% 11.50/1.97  --stats_out                             all
% 11.50/1.97  
% 11.50/1.97  ------ General Options
% 11.50/1.97  
% 11.50/1.97  --fof                                   false
% 11.50/1.97  --time_out_real                         305.
% 11.50/1.97  --time_out_virtual                      -1.
% 11.50/1.97  --symbol_type_check                     false
% 11.50/1.97  --clausify_out                          false
% 11.50/1.97  --sig_cnt_out                           false
% 11.50/1.97  --trig_cnt_out                          false
% 11.50/1.97  --trig_cnt_out_tolerance                1.
% 11.50/1.97  --trig_cnt_out_sk_spl                   false
% 11.50/1.97  --abstr_cl_out                          false
% 11.50/1.97  
% 11.50/1.97  ------ Global Options
% 11.50/1.97  
% 11.50/1.97  --schedule                              default
% 11.50/1.97  --add_important_lit                     false
% 11.50/1.97  --prop_solver_per_cl                    1000
% 11.50/1.97  --min_unsat_core                        false
% 11.50/1.97  --soft_assumptions                      false
% 11.50/1.97  --soft_lemma_size                       3
% 11.50/1.97  --prop_impl_unit_size                   0
% 11.50/1.97  --prop_impl_unit                        []
% 11.50/1.97  --share_sel_clauses                     true
% 11.50/1.97  --reset_solvers                         false
% 11.50/1.97  --bc_imp_inh                            [conj_cone]
% 11.50/1.97  --conj_cone_tolerance                   3.
% 11.50/1.97  --extra_neg_conj                        none
% 11.50/1.97  --large_theory_mode                     true
% 11.50/1.97  --prolific_symb_bound                   200
% 11.50/1.97  --lt_threshold                          2000
% 11.50/1.97  --clause_weak_htbl                      true
% 11.50/1.97  --gc_record_bc_elim                     false
% 11.50/1.97  
% 11.50/1.97  ------ Preprocessing Options
% 11.50/1.97  
% 11.50/1.97  --preprocessing_flag                    true
% 11.50/1.97  --time_out_prep_mult                    0.1
% 11.50/1.97  --splitting_mode                        input
% 11.50/1.97  --splitting_grd                         true
% 11.50/1.97  --splitting_cvd                         false
% 11.50/1.97  --splitting_cvd_svl                     false
% 11.50/1.97  --splitting_nvd                         32
% 11.50/1.97  --sub_typing                            true
% 11.50/1.97  --prep_gs_sim                           true
% 11.50/1.97  --prep_unflatten                        true
% 11.50/1.97  --prep_res_sim                          true
% 11.50/1.97  --prep_upred                            true
% 11.50/1.97  --prep_sem_filter                       exhaustive
% 11.50/1.97  --prep_sem_filter_out                   false
% 11.50/1.97  --pred_elim                             true
% 11.50/1.97  --res_sim_input                         true
% 11.50/1.97  --eq_ax_congr_red                       true
% 11.50/1.97  --pure_diseq_elim                       true
% 11.50/1.97  --brand_transform                       false
% 11.50/1.97  --non_eq_to_eq                          false
% 11.50/1.97  --prep_def_merge                        true
% 11.50/1.97  --prep_def_merge_prop_impl              false
% 11.50/1.97  --prep_def_merge_mbd                    true
% 11.50/1.97  --prep_def_merge_tr_red                 false
% 11.50/1.97  --prep_def_merge_tr_cl                  false
% 11.50/1.97  --smt_preprocessing                     true
% 11.50/1.97  --smt_ac_axioms                         fast
% 11.50/1.97  --preprocessed_out                      false
% 11.50/1.97  --preprocessed_stats                    false
% 11.50/1.97  
% 11.50/1.97  ------ Abstraction refinement Options
% 11.50/1.97  
% 11.50/1.97  --abstr_ref                             []
% 11.50/1.97  --abstr_ref_prep                        false
% 11.50/1.97  --abstr_ref_until_sat                   false
% 11.50/1.97  --abstr_ref_sig_restrict                funpre
% 11.50/1.97  --abstr_ref_af_restrict_to_split_sk     false
% 11.50/1.97  --abstr_ref_under                       []
% 11.50/1.97  
% 11.50/1.97  ------ SAT Options
% 11.50/1.97  
% 11.50/1.97  --sat_mode                              false
% 11.50/1.97  --sat_fm_restart_options                ""
% 11.50/1.97  --sat_gr_def                            false
% 11.50/1.97  --sat_epr_types                         true
% 11.50/1.97  --sat_non_cyclic_types                  false
% 11.50/1.97  --sat_finite_models                     false
% 11.50/1.97  --sat_fm_lemmas                         false
% 11.50/1.97  --sat_fm_prep                           false
% 11.50/1.97  --sat_fm_uc_incr                        true
% 11.50/1.97  --sat_out_model                         small
% 11.50/1.97  --sat_out_clauses                       false
% 11.50/1.97  
% 11.50/1.97  ------ QBF Options
% 11.50/1.97  
% 11.50/1.97  --qbf_mode                              false
% 11.50/1.97  --qbf_elim_univ                         false
% 11.50/1.97  --qbf_dom_inst                          none
% 11.50/1.97  --qbf_dom_pre_inst                      false
% 11.50/1.97  --qbf_sk_in                             false
% 11.50/1.97  --qbf_pred_elim                         true
% 11.50/1.97  --qbf_split                             512
% 11.50/1.97  
% 11.50/1.97  ------ BMC1 Options
% 11.50/1.97  
% 11.50/1.97  --bmc1_incremental                      false
% 11.50/1.97  --bmc1_axioms                           reachable_all
% 11.50/1.97  --bmc1_min_bound                        0
% 11.50/1.97  --bmc1_max_bound                        -1
% 11.50/1.97  --bmc1_max_bound_default                -1
% 11.50/1.97  --bmc1_symbol_reachability              true
% 11.50/1.97  --bmc1_property_lemmas                  false
% 11.50/1.97  --bmc1_k_induction                      false
% 11.50/1.97  --bmc1_non_equiv_states                 false
% 11.50/1.97  --bmc1_deadlock                         false
% 11.50/1.97  --bmc1_ucm                              false
% 11.50/1.97  --bmc1_add_unsat_core                   none
% 11.50/1.97  --bmc1_unsat_core_children              false
% 11.50/1.97  --bmc1_unsat_core_extrapolate_axioms    false
% 11.50/1.97  --bmc1_out_stat                         full
% 11.50/1.97  --bmc1_ground_init                      false
% 11.50/1.97  --bmc1_pre_inst_next_state              false
% 11.50/1.97  --bmc1_pre_inst_state                   false
% 11.50/1.97  --bmc1_pre_inst_reach_state             false
% 11.50/1.97  --bmc1_out_unsat_core                   false
% 11.50/1.97  --bmc1_aig_witness_out                  false
% 11.50/1.97  --bmc1_verbose                          false
% 11.50/1.97  --bmc1_dump_clauses_tptp                false
% 11.50/1.97  --bmc1_dump_unsat_core_tptp             false
% 11.50/1.97  --bmc1_dump_file                        -
% 11.50/1.97  --bmc1_ucm_expand_uc_limit              128
% 11.50/1.97  --bmc1_ucm_n_expand_iterations          6
% 11.50/1.97  --bmc1_ucm_extend_mode                  1
% 11.50/1.97  --bmc1_ucm_init_mode                    2
% 11.50/1.97  --bmc1_ucm_cone_mode                    none
% 11.50/1.97  --bmc1_ucm_reduced_relation_type        0
% 11.50/1.97  --bmc1_ucm_relax_model                  4
% 11.50/1.97  --bmc1_ucm_full_tr_after_sat            true
% 11.50/1.97  --bmc1_ucm_expand_neg_assumptions       false
% 11.50/1.97  --bmc1_ucm_layered_model                none
% 11.50/1.97  --bmc1_ucm_max_lemma_size               10
% 11.50/1.97  
% 11.50/1.97  ------ AIG Options
% 11.50/1.97  
% 11.50/1.97  --aig_mode                              false
% 11.50/1.97  
% 11.50/1.97  ------ Instantiation Options
% 11.50/1.97  
% 11.50/1.97  --instantiation_flag                    true
% 11.50/1.97  --inst_sos_flag                         true
% 11.50/1.97  --inst_sos_phase                        true
% 11.50/1.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.50/1.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.50/1.97  --inst_lit_sel_side                     num_symb
% 11.50/1.97  --inst_solver_per_active                1400
% 11.50/1.97  --inst_solver_calls_frac                1.
% 11.50/1.97  --inst_passive_queue_type               priority_queues
% 11.50/1.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.50/1.97  --inst_passive_queues_freq              [25;2]
% 11.50/1.97  --inst_dismatching                      true
% 11.50/1.97  --inst_eager_unprocessed_to_passive     true
% 11.50/1.97  --inst_prop_sim_given                   true
% 11.50/1.97  --inst_prop_sim_new                     false
% 11.50/1.97  --inst_subs_new                         false
% 11.50/1.97  --inst_eq_res_simp                      false
% 11.50/1.97  --inst_subs_given                       false
% 11.50/1.97  --inst_orphan_elimination               true
% 11.50/1.97  --inst_learning_loop_flag               true
% 11.50/1.97  --inst_learning_start                   3000
% 11.50/1.97  --inst_learning_factor                  2
% 11.50/1.97  --inst_start_prop_sim_after_learn       3
% 11.50/1.97  --inst_sel_renew                        solver
% 11.50/1.97  --inst_lit_activity_flag                true
% 11.50/1.97  --inst_restr_to_given                   false
% 11.50/1.97  --inst_activity_threshold               500
% 11.50/1.97  --inst_out_proof                        true
% 11.50/1.97  
% 11.50/1.97  ------ Resolution Options
% 11.50/1.97  
% 11.50/1.97  --resolution_flag                       true
% 11.50/1.97  --res_lit_sel                           adaptive
% 11.50/1.97  --res_lit_sel_side                      none
% 11.50/1.97  --res_ordering                          kbo
% 11.50/1.97  --res_to_prop_solver                    active
% 11.50/1.97  --res_prop_simpl_new                    false
% 11.50/1.97  --res_prop_simpl_given                  true
% 11.50/1.97  --res_passive_queue_type                priority_queues
% 11.50/1.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.50/1.97  --res_passive_queues_freq               [15;5]
% 11.50/1.97  --res_forward_subs                      full
% 11.50/1.97  --res_backward_subs                     full
% 11.50/1.97  --res_forward_subs_resolution           true
% 11.50/1.97  --res_backward_subs_resolution          true
% 11.50/1.97  --res_orphan_elimination                true
% 11.50/1.97  --res_time_limit                        2.
% 11.50/1.97  --res_out_proof                         true
% 11.50/1.97  
% 11.50/1.97  ------ Superposition Options
% 11.50/1.97  
% 11.50/1.97  --superposition_flag                    true
% 11.50/1.97  --sup_passive_queue_type                priority_queues
% 11.50/1.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.50/1.97  --sup_passive_queues_freq               [8;1;4]
% 11.50/1.97  --demod_completeness_check              fast
% 11.50/1.97  --demod_use_ground                      true
% 11.50/1.97  --sup_to_prop_solver                    passive
% 11.50/1.97  --sup_prop_simpl_new                    true
% 11.50/1.97  --sup_prop_simpl_given                  true
% 11.50/1.97  --sup_fun_splitting                     true
% 11.50/1.97  --sup_smt_interval                      50000
% 11.50/1.97  
% 11.50/1.97  ------ Superposition Simplification Setup
% 11.50/1.97  
% 11.50/1.97  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.50/1.97  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.50/1.97  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.50/1.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.50/1.97  --sup_full_triv                         [TrivRules;PropSubs]
% 11.50/1.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.50/1.97  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.50/1.97  --sup_immed_triv                        [TrivRules]
% 11.50/1.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.50/1.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.50/1.97  --sup_immed_bw_main                     []
% 11.50/1.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.50/1.97  --sup_input_triv                        [Unflattening;TrivRules]
% 11.50/1.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.50/1.97  --sup_input_bw                          []
% 11.50/1.97  
% 11.50/1.97  ------ Combination Options
% 11.50/1.97  
% 11.50/1.97  --comb_res_mult                         3
% 11.50/1.97  --comb_sup_mult                         2
% 11.50/1.97  --comb_inst_mult                        10
% 11.50/1.97  
% 11.50/1.97  ------ Debug Options
% 11.50/1.97  
% 11.50/1.97  --dbg_backtrace                         false
% 11.50/1.97  --dbg_dump_prop_clauses                 false
% 11.50/1.97  --dbg_dump_prop_clauses_file            -
% 11.50/1.97  --dbg_out_stat                          false
% 11.50/1.97  ------ Parsing...
% 11.50/1.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.50/1.97  
% 11.50/1.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 11.50/1.97  
% 11.50/1.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.50/1.97  
% 11.50/1.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.50/1.97  ------ Proving...
% 11.50/1.97  ------ Problem Properties 
% 11.50/1.97  
% 11.50/1.97  
% 11.50/1.97  clauses                                 44
% 11.50/1.97  conjectures                             11
% 11.50/1.97  EPR                                     9
% 11.50/1.97  Horn                                    44
% 11.50/1.97  unary                                   17
% 11.50/1.97  binary                                  7
% 11.50/1.97  lits                                    122
% 11.50/1.97  lits eq                                 29
% 11.50/1.97  fd_pure                                 0
% 11.50/1.97  fd_pseudo                               0
% 11.50/1.97  fd_cond                                 0
% 11.50/1.97  fd_pseudo_cond                          1
% 11.50/1.97  AC symbols                              0
% 11.50/1.97  
% 11.50/1.97  ------ Schedule dynamic 5 is on 
% 11.50/1.97  
% 11.50/1.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.50/1.97  
% 11.50/1.97  
% 11.50/1.97  ------ 
% 11.50/1.97  Current options:
% 11.50/1.97  ------ 
% 11.50/1.97  
% 11.50/1.97  ------ Input Options
% 11.50/1.97  
% 11.50/1.97  --out_options                           all
% 11.50/1.97  --tptp_safe_out                         true
% 11.50/1.97  --problem_path                          ""
% 11.50/1.97  --include_path                          ""
% 11.50/1.97  --clausifier                            res/vclausify_rel
% 11.50/1.97  --clausifier_options                    ""
% 11.50/1.97  --stdin                                 false
% 11.50/1.97  --stats_out                             all
% 11.50/1.97  
% 11.50/1.97  ------ General Options
% 11.50/1.97  
% 11.50/1.97  --fof                                   false
% 11.50/1.97  --time_out_real                         305.
% 11.50/1.97  --time_out_virtual                      -1.
% 11.50/1.97  --symbol_type_check                     false
% 11.50/1.97  --clausify_out                          false
% 11.50/1.97  --sig_cnt_out                           false
% 11.50/1.97  --trig_cnt_out                          false
% 11.50/1.97  --trig_cnt_out_tolerance                1.
% 11.50/1.97  --trig_cnt_out_sk_spl                   false
% 11.50/1.97  --abstr_cl_out                          false
% 11.50/1.97  
% 11.50/1.97  ------ Global Options
% 11.50/1.97  
% 11.50/1.97  --schedule                              default
% 11.50/1.97  --add_important_lit                     false
% 11.50/1.97  --prop_solver_per_cl                    1000
% 11.50/1.97  --min_unsat_core                        false
% 11.50/1.97  --soft_assumptions                      false
% 11.50/1.97  --soft_lemma_size                       3
% 11.50/1.97  --prop_impl_unit_size                   0
% 11.50/1.97  --prop_impl_unit                        []
% 11.50/1.97  --share_sel_clauses                     true
% 11.50/1.97  --reset_solvers                         false
% 11.50/1.97  --bc_imp_inh                            [conj_cone]
% 11.50/1.97  --conj_cone_tolerance                   3.
% 11.50/1.97  --extra_neg_conj                        none
% 11.50/1.97  --large_theory_mode                     true
% 11.50/1.97  --prolific_symb_bound                   200
% 11.50/1.97  --lt_threshold                          2000
% 11.50/1.97  --clause_weak_htbl                      true
% 11.50/1.97  --gc_record_bc_elim                     false
% 11.50/1.97  
% 11.50/1.97  ------ Preprocessing Options
% 11.50/1.97  
% 11.50/1.97  --preprocessing_flag                    true
% 11.50/1.97  --time_out_prep_mult                    0.1
% 11.50/1.97  --splitting_mode                        input
% 11.50/1.97  --splitting_grd                         true
% 11.50/1.97  --splitting_cvd                         false
% 11.50/1.97  --splitting_cvd_svl                     false
% 11.50/1.97  --splitting_nvd                         32
% 11.50/1.97  --sub_typing                            true
% 11.50/1.97  --prep_gs_sim                           true
% 11.50/1.97  --prep_unflatten                        true
% 11.50/1.97  --prep_res_sim                          true
% 11.50/1.97  --prep_upred                            true
% 11.50/1.97  --prep_sem_filter                       exhaustive
% 11.50/1.97  --prep_sem_filter_out                   false
% 11.50/1.97  --pred_elim                             true
% 11.50/1.97  --res_sim_input                         true
% 11.50/1.97  --eq_ax_congr_red                       true
% 11.50/1.97  --pure_diseq_elim                       true
% 11.50/1.97  --brand_transform                       false
% 11.50/1.97  --non_eq_to_eq                          false
% 11.50/1.97  --prep_def_merge                        true
% 11.50/1.97  --prep_def_merge_prop_impl              false
% 11.50/1.97  --prep_def_merge_mbd                    true
% 11.50/1.97  --prep_def_merge_tr_red                 false
% 11.50/1.97  --prep_def_merge_tr_cl                  false
% 11.50/1.97  --smt_preprocessing                     true
% 11.50/1.97  --smt_ac_axioms                         fast
% 11.50/1.97  --preprocessed_out                      false
% 11.50/1.97  --preprocessed_stats                    false
% 11.50/1.97  
% 11.50/1.97  ------ Abstraction refinement Options
% 11.50/1.97  
% 11.50/1.97  --abstr_ref                             []
% 11.50/1.97  --abstr_ref_prep                        false
% 11.50/1.97  --abstr_ref_until_sat                   false
% 11.50/1.97  --abstr_ref_sig_restrict                funpre
% 11.50/1.97  --abstr_ref_af_restrict_to_split_sk     false
% 11.50/1.97  --abstr_ref_under                       []
% 11.50/1.97  
% 11.50/1.97  ------ SAT Options
% 11.50/1.97  
% 11.50/1.97  --sat_mode                              false
% 11.50/1.97  --sat_fm_restart_options                ""
% 11.50/1.97  --sat_gr_def                            false
% 11.50/1.97  --sat_epr_types                         true
% 11.50/1.97  --sat_non_cyclic_types                  false
% 11.50/1.97  --sat_finite_models                     false
% 11.50/1.97  --sat_fm_lemmas                         false
% 11.50/1.97  --sat_fm_prep                           false
% 11.50/1.97  --sat_fm_uc_incr                        true
% 11.50/1.97  --sat_out_model                         small
% 11.50/1.97  --sat_out_clauses                       false
% 11.50/1.97  
% 11.50/1.97  ------ QBF Options
% 11.50/1.97  
% 11.50/1.97  --qbf_mode                              false
% 11.50/1.97  --qbf_elim_univ                         false
% 11.50/1.97  --qbf_dom_inst                          none
% 11.50/1.97  --qbf_dom_pre_inst                      false
% 11.50/1.97  --qbf_sk_in                             false
% 11.50/1.97  --qbf_pred_elim                         true
% 11.50/1.97  --qbf_split                             512
% 11.50/1.97  
% 11.50/1.97  ------ BMC1 Options
% 11.50/1.97  
% 11.50/1.97  --bmc1_incremental                      false
% 11.50/1.97  --bmc1_axioms                           reachable_all
% 11.50/1.97  --bmc1_min_bound                        0
% 11.50/1.97  --bmc1_max_bound                        -1
% 11.50/1.97  --bmc1_max_bound_default                -1
% 11.50/1.97  --bmc1_symbol_reachability              true
% 11.50/1.97  --bmc1_property_lemmas                  false
% 11.50/1.97  --bmc1_k_induction                      false
% 11.50/1.97  --bmc1_non_equiv_states                 false
% 11.50/1.97  --bmc1_deadlock                         false
% 11.50/1.97  --bmc1_ucm                              false
% 11.50/1.97  --bmc1_add_unsat_core                   none
% 11.50/1.97  --bmc1_unsat_core_children              false
% 11.50/1.97  --bmc1_unsat_core_extrapolate_axioms    false
% 11.50/1.97  --bmc1_out_stat                         full
% 11.50/1.97  --bmc1_ground_init                      false
% 11.50/1.97  --bmc1_pre_inst_next_state              false
% 11.50/1.97  --bmc1_pre_inst_state                   false
% 11.50/1.97  --bmc1_pre_inst_reach_state             false
% 11.50/1.97  --bmc1_out_unsat_core                   false
% 11.50/1.97  --bmc1_aig_witness_out                  false
% 11.50/1.97  --bmc1_verbose                          false
% 11.50/1.97  --bmc1_dump_clauses_tptp                false
% 11.50/1.97  --bmc1_dump_unsat_core_tptp             false
% 11.50/1.97  --bmc1_dump_file                        -
% 11.50/1.97  --bmc1_ucm_expand_uc_limit              128
% 11.50/1.97  --bmc1_ucm_n_expand_iterations          6
% 11.50/1.97  --bmc1_ucm_extend_mode                  1
% 11.50/1.97  --bmc1_ucm_init_mode                    2
% 11.50/1.97  --bmc1_ucm_cone_mode                    none
% 11.50/1.97  --bmc1_ucm_reduced_relation_type        0
% 11.50/1.97  --bmc1_ucm_relax_model                  4
% 11.50/1.97  --bmc1_ucm_full_tr_after_sat            true
% 11.50/1.97  --bmc1_ucm_expand_neg_assumptions       false
% 11.50/1.97  --bmc1_ucm_layered_model                none
% 11.50/1.97  --bmc1_ucm_max_lemma_size               10
% 11.50/1.97  
% 11.50/1.97  ------ AIG Options
% 11.50/1.97  
% 11.50/1.97  --aig_mode                              false
% 11.50/1.97  
% 11.50/1.97  ------ Instantiation Options
% 11.50/1.97  
% 11.50/1.97  --instantiation_flag                    true
% 11.50/1.97  --inst_sos_flag                         true
% 11.50/1.97  --inst_sos_phase                        true
% 11.50/1.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.50/1.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.50/1.97  --inst_lit_sel_side                     none
% 11.50/1.97  --inst_solver_per_active                1400
% 11.50/1.97  --inst_solver_calls_frac                1.
% 11.50/1.97  --inst_passive_queue_type               priority_queues
% 11.50/1.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.50/1.97  --inst_passive_queues_freq              [25;2]
% 11.50/1.97  --inst_dismatching                      true
% 11.50/1.97  --inst_eager_unprocessed_to_passive     true
% 11.50/1.97  --inst_prop_sim_given                   true
% 11.50/1.97  --inst_prop_sim_new                     false
% 11.50/1.97  --inst_subs_new                         false
% 11.50/1.97  --inst_eq_res_simp                      false
% 11.50/1.97  --inst_subs_given                       false
% 11.50/1.97  --inst_orphan_elimination               true
% 11.50/1.97  --inst_learning_loop_flag               true
% 11.50/1.97  --inst_learning_start                   3000
% 11.50/1.97  --inst_learning_factor                  2
% 11.50/1.97  --inst_start_prop_sim_after_learn       3
% 11.50/1.97  --inst_sel_renew                        solver
% 11.50/1.97  --inst_lit_activity_flag                true
% 11.50/1.97  --inst_restr_to_given                   false
% 11.50/1.97  --inst_activity_threshold               500
% 11.50/1.97  --inst_out_proof                        true
% 11.50/1.97  
% 11.50/1.97  ------ Resolution Options
% 11.50/1.97  
% 11.50/1.97  --resolution_flag                       false
% 11.50/1.97  --res_lit_sel                           adaptive
% 11.50/1.97  --res_lit_sel_side                      none
% 11.50/1.97  --res_ordering                          kbo
% 11.50/1.97  --res_to_prop_solver                    active
% 11.50/1.97  --res_prop_simpl_new                    false
% 11.50/1.97  --res_prop_simpl_given                  true
% 11.50/1.97  --res_passive_queue_type                priority_queues
% 11.50/1.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.50/1.97  --res_passive_queues_freq               [15;5]
% 11.50/1.97  --res_forward_subs                      full
% 11.50/1.97  --res_backward_subs                     full
% 11.50/1.97  --res_forward_subs_resolution           true
% 11.50/1.97  --res_backward_subs_resolution          true
% 11.50/1.97  --res_orphan_elimination                true
% 11.50/1.97  --res_time_limit                        2.
% 11.50/1.97  --res_out_proof                         true
% 11.50/1.97  
% 11.50/1.97  ------ Superposition Options
% 11.50/1.97  
% 11.50/1.97  --superposition_flag                    true
% 11.50/1.97  --sup_passive_queue_type                priority_queues
% 11.50/1.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.50/1.97  --sup_passive_queues_freq               [8;1;4]
% 11.50/1.97  --demod_completeness_check              fast
% 11.50/1.97  --demod_use_ground                      true
% 11.50/1.97  --sup_to_prop_solver                    passive
% 11.50/1.97  --sup_prop_simpl_new                    true
% 11.50/1.97  --sup_prop_simpl_given                  true
% 11.50/1.97  --sup_fun_splitting                     true
% 11.50/1.97  --sup_smt_interval                      50000
% 11.50/1.97  
% 11.50/1.97  ------ Superposition Simplification Setup
% 11.50/1.97  
% 11.50/1.97  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.50/1.97  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.50/1.97  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.50/1.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.50/1.97  --sup_full_triv                         [TrivRules;PropSubs]
% 11.50/1.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.50/1.97  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.50/1.97  --sup_immed_triv                        [TrivRules]
% 11.50/1.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.50/1.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.50/1.97  --sup_immed_bw_main                     []
% 11.50/1.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.50/1.97  --sup_input_triv                        [Unflattening;TrivRules]
% 11.50/1.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.50/1.97  --sup_input_bw                          []
% 11.50/1.97  
% 11.50/1.97  ------ Combination Options
% 11.50/1.97  
% 11.50/1.97  --comb_res_mult                         3
% 11.50/1.97  --comb_sup_mult                         2
% 11.50/1.97  --comb_inst_mult                        10
% 11.50/1.97  
% 11.50/1.97  ------ Debug Options
% 11.50/1.97  
% 11.50/1.97  --dbg_backtrace                         false
% 11.50/1.97  --dbg_dump_prop_clauses                 false
% 11.50/1.97  --dbg_dump_prop_clauses_file            -
% 11.50/1.97  --dbg_out_stat                          false
% 11.50/1.97  
% 11.50/1.97  
% 11.50/1.97  
% 11.50/1.97  
% 11.50/1.97  ------ Proving...
% 11.50/1.97  
% 11.50/1.97  
% 11.50/1.97  % SZS status Theorem for theBenchmark.p
% 11.50/1.97  
% 11.50/1.97  % SZS output start CNFRefutation for theBenchmark.p
% 11.50/1.97  
% 11.50/1.97  fof(f26,conjecture,(
% 11.50/1.97    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 11.50/1.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.50/1.97  
% 11.50/1.97  fof(f27,negated_conjecture,(
% 11.50/1.97    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 11.50/1.97    inference(negated_conjecture,[],[f26])).
% 11.50/1.97  
% 11.50/1.97  fof(f61,plain,(
% 11.50/1.97    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 11.50/1.97    inference(ennf_transformation,[],[f27])).
% 11.50/1.97  
% 11.50/1.97  fof(f62,plain,(
% 11.50/1.97    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 11.50/1.97    inference(flattening,[],[f61])).
% 11.50/1.97  
% 11.50/1.97  fof(f68,plain,(
% 11.50/1.97    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 11.50/1.97    introduced(choice_axiom,[])).
% 11.50/1.97  
% 11.50/1.97  fof(f67,plain,(
% 11.50/1.97    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 11.50/1.97    introduced(choice_axiom,[])).
% 11.50/1.97  
% 11.50/1.97  fof(f69,plain,(
% 11.50/1.97    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 11.50/1.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f62,f68,f67])).
% 11.50/1.97  
% 11.50/1.97  fof(f111,plain,(
% 11.50/1.97    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 11.50/1.97    inference(cnf_transformation,[],[f69])).
% 11.50/1.97  
% 11.50/1.97  fof(f17,axiom,(
% 11.50/1.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 11.50/1.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.50/1.97  
% 11.50/1.97  fof(f50,plain,(
% 11.50/1.97    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.50/1.97    inference(ennf_transformation,[],[f17])).
% 11.50/1.97  
% 11.50/1.97  fof(f95,plain,(
% 11.50/1.97    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.50/1.97    inference(cnf_transformation,[],[f50])).
% 11.50/1.97  
% 11.50/1.97  fof(f108,plain,(
% 11.50/1.97    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 11.50/1.97    inference(cnf_transformation,[],[f69])).
% 11.50/1.97  
% 11.50/1.97  fof(f106,plain,(
% 11.50/1.97    v1_funct_1(sK2)),
% 11.50/1.97    inference(cnf_transformation,[],[f69])).
% 11.50/1.97  
% 11.50/1.97  fof(f10,axiom,(
% 11.50/1.97    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 11.50/1.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.50/1.97  
% 11.50/1.97  fof(f38,plain,(
% 11.50/1.97    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.50/1.97    inference(ennf_transformation,[],[f10])).
% 11.50/1.97  
% 11.50/1.97  fof(f39,plain,(
% 11.50/1.97    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.50/1.97    inference(flattening,[],[f38])).
% 11.50/1.97  
% 11.50/1.97  fof(f83,plain,(
% 11.50/1.97    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.50/1.97    inference(cnf_transformation,[],[f39])).
% 11.50/1.97  
% 11.50/1.97  fof(f6,axiom,(
% 11.50/1.97    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2))))),
% 11.50/1.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.50/1.97  
% 11.50/1.97  fof(f34,plain,(
% 11.50/1.97    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 11.50/1.97    inference(ennf_transformation,[],[f6])).
% 11.50/1.97  
% 11.50/1.97  fof(f78,plain,(
% 11.50/1.97    ( ! [X2,X0,X1] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 11.50/1.97    inference(cnf_transformation,[],[f34])).
% 11.50/1.97  
% 11.50/1.97  fof(f114,plain,(
% 11.50/1.97    v2_funct_1(sK2)),
% 11.50/1.97    inference(cnf_transformation,[],[f69])).
% 11.50/1.97  
% 11.50/1.97  fof(f15,axiom,(
% 11.50/1.97    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 11.50/1.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.50/1.97  
% 11.50/1.97  fof(f46,plain,(
% 11.50/1.97    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.50/1.97    inference(ennf_transformation,[],[f15])).
% 11.50/1.97  
% 11.50/1.97  fof(f47,plain,(
% 11.50/1.97    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.50/1.97    inference(flattening,[],[f46])).
% 11.50/1.97  
% 11.50/1.97  fof(f93,plain,(
% 11.50/1.97    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.50/1.97    inference(cnf_transformation,[],[f47])).
% 11.50/1.97  
% 11.50/1.97  fof(f24,axiom,(
% 11.50/1.97    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 11.50/1.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.50/1.97  
% 11.50/1.97  fof(f104,plain,(
% 11.50/1.97    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 11.50/1.97    inference(cnf_transformation,[],[f24])).
% 11.50/1.97  
% 11.50/1.97  fof(f124,plain,(
% 11.50/1.97    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.50/1.97    inference(definition_unfolding,[],[f93,f104])).
% 11.50/1.97  
% 11.50/1.97  fof(f19,axiom,(
% 11.50/1.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 11.50/1.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.50/1.97  
% 11.50/1.97  fof(f52,plain,(
% 11.50/1.97    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.50/1.97    inference(ennf_transformation,[],[f19])).
% 11.50/1.97  
% 11.50/1.97  fof(f97,plain,(
% 11.50/1.97    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.50/1.97    inference(cnf_transformation,[],[f52])).
% 11.50/1.97  
% 11.50/1.97  fof(f112,plain,(
% 11.50/1.97    k2_relset_1(sK0,sK1,sK2) = sK1),
% 11.50/1.97    inference(cnf_transformation,[],[f69])).
% 11.50/1.97  
% 11.50/1.97  fof(f18,axiom,(
% 11.50/1.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 11.50/1.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.50/1.97  
% 11.50/1.97  fof(f28,plain,(
% 11.50/1.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 11.50/1.97    inference(pure_predicate_removal,[],[f18])).
% 11.50/1.97  
% 11.50/1.97  fof(f51,plain,(
% 11.50/1.97    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.50/1.97    inference(ennf_transformation,[],[f28])).
% 11.50/1.97  
% 11.50/1.97  fof(f96,plain,(
% 11.50/1.97    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.50/1.97    inference(cnf_transformation,[],[f51])).
% 11.50/1.97  
% 11.50/1.97  fof(f2,axiom,(
% 11.50/1.97    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 11.50/1.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.50/1.97  
% 11.50/1.97  fof(f29,plain,(
% 11.50/1.97    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 11.50/1.97    inference(ennf_transformation,[],[f2])).
% 11.50/1.97  
% 11.50/1.97  fof(f65,plain,(
% 11.50/1.97    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 11.50/1.97    inference(nnf_transformation,[],[f29])).
% 11.50/1.97  
% 11.50/1.97  fof(f73,plain,(
% 11.50/1.97    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.50/1.97    inference(cnf_transformation,[],[f65])).
% 11.50/1.97  
% 11.50/1.97  fof(f14,axiom,(
% 11.50/1.97    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 11.50/1.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.50/1.97  
% 11.50/1.97  fof(f44,plain,(
% 11.50/1.97    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.50/1.97    inference(ennf_transformation,[],[f14])).
% 11.50/1.97  
% 11.50/1.97  fof(f45,plain,(
% 11.50/1.97    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.50/1.97    inference(flattening,[],[f44])).
% 11.50/1.97  
% 11.50/1.97  fof(f91,plain,(
% 11.50/1.97    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.50/1.97    inference(cnf_transformation,[],[f45])).
% 11.50/1.97  
% 11.50/1.97  fof(f9,axiom,(
% 11.50/1.97    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 11.50/1.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.50/1.97  
% 11.50/1.97  fof(f36,plain,(
% 11.50/1.97    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 11.50/1.98    inference(ennf_transformation,[],[f9])).
% 11.50/1.98  
% 11.50/1.98  fof(f37,plain,(
% 11.50/1.98    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 11.50/1.98    inference(flattening,[],[f36])).
% 11.50/1.98  
% 11.50/1.98  fof(f82,plain,(
% 11.50/1.98    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 11.50/1.98    inference(cnf_transformation,[],[f37])).
% 11.50/1.98  
% 11.50/1.98  fof(f121,plain,(
% 11.50/1.98    ( ! [X0,X1] : (k5_relat_1(X1,k6_partfun1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 11.50/1.98    inference(definition_unfolding,[],[f82,f104])).
% 11.50/1.98  
% 11.50/1.98  fof(f23,axiom,(
% 11.50/1.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 11.50/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.50/1.98  
% 11.50/1.98  fof(f57,plain,(
% 11.50/1.98    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 11.50/1.98    inference(ennf_transformation,[],[f23])).
% 11.50/1.98  
% 11.50/1.98  fof(f58,plain,(
% 11.50/1.98    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 11.50/1.98    inference(flattening,[],[f57])).
% 11.50/1.98  
% 11.50/1.98  fof(f103,plain,(
% 11.50/1.98    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 11.50/1.98    inference(cnf_transformation,[],[f58])).
% 11.50/1.98  
% 11.50/1.98  fof(f109,plain,(
% 11.50/1.98    v1_funct_1(sK3)),
% 11.50/1.98    inference(cnf_transformation,[],[f69])).
% 11.50/1.98  
% 11.50/1.98  fof(f20,axiom,(
% 11.50/1.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 11.50/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.50/1.98  
% 11.50/1.98  fof(f53,plain,(
% 11.50/1.98    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 11.50/1.98    inference(ennf_transformation,[],[f20])).
% 11.50/1.98  
% 11.50/1.98  fof(f54,plain,(
% 11.50/1.98    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.50/1.98    inference(flattening,[],[f53])).
% 11.50/1.98  
% 11.50/1.98  fof(f66,plain,(
% 11.50/1.98    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.50/1.98    inference(nnf_transformation,[],[f54])).
% 11.50/1.98  
% 11.50/1.98  fof(f98,plain,(
% 11.50/1.98    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.50/1.98    inference(cnf_transformation,[],[f66])).
% 11.50/1.98  
% 11.50/1.98  fof(f113,plain,(
% 11.50/1.98    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 11.50/1.98    inference(cnf_transformation,[],[f69])).
% 11.50/1.98  
% 11.50/1.98  fof(f21,axiom,(
% 11.50/1.98    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 11.50/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.50/1.98  
% 11.50/1.98  fof(f100,plain,(
% 11.50/1.98    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 11.50/1.98    inference(cnf_transformation,[],[f21])).
% 11.50/1.98  
% 11.50/1.98  fof(f126,plain,(
% 11.50/1.98    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 11.50/1.98    inference(definition_unfolding,[],[f100,f104])).
% 11.50/1.98  
% 11.50/1.98  fof(f22,axiom,(
% 11.50/1.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 11.50/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.50/1.98  
% 11.50/1.98  fof(f55,plain,(
% 11.50/1.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 11.50/1.98    inference(ennf_transformation,[],[f22])).
% 11.50/1.98  
% 11.50/1.98  fof(f56,plain,(
% 11.50/1.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 11.50/1.98    inference(flattening,[],[f55])).
% 11.50/1.98  
% 11.50/1.98  fof(f102,plain,(
% 11.50/1.98    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 11.50/1.98    inference(cnf_transformation,[],[f56])).
% 11.50/1.98  
% 11.50/1.98  fof(f12,axiom,(
% 11.50/1.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 11.50/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.50/1.98  
% 11.50/1.98  fof(f40,plain,(
% 11.50/1.98    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 11.50/1.98    inference(ennf_transformation,[],[f12])).
% 11.50/1.98  
% 11.50/1.98  fof(f41,plain,(
% 11.50/1.98    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 11.50/1.98    inference(flattening,[],[f40])).
% 11.50/1.98  
% 11.50/1.98  fof(f87,plain,(
% 11.50/1.98    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 11.50/1.98    inference(cnf_transformation,[],[f41])).
% 11.50/1.98  
% 11.50/1.98  fof(f4,axiom,(
% 11.50/1.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 11.50/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.50/1.98  
% 11.50/1.98  fof(f31,plain,(
% 11.50/1.98    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 11.50/1.98    inference(ennf_transformation,[],[f4])).
% 11.50/1.98  
% 11.50/1.98  fof(f76,plain,(
% 11.50/1.98    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 11.50/1.98    inference(cnf_transformation,[],[f31])).
% 11.50/1.98  
% 11.50/1.98  fof(f7,axiom,(
% 11.50/1.98    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 11.50/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.50/1.98  
% 11.50/1.98  fof(f79,plain,(
% 11.50/1.98    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 11.50/1.98    inference(cnf_transformation,[],[f7])).
% 11.50/1.98  
% 11.50/1.98  fof(f119,plain,(
% 11.50/1.98    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 11.50/1.98    inference(definition_unfolding,[],[f79,f104])).
% 11.50/1.98  
% 11.50/1.98  fof(f5,axiom,(
% 11.50/1.98    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 11.50/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.50/1.98  
% 11.50/1.98  fof(f32,plain,(
% 11.50/1.98    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 11.50/1.98    inference(ennf_transformation,[],[f5])).
% 11.50/1.98  
% 11.50/1.98  fof(f33,plain,(
% 11.50/1.98    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 11.50/1.98    inference(flattening,[],[f32])).
% 11.50/1.98  
% 11.50/1.98  fof(f77,plain,(
% 11.50/1.98    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.50/1.98    inference(cnf_transformation,[],[f33])).
% 11.50/1.98  
% 11.50/1.98  fof(f3,axiom,(
% 11.50/1.98    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 11.50/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.50/1.98  
% 11.50/1.98  fof(f30,plain,(
% 11.50/1.98    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 11.50/1.98    inference(ennf_transformation,[],[f3])).
% 11.50/1.98  
% 11.50/1.98  fof(f75,plain,(
% 11.50/1.98    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.50/1.98    inference(cnf_transformation,[],[f30])).
% 11.50/1.98  
% 11.50/1.98  fof(f8,axiom,(
% 11.50/1.98    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 11.50/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.50/1.98  
% 11.50/1.98  fof(f35,plain,(
% 11.50/1.98    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 11.50/1.98    inference(ennf_transformation,[],[f8])).
% 11.50/1.98  
% 11.50/1.98  fof(f81,plain,(
% 11.50/1.98    ( ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 11.50/1.98    inference(cnf_transformation,[],[f35])).
% 11.50/1.98  
% 11.50/1.98  fof(f120,plain,(
% 11.50/1.98    ( ! [X0] : (k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 11.50/1.98    inference(definition_unfolding,[],[f81,f104])).
% 11.50/1.98  
% 11.50/1.98  fof(f117,plain,(
% 11.50/1.98    k2_funct_1(sK2) != sK3),
% 11.50/1.98    inference(cnf_transformation,[],[f69])).
% 11.50/1.98  
% 11.50/1.98  cnf(c_41,negated_conjecture,
% 11.50/1.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 11.50/1.98      inference(cnf_transformation,[],[f111]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_1524,plain,
% 11.50/1.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 11.50/1.98      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_25,plain,
% 11.50/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.50/1.98      | v1_relat_1(X0) ),
% 11.50/1.98      inference(cnf_transformation,[],[f95]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_1531,plain,
% 11.50/1.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.50/1.98      | v1_relat_1(X0) = iProver_top ),
% 11.50/1.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_2419,plain,
% 11.50/1.98      ( v1_relat_1(sK3) = iProver_top ),
% 11.50/1.98      inference(superposition,[status(thm)],[c_1524,c_1531]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_44,negated_conjecture,
% 11.50/1.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 11.50/1.98      inference(cnf_transformation,[],[f108]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_1521,plain,
% 11.50/1.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 11.50/1.98      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_2420,plain,
% 11.50/1.98      ( v1_relat_1(sK2) = iProver_top ),
% 11.50/1.98      inference(superposition,[status(thm)],[c_1521,c_1531]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_46,negated_conjecture,
% 11.50/1.98      ( v1_funct_1(sK2) ),
% 11.50/1.98      inference(cnf_transformation,[],[f106]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_1519,plain,
% 11.50/1.98      ( v1_funct_1(sK2) = iProver_top ),
% 11.50/1.98      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_14,plain,
% 11.50/1.98      ( ~ v1_funct_1(X0)
% 11.50/1.98      | ~ v1_relat_1(X0)
% 11.50/1.98      | v1_relat_1(k2_funct_1(X0)) ),
% 11.50/1.98      inference(cnf_transformation,[],[f83]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_1542,plain,
% 11.50/1.98      ( v1_funct_1(X0) != iProver_top
% 11.50/1.98      | v1_relat_1(X0) != iProver_top
% 11.50/1.98      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 11.50/1.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_8,plain,
% 11.50/1.98      ( ~ v1_relat_1(X0)
% 11.50/1.98      | ~ v1_relat_1(X1)
% 11.50/1.98      | ~ v1_relat_1(X2)
% 11.50/1.98      | k5_relat_1(k5_relat_1(X1,X0),X2) = k5_relat_1(X1,k5_relat_1(X0,X2)) ),
% 11.50/1.98      inference(cnf_transformation,[],[f78]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_1546,plain,
% 11.50/1.98      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
% 11.50/1.98      | v1_relat_1(X1) != iProver_top
% 11.50/1.98      | v1_relat_1(X0) != iProver_top
% 11.50/1.98      | v1_relat_1(X2) != iProver_top ),
% 11.50/1.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_7868,plain,
% 11.50/1.98      ( k5_relat_1(k2_funct_1(X0),k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(k2_funct_1(X0),X1),X2)
% 11.50/1.98      | v1_funct_1(X0) != iProver_top
% 11.50/1.98      | v1_relat_1(X0) != iProver_top
% 11.50/1.98      | v1_relat_1(X1) != iProver_top
% 11.50/1.98      | v1_relat_1(X2) != iProver_top ),
% 11.50/1.98      inference(superposition,[status(thm)],[c_1542,c_1546]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_32453,plain,
% 11.50/1.98      ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1))
% 11.50/1.98      | v1_relat_1(X0) != iProver_top
% 11.50/1.98      | v1_relat_1(X1) != iProver_top
% 11.50/1.98      | v1_relat_1(sK2) != iProver_top ),
% 11.50/1.98      inference(superposition,[status(thm)],[c_1519,c_7868]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_33301,plain,
% 11.50/1.98      ( v1_relat_1(X1) != iProver_top
% 11.50/1.98      | v1_relat_1(X0) != iProver_top
% 11.50/1.98      | k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1)) ),
% 11.50/1.98      inference(global_propositional_subsumption,
% 11.50/1.98                [status(thm)],
% 11.50/1.98                [c_32453,c_2420]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_33302,plain,
% 11.50/1.98      ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1))
% 11.50/1.98      | v1_relat_1(X0) != iProver_top
% 11.50/1.98      | v1_relat_1(X1) != iProver_top ),
% 11.50/1.98      inference(renaming,[status(thm)],[c_33301]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_33310,plain,
% 11.50/1.98      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),X0)
% 11.50/1.98      | v1_relat_1(X0) != iProver_top ),
% 11.50/1.98      inference(superposition,[status(thm)],[c_2420,c_33302]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_38,negated_conjecture,
% 11.50/1.98      ( v2_funct_1(sK2) ),
% 11.50/1.98      inference(cnf_transformation,[],[f114]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_1525,plain,
% 11.50/1.98      ( v2_funct_1(sK2) = iProver_top ),
% 11.50/1.98      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_22,plain,
% 11.50/1.98      ( ~ v2_funct_1(X0)
% 11.50/1.98      | ~ v1_funct_1(X0)
% 11.50/1.98      | ~ v1_relat_1(X0)
% 11.50/1.98      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
% 11.50/1.98      inference(cnf_transformation,[],[f124]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_1534,plain,
% 11.50/1.98      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
% 11.50/1.98      | v2_funct_1(X0) != iProver_top
% 11.50/1.98      | v1_funct_1(X0) != iProver_top
% 11.50/1.98      | v1_relat_1(X0) != iProver_top ),
% 11.50/1.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_6855,plain,
% 11.50/1.98      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
% 11.50/1.98      | v1_funct_1(sK2) != iProver_top
% 11.50/1.98      | v1_relat_1(sK2) != iProver_top ),
% 11.50/1.98      inference(superposition,[status(thm)],[c_1525,c_1534]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_27,plain,
% 11.50/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.50/1.98      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 11.50/1.98      inference(cnf_transformation,[],[f97]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_1530,plain,
% 11.50/1.98      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 11.50/1.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 11.50/1.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_3325,plain,
% 11.50/1.98      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 11.50/1.98      inference(superposition,[status(thm)],[c_1521,c_1530]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_40,negated_conjecture,
% 11.50/1.98      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 11.50/1.98      inference(cnf_transformation,[],[f112]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_3326,plain,
% 11.50/1.98      ( k2_relat_1(sK2) = sK1 ),
% 11.50/1.98      inference(light_normalisation,[status(thm)],[c_3325,c_40]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_6856,plain,
% 11.50/1.98      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 11.50/1.98      | v1_funct_1(sK2) != iProver_top
% 11.50/1.98      | v1_relat_1(sK2) != iProver_top ),
% 11.50/1.98      inference(light_normalisation,[status(thm)],[c_6855,c_3326]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_47,plain,
% 11.50/1.98      ( v1_funct_1(sK2) = iProver_top ),
% 11.50/1.98      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_7480,plain,
% 11.50/1.98      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
% 11.50/1.98      inference(global_propositional_subsumption,
% 11.50/1.98                [status(thm)],
% 11.50/1.98                [c_6856,c_47,c_2420]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_33315,plain,
% 11.50/1.98      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k6_partfun1(sK1),X0)
% 11.50/1.98      | v1_relat_1(X0) != iProver_top ),
% 11.50/1.98      inference(light_normalisation,[status(thm)],[c_33310,c_7480]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_35531,plain,
% 11.50/1.98      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
% 11.50/1.98      inference(superposition,[status(thm)],[c_2419,c_33315]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_26,plain,
% 11.50/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.50/1.98      | v4_relat_1(X0,X1) ),
% 11.50/1.98      inference(cnf_transformation,[],[f96]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_4,plain,
% 11.50/1.98      ( ~ v4_relat_1(X0,X1)
% 11.50/1.98      | r1_tarski(k1_relat_1(X0),X1)
% 11.50/1.98      | ~ v1_relat_1(X0) ),
% 11.50/1.98      inference(cnf_transformation,[],[f73]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_479,plain,
% 11.50/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.50/1.98      | r1_tarski(k1_relat_1(X0),X1)
% 11.50/1.98      | ~ v1_relat_1(X0) ),
% 11.50/1.98      inference(resolution,[status(thm)],[c_26,c_4]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_483,plain,
% 11.50/1.98      ( r1_tarski(k1_relat_1(X0),X1)
% 11.50/1.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 11.50/1.98      inference(global_propositional_subsumption,
% 11.50/1.98                [status(thm)],
% 11.50/1.98                [c_479,c_25]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_484,plain,
% 11.50/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.50/1.98      | r1_tarski(k1_relat_1(X0),X1) ),
% 11.50/1.98      inference(renaming,[status(thm)],[c_483]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_1517,plain,
% 11.50/1.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.50/1.98      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 11.50/1.98      inference(predicate_to_equality,[status(thm)],[c_484]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_3318,plain,
% 11.50/1.98      ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
% 11.50/1.98      inference(superposition,[status(thm)],[c_1521,c_1517]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_20,plain,
% 11.50/1.98      ( ~ v2_funct_1(X0)
% 11.50/1.98      | ~ v1_funct_1(X0)
% 11.50/1.98      | ~ v1_relat_1(X0)
% 11.50/1.98      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 11.50/1.98      inference(cnf_transformation,[],[f91]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_1536,plain,
% 11.50/1.98      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 11.50/1.98      | v2_funct_1(X0) != iProver_top
% 11.50/1.98      | v1_funct_1(X0) != iProver_top
% 11.50/1.98      | v1_relat_1(X0) != iProver_top ),
% 11.50/1.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_7386,plain,
% 11.50/1.98      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 11.50/1.98      | v1_funct_1(sK2) != iProver_top
% 11.50/1.98      | v1_relat_1(sK2) != iProver_top ),
% 11.50/1.98      inference(superposition,[status(thm)],[c_1525,c_1536]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_7453,plain,
% 11.50/1.98      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 11.50/1.98      inference(global_propositional_subsumption,
% 11.50/1.98                [status(thm)],
% 11.50/1.98                [c_7386,c_47,c_2420]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_12,plain,
% 11.50/1.98      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 11.50/1.98      | ~ v1_relat_1(X0)
% 11.50/1.98      | k5_relat_1(X0,k6_partfun1(X1)) = X0 ),
% 11.50/1.98      inference(cnf_transformation,[],[f121]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_1544,plain,
% 11.50/1.98      ( k5_relat_1(X0,k6_partfun1(X1)) = X0
% 11.50/1.98      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 11.50/1.98      | v1_relat_1(X0) != iProver_top ),
% 11.50/1.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_7456,plain,
% 11.50/1.98      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0)) = k2_funct_1(sK2)
% 11.50/1.98      | r1_tarski(k1_relat_1(sK2),X0) != iProver_top
% 11.50/1.98      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 11.50/1.98      inference(superposition,[status(thm)],[c_7453,c_1544]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_6817,plain,
% 11.50/1.98      ( ~ v1_funct_1(sK2)
% 11.50/1.98      | v1_relat_1(k2_funct_1(sK2))
% 11.50/1.98      | ~ v1_relat_1(sK2) ),
% 11.50/1.98      inference(instantiation,[status(thm)],[c_14]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_6818,plain,
% 11.50/1.98      ( v1_funct_1(sK2) != iProver_top
% 11.50/1.98      | v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 11.50/1.98      | v1_relat_1(sK2) != iProver_top ),
% 11.50/1.98      inference(predicate_to_equality,[status(thm)],[c_6817]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_7517,plain,
% 11.50/1.98      ( r1_tarski(k1_relat_1(sK2),X0) != iProver_top
% 11.50/1.98      | k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0)) = k2_funct_1(sK2) ),
% 11.50/1.98      inference(global_propositional_subsumption,
% 11.50/1.98                [status(thm)],
% 11.50/1.98                [c_7456,c_47,c_2420,c_6818]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_7518,plain,
% 11.50/1.98      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0)) = k2_funct_1(sK2)
% 11.50/1.98      | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
% 11.50/1.98      inference(renaming,[status(thm)],[c_7517]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_7524,plain,
% 11.50/1.98      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k2_funct_1(sK2) ),
% 11.50/1.98      inference(superposition,[status(thm)],[c_3318,c_7518]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_33,plain,
% 11.50/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.50/1.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 11.50/1.98      | ~ v1_funct_1(X0)
% 11.50/1.98      | ~ v1_funct_1(X3)
% 11.50/1.98      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 11.50/1.98      inference(cnf_transformation,[],[f103]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_1526,plain,
% 11.50/1.98      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 11.50/1.98      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 11.50/1.98      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.50/1.98      | v1_funct_1(X4) != iProver_top
% 11.50/1.98      | v1_funct_1(X5) != iProver_top ),
% 11.50/1.98      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_8216,plain,
% 11.50/1.98      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 11.50/1.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.50/1.98      | v1_funct_1(X2) != iProver_top
% 11.50/1.98      | v1_funct_1(sK3) != iProver_top ),
% 11.50/1.98      inference(superposition,[status(thm)],[c_1524,c_1526]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_43,negated_conjecture,
% 11.50/1.98      ( v1_funct_1(sK3) ),
% 11.50/1.98      inference(cnf_transformation,[],[f109]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_50,plain,
% 11.50/1.98      ( v1_funct_1(sK3) = iProver_top ),
% 11.50/1.98      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_8324,plain,
% 11.50/1.98      ( v1_funct_1(X2) != iProver_top
% 11.50/1.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.50/1.98      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 11.50/1.98      inference(global_propositional_subsumption,
% 11.50/1.98                [status(thm)],
% 11.50/1.98                [c_8216,c_50]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_8325,plain,
% 11.50/1.98      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 11.50/1.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.50/1.98      | v1_funct_1(X2) != iProver_top ),
% 11.50/1.98      inference(renaming,[status(thm)],[c_8324]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_8333,plain,
% 11.50/1.98      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 11.50/1.98      | v1_funct_1(sK2) != iProver_top ),
% 11.50/1.98      inference(superposition,[status(thm)],[c_1521,c_8325]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_29,plain,
% 11.50/1.98      ( ~ r2_relset_1(X0,X1,X2,X3)
% 11.50/1.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.50/1.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.50/1.98      | X3 = X2 ),
% 11.50/1.98      inference(cnf_transformation,[],[f98]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_39,negated_conjecture,
% 11.50/1.98      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 11.50/1.98      inference(cnf_transformation,[],[f113]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_558,plain,
% 11.50/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.50/1.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.50/1.98      | X3 = X0
% 11.50/1.98      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 11.50/1.98      | k6_partfun1(sK0) != X3
% 11.50/1.98      | sK0 != X2
% 11.50/1.98      | sK0 != X1 ),
% 11.50/1.98      inference(resolution_lifted,[status(thm)],[c_29,c_39]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_559,plain,
% 11.50/1.98      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.50/1.98      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.50/1.98      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 11.50/1.98      inference(unflattening,[status(thm)],[c_558]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_30,plain,
% 11.50/1.98      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 11.50/1.98      inference(cnf_transformation,[],[f126]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_68,plain,
% 11.50/1.98      ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 11.50/1.98      inference(instantiation,[status(thm)],[c_30]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_561,plain,
% 11.50/1.98      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.50/1.98      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 11.50/1.98      inference(global_propositional_subsumption,
% 11.50/1.98                [status(thm)],
% 11.50/1.98                [c_559,c_68]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_1514,plain,
% 11.50/1.98      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 11.50/1.98      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 11.50/1.98      inference(predicate_to_equality,[status(thm)],[c_561]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_31,plain,
% 11.50/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.50/1.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 11.50/1.98      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 11.50/1.98      | ~ v1_funct_1(X0)
% 11.50/1.98      | ~ v1_funct_1(X3) ),
% 11.50/1.98      inference(cnf_transformation,[],[f102]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_1611,plain,
% 11.50/1.98      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.50/1.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 11.50/1.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 11.50/1.98      | ~ v1_funct_1(sK3)
% 11.50/1.98      | ~ v1_funct_1(sK2) ),
% 11.50/1.98      inference(instantiation,[status(thm)],[c_31]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_2259,plain,
% 11.50/1.98      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 11.50/1.98      inference(global_propositional_subsumption,
% 11.50/1.98                [status(thm)],
% 11.50/1.98                [c_1514,c_46,c_44,c_43,c_41,c_68,c_559,c_1611]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_8334,plain,
% 11.50/1.98      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 11.50/1.98      | v1_funct_1(sK2) != iProver_top ),
% 11.50/1.98      inference(light_normalisation,[status(thm)],[c_8333,c_2259]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_8458,plain,
% 11.50/1.98      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 11.50/1.98      inference(global_propositional_subsumption,
% 11.50/1.98                [status(thm)],
% 11.50/1.98                [c_8334,c_47]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_3317,plain,
% 11.50/1.98      ( r1_tarski(k1_relat_1(sK3),sK1) = iProver_top ),
% 11.50/1.98      inference(superposition,[status(thm)],[c_1524,c_1517]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_17,plain,
% 11.50/1.98      ( ~ r1_tarski(X0,k2_relat_1(X1))
% 11.50/1.98      | ~ v1_funct_1(X1)
% 11.50/1.98      | ~ v1_relat_1(X1)
% 11.50/1.98      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
% 11.50/1.98      inference(cnf_transformation,[],[f87]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_1539,plain,
% 11.50/1.98      ( k9_relat_1(X0,k10_relat_1(X0,X1)) = X1
% 11.50/1.98      | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
% 11.50/1.98      | v1_funct_1(X0) != iProver_top
% 11.50/1.98      | v1_relat_1(X0) != iProver_top ),
% 11.50/1.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_7427,plain,
% 11.50/1.98      ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
% 11.50/1.98      | r1_tarski(X0,sK1) != iProver_top
% 11.50/1.98      | v1_funct_1(sK2) != iProver_top
% 11.50/1.98      | v1_relat_1(sK2) != iProver_top ),
% 11.50/1.98      inference(superposition,[status(thm)],[c_3326,c_1539]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_7483,plain,
% 11.50/1.98      ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
% 11.50/1.98      | r1_tarski(X0,sK1) != iProver_top ),
% 11.50/1.98      inference(global_propositional_subsumption,
% 11.50/1.98                [status(thm)],
% 11.50/1.98                [c_7427,c_47,c_2420]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_7490,plain,
% 11.50/1.98      ( k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(sK3))) = k1_relat_1(sK3) ),
% 11.50/1.98      inference(superposition,[status(thm)],[c_3317,c_7483]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_6,plain,
% 11.50/1.98      ( ~ v1_relat_1(X0)
% 11.50/1.98      | ~ v1_relat_1(X1)
% 11.50/1.98      | k10_relat_1(X1,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(X1,X0)) ),
% 11.50/1.98      inference(cnf_transformation,[],[f76]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_1547,plain,
% 11.50/1.98      ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
% 11.50/1.98      | v1_relat_1(X1) != iProver_top
% 11.50/1.98      | v1_relat_1(X0) != iProver_top ),
% 11.50/1.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_4841,plain,
% 11.50/1.98      ( k10_relat_1(sK2,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(sK2,X0))
% 11.50/1.98      | v1_relat_1(X0) != iProver_top ),
% 11.50/1.98      inference(superposition,[status(thm)],[c_2420,c_1547]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_5440,plain,
% 11.50/1.98      ( k10_relat_1(sK2,k1_relat_1(sK3)) = k1_relat_1(k5_relat_1(sK2,sK3)) ),
% 11.50/1.98      inference(superposition,[status(thm)],[c_2419,c_4841]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_7491,plain,
% 11.50/1.98      ( k9_relat_1(sK2,k1_relat_1(k5_relat_1(sK2,sK3))) = k1_relat_1(sK3) ),
% 11.50/1.98      inference(light_normalisation,[status(thm)],[c_7490,c_5440]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_19933,plain,
% 11.50/1.98      ( k9_relat_1(sK2,k1_relat_1(k6_partfun1(sK0))) = k1_relat_1(sK3) ),
% 11.50/1.98      inference(light_normalisation,[status(thm)],[c_7491,c_7491,c_8458]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_10,plain,
% 11.50/1.98      ( k1_relat_1(k6_partfun1(X0)) = X0 ),
% 11.50/1.98      inference(cnf_transformation,[],[f119]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_7,plain,
% 11.50/1.98      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 11.50/1.98      inference(cnf_transformation,[],[f77]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_462,plain,
% 11.50/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.50/1.98      | ~ v1_relat_1(X0)
% 11.50/1.98      | k7_relat_1(X0,X1) = X0 ),
% 11.50/1.98      inference(resolution,[status(thm)],[c_26,c_7]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_466,plain,
% 11.50/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.50/1.98      | k7_relat_1(X0,X1) = X0 ),
% 11.50/1.98      inference(global_propositional_subsumption,
% 11.50/1.98                [status(thm)],
% 11.50/1.98                [c_462,c_26,c_25,c_7]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_1518,plain,
% 11.50/1.98      ( k7_relat_1(X0,X1) = X0
% 11.50/1.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 11.50/1.98      inference(predicate_to_equality,[status(thm)],[c_466]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_3113,plain,
% 11.50/1.98      ( k7_relat_1(sK2,sK0) = sK2 ),
% 11.50/1.98      inference(superposition,[status(thm)],[c_1521,c_1518]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_5,plain,
% 11.50/1.98      ( ~ v1_relat_1(X0)
% 11.50/1.98      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 11.50/1.98      inference(cnf_transformation,[],[f75]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_1548,plain,
% 11.50/1.98      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 11.50/1.98      | v1_relat_1(X0) != iProver_top ),
% 11.50/1.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_2629,plain,
% 11.50/1.98      ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
% 11.50/1.98      inference(superposition,[status(thm)],[c_2420,c_1548]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_3639,plain,
% 11.50/1.98      ( k9_relat_1(sK2,sK0) = k2_relat_1(sK2) ),
% 11.50/1.98      inference(superposition,[status(thm)],[c_3113,c_2629]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_3640,plain,
% 11.50/1.98      ( k9_relat_1(sK2,sK0) = sK1 ),
% 11.50/1.98      inference(light_normalisation,[status(thm)],[c_3639,c_3326]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_19934,plain,
% 11.50/1.98      ( k1_relat_1(sK3) = sK1 ),
% 11.50/1.98      inference(demodulation,[status(thm)],[c_19933,c_10,c_3640]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_11,plain,
% 11.50/1.98      ( ~ v1_relat_1(X0)
% 11.50/1.98      | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 ),
% 11.50/1.98      inference(cnf_transformation,[],[f120]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_1545,plain,
% 11.50/1.98      ( k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0
% 11.50/1.98      | v1_relat_1(X0) != iProver_top ),
% 11.50/1.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_2626,plain,
% 11.50/1.98      ( k5_relat_1(k6_partfun1(k1_relat_1(sK3)),sK3) = sK3 ),
% 11.50/1.98      inference(superposition,[status(thm)],[c_2419,c_1545]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_19950,plain,
% 11.50/1.98      ( k5_relat_1(k6_partfun1(sK1),sK3) = sK3 ),
% 11.50/1.98      inference(demodulation,[status(thm)],[c_19934,c_2626]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_35539,plain,
% 11.50/1.98      ( k2_funct_1(sK2) = sK3 ),
% 11.50/1.98      inference(light_normalisation,
% 11.50/1.98                [status(thm)],
% 11.50/1.98                [c_35531,c_7524,c_8458,c_19950]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(c_35,negated_conjecture,
% 11.50/1.98      ( k2_funct_1(sK2) != sK3 ),
% 11.50/1.98      inference(cnf_transformation,[],[f117]) ).
% 11.50/1.98  
% 11.50/1.98  cnf(contradiction,plain,
% 11.50/1.98      ( $false ),
% 11.50/1.98      inference(minisat,[status(thm)],[c_35539,c_35]) ).
% 11.50/1.98  
% 11.50/1.98  
% 11.50/1.98  % SZS output end CNFRefutation for theBenchmark.p
% 11.50/1.98  
% 11.50/1.98  ------                               Statistics
% 11.50/1.98  
% 11.50/1.98  ------ General
% 11.50/1.98  
% 11.50/1.98  abstr_ref_over_cycles:                  0
% 11.50/1.98  abstr_ref_under_cycles:                 0
% 11.50/1.98  gc_basic_clause_elim:                   0
% 11.50/1.98  forced_gc_time:                         0
% 11.50/1.98  parsing_time:                           0.01
% 11.50/1.98  unif_index_cands_time:                  0.
% 11.50/1.98  unif_index_add_time:                    0.
% 11.50/1.98  orderings_time:                         0.
% 11.50/1.98  out_proof_time:                         0.017
% 11.50/1.98  total_time:                             1.315
% 11.50/1.98  num_of_symbols:                         56
% 11.50/1.98  num_of_terms:                           54913
% 11.50/1.98  
% 11.50/1.98  ------ Preprocessing
% 11.50/1.98  
% 11.50/1.98  num_of_splits:                          0
% 11.50/1.98  num_of_split_atoms:                     0
% 11.50/1.98  num_of_reused_defs:                     0
% 11.50/1.98  num_eq_ax_congr_red:                    14
% 11.50/1.98  num_of_sem_filtered_clauses:            1
% 11.50/1.98  num_of_subtypes:                        0
% 11.50/1.98  monotx_restored_types:                  0
% 11.50/1.98  sat_num_of_epr_types:                   0
% 11.50/1.98  sat_num_of_non_cyclic_types:            0
% 11.50/1.98  sat_guarded_non_collapsed_types:        0
% 11.50/1.98  num_pure_diseq_elim:                    0
% 11.50/1.98  simp_replaced_by:                       0
% 11.50/1.98  res_preprocessed:                       217
% 11.50/1.98  prep_upred:                             0
% 11.50/1.98  prep_unflattend:                        12
% 11.50/1.98  smt_new_axioms:                         0
% 11.50/1.98  pred_elim_cands:                        6
% 11.50/1.98  pred_elim:                              2
% 11.50/1.98  pred_elim_cl:                           2
% 11.50/1.98  pred_elim_cycles:                       4
% 11.50/1.98  merged_defs:                            0
% 11.50/1.98  merged_defs_ncl:                        0
% 11.50/1.98  bin_hyper_res:                          0
% 11.50/1.98  prep_cycles:                            4
% 11.50/1.98  pred_elim_time:                         0.006
% 11.50/1.98  splitting_time:                         0.
% 11.50/1.98  sem_filter_time:                        0.
% 11.50/1.98  monotx_time:                            0.001
% 11.50/1.98  subtype_inf_time:                       0.
% 11.50/1.98  
% 11.50/1.98  ------ Problem properties
% 11.50/1.98  
% 11.50/1.98  clauses:                                44
% 11.50/1.98  conjectures:                            11
% 11.50/1.98  epr:                                    9
% 11.50/1.98  horn:                                   44
% 11.50/1.98  ground:                                 12
% 11.50/1.98  unary:                                  17
% 11.50/1.98  binary:                                 7
% 11.50/1.98  lits:                                   122
% 11.50/1.98  lits_eq:                                29
% 11.50/1.98  fd_pure:                                0
% 11.50/1.98  fd_pseudo:                              0
% 11.50/1.98  fd_cond:                                0
% 11.50/1.98  fd_pseudo_cond:                         1
% 11.50/1.98  ac_symbols:                             0
% 11.50/1.98  
% 11.50/1.98  ------ Propositional Solver
% 11.50/1.98  
% 11.50/1.98  prop_solver_calls:                      34
% 11.50/1.98  prop_fast_solver_calls:                 2959
% 11.50/1.98  smt_solver_calls:                       0
% 11.50/1.98  smt_fast_solver_calls:                  0
% 11.50/1.98  prop_num_of_clauses:                    21146
% 11.50/1.98  prop_preprocess_simplified:             31815
% 11.50/1.98  prop_fo_subsumed:                       258
% 11.50/1.98  prop_solver_time:                       0.
% 11.50/1.98  smt_solver_time:                        0.
% 11.50/1.98  smt_fast_solver_time:                   0.
% 11.50/1.98  prop_fast_solver_time:                  0.
% 11.50/1.98  prop_unsat_core_time:                   0.002
% 11.50/1.98  
% 11.50/1.98  ------ QBF
% 11.50/1.98  
% 11.50/1.98  qbf_q_res:                              0
% 11.50/1.98  qbf_num_tautologies:                    0
% 11.50/1.98  qbf_prep_cycles:                        0
% 11.50/1.98  
% 11.50/1.98  ------ BMC1
% 11.50/1.98  
% 11.50/1.98  bmc1_current_bound:                     -1
% 11.50/1.98  bmc1_last_solved_bound:                 -1
% 11.50/1.98  bmc1_unsat_core_size:                   -1
% 11.50/1.98  bmc1_unsat_core_parents_size:           -1
% 11.50/1.98  bmc1_merge_next_fun:                    0
% 11.50/1.98  bmc1_unsat_core_clauses_time:           0.
% 11.50/1.98  
% 11.50/1.98  ------ Instantiation
% 11.50/1.98  
% 11.50/1.98  inst_num_of_clauses:                    5313
% 11.50/1.98  inst_num_in_passive:                    1627
% 11.50/1.98  inst_num_in_active:                     2453
% 11.50/1.98  inst_num_in_unprocessed:                1233
% 11.50/1.98  inst_num_of_loops:                      2660
% 11.50/1.98  inst_num_of_learning_restarts:          0
% 11.50/1.98  inst_num_moves_active_passive:          203
% 11.50/1.98  inst_lit_activity:                      0
% 11.50/1.98  inst_lit_activity_moves:                1
% 11.50/1.98  inst_num_tautologies:                   0
% 11.50/1.98  inst_num_prop_implied:                  0
% 11.50/1.98  inst_num_existing_simplified:           0
% 11.50/1.98  inst_num_eq_res_simplified:             0
% 11.50/1.98  inst_num_child_elim:                    0
% 11.50/1.98  inst_num_of_dismatching_blockings:      1554
% 11.50/1.98  inst_num_of_non_proper_insts:           5674
% 11.50/1.98  inst_num_of_duplicates:                 0
% 11.50/1.98  inst_inst_num_from_inst_to_res:         0
% 11.50/1.98  inst_dismatching_checking_time:         0.
% 11.50/1.98  
% 11.50/1.98  ------ Resolution
% 11.50/1.98  
% 11.50/1.98  res_num_of_clauses:                     0
% 11.50/1.98  res_num_in_passive:                     0
% 11.50/1.98  res_num_in_active:                      0
% 11.50/1.98  res_num_of_loops:                       221
% 11.50/1.98  res_forward_subset_subsumed:            226
% 11.50/1.98  res_backward_subset_subsumed:           0
% 11.50/1.98  res_forward_subsumed:                   0
% 11.50/1.98  res_backward_subsumed:                  0
% 11.50/1.98  res_forward_subsumption_resolution:     1
% 11.50/1.98  res_backward_subsumption_resolution:    0
% 11.50/1.98  res_clause_to_clause_subsumption:       3034
% 11.50/1.98  res_orphan_elimination:                 0
% 11.50/1.98  res_tautology_del:                      187
% 11.50/1.98  res_num_eq_res_simplified:              1
% 11.50/1.98  res_num_sel_changes:                    0
% 11.50/1.98  res_moves_from_active_to_pass:          0
% 11.50/1.98  
% 11.50/1.98  ------ Superposition
% 11.50/1.98  
% 11.50/1.98  sup_time_total:                         0.
% 11.50/1.98  sup_time_generating:                    0.
% 11.50/1.98  sup_time_sim_full:                      0.
% 11.50/1.98  sup_time_sim_immed:                     0.
% 11.50/1.98  
% 11.50/1.98  sup_num_of_clauses:                     1452
% 11.50/1.98  sup_num_in_active:                      441
% 11.50/1.98  sup_num_in_passive:                     1011
% 11.50/1.98  sup_num_of_loops:                       531
% 11.50/1.98  sup_fw_superposition:                   1158
% 11.50/1.98  sup_bw_superposition:                   566
% 11.50/1.98  sup_immediate_simplified:               463
% 11.50/1.98  sup_given_eliminated:                   1
% 11.50/1.98  comparisons_done:                       0
% 11.50/1.98  comparisons_avoided:                    0
% 11.50/1.98  
% 11.50/1.98  ------ Simplifications
% 11.50/1.98  
% 11.50/1.98  
% 11.50/1.98  sim_fw_subset_subsumed:                 39
% 11.50/1.98  sim_bw_subset_subsumed:                 39
% 11.50/1.98  sim_fw_subsumed:                        50
% 11.50/1.98  sim_bw_subsumed:                        5
% 11.50/1.98  sim_fw_subsumption_res:                 0
% 11.50/1.98  sim_bw_subsumption_res:                 0
% 11.50/1.98  sim_tautology_del:                      4
% 11.50/1.98  sim_eq_tautology_del:                   112
% 11.50/1.98  sim_eq_res_simp:                        4
% 11.50/1.98  sim_fw_demodulated:                     44
% 11.50/1.98  sim_bw_demodulated:                     78
% 11.50/1.98  sim_light_normalised:                   399
% 11.50/1.98  sim_joinable_taut:                      0
% 11.50/1.98  sim_joinable_simp:                      0
% 11.50/1.98  sim_ac_normalised:                      0
% 11.50/1.98  sim_smt_subsumption:                    0
% 11.50/1.98  
%------------------------------------------------------------------------------
