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
% DateTime   : Thu Dec  3 12:03:01 EST 2020

% Result     : Theorem 11.24s
% Output     : CNFRefutation 11.24s
% Verified   : 
% Statistics : Number of formulae       :  279 (4327 expanded)
%              Number of clauses        :  176 (1138 expanded)
%              Number of leaves         :   25 (1127 expanded)
%              Depth                    :   30
%              Number of atoms          : 1100 (35930 expanded)
%              Number of equality atoms :  560 (12830 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f45])).

fof(f63,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f25,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,negated_conjecture,(
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
    inference(negated_conjecture,[],[f25])).

fof(f57,plain,(
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
    inference(ennf_transformation,[],[f26])).

fof(f58,plain,(
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
    inference(flattening,[],[f57])).

fof(f65,plain,(
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
     => ( k2_funct_1(X2) != sK4
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & v2_funct_1(X2)
        & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK4),k6_partfun1(X0))
        & k2_relset_1(X0,X1,X2) = X1
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(sK4,X1,X0)
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,
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
          ( k2_funct_1(sK3) != X3
          & k1_xboole_0 != sK2
          & k1_xboole_0 != sK1
          & v2_funct_1(sK3)
          & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,X3),k6_partfun1(sK1))
          & k2_relset_1(sK1,sK2,sK3) = sK2
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
          & v1_funct_2(X3,sK2,sK1)
          & v1_funct_1(X3) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,
    ( k2_funct_1(sK3) != sK4
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & v2_funct_1(sK3)
    & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1))
    & k2_relset_1(sK1,sK2,sK3) = sK2
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    & v1_funct_2(sK4,sK2,sK1)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f58,f65,f64])).

fof(f112,plain,(
    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f66])).

fof(f18,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f93,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f21,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f97,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f21])).

fof(f124,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f93,f97])).

fof(f105,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f66])).

fof(f107,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f66])).

fof(f108,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f66])).

fof(f110,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f66])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f48,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f47])).

fof(f95,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f111,plain,(
    k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f66])).

fof(f23,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( ( k2_relset_1(X0,X1,X3) = X1
              & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) )
           => ( ( v2_funct_1(X4)
                & v2_funct_1(X3) )
              | ( k1_xboole_0 != X1
                & k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( v2_funct_1(X4)
            & v2_funct_1(X3) )
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | k2_relset_1(X0,X1,X3) != X1
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f54,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( v2_funct_1(X4)
            & v2_funct_1(X3) )
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | k2_relset_1(X0,X1,X3) != X1
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f53])).

fof(f101,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v2_funct_1(X4)
      | k1_xboole_0 = X2
      | k2_relset_1(X0,X1,X3) != X1
      | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f106,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f66])).

fof(f109,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f66])).

fof(f114,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f66])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f61])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f62])).

fof(f126,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f69])).

fof(f71,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f8,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f120,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f79,f97])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f34,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f82,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f40,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f39])).

fof(f86,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f80,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f81,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f36,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f83,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f22,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
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
    inference(ennf_transformation,[],[f22])).

fof(f52,plain,(
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
    inference(flattening,[],[f51])).

fof(f98,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
           => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
      | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
            & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f55])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f84,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f5,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f117,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f74,f97])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f76,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f50,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f49])).

fof(f96,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
              & k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f37])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f122,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f85,f97])).

fof(f113,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f66])).

fof(f77,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( v2_funct_1(X1)
              & v2_funct_1(X0) )
           => k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) = k2_funct_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) = k2_funct_1(k5_relat_1(X0,X1))
          | ~ v2_funct_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) = k2_funct_1(k5_relat_1(X0,X1))
          | ~ v2_funct_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f41])).

fof(f87,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) = k2_funct_1(k5_relat_1(X0,X1))
      | ~ v2_funct_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f14,axiom,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f88,plain,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f123,plain,(
    ! [X0] : k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
    inference(definition_unfolding,[],[f88,f97,f97])).

fof(f115,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f66])).

fof(f116,plain,(
    k2_funct_1(sK3) != sK4 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_25,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_41,negated_conjecture,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_512,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) != X0
    | k6_partfun1(sK1) != X3
    | sK1 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_41])).

cnf(c_513,plain,
    ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
    inference(unflattening,[status(thm)],[c_512])).

cnf(c_26,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_521,plain,
    ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_513,c_26])).

cnf(c_1414,plain,
    ( k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_521])).

cnf(c_48,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_46,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_45,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_43,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1848,plain,
    ( m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_2433,plain,
    ( k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1414,c_48,c_46,c_45,c_43,c_521,c_1848])).

cnf(c_42,negated_conjecture,
    ( k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f111])).

cnf(c_32,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v2_funct_1(X0)
    | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X4,X1,X3) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1427,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k1_xboole_0 = X3
    | v1_funct_2(X4,X1,X3) != iProver_top
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v2_funct_1(X4) = iProver_top
    | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_5642,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,sK2,X0) != iProver_top
    | v1_funct_2(sK3,sK1,sK2) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK1,sK2,sK2,X0,sK3,X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_42,c_1427])).

cnf(c_49,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_47,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_50,plain,
    ( v1_funct_2(sK3,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_51,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_7201,plain,
    ( v1_funct_1(X1) != iProver_top
    | v2_funct_1(k1_partfun1(sK1,sK2,sK2,X0,sK3,X1)) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v1_funct_2(X1,sK2,X0) != iProver_top
    | k1_xboole_0 = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5642,c_49,c_50,c_51])).

cnf(c_7202,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,sK2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK1,sK2,sK2,X0,sK3,X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_7201])).

cnf(c_7205,plain,
    ( sK1 = k1_xboole_0
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v2_funct_1(k6_partfun1(sK1)) != iProver_top
    | v2_funct_1(sK4) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2433,c_7202])).

cnf(c_52,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_44,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_53,plain,
    ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_54,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_39,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f114])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_144,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_148,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_823,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1546,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_823])).

cnf(c_1547,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1546])).

cnf(c_11,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_2917,plain,
    ( v2_funct_1(k6_partfun1(sK1)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2918,plain,
    ( v2_funct_1(k6_partfun1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2917])).

cnf(c_8416,plain,
    ( v2_funct_1(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7205,c_52,c_53,c_54,c_39,c_144,c_148,c_1547,c_2918])).

cnf(c_13,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1440,plain,
    ( v2_funct_1(X0) != iProver_top
    | v2_funct_1(k2_funct_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_19,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1436,plain,
    ( k2_funct_1(k2_funct_1(X0)) = X0
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3365,plain,
    ( k2_funct_1(k2_funct_1(k2_funct_1(X0))) = k2_funct_1(X0)
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1440,c_1436])).

cnf(c_15,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_114,plain,
    ( v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_14,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_117,plain,
    ( v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_10831,plain,
    ( v1_relat_1(X0) != iProver_top
    | k2_funct_1(k2_funct_1(k2_funct_1(X0))) = k2_funct_1(X0)
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3365,c_114,c_117])).

cnf(c_10832,plain,
    ( k2_funct_1(k2_funct_1(k2_funct_1(X0))) = k2_funct_1(X0)
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_10831])).

cnf(c_10838,plain,
    ( k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X0)))) = k2_funct_1(k2_funct_1(X0))
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1440,c_10832])).

cnf(c_27473,plain,
    ( v1_relat_1(X0) != iProver_top
    | k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X0)))) = k2_funct_1(k2_funct_1(X0))
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10838,c_114,c_117])).

cnf(c_27474,plain,
    ( k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X0)))) = k2_funct_1(k2_funct_1(X0))
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_27473])).

cnf(c_27482,plain,
    ( k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK4)))) = k2_funct_1(k2_funct_1(sK4))
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_8416,c_27474])).

cnf(c_8422,plain,
    ( k2_funct_1(k2_funct_1(sK4)) = sK4
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_8416,c_1436])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1570,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_1870,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1570])).

cnf(c_1871,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1870])).

cnf(c_5668,plain,
    ( ~ v2_funct_1(sK4)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k2_funct_1(k2_funct_1(sK4)) = sK4 ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_5669,plain,
    ( k2_funct_1(k2_funct_1(sK4)) = sK4
    | v2_funct_1(sK4) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5668])).

cnf(c_8725,plain,
    ( k2_funct_1(k2_funct_1(sK4)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8422,c_52,c_53,c_54,c_39,c_144,c_148,c_1547,c_1871,c_2918,c_5669,c_7205])).

cnf(c_17,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1438,plain,
    ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_8421,plain,
    ( k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4)
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_8416,c_1438])).

cnf(c_1421,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1433,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2834,plain,
    ( k2_relset_1(sK2,sK1,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1421,c_1433])).

cnf(c_30,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_525,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X2,X1,X1,X2,X3,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | k2_relset_1(X1,X2,X0) = X2
    | k6_partfun1(X2) != k6_partfun1(sK1)
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_41])).

cnf(c_526,plain,
    ( ~ v1_funct_2(X0,X1,sK1)
    | ~ v1_funct_2(X2,sK1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK1,X1,X1,sK1,X2,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | k2_relset_1(X1,sK1,X0) = sK1
    | k6_partfun1(sK1) != k6_partfun1(sK1) ),
    inference(unflattening,[status(thm)],[c_525])).

cnf(c_616,plain,
    ( ~ v1_funct_2(X0,X1,sK1)
    | ~ v1_funct_2(X2,sK1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK1,X1,X1,sK1,X2,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | k2_relset_1(X1,sK1,X0) = sK1 ),
    inference(equality_resolution_simp,[status(thm)],[c_526])).

cnf(c_1413,plain,
    ( k1_partfun1(sK1,X0,X0,sK1,X1,X2) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | k2_relset_1(X0,sK1,X2) = sK1
    | v1_funct_2(X2,X0,sK1) != iProver_top
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_616])).

cnf(c_2436,plain,
    ( k1_partfun1(sK1,X0,X0,sK1,X1,X2) != k6_partfun1(sK1)
    | k2_relset_1(X0,sK1,X2) = sK1
    | v1_funct_2(X2,X0,sK1) != iProver_top
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1413,c_2433])).

cnf(c_2440,plain,
    ( k2_relset_1(sK2,sK1,sK4) = sK1
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | v1_funct_2(sK3,sK1,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2433,c_2436])).

cnf(c_2479,plain,
    ( k2_relset_1(sK2,sK1,sK4) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2440,c_49,c_50,c_51,c_52,c_53,c_54])).

cnf(c_2837,plain,
    ( k2_relat_1(sK4) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2834,c_2479])).

cnf(c_8424,plain,
    ( k1_relat_1(k2_funct_1(sK4)) = sK1
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8421,c_2837])).

cnf(c_13177,plain,
    ( k1_relat_1(k2_funct_1(sK4)) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8424,c_52,c_54,c_1871])).

cnf(c_5,plain,
    ( ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1446,plain,
    ( k2_relat_1(k5_relat_1(X0,X1)) = k2_relat_1(X1)
    | r1_tarski(k1_relat_1(X1),k2_relat_1(X0)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3445,plain,
    ( k2_relat_1(k5_relat_1(sK4,X0)) = k2_relat_1(X0)
    | r1_tarski(k1_relat_1(X0),sK1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2837,c_1446])).

cnf(c_5582,plain,
    ( v1_relat_1(X0) != iProver_top
    | r1_tarski(k1_relat_1(X0),sK1) != iProver_top
    | k2_relat_1(k5_relat_1(sK4,X0)) = k2_relat_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3445,c_54,c_1871])).

cnf(c_5583,plain,
    ( k2_relat_1(k5_relat_1(sK4,X0)) = k2_relat_1(X0)
    | r1_tarski(k1_relat_1(X0),sK1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5582])).

cnf(c_13181,plain,
    ( k2_relat_1(k5_relat_1(sK4,k2_funct_1(sK4))) = k2_relat_1(k2_funct_1(sK4))
    | r1_tarski(sK1,sK1) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13177,c_5583])).

cnf(c_36,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1423,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v2_funct_1(X2) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_2981,plain,
    ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(sK2)
    | sK1 = k1_xboole_0
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v2_funct_1(sK4) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2479,c_1423])).

cnf(c_3117,plain,
    ( v2_funct_1(sK4) != iProver_top
    | k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2981,c_52,c_53,c_54,c_39,c_144,c_148,c_1547])).

cnf(c_3118,plain,
    ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(sK2)
    | v2_funct_1(sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_3117])).

cnf(c_8423,plain,
    ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(sK2) ),
    inference(superposition,[status(thm)],[c_8416,c_3118])).

cnf(c_16,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1439,plain,
    ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_8420,plain,
    ( k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4)
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_8416,c_1439])).

cnf(c_8779,plain,
    ( k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8420,c_52,c_54,c_1871])).

cnf(c_13190,plain,
    ( k2_relat_1(k6_partfun1(sK2)) = k1_relat_1(sK4)
    | r1_tarski(sK1,sK1) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13181,c_8423,c_8779])).

cnf(c_6,plain,
    ( k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f117])).

cnf(c_13191,plain,
    ( k1_relat_1(sK4) = sK2
    | r1_tarski(sK1,sK1) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_13190,c_6])).

cnf(c_2464,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2465,plain,
    ( r1_tarski(sK1,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2464])).

cnf(c_10,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_4235,plain,
    ( ~ v1_funct_1(sK4)
    | v1_relat_1(k2_funct_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_4236,plain,
    ( v1_funct_1(sK4) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4235])).

cnf(c_13693,plain,
    ( k1_relat_1(sK4) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_13191,c_52,c_54,c_1871,c_2465,c_4236])).

cnf(c_1418,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_29,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1429,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_6774,plain,
    ( k1_partfun1(X0,X1,sK2,sK1,X2,sK4) = k5_relat_1(X2,sK4)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1421,c_1429])).

cnf(c_7208,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK2,sK1,X2,sK4) = k5_relat_1(X2,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6774,c_52])).

cnf(c_7209,plain,
    ( k1_partfun1(X0,X1,sK2,sK1,X2,sK4) = k5_relat_1(X2,sK4)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_7208])).

cnf(c_7217,plain,
    ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k5_relat_1(sK3,sK4)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1418,c_7209])).

cnf(c_7218,plain,
    ( k5_relat_1(sK3,sK4) = k6_partfun1(sK1)
    | v1_funct_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7217,c_2433])).

cnf(c_8692,plain,
    ( k5_relat_1(sK3,sK4) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7218,c_49])).

cnf(c_18,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
    | k2_funct_1(X0) = X1
    | k1_relat_1(X0) != k2_relat_1(X1) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_1437,plain,
    ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k1_relat_1(X1) != k2_relat_1(X0)
    | v2_funct_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_8694,plain,
    ( k2_funct_1(sK4) = sK3
    | k6_partfun1(k2_relat_1(sK4)) != k6_partfun1(sK1)
    | k1_relat_1(sK4) != k2_relat_1(sK3)
    | v2_funct_1(sK4) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_8692,c_1437])).

cnf(c_2835,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1418,c_1433])).

cnf(c_2836,plain,
    ( k2_relat_1(sK3) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_2835,c_42])).

cnf(c_8695,plain,
    ( k2_funct_1(sK4) = sK3
    | k6_partfun1(sK1) != k6_partfun1(sK1)
    | k1_relat_1(sK4) != sK2
    | v2_funct_1(sK4) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8694,c_2836,c_2837])).

cnf(c_8696,plain,
    ( k2_funct_1(sK4) = sK3
    | k1_relat_1(sK4) != sK2
    | v2_funct_1(sK4) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_8695])).

cnf(c_40,negated_conjecture,
    ( v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_2319,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_2500,plain,
    ( v2_funct_1(k2_funct_1(sK3))
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_9,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2732,plain,
    ( v1_funct_1(k2_funct_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2735,plain,
    ( v1_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_4238,plain,
    ( ~ v1_funct_1(sK3)
    | v1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1422,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_20,plain,
    ( ~ v2_funct_1(X0)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) = k2_funct_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1435,plain,
    ( k5_relat_1(k2_funct_1(X0),k2_funct_1(X1)) = k2_funct_1(k5_relat_1(X1,X0))
    | v2_funct_1(X1) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_8469,plain,
    ( k5_relat_1(k2_funct_1(sK4),k2_funct_1(X0)) = k2_funct_1(k5_relat_1(X0,sK4))
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_8416,c_1435])).

cnf(c_10809,plain,
    ( v1_relat_1(X0) != iProver_top
    | k5_relat_1(k2_funct_1(sK4),k2_funct_1(X0)) = k2_funct_1(k5_relat_1(X0,sK4))
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8469,c_52,c_54,c_1871])).

cnf(c_10810,plain,
    ( k5_relat_1(k2_funct_1(sK4),k2_funct_1(X0)) = k2_funct_1(k5_relat_1(X0,sK4))
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_10809])).

cnf(c_10817,plain,
    ( k5_relat_1(k2_funct_1(sK4),k2_funct_1(sK3)) = k2_funct_1(k5_relat_1(sK3,sK4))
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1422,c_10810])).

cnf(c_10819,plain,
    ( k5_relat_1(k2_funct_1(sK4),k2_funct_1(sK3)) = k2_funct_1(k6_partfun1(sK1))
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10817,c_8692])).

cnf(c_21,plain,
    ( k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_10820,plain,
    ( k5_relat_1(k2_funct_1(sK4),k2_funct_1(sK3)) = k6_partfun1(sK1)
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10819,c_21])).

cnf(c_2320,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2319])).

cnf(c_11074,plain,
    ( k5_relat_1(k2_funct_1(sK4),k2_funct_1(sK3)) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10820,c_49,c_51,c_2320])).

cnf(c_11076,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = k2_funct_1(sK4)
    | k6_partfun1(k2_relat_1(k2_funct_1(sK3))) != k6_partfun1(sK1)
    | k1_relat_1(k2_funct_1(sK3)) != k2_relat_1(k2_funct_1(sK4))
    | v2_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11074,c_1437])).

cnf(c_3238,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = sK3
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1422,c_1436])).

cnf(c_3275,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3238,c_49,c_51,c_2320])).

cnf(c_3372,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1422,c_1438])).

cnf(c_3373,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = sK2
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3372,c_2836])).

cnf(c_3765,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3373,c_49,c_51,c_2320])).

cnf(c_3444,plain,
    ( k2_relat_1(k5_relat_1(sK3,X0)) = k2_relat_1(X0)
    | r1_tarski(k1_relat_1(X0),sK2) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2836,c_1446])).

cnf(c_4220,plain,
    ( v1_relat_1(X0) != iProver_top
    | r1_tarski(k1_relat_1(X0),sK2) != iProver_top
    | k2_relat_1(k5_relat_1(sK3,X0)) = k2_relat_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3444,c_51,c_2320])).

cnf(c_4221,plain,
    ( k2_relat_1(k5_relat_1(sK3,X0)) = k2_relat_1(X0)
    | r1_tarski(k1_relat_1(X0),sK2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4220])).

cnf(c_4227,plain,
    ( k2_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) = k2_relat_1(k2_funct_1(sK3))
    | r1_tarski(sK2,sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3765,c_4221])).

cnf(c_2980,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | sK2 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_42,c_1423])).

cnf(c_38,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f115])).

cnf(c_1508,plain,
    ( ~ v1_funct_2(X0,X1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,sK2,X0) != sK2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_36])).

cnf(c_1642,plain,
    ( ~ v1_funct_2(sK3,X0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | k2_relset_1(X0,sK2,sK3) != sK2
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(X0)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_1508])).

cnf(c_1765,plain,
    ( ~ v1_funct_2(sK3,sK1,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | k2_relset_1(sK1,sK2,sK3) != sK2
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_1642])).

cnf(c_3114,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2980,c_48,c_47,c_46,c_42,c_40,c_38,c_1765])).

cnf(c_3435,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1422,c_1439])).

cnf(c_4213,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3435,c_49,c_51,c_2320])).

cnf(c_4228,plain,
    ( k2_relat_1(k6_partfun1(sK1)) = k1_relat_1(sK3)
    | r1_tarski(sK2,sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4227,c_3114,c_4213])).

cnf(c_4229,plain,
    ( k1_relat_1(sK3) = sK1
    | r1_tarski(sK2,sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4228,c_6])).

cnf(c_2460,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_4231,plain,
    ( ~ r1_tarski(sK2,sK2)
    | ~ v1_relat_1(k2_funct_1(sK3))
    | k1_relat_1(sK3) = sK1 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4229])).

cnf(c_4309,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4229,c_48,c_46,c_2319,c_2460,c_4231,c_4238])).

cnf(c_4311,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = sK1 ),
    inference(demodulation,[status(thm)],[c_4309,c_4213])).

cnf(c_11077,plain,
    ( k2_funct_1(sK4) = sK3
    | k6_partfun1(sK1) != k6_partfun1(sK1)
    | k1_relat_1(sK4) != sK2
    | v2_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11076,c_3275,c_3765,c_4311,c_8779])).

cnf(c_11078,plain,
    ( k2_funct_1(sK4) = sK3
    | k1_relat_1(sK4) != sK2
    | v2_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_11077])).

cnf(c_11079,plain,
    ( ~ v2_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(k2_funct_1(sK4))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK4))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | k2_funct_1(sK4) = sK3
    | k1_relat_1(sK4) != sK2 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_11078])).

cnf(c_11231,plain,
    ( k1_relat_1(sK4) != sK2
    | k2_funct_1(sK4) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8696,c_48,c_46,c_45,c_43,c_40,c_1870,c_2319,c_2500,c_2732,c_2735,c_4235,c_4238,c_11079])).

cnf(c_11232,plain,
    ( k2_funct_1(sK4) = sK3
    | k1_relat_1(sK4) != sK2 ),
    inference(renaming,[status(thm)],[c_11231])).

cnf(c_13696,plain,
    ( k2_funct_1(sK4) = sK3
    | sK2 != sK2 ),
    inference(demodulation,[status(thm)],[c_13693,c_11232])).

cnf(c_13700,plain,
    ( k2_funct_1(sK4) = sK3 ),
    inference(equality_resolution_simp,[status(thm)],[c_13696])).

cnf(c_27484,plain,
    ( k2_funct_1(sK3) = sK4
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_27482,c_8725,c_13700])).

cnf(c_37,negated_conjecture,
    ( k2_funct_1(sK3) != sK4 ),
    inference(cnf_transformation,[],[f116])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_27484,c_1871,c_37,c_54,c_52])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:16:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 11.24/1.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.24/1.99  
% 11.24/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.24/1.99  
% 11.24/1.99  ------  iProver source info
% 11.24/1.99  
% 11.24/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.24/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.24/1.99  git: non_committed_changes: false
% 11.24/1.99  git: last_make_outside_of_git: false
% 11.24/1.99  
% 11.24/1.99  ------ 
% 11.24/1.99  
% 11.24/1.99  ------ Input Options
% 11.24/1.99  
% 11.24/1.99  --out_options                           all
% 11.24/1.99  --tptp_safe_out                         true
% 11.24/1.99  --problem_path                          ""
% 11.24/1.99  --include_path                          ""
% 11.24/1.99  --clausifier                            res/vclausify_rel
% 11.24/1.99  --clausifier_options                    ""
% 11.24/1.99  --stdin                                 false
% 11.24/1.99  --stats_out                             all
% 11.24/1.99  
% 11.24/1.99  ------ General Options
% 11.24/1.99  
% 11.24/1.99  --fof                                   false
% 11.24/1.99  --time_out_real                         305.
% 11.24/1.99  --time_out_virtual                      -1.
% 11.24/1.99  --symbol_type_check                     false
% 11.24/1.99  --clausify_out                          false
% 11.24/1.99  --sig_cnt_out                           false
% 11.24/1.99  --trig_cnt_out                          false
% 11.24/1.99  --trig_cnt_out_tolerance                1.
% 11.24/1.99  --trig_cnt_out_sk_spl                   false
% 11.24/1.99  --abstr_cl_out                          false
% 11.24/1.99  
% 11.24/1.99  ------ Global Options
% 11.24/1.99  
% 11.24/1.99  --schedule                              default
% 11.24/1.99  --add_important_lit                     false
% 11.24/1.99  --prop_solver_per_cl                    1000
% 11.24/1.99  --min_unsat_core                        false
% 11.24/1.99  --soft_assumptions                      false
% 11.24/1.99  --soft_lemma_size                       3
% 11.24/1.99  --prop_impl_unit_size                   0
% 11.24/1.99  --prop_impl_unit                        []
% 11.24/1.99  --share_sel_clauses                     true
% 11.24/1.99  --reset_solvers                         false
% 11.24/1.99  --bc_imp_inh                            [conj_cone]
% 11.24/1.99  --conj_cone_tolerance                   3.
% 11.24/1.99  --extra_neg_conj                        none
% 11.24/1.99  --large_theory_mode                     true
% 11.24/1.99  --prolific_symb_bound                   200
% 11.24/1.99  --lt_threshold                          2000
% 11.24/1.99  --clause_weak_htbl                      true
% 11.24/1.99  --gc_record_bc_elim                     false
% 11.24/1.99  
% 11.24/1.99  ------ Preprocessing Options
% 11.24/1.99  
% 11.24/1.99  --preprocessing_flag                    true
% 11.24/1.99  --time_out_prep_mult                    0.1
% 11.24/1.99  --splitting_mode                        input
% 11.24/1.99  --splitting_grd                         true
% 11.24/1.99  --splitting_cvd                         false
% 11.24/1.99  --splitting_cvd_svl                     false
% 11.24/1.99  --splitting_nvd                         32
% 11.24/1.99  --sub_typing                            true
% 11.24/1.99  --prep_gs_sim                           true
% 11.24/1.99  --prep_unflatten                        true
% 11.24/1.99  --prep_res_sim                          true
% 11.24/1.99  --prep_upred                            true
% 11.24/1.99  --prep_sem_filter                       exhaustive
% 11.24/1.99  --prep_sem_filter_out                   false
% 11.24/1.99  --pred_elim                             true
% 11.24/1.99  --res_sim_input                         true
% 11.24/1.99  --eq_ax_congr_red                       true
% 11.24/1.99  --pure_diseq_elim                       true
% 11.24/1.99  --brand_transform                       false
% 11.24/1.99  --non_eq_to_eq                          false
% 11.24/1.99  --prep_def_merge                        true
% 11.24/1.99  --prep_def_merge_prop_impl              false
% 11.24/1.99  --prep_def_merge_mbd                    true
% 11.24/1.99  --prep_def_merge_tr_red                 false
% 11.24/1.99  --prep_def_merge_tr_cl                  false
% 11.24/1.99  --smt_preprocessing                     true
% 11.24/1.99  --smt_ac_axioms                         fast
% 11.24/1.99  --preprocessed_out                      false
% 11.24/1.99  --preprocessed_stats                    false
% 11.24/1.99  
% 11.24/1.99  ------ Abstraction refinement Options
% 11.24/1.99  
% 11.24/1.99  --abstr_ref                             []
% 11.24/1.99  --abstr_ref_prep                        false
% 11.24/1.99  --abstr_ref_until_sat                   false
% 11.24/1.99  --abstr_ref_sig_restrict                funpre
% 11.24/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.24/1.99  --abstr_ref_under                       []
% 11.24/1.99  
% 11.24/1.99  ------ SAT Options
% 11.24/1.99  
% 11.24/1.99  --sat_mode                              false
% 11.24/1.99  --sat_fm_restart_options                ""
% 11.24/1.99  --sat_gr_def                            false
% 11.24/1.99  --sat_epr_types                         true
% 11.24/1.99  --sat_non_cyclic_types                  false
% 11.24/1.99  --sat_finite_models                     false
% 11.24/1.99  --sat_fm_lemmas                         false
% 11.24/1.99  --sat_fm_prep                           false
% 11.24/1.99  --sat_fm_uc_incr                        true
% 11.24/1.99  --sat_out_model                         small
% 11.24/1.99  --sat_out_clauses                       false
% 11.24/1.99  
% 11.24/1.99  ------ QBF Options
% 11.24/1.99  
% 11.24/1.99  --qbf_mode                              false
% 11.24/1.99  --qbf_elim_univ                         false
% 11.24/1.99  --qbf_dom_inst                          none
% 11.24/1.99  --qbf_dom_pre_inst                      false
% 11.24/1.99  --qbf_sk_in                             false
% 11.24/1.99  --qbf_pred_elim                         true
% 11.24/1.99  --qbf_split                             512
% 11.24/1.99  
% 11.24/1.99  ------ BMC1 Options
% 11.24/1.99  
% 11.24/1.99  --bmc1_incremental                      false
% 11.24/1.99  --bmc1_axioms                           reachable_all
% 11.24/1.99  --bmc1_min_bound                        0
% 11.24/1.99  --bmc1_max_bound                        -1
% 11.24/1.99  --bmc1_max_bound_default                -1
% 11.24/1.99  --bmc1_symbol_reachability              true
% 11.24/1.99  --bmc1_property_lemmas                  false
% 11.24/1.99  --bmc1_k_induction                      false
% 11.24/1.99  --bmc1_non_equiv_states                 false
% 11.24/1.99  --bmc1_deadlock                         false
% 11.24/1.99  --bmc1_ucm                              false
% 11.24/1.99  --bmc1_add_unsat_core                   none
% 11.24/1.99  --bmc1_unsat_core_children              false
% 11.24/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.24/1.99  --bmc1_out_stat                         full
% 11.24/1.99  --bmc1_ground_init                      false
% 11.24/1.99  --bmc1_pre_inst_next_state              false
% 11.24/1.99  --bmc1_pre_inst_state                   false
% 11.24/1.99  --bmc1_pre_inst_reach_state             false
% 11.24/1.99  --bmc1_out_unsat_core                   false
% 11.24/1.99  --bmc1_aig_witness_out                  false
% 11.24/1.99  --bmc1_verbose                          false
% 11.24/1.99  --bmc1_dump_clauses_tptp                false
% 11.24/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.24/1.99  --bmc1_dump_file                        -
% 11.24/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.24/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.24/1.99  --bmc1_ucm_extend_mode                  1
% 11.24/1.99  --bmc1_ucm_init_mode                    2
% 11.24/1.99  --bmc1_ucm_cone_mode                    none
% 11.24/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.24/1.99  --bmc1_ucm_relax_model                  4
% 11.24/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.24/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.24/1.99  --bmc1_ucm_layered_model                none
% 11.24/1.99  --bmc1_ucm_max_lemma_size               10
% 11.24/1.99  
% 11.24/1.99  ------ AIG Options
% 11.24/1.99  
% 11.24/1.99  --aig_mode                              false
% 11.24/1.99  
% 11.24/1.99  ------ Instantiation Options
% 11.24/1.99  
% 11.24/1.99  --instantiation_flag                    true
% 11.24/1.99  --inst_sos_flag                         true
% 11.24/1.99  --inst_sos_phase                        true
% 11.24/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.24/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.24/1.99  --inst_lit_sel_side                     num_symb
% 11.24/1.99  --inst_solver_per_active                1400
% 11.24/1.99  --inst_solver_calls_frac                1.
% 11.24/1.99  --inst_passive_queue_type               priority_queues
% 11.24/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.24/1.99  --inst_passive_queues_freq              [25;2]
% 11.24/1.99  --inst_dismatching                      true
% 11.24/1.99  --inst_eager_unprocessed_to_passive     true
% 11.24/1.99  --inst_prop_sim_given                   true
% 11.24/1.99  --inst_prop_sim_new                     false
% 11.24/1.99  --inst_subs_new                         false
% 11.24/1.99  --inst_eq_res_simp                      false
% 11.24/1.99  --inst_subs_given                       false
% 11.24/1.99  --inst_orphan_elimination               true
% 11.24/1.99  --inst_learning_loop_flag               true
% 11.24/1.99  --inst_learning_start                   3000
% 11.24/1.99  --inst_learning_factor                  2
% 11.24/1.99  --inst_start_prop_sim_after_learn       3
% 11.24/1.99  --inst_sel_renew                        solver
% 11.24/1.99  --inst_lit_activity_flag                true
% 11.24/1.99  --inst_restr_to_given                   false
% 11.24/1.99  --inst_activity_threshold               500
% 11.24/1.99  --inst_out_proof                        true
% 11.24/1.99  
% 11.24/1.99  ------ Resolution Options
% 11.24/1.99  
% 11.24/1.99  --resolution_flag                       true
% 11.24/1.99  --res_lit_sel                           adaptive
% 11.24/1.99  --res_lit_sel_side                      none
% 11.24/1.99  --res_ordering                          kbo
% 11.24/1.99  --res_to_prop_solver                    active
% 11.24/1.99  --res_prop_simpl_new                    false
% 11.24/1.99  --res_prop_simpl_given                  true
% 11.24/1.99  --res_passive_queue_type                priority_queues
% 11.24/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.24/1.99  --res_passive_queues_freq               [15;5]
% 11.24/1.99  --res_forward_subs                      full
% 11.24/1.99  --res_backward_subs                     full
% 11.24/1.99  --res_forward_subs_resolution           true
% 11.24/1.99  --res_backward_subs_resolution          true
% 11.24/1.99  --res_orphan_elimination                true
% 11.24/1.99  --res_time_limit                        2.
% 11.24/1.99  --res_out_proof                         true
% 11.24/1.99  
% 11.24/1.99  ------ Superposition Options
% 11.24/1.99  
% 11.24/1.99  --superposition_flag                    true
% 11.24/1.99  --sup_passive_queue_type                priority_queues
% 11.24/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.24/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.24/1.99  --demod_completeness_check              fast
% 11.24/1.99  --demod_use_ground                      true
% 11.24/1.99  --sup_to_prop_solver                    passive
% 11.24/1.99  --sup_prop_simpl_new                    true
% 11.24/1.99  --sup_prop_simpl_given                  true
% 11.24/1.99  --sup_fun_splitting                     true
% 11.24/1.99  --sup_smt_interval                      50000
% 11.24/1.99  
% 11.24/1.99  ------ Superposition Simplification Setup
% 11.24/1.99  
% 11.24/1.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.24/1.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.24/1.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.24/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.24/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.24/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.24/1.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.24/1.99  --sup_immed_triv                        [TrivRules]
% 11.24/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.24/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.24/1.99  --sup_immed_bw_main                     []
% 11.24/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.24/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.24/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.24/1.99  --sup_input_bw                          []
% 11.24/1.99  
% 11.24/1.99  ------ Combination Options
% 11.24/1.99  
% 11.24/1.99  --comb_res_mult                         3
% 11.24/1.99  --comb_sup_mult                         2
% 11.24/1.99  --comb_inst_mult                        10
% 11.24/1.99  
% 11.24/1.99  ------ Debug Options
% 11.24/1.99  
% 11.24/1.99  --dbg_backtrace                         false
% 11.24/1.99  --dbg_dump_prop_clauses                 false
% 11.24/1.99  --dbg_dump_prop_clauses_file            -
% 11.24/1.99  --dbg_out_stat                          false
% 11.24/1.99  ------ Parsing...
% 11.24/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.24/1.99  
% 11.24/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 11.24/1.99  
% 11.24/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.24/1.99  
% 11.24/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.24/1.99  ------ Proving...
% 11.24/1.99  ------ Problem Properties 
% 11.24/1.99  
% 11.24/1.99  
% 11.24/1.99  clauses                                 44
% 11.24/1.99  conjectures                             11
% 11.24/1.99  EPR                                     10
% 11.24/1.99  Horn                                    40
% 11.24/1.99  unary                                   19
% 11.24/1.99  binary                                  4
% 11.24/1.99  lits                                    154
% 11.24/1.99  lits eq                                 37
% 11.24/1.99  fd_pure                                 0
% 11.24/1.99  fd_pseudo                               0
% 11.24/1.99  fd_cond                                 4
% 11.24/1.99  fd_pseudo_cond                          2
% 11.24/1.99  AC symbols                              0
% 11.24/1.99  
% 11.24/1.99  ------ Schedule dynamic 5 is on 
% 11.24/1.99  
% 11.24/1.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.24/1.99  
% 11.24/1.99  
% 11.24/1.99  ------ 
% 11.24/1.99  Current options:
% 11.24/1.99  ------ 
% 11.24/1.99  
% 11.24/1.99  ------ Input Options
% 11.24/1.99  
% 11.24/1.99  --out_options                           all
% 11.24/1.99  --tptp_safe_out                         true
% 11.24/1.99  --problem_path                          ""
% 11.24/1.99  --include_path                          ""
% 11.24/1.99  --clausifier                            res/vclausify_rel
% 11.24/1.99  --clausifier_options                    ""
% 11.24/1.99  --stdin                                 false
% 11.24/1.99  --stats_out                             all
% 11.24/1.99  
% 11.24/1.99  ------ General Options
% 11.24/1.99  
% 11.24/1.99  --fof                                   false
% 11.24/1.99  --time_out_real                         305.
% 11.24/1.99  --time_out_virtual                      -1.
% 11.24/1.99  --symbol_type_check                     false
% 11.24/1.99  --clausify_out                          false
% 11.24/1.99  --sig_cnt_out                           false
% 11.24/1.99  --trig_cnt_out                          false
% 11.24/1.99  --trig_cnt_out_tolerance                1.
% 11.24/1.99  --trig_cnt_out_sk_spl                   false
% 11.24/1.99  --abstr_cl_out                          false
% 11.24/1.99  
% 11.24/1.99  ------ Global Options
% 11.24/1.99  
% 11.24/1.99  --schedule                              default
% 11.24/1.99  --add_important_lit                     false
% 11.24/1.99  --prop_solver_per_cl                    1000
% 11.24/1.99  --min_unsat_core                        false
% 11.24/1.99  --soft_assumptions                      false
% 11.24/1.99  --soft_lemma_size                       3
% 11.24/1.99  --prop_impl_unit_size                   0
% 11.24/1.99  --prop_impl_unit                        []
% 11.24/1.99  --share_sel_clauses                     true
% 11.24/1.99  --reset_solvers                         false
% 11.24/1.99  --bc_imp_inh                            [conj_cone]
% 11.24/1.99  --conj_cone_tolerance                   3.
% 11.24/1.99  --extra_neg_conj                        none
% 11.24/1.99  --large_theory_mode                     true
% 11.24/1.99  --prolific_symb_bound                   200
% 11.24/1.99  --lt_threshold                          2000
% 11.24/1.99  --clause_weak_htbl                      true
% 11.24/1.99  --gc_record_bc_elim                     false
% 11.24/1.99  
% 11.24/1.99  ------ Preprocessing Options
% 11.24/1.99  
% 11.24/1.99  --preprocessing_flag                    true
% 11.24/1.99  --time_out_prep_mult                    0.1
% 11.24/1.99  --splitting_mode                        input
% 11.24/1.99  --splitting_grd                         true
% 11.24/1.99  --splitting_cvd                         false
% 11.24/1.99  --splitting_cvd_svl                     false
% 11.24/1.99  --splitting_nvd                         32
% 11.24/1.99  --sub_typing                            true
% 11.24/1.99  --prep_gs_sim                           true
% 11.24/1.99  --prep_unflatten                        true
% 11.24/1.99  --prep_res_sim                          true
% 11.24/1.99  --prep_upred                            true
% 11.24/1.99  --prep_sem_filter                       exhaustive
% 11.24/1.99  --prep_sem_filter_out                   false
% 11.24/1.99  --pred_elim                             true
% 11.24/1.99  --res_sim_input                         true
% 11.24/1.99  --eq_ax_congr_red                       true
% 11.24/1.99  --pure_diseq_elim                       true
% 11.24/1.99  --brand_transform                       false
% 11.24/1.99  --non_eq_to_eq                          false
% 11.24/1.99  --prep_def_merge                        true
% 11.24/1.99  --prep_def_merge_prop_impl              false
% 11.24/1.99  --prep_def_merge_mbd                    true
% 11.24/1.99  --prep_def_merge_tr_red                 false
% 11.24/1.99  --prep_def_merge_tr_cl                  false
% 11.24/1.99  --smt_preprocessing                     true
% 11.24/1.99  --smt_ac_axioms                         fast
% 11.24/1.99  --preprocessed_out                      false
% 11.24/1.99  --preprocessed_stats                    false
% 11.24/1.99  
% 11.24/1.99  ------ Abstraction refinement Options
% 11.24/1.99  
% 11.24/1.99  --abstr_ref                             []
% 11.24/1.99  --abstr_ref_prep                        false
% 11.24/1.99  --abstr_ref_until_sat                   false
% 11.24/1.99  --abstr_ref_sig_restrict                funpre
% 11.24/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.24/1.99  --abstr_ref_under                       []
% 11.24/1.99  
% 11.24/1.99  ------ SAT Options
% 11.24/1.99  
% 11.24/1.99  --sat_mode                              false
% 11.24/1.99  --sat_fm_restart_options                ""
% 11.24/1.99  --sat_gr_def                            false
% 11.24/1.99  --sat_epr_types                         true
% 11.24/1.99  --sat_non_cyclic_types                  false
% 11.24/1.99  --sat_finite_models                     false
% 11.24/1.99  --sat_fm_lemmas                         false
% 11.24/1.99  --sat_fm_prep                           false
% 11.24/1.99  --sat_fm_uc_incr                        true
% 11.24/1.99  --sat_out_model                         small
% 11.24/1.99  --sat_out_clauses                       false
% 11.24/1.99  
% 11.24/1.99  ------ QBF Options
% 11.24/1.99  
% 11.24/1.99  --qbf_mode                              false
% 11.24/1.99  --qbf_elim_univ                         false
% 11.24/1.99  --qbf_dom_inst                          none
% 11.24/1.99  --qbf_dom_pre_inst                      false
% 11.24/1.99  --qbf_sk_in                             false
% 11.24/1.99  --qbf_pred_elim                         true
% 11.24/1.99  --qbf_split                             512
% 11.24/1.99  
% 11.24/1.99  ------ BMC1 Options
% 11.24/1.99  
% 11.24/1.99  --bmc1_incremental                      false
% 11.24/1.99  --bmc1_axioms                           reachable_all
% 11.24/1.99  --bmc1_min_bound                        0
% 11.24/1.99  --bmc1_max_bound                        -1
% 11.24/1.99  --bmc1_max_bound_default                -1
% 11.24/1.99  --bmc1_symbol_reachability              true
% 11.24/1.99  --bmc1_property_lemmas                  false
% 11.24/1.99  --bmc1_k_induction                      false
% 11.24/1.99  --bmc1_non_equiv_states                 false
% 11.24/1.99  --bmc1_deadlock                         false
% 11.24/1.99  --bmc1_ucm                              false
% 11.24/1.99  --bmc1_add_unsat_core                   none
% 11.24/1.99  --bmc1_unsat_core_children              false
% 11.24/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.24/1.99  --bmc1_out_stat                         full
% 11.24/1.99  --bmc1_ground_init                      false
% 11.24/1.99  --bmc1_pre_inst_next_state              false
% 11.24/1.99  --bmc1_pre_inst_state                   false
% 11.24/1.99  --bmc1_pre_inst_reach_state             false
% 11.24/1.99  --bmc1_out_unsat_core                   false
% 11.24/1.99  --bmc1_aig_witness_out                  false
% 11.24/1.99  --bmc1_verbose                          false
% 11.24/1.99  --bmc1_dump_clauses_tptp                false
% 11.24/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.24/1.99  --bmc1_dump_file                        -
% 11.24/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.24/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.24/1.99  --bmc1_ucm_extend_mode                  1
% 11.24/1.99  --bmc1_ucm_init_mode                    2
% 11.24/1.99  --bmc1_ucm_cone_mode                    none
% 11.24/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.24/1.99  --bmc1_ucm_relax_model                  4
% 11.24/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.24/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.24/1.99  --bmc1_ucm_layered_model                none
% 11.24/1.99  --bmc1_ucm_max_lemma_size               10
% 11.24/1.99  
% 11.24/1.99  ------ AIG Options
% 11.24/1.99  
% 11.24/1.99  --aig_mode                              false
% 11.24/1.99  
% 11.24/1.99  ------ Instantiation Options
% 11.24/1.99  
% 11.24/1.99  --instantiation_flag                    true
% 11.24/1.99  --inst_sos_flag                         true
% 11.24/1.99  --inst_sos_phase                        true
% 11.24/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.24/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.24/1.99  --inst_lit_sel_side                     none
% 11.24/1.99  --inst_solver_per_active                1400
% 11.24/1.99  --inst_solver_calls_frac                1.
% 11.24/1.99  --inst_passive_queue_type               priority_queues
% 11.24/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.24/1.99  --inst_passive_queues_freq              [25;2]
% 11.24/1.99  --inst_dismatching                      true
% 11.24/1.99  --inst_eager_unprocessed_to_passive     true
% 11.24/1.99  --inst_prop_sim_given                   true
% 11.24/1.99  --inst_prop_sim_new                     false
% 11.24/1.99  --inst_subs_new                         false
% 11.24/1.99  --inst_eq_res_simp                      false
% 11.24/1.99  --inst_subs_given                       false
% 11.24/1.99  --inst_orphan_elimination               true
% 11.24/1.99  --inst_learning_loop_flag               true
% 11.24/1.99  --inst_learning_start                   3000
% 11.24/1.99  --inst_learning_factor                  2
% 11.24/1.99  --inst_start_prop_sim_after_learn       3
% 11.24/1.99  --inst_sel_renew                        solver
% 11.24/1.99  --inst_lit_activity_flag                true
% 11.24/1.99  --inst_restr_to_given                   false
% 11.24/1.99  --inst_activity_threshold               500
% 11.24/1.99  --inst_out_proof                        true
% 11.24/1.99  
% 11.24/1.99  ------ Resolution Options
% 11.24/1.99  
% 11.24/1.99  --resolution_flag                       false
% 11.24/1.99  --res_lit_sel                           adaptive
% 11.24/1.99  --res_lit_sel_side                      none
% 11.24/1.99  --res_ordering                          kbo
% 11.24/1.99  --res_to_prop_solver                    active
% 11.24/1.99  --res_prop_simpl_new                    false
% 11.24/1.99  --res_prop_simpl_given                  true
% 11.24/1.99  --res_passive_queue_type                priority_queues
% 11.24/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.24/1.99  --res_passive_queues_freq               [15;5]
% 11.24/1.99  --res_forward_subs                      full
% 11.24/1.99  --res_backward_subs                     full
% 11.24/1.99  --res_forward_subs_resolution           true
% 11.24/1.99  --res_backward_subs_resolution          true
% 11.24/1.99  --res_orphan_elimination                true
% 11.24/1.99  --res_time_limit                        2.
% 11.24/1.99  --res_out_proof                         true
% 11.24/1.99  
% 11.24/1.99  ------ Superposition Options
% 11.24/1.99  
% 11.24/1.99  --superposition_flag                    true
% 11.24/1.99  --sup_passive_queue_type                priority_queues
% 11.24/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.24/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.24/1.99  --demod_completeness_check              fast
% 11.24/1.99  --demod_use_ground                      true
% 11.24/1.99  --sup_to_prop_solver                    passive
% 11.24/1.99  --sup_prop_simpl_new                    true
% 11.24/1.99  --sup_prop_simpl_given                  true
% 11.24/1.99  --sup_fun_splitting                     true
% 11.24/1.99  --sup_smt_interval                      50000
% 11.24/1.99  
% 11.24/1.99  ------ Superposition Simplification Setup
% 11.24/1.99  
% 11.24/1.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.24/1.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.24/1.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.24/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.24/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.24/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.24/1.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.24/1.99  --sup_immed_triv                        [TrivRules]
% 11.24/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.24/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.24/1.99  --sup_immed_bw_main                     []
% 11.24/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.24/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.24/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.24/1.99  --sup_input_bw                          []
% 11.24/1.99  
% 11.24/1.99  ------ Combination Options
% 11.24/1.99  
% 11.24/1.99  --comb_res_mult                         3
% 11.24/1.99  --comb_sup_mult                         2
% 11.24/1.99  --comb_inst_mult                        10
% 11.24/1.99  
% 11.24/1.99  ------ Debug Options
% 11.24/1.99  
% 11.24/1.99  --dbg_backtrace                         false
% 11.24/1.99  --dbg_dump_prop_clauses                 false
% 11.24/1.99  --dbg_dump_prop_clauses_file            -
% 11.24/1.99  --dbg_out_stat                          false
% 11.24/1.99  
% 11.24/1.99  
% 11.24/1.99  
% 11.24/1.99  
% 11.24/1.99  ------ Proving...
% 11.24/1.99  
% 11.24/1.99  
% 11.24/1.99  % SZS status Theorem for theBenchmark.p
% 11.24/1.99  
% 11.24/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 11.24/1.99  
% 11.24/1.99  fof(f17,axiom,(
% 11.24/1.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 11.24/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.24/1.99  
% 11.24/1.99  fof(f45,plain,(
% 11.24/1.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 11.24/1.99    inference(ennf_transformation,[],[f17])).
% 11.24/1.99  
% 11.24/1.99  fof(f46,plain,(
% 11.24/1.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.24/1.99    inference(flattening,[],[f45])).
% 11.24/1.99  
% 11.24/1.99  fof(f63,plain,(
% 11.24/1.99    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.24/1.99    inference(nnf_transformation,[],[f46])).
% 11.24/1.99  
% 11.24/1.99  fof(f91,plain,(
% 11.24/1.99    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.24/1.99    inference(cnf_transformation,[],[f63])).
% 11.24/1.99  
% 11.24/1.99  fof(f25,conjecture,(
% 11.24/1.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 11.24/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.24/1.99  
% 11.24/1.99  fof(f26,negated_conjecture,(
% 11.24/1.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 11.24/1.99    inference(negated_conjecture,[],[f25])).
% 11.24/1.99  
% 11.24/1.99  fof(f57,plain,(
% 11.24/1.99    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 11.24/1.99    inference(ennf_transformation,[],[f26])).
% 11.24/1.99  
% 11.24/1.99  fof(f58,plain,(
% 11.24/1.99    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 11.24/1.99    inference(flattening,[],[f57])).
% 11.24/1.99  
% 11.24/1.99  fof(f65,plain,(
% 11.24/1.99    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK4 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK4),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK4,X1,X0) & v1_funct_1(sK4))) )),
% 11.24/1.99    introduced(choice_axiom,[])).
% 11.24/1.99  
% 11.24/1.99  fof(f64,plain,(
% 11.24/1.99    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK3) != X3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & v2_funct_1(sK3) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,X3),k6_partfun1(sK1)) & k2_relset_1(sK1,sK2,sK3) = sK2 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(X3,sK2,sK1) & v1_funct_1(X3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 11.24/1.99    introduced(choice_axiom,[])).
% 11.24/1.99  
% 11.24/1.99  fof(f66,plain,(
% 11.24/1.99    (k2_funct_1(sK3) != sK4 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & v2_funct_1(sK3) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) & k2_relset_1(sK1,sK2,sK3) = sK2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 11.24/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f58,f65,f64])).
% 11.24/1.99  
% 11.24/1.99  fof(f112,plain,(
% 11.24/1.99    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1))),
% 11.24/1.99    inference(cnf_transformation,[],[f66])).
% 11.24/1.99  
% 11.24/1.99  fof(f18,axiom,(
% 11.24/1.99    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 11.24/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.24/1.99  
% 11.24/1.99  fof(f93,plain,(
% 11.24/1.99    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 11.24/1.99    inference(cnf_transformation,[],[f18])).
% 11.24/1.99  
% 11.24/1.99  fof(f21,axiom,(
% 11.24/1.99    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 11.24/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.24/1.99  
% 11.24/1.99  fof(f97,plain,(
% 11.24/1.99    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 11.24/1.99    inference(cnf_transformation,[],[f21])).
% 11.24/1.99  
% 11.24/1.99  fof(f124,plain,(
% 11.24/1.99    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 11.24/1.99    inference(definition_unfolding,[],[f93,f97])).
% 11.24/1.99  
% 11.24/1.99  fof(f105,plain,(
% 11.24/1.99    v1_funct_1(sK3)),
% 11.24/1.99    inference(cnf_transformation,[],[f66])).
% 11.24/1.99  
% 11.24/1.99  fof(f107,plain,(
% 11.24/1.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 11.24/1.99    inference(cnf_transformation,[],[f66])).
% 11.24/1.99  
% 11.24/1.99  fof(f108,plain,(
% 11.24/1.99    v1_funct_1(sK4)),
% 11.24/1.99    inference(cnf_transformation,[],[f66])).
% 11.24/1.99  
% 11.24/1.99  fof(f110,plain,(
% 11.24/1.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 11.24/1.99    inference(cnf_transformation,[],[f66])).
% 11.24/1.99  
% 11.24/1.99  fof(f19,axiom,(
% 11.24/1.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 11.24/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.24/1.99  
% 11.24/1.99  fof(f47,plain,(
% 11.24/1.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 11.24/1.99    inference(ennf_transformation,[],[f19])).
% 11.24/1.99  
% 11.24/1.99  fof(f48,plain,(
% 11.24/1.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 11.24/1.99    inference(flattening,[],[f47])).
% 11.24/1.99  
% 11.24/1.99  fof(f95,plain,(
% 11.24/1.99    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 11.24/1.99    inference(cnf_transformation,[],[f48])).
% 11.24/1.99  
% 11.24/1.99  fof(f111,plain,(
% 11.24/1.99    k2_relset_1(sK1,sK2,sK3) = sK2),
% 11.24/1.99    inference(cnf_transformation,[],[f66])).
% 11.24/1.99  
% 11.24/1.99  fof(f23,axiom,(
% 11.24/1.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 11.24/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.24/1.99  
% 11.24/1.99  fof(f53,plain,(
% 11.24/1.99    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 11.24/1.99    inference(ennf_transformation,[],[f23])).
% 11.24/1.99  
% 11.24/1.99  fof(f54,plain,(
% 11.24/1.99    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 11.24/1.99    inference(flattening,[],[f53])).
% 11.24/1.99  
% 11.24/1.99  fof(f101,plain,(
% 11.24/1.99    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X4) | k1_xboole_0 = X2 | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 11.24/1.99    inference(cnf_transformation,[],[f54])).
% 11.24/1.99  
% 11.24/1.99  fof(f106,plain,(
% 11.24/1.99    v1_funct_2(sK3,sK1,sK2)),
% 11.24/1.99    inference(cnf_transformation,[],[f66])).
% 11.24/1.99  
% 11.24/1.99  fof(f109,plain,(
% 11.24/1.99    v1_funct_2(sK4,sK2,sK1)),
% 11.24/1.99    inference(cnf_transformation,[],[f66])).
% 11.24/1.99  
% 11.24/1.99  fof(f114,plain,(
% 11.24/1.99    k1_xboole_0 != sK1),
% 11.24/1.99    inference(cnf_transformation,[],[f66])).
% 11.24/1.99  
% 11.24/1.99  fof(f3,axiom,(
% 11.24/1.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.24/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.24/1.99  
% 11.24/1.99  fof(f61,plain,(
% 11.24/1.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.24/1.99    inference(nnf_transformation,[],[f3])).
% 11.24/1.99  
% 11.24/1.99  fof(f62,plain,(
% 11.24/1.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.24/1.99    inference(flattening,[],[f61])).
% 11.24/1.99  
% 11.24/1.99  fof(f69,plain,(
% 11.24/1.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 11.24/1.99    inference(cnf_transformation,[],[f62])).
% 11.24/1.99  
% 11.24/1.99  fof(f126,plain,(
% 11.24/1.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.24/1.99    inference(equality_resolution,[],[f69])).
% 11.24/1.99  
% 11.24/1.99  fof(f71,plain,(
% 11.24/1.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 11.24/1.99    inference(cnf_transformation,[],[f62])).
% 11.24/1.99  
% 11.24/1.99  fof(f8,axiom,(
% 11.24/1.99    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 11.24/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.24/1.99  
% 11.24/1.99  fof(f79,plain,(
% 11.24/1.99    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 11.24/1.99    inference(cnf_transformation,[],[f8])).
% 11.24/1.99  
% 11.24/1.99  fof(f120,plain,(
% 11.24/1.99    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 11.24/1.99    inference(definition_unfolding,[],[f79,f97])).
% 11.24/1.99  
% 11.24/1.99  fof(f9,axiom,(
% 11.24/1.99    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 11.24/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.24/1.99  
% 11.24/1.99  fof(f33,plain,(
% 11.24/1.99    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.24/1.99    inference(ennf_transformation,[],[f9])).
% 11.24/1.99  
% 11.24/1.99  fof(f34,plain,(
% 11.24/1.99    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.24/1.99    inference(flattening,[],[f33])).
% 11.24/1.99  
% 11.24/1.99  fof(f82,plain,(
% 11.24/1.99    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.24/1.99    inference(cnf_transformation,[],[f34])).
% 11.24/1.99  
% 11.24/1.99  fof(f12,axiom,(
% 11.24/1.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 11.24/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.24/1.99  
% 11.24/1.99  fof(f39,plain,(
% 11.24/1.99    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.24/1.99    inference(ennf_transformation,[],[f12])).
% 11.24/1.99  
% 11.24/1.99  fof(f40,plain,(
% 11.24/1.99    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.24/1.99    inference(flattening,[],[f39])).
% 11.24/1.99  
% 11.24/1.99  fof(f86,plain,(
% 11.24/1.99    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.24/1.99    inference(cnf_transformation,[],[f40])).
% 11.24/1.99  
% 11.24/1.99  fof(f80,plain,(
% 11.24/1.99    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.24/1.99    inference(cnf_transformation,[],[f34])).
% 11.24/1.99  
% 11.24/1.99  fof(f81,plain,(
% 11.24/1.99    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.24/1.99    inference(cnf_transformation,[],[f34])).
% 11.24/1.99  
% 11.24/1.99  fof(f15,axiom,(
% 11.24/1.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 11.24/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.24/1.99  
% 11.24/1.99  fof(f43,plain,(
% 11.24/1.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.24/1.99    inference(ennf_transformation,[],[f15])).
% 11.24/1.99  
% 11.24/1.99  fof(f89,plain,(
% 11.24/1.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.24/1.99    inference(cnf_transformation,[],[f43])).
% 11.24/1.99  
% 11.24/1.99  fof(f10,axiom,(
% 11.24/1.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 11.24/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.24/1.99  
% 11.24/1.99  fof(f35,plain,(
% 11.24/1.99    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.24/1.99    inference(ennf_transformation,[],[f10])).
% 11.24/1.99  
% 11.24/1.99  fof(f36,plain,(
% 11.24/1.99    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.24/1.99    inference(flattening,[],[f35])).
% 11.24/1.99  
% 11.24/1.99  fof(f83,plain,(
% 11.24/1.99    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.24/1.99    inference(cnf_transformation,[],[f36])).
% 11.24/1.99  
% 11.24/1.99  fof(f16,axiom,(
% 11.24/1.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 11.24/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.24/1.99  
% 11.24/1.99  fof(f44,plain,(
% 11.24/1.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.24/1.99    inference(ennf_transformation,[],[f16])).
% 11.24/1.99  
% 11.24/1.99  fof(f90,plain,(
% 11.24/1.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.24/1.99    inference(cnf_transformation,[],[f44])).
% 11.24/1.99  
% 11.24/1.99  fof(f22,axiom,(
% 11.24/1.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 11.24/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.24/1.99  
% 11.24/1.99  fof(f51,plain,(
% 11.24/1.99    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 11.24/1.99    inference(ennf_transformation,[],[f22])).
% 11.24/1.99  
% 11.24/1.99  fof(f52,plain,(
% 11.24/1.99    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 11.24/1.99    inference(flattening,[],[f51])).
% 11.24/1.99  
% 11.24/1.99  fof(f98,plain,(
% 11.24/1.99    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 11.24/1.99    inference(cnf_transformation,[],[f52])).
% 11.24/1.99  
% 11.24/1.99  fof(f4,axiom,(
% 11.24/1.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)))))),
% 11.24/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.24/1.99  
% 11.24/1.99  fof(f28,plain,(
% 11.24/1.99    ! [X0] : (! [X1] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 11.24/1.99    inference(ennf_transformation,[],[f4])).
% 11.24/1.99  
% 11.24/1.99  fof(f29,plain,(
% 11.24/1.99    ! [X0] : (! [X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 11.24/1.99    inference(flattening,[],[f28])).
% 11.24/1.99  
% 11.24/1.99  fof(f72,plain,(
% 11.24/1.99    ( ! [X0,X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 11.24/1.99    inference(cnf_transformation,[],[f29])).
% 11.24/1.99  
% 11.24/1.99  fof(f24,axiom,(
% 11.24/1.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 11.24/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.24/1.99  
% 11.24/1.99  fof(f55,plain,(
% 11.24/1.99    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 11.24/1.99    inference(ennf_transformation,[],[f24])).
% 11.24/1.99  
% 11.24/1.99  fof(f56,plain,(
% 11.24/1.99    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 11.24/1.99    inference(flattening,[],[f55])).
% 11.24/1.99  
% 11.24/1.99  fof(f103,plain,(
% 11.24/1.99    ( ! [X2,X0,X1] : (k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 11.24/1.99    inference(cnf_transformation,[],[f56])).
% 11.24/1.99  
% 11.24/1.99  fof(f84,plain,(
% 11.24/1.99    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.24/1.99    inference(cnf_transformation,[],[f36])).
% 11.24/1.99  
% 11.24/1.99  fof(f5,axiom,(
% 11.24/1.99    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 11.24/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.24/1.99  
% 11.24/1.99  fof(f74,plain,(
% 11.24/1.99    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 11.24/1.99    inference(cnf_transformation,[],[f5])).
% 11.24/1.99  
% 11.24/1.99  fof(f117,plain,(
% 11.24/1.99    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 11.24/1.99    inference(definition_unfolding,[],[f74,f97])).
% 11.24/1.99  
% 11.24/1.99  fof(f7,axiom,(
% 11.24/1.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 11.24/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.24/1.99  
% 11.24/1.99  fof(f31,plain,(
% 11.24/1.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.24/1.99    inference(ennf_transformation,[],[f7])).
% 11.24/1.99  
% 11.24/1.99  fof(f32,plain,(
% 11.24/1.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.24/1.99    inference(flattening,[],[f31])).
% 11.24/1.99  
% 11.24/1.99  fof(f76,plain,(
% 11.24/1.99    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.24/1.99    inference(cnf_transformation,[],[f32])).
% 11.24/1.99  
% 11.24/1.99  fof(f20,axiom,(
% 11.24/1.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 11.24/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.24/1.99  
% 11.24/1.99  fof(f49,plain,(
% 11.24/1.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 11.24/1.99    inference(ennf_transformation,[],[f20])).
% 11.24/1.99  
% 11.24/1.99  fof(f50,plain,(
% 11.24/1.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 11.24/1.99    inference(flattening,[],[f49])).
% 11.24/1.99  
% 11.24/1.99  fof(f96,plain,(
% 11.24/1.99    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 11.24/1.99    inference(cnf_transformation,[],[f50])).
% 11.24/1.99  
% 11.24/1.99  fof(f11,axiom,(
% 11.24/1.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 11.24/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.24/1.99  
% 11.24/1.99  fof(f37,plain,(
% 11.24/1.99    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.24/1.99    inference(ennf_transformation,[],[f11])).
% 11.24/1.99  
% 11.24/1.99  fof(f38,plain,(
% 11.24/1.99    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.24/1.99    inference(flattening,[],[f37])).
% 11.24/1.99  
% 11.24/1.99  fof(f85,plain,(
% 11.24/1.99    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.24/1.99    inference(cnf_transformation,[],[f38])).
% 11.24/1.99  
% 11.24/1.99  fof(f122,plain,(
% 11.24/1.99    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.24/1.99    inference(definition_unfolding,[],[f85,f97])).
% 11.24/1.99  
% 11.24/1.99  fof(f113,plain,(
% 11.24/1.99    v2_funct_1(sK3)),
% 11.24/1.99    inference(cnf_transformation,[],[f66])).
% 11.24/1.99  
% 11.24/1.99  fof(f77,plain,(
% 11.24/1.99    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.24/1.99    inference(cnf_transformation,[],[f32])).
% 11.24/1.99  
% 11.24/1.99  fof(f13,axiom,(
% 11.24/1.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & v2_funct_1(X0)) => k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) = k2_funct_1(k5_relat_1(X0,X1)))))),
% 11.24/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.24/1.99  
% 11.24/1.99  fof(f41,plain,(
% 11.24/1.99    ! [X0] : (! [X1] : ((k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) = k2_funct_1(k5_relat_1(X0,X1)) | (~v2_funct_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.24/1.99    inference(ennf_transformation,[],[f13])).
% 11.24/1.99  
% 11.24/1.99  fof(f42,plain,(
% 11.24/1.99    ! [X0] : (! [X1] : (k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) = k2_funct_1(k5_relat_1(X0,X1)) | ~v2_funct_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.24/1.99    inference(flattening,[],[f41])).
% 11.24/1.99  
% 11.24/1.99  fof(f87,plain,(
% 11.24/1.99    ( ! [X0,X1] : (k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) = k2_funct_1(k5_relat_1(X0,X1)) | ~v2_funct_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.24/1.99    inference(cnf_transformation,[],[f42])).
% 11.24/1.99  
% 11.24/1.99  fof(f14,axiom,(
% 11.24/1.99    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))),
% 11.24/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.24/1.99  
% 11.24/1.99  fof(f88,plain,(
% 11.24/1.99    ( ! [X0] : (k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))) )),
% 11.24/1.99    inference(cnf_transformation,[],[f14])).
% 11.24/1.99  
% 11.24/1.99  fof(f123,plain,(
% 11.24/1.99    ( ! [X0] : (k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0)) )),
% 11.24/1.99    inference(definition_unfolding,[],[f88,f97,f97])).
% 11.24/1.99  
% 11.24/1.99  fof(f115,plain,(
% 11.24/1.99    k1_xboole_0 != sK2),
% 11.24/1.99    inference(cnf_transformation,[],[f66])).
% 11.24/1.99  
% 11.24/1.99  fof(f116,plain,(
% 11.24/1.99    k2_funct_1(sK3) != sK4),
% 11.24/1.99    inference(cnf_transformation,[],[f66])).
% 11.24/1.99  
% 11.24/1.99  cnf(c_25,plain,
% 11.24/1.99      ( ~ r2_relset_1(X0,X1,X2,X3)
% 11.24/1.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.24/1.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.24/1.99      | X3 = X2 ),
% 11.24/1.99      inference(cnf_transformation,[],[f91]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_41,negated_conjecture,
% 11.24/1.99      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) ),
% 11.24/1.99      inference(cnf_transformation,[],[f112]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_512,plain,
% 11.24/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.24/1.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.24/1.99      | X3 = X0
% 11.24/1.99      | k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) != X0
% 11.24/1.99      | k6_partfun1(sK1) != X3
% 11.24/1.99      | sK1 != X2
% 11.24/1.99      | sK1 != X1 ),
% 11.24/1.99      inference(resolution_lifted,[status(thm)],[c_25,c_41]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_513,plain,
% 11.24/1.99      ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 11.24/1.99      | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 11.24/1.99      | k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
% 11.24/1.99      inference(unflattening,[status(thm)],[c_512]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_26,plain,
% 11.24/1.99      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 11.24/1.99      inference(cnf_transformation,[],[f124]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_521,plain,
% 11.24/1.99      ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 11.24/1.99      | k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
% 11.24/1.99      inference(forward_subsumption_resolution,
% 11.24/1.99                [status(thm)],
% 11.24/1.99                [c_513,c_26]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_1414,plain,
% 11.24/1.99      ( k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 11.24/1.99      | m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
% 11.24/1.99      inference(predicate_to_equality,[status(thm)],[c_521]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_48,negated_conjecture,
% 11.24/1.99      ( v1_funct_1(sK3) ),
% 11.24/1.99      inference(cnf_transformation,[],[f105]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_46,negated_conjecture,
% 11.24/1.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 11.24/1.99      inference(cnf_transformation,[],[f107]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_45,negated_conjecture,
% 11.24/1.99      ( v1_funct_1(sK4) ),
% 11.24/1.99      inference(cnf_transformation,[],[f108]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_43,negated_conjecture,
% 11.24/1.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 11.24/1.99      inference(cnf_transformation,[],[f110]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_27,plain,
% 11.24/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.24/1.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 11.24/1.99      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 11.24/1.99      | ~ v1_funct_1(X0)
% 11.24/1.99      | ~ v1_funct_1(X3) ),
% 11.24/1.99      inference(cnf_transformation,[],[f95]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_1848,plain,
% 11.24/1.99      ( m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 11.24/1.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 11.24/1.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 11.24/1.99      | ~ v1_funct_1(sK4)
% 11.24/1.99      | ~ v1_funct_1(sK3) ),
% 11.24/1.99      inference(instantiation,[status(thm)],[c_27]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_2433,plain,
% 11.24/1.99      ( k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
% 11.24/1.99      inference(global_propositional_subsumption,
% 11.24/1.99                [status(thm)],
% 11.24/1.99                [c_1414,c_48,c_46,c_45,c_43,c_521,c_1848]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_42,negated_conjecture,
% 11.24/1.99      ( k2_relset_1(sK1,sK2,sK3) = sK2 ),
% 11.24/1.99      inference(cnf_transformation,[],[f111]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_32,plain,
% 11.24/1.99      ( ~ v1_funct_2(X0,X1,X2)
% 11.24/1.99      | ~ v1_funct_2(X3,X4,X1)
% 11.24/1.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 11.24/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.24/1.99      | v2_funct_1(X0)
% 11.24/1.99      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 11.24/1.99      | ~ v1_funct_1(X0)
% 11.24/1.99      | ~ v1_funct_1(X3)
% 11.24/1.99      | k2_relset_1(X4,X1,X3) != X1
% 11.24/1.99      | k1_xboole_0 = X2 ),
% 11.24/1.99      inference(cnf_transformation,[],[f101]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_1427,plain,
% 11.24/1.99      ( k2_relset_1(X0,X1,X2) != X1
% 11.24/1.99      | k1_xboole_0 = X3
% 11.24/1.99      | v1_funct_2(X4,X1,X3) != iProver_top
% 11.24/1.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 11.24/1.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
% 11.24/1.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.24/1.99      | v2_funct_1(X4) = iProver_top
% 11.24/1.99      | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top
% 11.24/1.99      | v1_funct_1(X4) != iProver_top
% 11.24/1.99      | v1_funct_1(X2) != iProver_top ),
% 11.24/1.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_5642,plain,
% 11.24/1.99      ( k1_xboole_0 = X0
% 11.24/1.99      | v1_funct_2(X1,sK2,X0) != iProver_top
% 11.24/1.99      | v1_funct_2(sK3,sK1,sK2) != iProver_top
% 11.24/1.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
% 11.24/1.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 11.24/1.99      | v2_funct_1(X1) = iProver_top
% 11.24/1.99      | v2_funct_1(k1_partfun1(sK1,sK2,sK2,X0,sK3,X1)) != iProver_top
% 11.24/1.99      | v1_funct_1(X1) != iProver_top
% 11.24/1.99      | v1_funct_1(sK3) != iProver_top ),
% 11.24/1.99      inference(superposition,[status(thm)],[c_42,c_1427]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_49,plain,
% 11.24/1.99      ( v1_funct_1(sK3) = iProver_top ),
% 11.24/1.99      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_47,negated_conjecture,
% 11.24/1.99      ( v1_funct_2(sK3,sK1,sK2) ),
% 11.24/1.99      inference(cnf_transformation,[],[f106]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_50,plain,
% 11.24/1.99      ( v1_funct_2(sK3,sK1,sK2) = iProver_top ),
% 11.24/1.99      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_51,plain,
% 11.24/1.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 11.24/1.99      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_7201,plain,
% 11.24/1.99      ( v1_funct_1(X1) != iProver_top
% 11.24/1.99      | v2_funct_1(k1_partfun1(sK1,sK2,sK2,X0,sK3,X1)) != iProver_top
% 11.24/1.99      | v2_funct_1(X1) = iProver_top
% 11.24/1.99      | v1_funct_2(X1,sK2,X0) != iProver_top
% 11.24/1.99      | k1_xboole_0 = X0
% 11.24/1.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top ),
% 11.24/1.99      inference(global_propositional_subsumption,
% 11.24/1.99                [status(thm)],
% 11.24/1.99                [c_5642,c_49,c_50,c_51]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_7202,plain,
% 11.24/1.99      ( k1_xboole_0 = X0
% 11.24/1.99      | v1_funct_2(X1,sK2,X0) != iProver_top
% 11.24/1.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
% 11.24/1.99      | v2_funct_1(X1) = iProver_top
% 11.24/1.99      | v2_funct_1(k1_partfun1(sK1,sK2,sK2,X0,sK3,X1)) != iProver_top
% 11.24/1.99      | v1_funct_1(X1) != iProver_top ),
% 11.24/1.99      inference(renaming,[status(thm)],[c_7201]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_7205,plain,
% 11.24/1.99      ( sK1 = k1_xboole_0
% 11.24/1.99      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 11.24/1.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 11.24/1.99      | v2_funct_1(k6_partfun1(sK1)) != iProver_top
% 11.24/1.99      | v2_funct_1(sK4) = iProver_top
% 11.24/1.99      | v1_funct_1(sK4) != iProver_top ),
% 11.24/1.99      inference(superposition,[status(thm)],[c_2433,c_7202]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_52,plain,
% 11.24/1.99      ( v1_funct_1(sK4) = iProver_top ),
% 11.24/1.99      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_44,negated_conjecture,
% 11.24/1.99      ( v1_funct_2(sK4,sK2,sK1) ),
% 11.24/1.99      inference(cnf_transformation,[],[f109]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_53,plain,
% 11.24/1.99      ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
% 11.24/1.99      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_54,plain,
% 11.24/1.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 11.24/1.99      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_39,negated_conjecture,
% 11.24/1.99      ( k1_xboole_0 != sK1 ),
% 11.24/1.99      inference(cnf_transformation,[],[f114]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_4,plain,
% 11.24/1.99      ( r1_tarski(X0,X0) ),
% 11.24/1.99      inference(cnf_transformation,[],[f126]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_144,plain,
% 11.24/1.99      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 11.24/1.99      inference(instantiation,[status(thm)],[c_4]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_2,plain,
% 11.24/1.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 11.24/1.99      inference(cnf_transformation,[],[f71]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_148,plain,
% 11.24/1.99      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 11.24/1.99      | k1_xboole_0 = k1_xboole_0 ),
% 11.24/1.99      inference(instantiation,[status(thm)],[c_2]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_823,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_1546,plain,
% 11.24/1.99      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 11.24/1.99      inference(instantiation,[status(thm)],[c_823]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_1547,plain,
% 11.24/1.99      ( sK1 != k1_xboole_0
% 11.24/1.99      | k1_xboole_0 = sK1
% 11.24/1.99      | k1_xboole_0 != k1_xboole_0 ),
% 11.24/1.99      inference(instantiation,[status(thm)],[c_1546]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_11,plain,
% 11.24/1.99      ( v2_funct_1(k6_partfun1(X0)) ),
% 11.24/1.99      inference(cnf_transformation,[],[f120]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_2917,plain,
% 11.24/1.99      ( v2_funct_1(k6_partfun1(sK1)) ),
% 11.24/1.99      inference(instantiation,[status(thm)],[c_11]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_2918,plain,
% 11.24/1.99      ( v2_funct_1(k6_partfun1(sK1)) = iProver_top ),
% 11.24/1.99      inference(predicate_to_equality,[status(thm)],[c_2917]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_8416,plain,
% 11.24/1.99      ( v2_funct_1(sK4) = iProver_top ),
% 11.24/1.99      inference(global_propositional_subsumption,
% 11.24/1.99                [status(thm)],
% 11.24/1.99                [c_7205,c_52,c_53,c_54,c_39,c_144,c_148,c_1547,c_2918]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_13,plain,
% 11.24/1.99      ( ~ v2_funct_1(X0)
% 11.24/1.99      | v2_funct_1(k2_funct_1(X0))
% 11.24/1.99      | ~ v1_funct_1(X0)
% 11.24/1.99      | ~ v1_relat_1(X0) ),
% 11.24/1.99      inference(cnf_transformation,[],[f82]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_1440,plain,
% 11.24/1.99      ( v2_funct_1(X0) != iProver_top
% 11.24/1.99      | v2_funct_1(k2_funct_1(X0)) = iProver_top
% 11.24/1.99      | v1_funct_1(X0) != iProver_top
% 11.24/1.99      | v1_relat_1(X0) != iProver_top ),
% 11.24/1.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_19,plain,
% 11.24/1.99      ( ~ v2_funct_1(X0)
% 11.24/1.99      | ~ v1_funct_1(X0)
% 11.24/1.99      | ~ v1_relat_1(X0)
% 11.24/1.99      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 11.24/1.99      inference(cnf_transformation,[],[f86]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_1436,plain,
% 11.24/1.99      ( k2_funct_1(k2_funct_1(X0)) = X0
% 11.24/1.99      | v2_funct_1(X0) != iProver_top
% 11.24/1.99      | v1_funct_1(X0) != iProver_top
% 11.24/1.99      | v1_relat_1(X0) != iProver_top ),
% 11.24/1.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_3365,plain,
% 11.24/1.99      ( k2_funct_1(k2_funct_1(k2_funct_1(X0))) = k2_funct_1(X0)
% 11.24/1.99      | v2_funct_1(X0) != iProver_top
% 11.24/1.99      | v1_funct_1(X0) != iProver_top
% 11.24/1.99      | v1_funct_1(k2_funct_1(X0)) != iProver_top
% 11.24/1.99      | v1_relat_1(X0) != iProver_top
% 11.24/1.99      | v1_relat_1(k2_funct_1(X0)) != iProver_top ),
% 11.24/1.99      inference(superposition,[status(thm)],[c_1440,c_1436]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_15,plain,
% 11.24/1.99      ( ~ v2_funct_1(X0)
% 11.24/1.99      | ~ v1_funct_1(X0)
% 11.24/1.99      | ~ v1_relat_1(X0)
% 11.24/1.99      | v1_relat_1(k2_funct_1(X0)) ),
% 11.24/1.99      inference(cnf_transformation,[],[f80]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_114,plain,
% 11.24/1.99      ( v2_funct_1(X0) != iProver_top
% 11.24/1.99      | v1_funct_1(X0) != iProver_top
% 11.24/1.99      | v1_relat_1(X0) != iProver_top
% 11.24/1.99      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 11.24/1.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_14,plain,
% 11.24/1.99      ( ~ v2_funct_1(X0)
% 11.24/1.99      | ~ v1_funct_1(X0)
% 11.24/1.99      | v1_funct_1(k2_funct_1(X0))
% 11.24/1.99      | ~ v1_relat_1(X0) ),
% 11.24/1.99      inference(cnf_transformation,[],[f81]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_117,plain,
% 11.24/1.99      ( v2_funct_1(X0) != iProver_top
% 11.24/1.99      | v1_funct_1(X0) != iProver_top
% 11.24/1.99      | v1_funct_1(k2_funct_1(X0)) = iProver_top
% 11.24/1.99      | v1_relat_1(X0) != iProver_top ),
% 11.24/1.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_10831,plain,
% 11.24/1.99      ( v1_relat_1(X0) != iProver_top
% 11.24/1.99      | k2_funct_1(k2_funct_1(k2_funct_1(X0))) = k2_funct_1(X0)
% 11.24/1.99      | v2_funct_1(X0) != iProver_top
% 11.24/1.99      | v1_funct_1(X0) != iProver_top ),
% 11.24/1.99      inference(global_propositional_subsumption,
% 11.24/1.99                [status(thm)],
% 11.24/1.99                [c_3365,c_114,c_117]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_10832,plain,
% 11.24/1.99      ( k2_funct_1(k2_funct_1(k2_funct_1(X0))) = k2_funct_1(X0)
% 11.24/1.99      | v2_funct_1(X0) != iProver_top
% 11.24/1.99      | v1_funct_1(X0) != iProver_top
% 11.24/1.99      | v1_relat_1(X0) != iProver_top ),
% 11.24/1.99      inference(renaming,[status(thm)],[c_10831]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_10838,plain,
% 11.24/1.99      ( k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X0)))) = k2_funct_1(k2_funct_1(X0))
% 11.24/1.99      | v2_funct_1(X0) != iProver_top
% 11.24/1.99      | v1_funct_1(X0) != iProver_top
% 11.24/1.99      | v1_funct_1(k2_funct_1(X0)) != iProver_top
% 11.24/1.99      | v1_relat_1(X0) != iProver_top
% 11.24/1.99      | v1_relat_1(k2_funct_1(X0)) != iProver_top ),
% 11.24/1.99      inference(superposition,[status(thm)],[c_1440,c_10832]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_27473,plain,
% 11.24/1.99      ( v1_relat_1(X0) != iProver_top
% 11.24/1.99      | k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X0)))) = k2_funct_1(k2_funct_1(X0))
% 11.24/1.99      | v2_funct_1(X0) != iProver_top
% 11.24/1.99      | v1_funct_1(X0) != iProver_top ),
% 11.24/1.99      inference(global_propositional_subsumption,
% 11.24/1.99                [status(thm)],
% 11.24/1.99                [c_10838,c_114,c_117]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_27474,plain,
% 11.24/1.99      ( k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(X0)))) = k2_funct_1(k2_funct_1(X0))
% 11.24/1.99      | v2_funct_1(X0) != iProver_top
% 11.24/1.99      | v1_funct_1(X0) != iProver_top
% 11.24/1.99      | v1_relat_1(X0) != iProver_top ),
% 11.24/1.99      inference(renaming,[status(thm)],[c_27473]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_27482,plain,
% 11.24/1.99      ( k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK4)))) = k2_funct_1(k2_funct_1(sK4))
% 11.24/1.99      | v1_funct_1(sK4) != iProver_top
% 11.24/1.99      | v1_relat_1(sK4) != iProver_top ),
% 11.24/1.99      inference(superposition,[status(thm)],[c_8416,c_27474]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_8422,plain,
% 11.24/1.99      ( k2_funct_1(k2_funct_1(sK4)) = sK4
% 11.24/1.99      | v1_funct_1(sK4) != iProver_top
% 11.24/1.99      | v1_relat_1(sK4) != iProver_top ),
% 11.24/1.99      inference(superposition,[status(thm)],[c_8416,c_1436]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_22,plain,
% 11.24/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.24/1.99      | v1_relat_1(X0) ),
% 11.24/1.99      inference(cnf_transformation,[],[f89]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_1570,plain,
% 11.24/1.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.24/1.99      | v1_relat_1(sK4) ),
% 11.24/1.99      inference(instantiation,[status(thm)],[c_22]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_1870,plain,
% 11.24/1.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 11.24/1.99      | v1_relat_1(sK4) ),
% 11.24/1.99      inference(instantiation,[status(thm)],[c_1570]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_1871,plain,
% 11.24/1.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 11.24/1.99      | v1_relat_1(sK4) = iProver_top ),
% 11.24/1.99      inference(predicate_to_equality,[status(thm)],[c_1870]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_5668,plain,
% 11.24/1.99      ( ~ v2_funct_1(sK4)
% 11.24/1.99      | ~ v1_funct_1(sK4)
% 11.24/1.99      | ~ v1_relat_1(sK4)
% 11.24/1.99      | k2_funct_1(k2_funct_1(sK4)) = sK4 ),
% 11.24/1.99      inference(instantiation,[status(thm)],[c_19]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_5669,plain,
% 11.24/1.99      ( k2_funct_1(k2_funct_1(sK4)) = sK4
% 11.24/1.99      | v2_funct_1(sK4) != iProver_top
% 11.24/1.99      | v1_funct_1(sK4) != iProver_top
% 11.24/1.99      | v1_relat_1(sK4) != iProver_top ),
% 11.24/1.99      inference(predicate_to_equality,[status(thm)],[c_5668]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_8725,plain,
% 11.24/1.99      ( k2_funct_1(k2_funct_1(sK4)) = sK4 ),
% 11.24/1.99      inference(global_propositional_subsumption,
% 11.24/1.99                [status(thm)],
% 11.24/1.99                [c_8422,c_52,c_53,c_54,c_39,c_144,c_148,c_1547,c_1871,
% 11.24/1.99                 c_2918,c_5669,c_7205]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_17,plain,
% 11.24/1.99      ( ~ v2_funct_1(X0)
% 11.24/1.99      | ~ v1_funct_1(X0)
% 11.24/1.99      | ~ v1_relat_1(X0)
% 11.24/1.99      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 11.24/1.99      inference(cnf_transformation,[],[f83]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_1438,plain,
% 11.24/1.99      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 11.24/1.99      | v2_funct_1(X0) != iProver_top
% 11.24/1.99      | v1_funct_1(X0) != iProver_top
% 11.24/1.99      | v1_relat_1(X0) != iProver_top ),
% 11.24/1.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_8421,plain,
% 11.24/1.99      ( k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4)
% 11.24/1.99      | v1_funct_1(sK4) != iProver_top
% 11.24/1.99      | v1_relat_1(sK4) != iProver_top ),
% 11.24/1.99      inference(superposition,[status(thm)],[c_8416,c_1438]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_1421,plain,
% 11.24/1.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 11.24/1.99      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_23,plain,
% 11.24/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.24/1.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 11.24/1.99      inference(cnf_transformation,[],[f90]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_1433,plain,
% 11.24/1.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 11.24/1.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 11.24/1.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_2834,plain,
% 11.24/1.99      ( k2_relset_1(sK2,sK1,sK4) = k2_relat_1(sK4) ),
% 11.24/1.99      inference(superposition,[status(thm)],[c_1421,c_1433]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_30,plain,
% 11.24/1.99      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 11.24/1.99      | ~ v1_funct_2(X2,X0,X1)
% 11.24/1.99      | ~ v1_funct_2(X3,X1,X0)
% 11.24/1.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 11.24/1.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.24/1.99      | ~ v1_funct_1(X2)
% 11.24/1.99      | ~ v1_funct_1(X3)
% 11.24/1.99      | k2_relset_1(X1,X0,X3) = X0 ),
% 11.24/1.99      inference(cnf_transformation,[],[f98]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_525,plain,
% 11.24/1.99      ( ~ v1_funct_2(X0,X1,X2)
% 11.24/1.99      | ~ v1_funct_2(X3,X2,X1)
% 11.24/1.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 11.24/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.24/1.99      | ~ v1_funct_1(X0)
% 11.24/1.99      | ~ v1_funct_1(X3)
% 11.24/1.99      | k1_partfun1(X2,X1,X1,X2,X3,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 11.24/1.99      | k2_relset_1(X1,X2,X0) = X2
% 11.24/1.99      | k6_partfun1(X2) != k6_partfun1(sK1)
% 11.24/1.99      | sK1 != X2 ),
% 11.24/1.99      inference(resolution_lifted,[status(thm)],[c_30,c_41]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_526,plain,
% 11.24/1.99      ( ~ v1_funct_2(X0,X1,sK1)
% 11.24/1.99      | ~ v1_funct_2(X2,sK1,X1)
% 11.24/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 11.24/1.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
% 11.24/1.99      | ~ v1_funct_1(X0)
% 11.24/1.99      | ~ v1_funct_1(X2)
% 11.24/1.99      | k1_partfun1(sK1,X1,X1,sK1,X2,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 11.24/1.99      | k2_relset_1(X1,sK1,X0) = sK1
% 11.24/1.99      | k6_partfun1(sK1) != k6_partfun1(sK1) ),
% 11.24/1.99      inference(unflattening,[status(thm)],[c_525]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_616,plain,
% 11.24/1.99      ( ~ v1_funct_2(X0,X1,sK1)
% 11.24/1.99      | ~ v1_funct_2(X2,sK1,X1)
% 11.24/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 11.24/1.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
% 11.24/1.99      | ~ v1_funct_1(X0)
% 11.24/1.99      | ~ v1_funct_1(X2)
% 11.24/1.99      | k1_partfun1(sK1,X1,X1,sK1,X2,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 11.24/1.99      | k2_relset_1(X1,sK1,X0) = sK1 ),
% 11.24/1.99      inference(equality_resolution_simp,[status(thm)],[c_526]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_1413,plain,
% 11.24/1.99      ( k1_partfun1(sK1,X0,X0,sK1,X1,X2) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 11.24/1.99      | k2_relset_1(X0,sK1,X2) = sK1
% 11.24/1.99      | v1_funct_2(X2,X0,sK1) != iProver_top
% 11.24/1.99      | v1_funct_2(X1,sK1,X0) != iProver_top
% 11.24/1.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 11.24/1.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 11.24/1.99      | v1_funct_1(X2) != iProver_top
% 11.24/1.99      | v1_funct_1(X1) != iProver_top ),
% 11.24/1.99      inference(predicate_to_equality,[status(thm)],[c_616]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_2436,plain,
% 11.24/1.99      ( k1_partfun1(sK1,X0,X0,sK1,X1,X2) != k6_partfun1(sK1)
% 11.24/1.99      | k2_relset_1(X0,sK1,X2) = sK1
% 11.24/1.99      | v1_funct_2(X2,X0,sK1) != iProver_top
% 11.24/1.99      | v1_funct_2(X1,sK1,X0) != iProver_top
% 11.24/1.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 11.24/1.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 11.24/1.99      | v1_funct_1(X2) != iProver_top
% 11.24/1.99      | v1_funct_1(X1) != iProver_top ),
% 11.24/1.99      inference(light_normalisation,[status(thm)],[c_1413,c_2433]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_2440,plain,
% 11.24/1.99      ( k2_relset_1(sK2,sK1,sK4) = sK1
% 11.24/1.99      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 11.24/1.99      | v1_funct_2(sK3,sK1,sK2) != iProver_top
% 11.24/1.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 11.24/1.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 11.24/1.99      | v1_funct_1(sK4) != iProver_top
% 11.24/1.99      | v1_funct_1(sK3) != iProver_top ),
% 11.24/1.99      inference(superposition,[status(thm)],[c_2433,c_2436]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_2479,plain,
% 11.24/1.99      ( k2_relset_1(sK2,sK1,sK4) = sK1 ),
% 11.24/1.99      inference(global_propositional_subsumption,
% 11.24/1.99                [status(thm)],
% 11.24/1.99                [c_2440,c_49,c_50,c_51,c_52,c_53,c_54]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_2837,plain,
% 11.24/1.99      ( k2_relat_1(sK4) = sK1 ),
% 11.24/1.99      inference(light_normalisation,[status(thm)],[c_2834,c_2479]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_8424,plain,
% 11.24/1.99      ( k1_relat_1(k2_funct_1(sK4)) = sK1
% 11.24/1.99      | v1_funct_1(sK4) != iProver_top
% 11.24/1.99      | v1_relat_1(sK4) != iProver_top ),
% 11.24/1.99      inference(light_normalisation,[status(thm)],[c_8421,c_2837]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_13177,plain,
% 11.24/1.99      ( k1_relat_1(k2_funct_1(sK4)) = sK1 ),
% 11.24/1.99      inference(global_propositional_subsumption,
% 11.24/1.99                [status(thm)],
% 11.24/1.99                [c_8424,c_52,c_54,c_1871]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_5,plain,
% 11.24/1.99      ( ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
% 11.24/1.99      | ~ v1_relat_1(X1)
% 11.24/1.99      | ~ v1_relat_1(X0)
% 11.24/1.99      | k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) ),
% 11.24/1.99      inference(cnf_transformation,[],[f72]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_1446,plain,
% 11.24/1.99      ( k2_relat_1(k5_relat_1(X0,X1)) = k2_relat_1(X1)
% 11.24/1.99      | r1_tarski(k1_relat_1(X1),k2_relat_1(X0)) != iProver_top
% 11.24/1.99      | v1_relat_1(X1) != iProver_top
% 11.24/1.99      | v1_relat_1(X0) != iProver_top ),
% 11.24/1.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_3445,plain,
% 11.24/1.99      ( k2_relat_1(k5_relat_1(sK4,X0)) = k2_relat_1(X0)
% 11.24/1.99      | r1_tarski(k1_relat_1(X0),sK1) != iProver_top
% 11.24/1.99      | v1_relat_1(X0) != iProver_top
% 11.24/1.99      | v1_relat_1(sK4) != iProver_top ),
% 11.24/1.99      inference(superposition,[status(thm)],[c_2837,c_1446]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_5582,plain,
% 11.24/1.99      ( v1_relat_1(X0) != iProver_top
% 11.24/1.99      | r1_tarski(k1_relat_1(X0),sK1) != iProver_top
% 11.24/1.99      | k2_relat_1(k5_relat_1(sK4,X0)) = k2_relat_1(X0) ),
% 11.24/1.99      inference(global_propositional_subsumption,
% 11.24/1.99                [status(thm)],
% 11.24/1.99                [c_3445,c_54,c_1871]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_5583,plain,
% 11.24/1.99      ( k2_relat_1(k5_relat_1(sK4,X0)) = k2_relat_1(X0)
% 11.24/1.99      | r1_tarski(k1_relat_1(X0),sK1) != iProver_top
% 11.24/1.99      | v1_relat_1(X0) != iProver_top ),
% 11.24/1.99      inference(renaming,[status(thm)],[c_5582]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_13181,plain,
% 11.24/1.99      ( k2_relat_1(k5_relat_1(sK4,k2_funct_1(sK4))) = k2_relat_1(k2_funct_1(sK4))
% 11.24/1.99      | r1_tarski(sK1,sK1) != iProver_top
% 11.24/1.99      | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
% 11.24/1.99      inference(superposition,[status(thm)],[c_13177,c_5583]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_36,plain,
% 11.24/1.99      ( ~ v1_funct_2(X0,X1,X2)
% 11.24/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.24/1.99      | ~ v2_funct_1(X0)
% 11.24/1.99      | ~ v1_funct_1(X0)
% 11.24/1.99      | k2_relset_1(X1,X2,X0) != X2
% 11.24/1.99      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 11.24/1.99      | k1_xboole_0 = X2 ),
% 11.24/1.99      inference(cnf_transformation,[],[f103]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_1423,plain,
% 11.24/1.99      ( k2_relset_1(X0,X1,X2) != X1
% 11.24/1.99      | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
% 11.24/1.99      | k1_xboole_0 = X1
% 11.24/1.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 11.24/1.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.24/1.99      | v2_funct_1(X2) != iProver_top
% 11.24/1.99      | v1_funct_1(X2) != iProver_top ),
% 11.24/1.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_2981,plain,
% 11.24/1.99      ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(sK2)
% 11.24/1.99      | sK1 = k1_xboole_0
% 11.24/1.99      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 11.24/1.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 11.24/1.99      | v2_funct_1(sK4) != iProver_top
% 11.24/1.99      | v1_funct_1(sK4) != iProver_top ),
% 11.24/1.99      inference(superposition,[status(thm)],[c_2479,c_1423]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_3117,plain,
% 11.24/1.99      ( v2_funct_1(sK4) != iProver_top
% 11.24/1.99      | k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(sK2) ),
% 11.24/1.99      inference(global_propositional_subsumption,
% 11.24/1.99                [status(thm)],
% 11.24/1.99                [c_2981,c_52,c_53,c_54,c_39,c_144,c_148,c_1547]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_3118,plain,
% 11.24/1.99      ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(sK2)
% 11.24/1.99      | v2_funct_1(sK4) != iProver_top ),
% 11.24/1.99      inference(renaming,[status(thm)],[c_3117]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_8423,plain,
% 11.24/1.99      ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(sK2) ),
% 11.24/1.99      inference(superposition,[status(thm)],[c_8416,c_3118]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_16,plain,
% 11.24/1.99      ( ~ v2_funct_1(X0)
% 11.24/1.99      | ~ v1_funct_1(X0)
% 11.24/1.99      | ~ v1_relat_1(X0)
% 11.24/1.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 11.24/1.99      inference(cnf_transformation,[],[f84]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_1439,plain,
% 11.24/1.99      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 11.24/1.99      | v2_funct_1(X0) != iProver_top
% 11.24/1.99      | v1_funct_1(X0) != iProver_top
% 11.24/1.99      | v1_relat_1(X0) != iProver_top ),
% 11.24/1.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_8420,plain,
% 11.24/1.99      ( k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4)
% 11.24/1.99      | v1_funct_1(sK4) != iProver_top
% 11.24/1.99      | v1_relat_1(sK4) != iProver_top ),
% 11.24/1.99      inference(superposition,[status(thm)],[c_8416,c_1439]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_8779,plain,
% 11.24/1.99      ( k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
% 11.24/1.99      inference(global_propositional_subsumption,
% 11.24/1.99                [status(thm)],
% 11.24/1.99                [c_8420,c_52,c_54,c_1871]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_13190,plain,
% 11.24/1.99      ( k2_relat_1(k6_partfun1(sK2)) = k1_relat_1(sK4)
% 11.24/1.99      | r1_tarski(sK1,sK1) != iProver_top
% 11.24/1.99      | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
% 11.24/1.99      inference(light_normalisation,
% 11.24/1.99                [status(thm)],
% 11.24/1.99                [c_13181,c_8423,c_8779]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_6,plain,
% 11.24/1.99      ( k2_relat_1(k6_partfun1(X0)) = X0 ),
% 11.24/1.99      inference(cnf_transformation,[],[f117]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_13191,plain,
% 11.24/1.99      ( k1_relat_1(sK4) = sK2
% 11.24/1.99      | r1_tarski(sK1,sK1) != iProver_top
% 11.24/1.99      | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
% 11.24/1.99      inference(demodulation,[status(thm)],[c_13190,c_6]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_2464,plain,
% 11.24/1.99      ( r1_tarski(sK1,sK1) ),
% 11.24/1.99      inference(instantiation,[status(thm)],[c_4]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_2465,plain,
% 11.24/1.99      ( r1_tarski(sK1,sK1) = iProver_top ),
% 11.24/1.99      inference(predicate_to_equality,[status(thm)],[c_2464]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_10,plain,
% 11.24/1.99      ( ~ v1_funct_1(X0)
% 11.24/1.99      | ~ v1_relat_1(X0)
% 11.24/1.99      | v1_relat_1(k2_funct_1(X0)) ),
% 11.24/1.99      inference(cnf_transformation,[],[f76]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_4235,plain,
% 11.24/1.99      ( ~ v1_funct_1(sK4)
% 11.24/1.99      | v1_relat_1(k2_funct_1(sK4))
% 11.24/1.99      | ~ v1_relat_1(sK4) ),
% 11.24/1.99      inference(instantiation,[status(thm)],[c_10]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_4236,plain,
% 11.24/1.99      ( v1_funct_1(sK4) != iProver_top
% 11.24/1.99      | v1_relat_1(k2_funct_1(sK4)) = iProver_top
% 11.24/1.99      | v1_relat_1(sK4) != iProver_top ),
% 11.24/1.99      inference(predicate_to_equality,[status(thm)],[c_4235]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_13693,plain,
% 11.24/1.99      ( k1_relat_1(sK4) = sK2 ),
% 11.24/1.99      inference(global_propositional_subsumption,
% 11.24/1.99                [status(thm)],
% 11.24/1.99                [c_13191,c_52,c_54,c_1871,c_2465,c_4236]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_1418,plain,
% 11.24/1.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 11.24/1.99      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_29,plain,
% 11.24/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.24/1.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 11.24/1.99      | ~ v1_funct_1(X0)
% 11.24/1.99      | ~ v1_funct_1(X3)
% 11.24/1.99      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 11.24/1.99      inference(cnf_transformation,[],[f96]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_1429,plain,
% 11.24/1.99      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 11.24/1.99      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 11.24/1.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.24/1.99      | v1_funct_1(X5) != iProver_top
% 11.24/1.99      | v1_funct_1(X4) != iProver_top ),
% 11.24/1.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_6774,plain,
% 11.24/1.99      ( k1_partfun1(X0,X1,sK2,sK1,X2,sK4) = k5_relat_1(X2,sK4)
% 11.24/1.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.24/1.99      | v1_funct_1(X2) != iProver_top
% 11.24/1.99      | v1_funct_1(sK4) != iProver_top ),
% 11.24/1.99      inference(superposition,[status(thm)],[c_1421,c_1429]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_7208,plain,
% 11.24/1.99      ( v1_funct_1(X2) != iProver_top
% 11.24/1.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.24/1.99      | k1_partfun1(X0,X1,sK2,sK1,X2,sK4) = k5_relat_1(X2,sK4) ),
% 11.24/1.99      inference(global_propositional_subsumption,
% 11.24/1.99                [status(thm)],
% 11.24/1.99                [c_6774,c_52]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_7209,plain,
% 11.24/1.99      ( k1_partfun1(X0,X1,sK2,sK1,X2,sK4) = k5_relat_1(X2,sK4)
% 11.24/1.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.24/1.99      | v1_funct_1(X2) != iProver_top ),
% 11.24/1.99      inference(renaming,[status(thm)],[c_7208]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_7217,plain,
% 11.24/1.99      ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k5_relat_1(sK3,sK4)
% 11.24/1.99      | v1_funct_1(sK3) != iProver_top ),
% 11.24/1.99      inference(superposition,[status(thm)],[c_1418,c_7209]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_7218,plain,
% 11.24/1.99      ( k5_relat_1(sK3,sK4) = k6_partfun1(sK1)
% 11.24/1.99      | v1_funct_1(sK3) != iProver_top ),
% 11.24/1.99      inference(light_normalisation,[status(thm)],[c_7217,c_2433]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_8692,plain,
% 11.24/1.99      ( k5_relat_1(sK3,sK4) = k6_partfun1(sK1) ),
% 11.24/1.99      inference(global_propositional_subsumption,
% 11.24/1.99                [status(thm)],
% 11.24/1.99                [c_7218,c_49]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_18,plain,
% 11.24/1.99      ( ~ v2_funct_1(X0)
% 11.24/1.99      | ~ v1_funct_1(X0)
% 11.24/1.99      | ~ v1_funct_1(X1)
% 11.24/1.99      | ~ v1_relat_1(X1)
% 11.24/1.99      | ~ v1_relat_1(X0)
% 11.24/1.99      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
% 11.24/1.99      | k2_funct_1(X0) = X1
% 11.24/1.99      | k1_relat_1(X0) != k2_relat_1(X1) ),
% 11.24/1.99      inference(cnf_transformation,[],[f122]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_1437,plain,
% 11.24/1.99      ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 11.24/1.99      | k2_funct_1(X1) = X0
% 11.24/1.99      | k1_relat_1(X1) != k2_relat_1(X0)
% 11.24/1.99      | v2_funct_1(X1) != iProver_top
% 11.24/1.99      | v1_funct_1(X1) != iProver_top
% 11.24/1.99      | v1_funct_1(X0) != iProver_top
% 11.24/1.99      | v1_relat_1(X1) != iProver_top
% 11.24/1.99      | v1_relat_1(X0) != iProver_top ),
% 11.24/1.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_8694,plain,
% 11.24/1.99      ( k2_funct_1(sK4) = sK3
% 11.24/1.99      | k6_partfun1(k2_relat_1(sK4)) != k6_partfun1(sK1)
% 11.24/1.99      | k1_relat_1(sK4) != k2_relat_1(sK3)
% 11.24/1.99      | v2_funct_1(sK4) != iProver_top
% 11.24/1.99      | v1_funct_1(sK4) != iProver_top
% 11.24/1.99      | v1_funct_1(sK3) != iProver_top
% 11.24/1.99      | v1_relat_1(sK4) != iProver_top
% 11.24/1.99      | v1_relat_1(sK3) != iProver_top ),
% 11.24/1.99      inference(superposition,[status(thm)],[c_8692,c_1437]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_2835,plain,
% 11.24/1.99      ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
% 11.24/1.99      inference(superposition,[status(thm)],[c_1418,c_1433]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_2836,plain,
% 11.24/1.99      ( k2_relat_1(sK3) = sK2 ),
% 11.24/1.99      inference(light_normalisation,[status(thm)],[c_2835,c_42]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_8695,plain,
% 11.24/1.99      ( k2_funct_1(sK4) = sK3
% 11.24/1.99      | k6_partfun1(sK1) != k6_partfun1(sK1)
% 11.24/1.99      | k1_relat_1(sK4) != sK2
% 11.24/1.99      | v2_funct_1(sK4) != iProver_top
% 11.24/1.99      | v1_funct_1(sK4) != iProver_top
% 11.24/1.99      | v1_funct_1(sK3) != iProver_top
% 11.24/1.99      | v1_relat_1(sK4) != iProver_top
% 11.24/1.99      | v1_relat_1(sK3) != iProver_top ),
% 11.24/1.99      inference(light_normalisation,[status(thm)],[c_8694,c_2836,c_2837]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_8696,plain,
% 11.24/1.99      ( k2_funct_1(sK4) = sK3
% 11.24/1.99      | k1_relat_1(sK4) != sK2
% 11.24/1.99      | v2_funct_1(sK4) != iProver_top
% 11.24/1.99      | v1_funct_1(sK4) != iProver_top
% 11.24/1.99      | v1_funct_1(sK3) != iProver_top
% 11.24/1.99      | v1_relat_1(sK4) != iProver_top
% 11.24/1.99      | v1_relat_1(sK3) != iProver_top ),
% 11.24/1.99      inference(equality_resolution_simp,[status(thm)],[c_8695]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_40,negated_conjecture,
% 11.24/1.99      ( v2_funct_1(sK3) ),
% 11.24/1.99      inference(cnf_transformation,[],[f113]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_2319,plain,
% 11.24/1.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 11.24/1.99      | v1_relat_1(sK3) ),
% 11.24/1.99      inference(instantiation,[status(thm)],[c_22]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_2500,plain,
% 11.24/1.99      ( v2_funct_1(k2_funct_1(sK3))
% 11.24/1.99      | ~ v2_funct_1(sK3)
% 11.24/1.99      | ~ v1_funct_1(sK3)
% 11.24/1.99      | ~ v1_relat_1(sK3) ),
% 11.24/1.99      inference(instantiation,[status(thm)],[c_13]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_9,plain,
% 11.24/1.99      ( ~ v1_funct_1(X0)
% 11.24/1.99      | v1_funct_1(k2_funct_1(X0))
% 11.24/1.99      | ~ v1_relat_1(X0) ),
% 11.24/1.99      inference(cnf_transformation,[],[f77]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_2732,plain,
% 11.24/1.99      ( v1_funct_1(k2_funct_1(sK4))
% 11.24/1.99      | ~ v1_funct_1(sK4)
% 11.24/1.99      | ~ v1_relat_1(sK4) ),
% 11.24/1.99      inference(instantiation,[status(thm)],[c_9]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_2735,plain,
% 11.24/1.99      ( v1_funct_1(k2_funct_1(sK3))
% 11.24/1.99      | ~ v1_funct_1(sK3)
% 11.24/1.99      | ~ v1_relat_1(sK3) ),
% 11.24/1.99      inference(instantiation,[status(thm)],[c_9]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_4238,plain,
% 11.24/1.99      ( ~ v1_funct_1(sK3)
% 11.24/1.99      | v1_relat_1(k2_funct_1(sK3))
% 11.24/1.99      | ~ v1_relat_1(sK3) ),
% 11.24/1.99      inference(instantiation,[status(thm)],[c_10]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_1422,plain,
% 11.24/1.99      ( v2_funct_1(sK3) = iProver_top ),
% 11.24/1.99      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_20,plain,
% 11.24/1.99      ( ~ v2_funct_1(X0)
% 11.24/1.99      | ~ v2_funct_1(X1)
% 11.24/1.99      | ~ v1_funct_1(X0)
% 11.24/1.99      | ~ v1_funct_1(X1)
% 11.24/1.99      | ~ v1_relat_1(X1)
% 11.24/1.99      | ~ v1_relat_1(X0)
% 11.24/1.99      | k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) = k2_funct_1(k5_relat_1(X0,X1)) ),
% 11.24/1.99      inference(cnf_transformation,[],[f87]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_1435,plain,
% 11.24/1.99      ( k5_relat_1(k2_funct_1(X0),k2_funct_1(X1)) = k2_funct_1(k5_relat_1(X1,X0))
% 11.24/1.99      | v2_funct_1(X1) != iProver_top
% 11.24/1.99      | v2_funct_1(X0) != iProver_top
% 11.24/1.99      | v1_funct_1(X1) != iProver_top
% 11.24/1.99      | v1_funct_1(X0) != iProver_top
% 11.24/1.99      | v1_relat_1(X1) != iProver_top
% 11.24/1.99      | v1_relat_1(X0) != iProver_top ),
% 11.24/1.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_8469,plain,
% 11.24/1.99      ( k5_relat_1(k2_funct_1(sK4),k2_funct_1(X0)) = k2_funct_1(k5_relat_1(X0,sK4))
% 11.24/1.99      | v2_funct_1(X0) != iProver_top
% 11.24/1.99      | v1_funct_1(X0) != iProver_top
% 11.24/1.99      | v1_funct_1(sK4) != iProver_top
% 11.24/1.99      | v1_relat_1(X0) != iProver_top
% 11.24/1.99      | v1_relat_1(sK4) != iProver_top ),
% 11.24/1.99      inference(superposition,[status(thm)],[c_8416,c_1435]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_10809,plain,
% 11.24/1.99      ( v1_relat_1(X0) != iProver_top
% 11.24/1.99      | k5_relat_1(k2_funct_1(sK4),k2_funct_1(X0)) = k2_funct_1(k5_relat_1(X0,sK4))
% 11.24/1.99      | v2_funct_1(X0) != iProver_top
% 11.24/1.99      | v1_funct_1(X0) != iProver_top ),
% 11.24/1.99      inference(global_propositional_subsumption,
% 11.24/1.99                [status(thm)],
% 11.24/1.99                [c_8469,c_52,c_54,c_1871]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_10810,plain,
% 11.24/1.99      ( k5_relat_1(k2_funct_1(sK4),k2_funct_1(X0)) = k2_funct_1(k5_relat_1(X0,sK4))
% 11.24/1.99      | v2_funct_1(X0) != iProver_top
% 11.24/1.99      | v1_funct_1(X0) != iProver_top
% 11.24/1.99      | v1_relat_1(X0) != iProver_top ),
% 11.24/1.99      inference(renaming,[status(thm)],[c_10809]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_10817,plain,
% 11.24/1.99      ( k5_relat_1(k2_funct_1(sK4),k2_funct_1(sK3)) = k2_funct_1(k5_relat_1(sK3,sK4))
% 11.24/1.99      | v1_funct_1(sK3) != iProver_top
% 11.24/1.99      | v1_relat_1(sK3) != iProver_top ),
% 11.24/1.99      inference(superposition,[status(thm)],[c_1422,c_10810]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_10819,plain,
% 11.24/1.99      ( k5_relat_1(k2_funct_1(sK4),k2_funct_1(sK3)) = k2_funct_1(k6_partfun1(sK1))
% 11.24/1.99      | v1_funct_1(sK3) != iProver_top
% 11.24/1.99      | v1_relat_1(sK3) != iProver_top ),
% 11.24/1.99      inference(light_normalisation,[status(thm)],[c_10817,c_8692]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_21,plain,
% 11.24/1.99      ( k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
% 11.24/1.99      inference(cnf_transformation,[],[f123]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_10820,plain,
% 11.24/1.99      ( k5_relat_1(k2_funct_1(sK4),k2_funct_1(sK3)) = k6_partfun1(sK1)
% 11.24/1.99      | v1_funct_1(sK3) != iProver_top
% 11.24/1.99      | v1_relat_1(sK3) != iProver_top ),
% 11.24/1.99      inference(demodulation,[status(thm)],[c_10819,c_21]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_2320,plain,
% 11.24/1.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 11.24/1.99      | v1_relat_1(sK3) = iProver_top ),
% 11.24/1.99      inference(predicate_to_equality,[status(thm)],[c_2319]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_11074,plain,
% 11.24/1.99      ( k5_relat_1(k2_funct_1(sK4),k2_funct_1(sK3)) = k6_partfun1(sK1) ),
% 11.24/1.99      inference(global_propositional_subsumption,
% 11.24/1.99                [status(thm)],
% 11.24/1.99                [c_10820,c_49,c_51,c_2320]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_11076,plain,
% 11.24/1.99      ( k2_funct_1(k2_funct_1(sK3)) = k2_funct_1(sK4)
% 11.24/1.99      | k6_partfun1(k2_relat_1(k2_funct_1(sK3))) != k6_partfun1(sK1)
% 11.24/1.99      | k1_relat_1(k2_funct_1(sK3)) != k2_relat_1(k2_funct_1(sK4))
% 11.24/1.99      | v2_funct_1(k2_funct_1(sK3)) != iProver_top
% 11.24/1.99      | v1_funct_1(k2_funct_1(sK4)) != iProver_top
% 11.24/1.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 11.24/1.99      | v1_relat_1(k2_funct_1(sK4)) != iProver_top
% 11.24/1.99      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 11.24/1.99      inference(superposition,[status(thm)],[c_11074,c_1437]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_3238,plain,
% 11.24/1.99      ( k2_funct_1(k2_funct_1(sK3)) = sK3
% 11.24/1.99      | v1_funct_1(sK3) != iProver_top
% 11.24/1.99      | v1_relat_1(sK3) != iProver_top ),
% 11.24/1.99      inference(superposition,[status(thm)],[c_1422,c_1436]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_3275,plain,
% 11.24/1.99      ( k2_funct_1(k2_funct_1(sK3)) = sK3 ),
% 11.24/1.99      inference(global_propositional_subsumption,
% 11.24/1.99                [status(thm)],
% 11.24/1.99                [c_3238,c_49,c_51,c_2320]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_3372,plain,
% 11.24/1.99      ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
% 11.24/1.99      | v1_funct_1(sK3) != iProver_top
% 11.24/1.99      | v1_relat_1(sK3) != iProver_top ),
% 11.24/1.99      inference(superposition,[status(thm)],[c_1422,c_1438]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_3373,plain,
% 11.24/1.99      ( k1_relat_1(k2_funct_1(sK3)) = sK2
% 11.24/1.99      | v1_funct_1(sK3) != iProver_top
% 11.24/1.99      | v1_relat_1(sK3) != iProver_top ),
% 11.24/1.99      inference(light_normalisation,[status(thm)],[c_3372,c_2836]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_3765,plain,
% 11.24/1.99      ( k1_relat_1(k2_funct_1(sK3)) = sK2 ),
% 11.24/1.99      inference(global_propositional_subsumption,
% 11.24/1.99                [status(thm)],
% 11.24/1.99                [c_3373,c_49,c_51,c_2320]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_3444,plain,
% 11.24/1.99      ( k2_relat_1(k5_relat_1(sK3,X0)) = k2_relat_1(X0)
% 11.24/1.99      | r1_tarski(k1_relat_1(X0),sK2) != iProver_top
% 11.24/1.99      | v1_relat_1(X0) != iProver_top
% 11.24/1.99      | v1_relat_1(sK3) != iProver_top ),
% 11.24/1.99      inference(superposition,[status(thm)],[c_2836,c_1446]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_4220,plain,
% 11.24/1.99      ( v1_relat_1(X0) != iProver_top
% 11.24/1.99      | r1_tarski(k1_relat_1(X0),sK2) != iProver_top
% 11.24/1.99      | k2_relat_1(k5_relat_1(sK3,X0)) = k2_relat_1(X0) ),
% 11.24/1.99      inference(global_propositional_subsumption,
% 11.24/1.99                [status(thm)],
% 11.24/1.99                [c_3444,c_51,c_2320]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_4221,plain,
% 11.24/1.99      ( k2_relat_1(k5_relat_1(sK3,X0)) = k2_relat_1(X0)
% 11.24/1.99      | r1_tarski(k1_relat_1(X0),sK2) != iProver_top
% 11.24/1.99      | v1_relat_1(X0) != iProver_top ),
% 11.24/1.99      inference(renaming,[status(thm)],[c_4220]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_4227,plain,
% 11.24/1.99      ( k2_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) = k2_relat_1(k2_funct_1(sK3))
% 11.24/1.99      | r1_tarski(sK2,sK2) != iProver_top
% 11.24/1.99      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 11.24/1.99      inference(superposition,[status(thm)],[c_3765,c_4221]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_2980,plain,
% 11.24/1.99      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
% 11.24/1.99      | sK2 = k1_xboole_0
% 11.24/1.99      | v1_funct_2(sK3,sK1,sK2) != iProver_top
% 11.24/1.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 11.24/1.99      | v2_funct_1(sK3) != iProver_top
% 11.24/1.99      | v1_funct_1(sK3) != iProver_top ),
% 11.24/1.99      inference(superposition,[status(thm)],[c_42,c_1423]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_38,negated_conjecture,
% 11.24/1.99      ( k1_xboole_0 != sK2 ),
% 11.24/1.99      inference(cnf_transformation,[],[f115]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_1508,plain,
% 11.24/1.99      ( ~ v1_funct_2(X0,X1,sK2)
% 11.24/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK2)))
% 11.24/1.99      | ~ v2_funct_1(X0)
% 11.24/1.99      | ~ v1_funct_1(X0)
% 11.24/1.99      | k2_relset_1(X1,sK2,X0) != sK2
% 11.24/1.99      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 11.24/1.99      | k1_xboole_0 = sK2 ),
% 11.24/1.99      inference(instantiation,[status(thm)],[c_36]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_1642,plain,
% 11.24/1.99      ( ~ v1_funct_2(sK3,X0,sK2)
% 11.24/1.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
% 11.24/1.99      | ~ v2_funct_1(sK3)
% 11.24/1.99      | ~ v1_funct_1(sK3)
% 11.24/1.99      | k2_relset_1(X0,sK2,sK3) != sK2
% 11.24/1.99      | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(X0)
% 11.24/1.99      | k1_xboole_0 = sK2 ),
% 11.24/1.99      inference(instantiation,[status(thm)],[c_1508]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_1765,plain,
% 11.24/1.99      ( ~ v1_funct_2(sK3,sK1,sK2)
% 11.24/1.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 11.24/1.99      | ~ v2_funct_1(sK3)
% 11.24/1.99      | ~ v1_funct_1(sK3)
% 11.24/1.99      | k2_relset_1(sK1,sK2,sK3) != sK2
% 11.24/1.99      | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
% 11.24/1.99      | k1_xboole_0 = sK2 ),
% 11.24/1.99      inference(instantiation,[status(thm)],[c_1642]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_3114,plain,
% 11.24/1.99      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
% 11.24/1.99      inference(global_propositional_subsumption,
% 11.24/1.99                [status(thm)],
% 11.24/1.99                [c_2980,c_48,c_47,c_46,c_42,c_40,c_38,c_1765]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_3435,plain,
% 11.24/1.99      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
% 11.24/1.99      | v1_funct_1(sK3) != iProver_top
% 11.24/1.99      | v1_relat_1(sK3) != iProver_top ),
% 11.24/1.99      inference(superposition,[status(thm)],[c_1422,c_1439]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_4213,plain,
% 11.24/1.99      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 11.24/1.99      inference(global_propositional_subsumption,
% 11.24/1.99                [status(thm)],
% 11.24/1.99                [c_3435,c_49,c_51,c_2320]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_4228,plain,
% 11.24/1.99      ( k2_relat_1(k6_partfun1(sK1)) = k1_relat_1(sK3)
% 11.24/1.99      | r1_tarski(sK2,sK2) != iProver_top
% 11.24/1.99      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 11.24/1.99      inference(light_normalisation,[status(thm)],[c_4227,c_3114,c_4213]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_4229,plain,
% 11.24/1.99      ( k1_relat_1(sK3) = sK1
% 11.24/1.99      | r1_tarski(sK2,sK2) != iProver_top
% 11.24/1.99      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 11.24/1.99      inference(demodulation,[status(thm)],[c_4228,c_6]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_2460,plain,
% 11.24/1.99      ( r1_tarski(sK2,sK2) ),
% 11.24/1.99      inference(instantiation,[status(thm)],[c_4]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_4231,plain,
% 11.24/1.99      ( ~ r1_tarski(sK2,sK2)
% 11.24/1.99      | ~ v1_relat_1(k2_funct_1(sK3))
% 11.24/1.99      | k1_relat_1(sK3) = sK1 ),
% 11.24/1.99      inference(predicate_to_equality_rev,[status(thm)],[c_4229]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_4309,plain,
% 11.24/1.99      ( k1_relat_1(sK3) = sK1 ),
% 11.24/1.99      inference(global_propositional_subsumption,
% 11.24/1.99                [status(thm)],
% 11.24/1.99                [c_4229,c_48,c_46,c_2319,c_2460,c_4231,c_4238]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_4311,plain,
% 11.24/1.99      ( k2_relat_1(k2_funct_1(sK3)) = sK1 ),
% 11.24/1.99      inference(demodulation,[status(thm)],[c_4309,c_4213]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_11077,plain,
% 11.24/1.99      ( k2_funct_1(sK4) = sK3
% 11.24/1.99      | k6_partfun1(sK1) != k6_partfun1(sK1)
% 11.24/1.99      | k1_relat_1(sK4) != sK2
% 11.24/1.99      | v2_funct_1(k2_funct_1(sK3)) != iProver_top
% 11.24/1.99      | v1_funct_1(k2_funct_1(sK4)) != iProver_top
% 11.24/1.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 11.24/1.99      | v1_relat_1(k2_funct_1(sK4)) != iProver_top
% 11.24/1.99      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 11.24/1.99      inference(light_normalisation,
% 11.24/1.99                [status(thm)],
% 11.24/1.99                [c_11076,c_3275,c_3765,c_4311,c_8779]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_11078,plain,
% 11.24/1.99      ( k2_funct_1(sK4) = sK3
% 11.24/1.99      | k1_relat_1(sK4) != sK2
% 11.24/1.99      | v2_funct_1(k2_funct_1(sK3)) != iProver_top
% 11.24/1.99      | v1_funct_1(k2_funct_1(sK4)) != iProver_top
% 11.24/1.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 11.24/1.99      | v1_relat_1(k2_funct_1(sK4)) != iProver_top
% 11.24/1.99      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 11.24/1.99      inference(equality_resolution_simp,[status(thm)],[c_11077]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_11079,plain,
% 11.24/1.99      ( ~ v2_funct_1(k2_funct_1(sK3))
% 11.24/1.99      | ~ v1_funct_1(k2_funct_1(sK4))
% 11.24/1.99      | ~ v1_funct_1(k2_funct_1(sK3))
% 11.24/1.99      | ~ v1_relat_1(k2_funct_1(sK4))
% 11.24/1.99      | ~ v1_relat_1(k2_funct_1(sK3))
% 11.24/1.99      | k2_funct_1(sK4) = sK3
% 11.24/1.99      | k1_relat_1(sK4) != sK2 ),
% 11.24/1.99      inference(predicate_to_equality_rev,[status(thm)],[c_11078]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_11231,plain,
% 11.24/1.99      ( k1_relat_1(sK4) != sK2 | k2_funct_1(sK4) = sK3 ),
% 11.24/1.99      inference(global_propositional_subsumption,
% 11.24/1.99                [status(thm)],
% 11.24/1.99                [c_8696,c_48,c_46,c_45,c_43,c_40,c_1870,c_2319,c_2500,
% 11.24/1.99                 c_2732,c_2735,c_4235,c_4238,c_11079]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_11232,plain,
% 11.24/1.99      ( k2_funct_1(sK4) = sK3 | k1_relat_1(sK4) != sK2 ),
% 11.24/1.99      inference(renaming,[status(thm)],[c_11231]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_13696,plain,
% 11.24/1.99      ( k2_funct_1(sK4) = sK3 | sK2 != sK2 ),
% 11.24/1.99      inference(demodulation,[status(thm)],[c_13693,c_11232]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_13700,plain,
% 11.24/1.99      ( k2_funct_1(sK4) = sK3 ),
% 11.24/1.99      inference(equality_resolution_simp,[status(thm)],[c_13696]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_27484,plain,
% 11.24/1.99      ( k2_funct_1(sK3) = sK4
% 11.24/1.99      | v1_funct_1(sK4) != iProver_top
% 11.24/1.99      | v1_relat_1(sK4) != iProver_top ),
% 11.24/1.99      inference(light_normalisation,
% 11.24/1.99                [status(thm)],
% 11.24/1.99                [c_27482,c_8725,c_13700]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(c_37,negated_conjecture,
% 11.24/1.99      ( k2_funct_1(sK3) != sK4 ),
% 11.24/1.99      inference(cnf_transformation,[],[f116]) ).
% 11.24/1.99  
% 11.24/1.99  cnf(contradiction,plain,
% 11.24/1.99      ( $false ),
% 11.24/1.99      inference(minisat,[status(thm)],[c_27484,c_1871,c_37,c_54,c_52]) ).
% 11.24/1.99  
% 11.24/1.99  
% 11.24/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.24/1.99  
% 11.24/1.99  ------                               Statistics
% 11.24/1.99  
% 11.24/1.99  ------ General
% 11.24/1.99  
% 11.24/1.99  abstr_ref_over_cycles:                  0
% 11.24/1.99  abstr_ref_under_cycles:                 0
% 11.24/1.99  gc_basic_clause_elim:                   0
% 11.24/1.99  forced_gc_time:                         0
% 11.24/1.99  parsing_time:                           0.012
% 11.24/1.99  unif_index_cands_time:                  0.
% 11.24/1.99  unif_index_add_time:                    0.
% 11.24/1.99  orderings_time:                         0.
% 11.24/1.99  out_proof_time:                         0.023
% 11.24/1.99  total_time:                             1.088
% 11.24/1.99  num_of_symbols:                         54
% 11.24/1.99  num_of_terms:                           37563
% 11.24/1.99  
% 11.24/1.99  ------ Preprocessing
% 11.24/1.99  
% 11.24/1.99  num_of_splits:                          0
% 11.24/1.99  num_of_split_atoms:                     0
% 11.24/1.99  num_of_reused_defs:                     0
% 11.24/1.99  num_eq_ax_congr_red:                    0
% 11.24/1.99  num_of_sem_filtered_clauses:            1
% 11.24/1.99  num_of_subtypes:                        0
% 11.24/1.99  monotx_restored_types:                  0
% 11.24/1.99  sat_num_of_epr_types:                   0
% 11.24/1.99  sat_num_of_non_cyclic_types:            0
% 11.24/1.99  sat_guarded_non_collapsed_types:        0
% 11.24/1.99  num_pure_diseq_elim:                    0
% 11.24/1.99  simp_replaced_by:                       0
% 11.24/1.99  res_preprocessed:                       213
% 11.24/1.99  prep_upred:                             0
% 11.24/1.99  prep_unflattend:                        13
% 11.24/1.99  smt_new_axioms:                         0
% 11.24/1.99  pred_elim_cands:                        6
% 11.24/1.99  pred_elim:                              2
% 11.24/1.99  pred_elim_cl:                           2
% 11.24/1.99  pred_elim_cycles:                       4
% 11.24/1.99  merged_defs:                            0
% 11.24/1.99  merged_defs_ncl:                        0
% 11.24/1.99  bin_hyper_res:                          0
% 11.24/1.99  prep_cycles:                            4
% 11.24/1.99  pred_elim_time:                         0.005
% 11.24/1.99  splitting_time:                         0.
% 11.24/1.99  sem_filter_time:                        0.
% 11.24/1.99  monotx_time:                            0.001
% 11.24/1.99  subtype_inf_time:                       0.
% 11.24/1.99  
% 11.24/1.99  ------ Problem properties
% 11.24/1.99  
% 11.24/1.99  clauses:                                44
% 11.24/1.99  conjectures:                            11
% 11.24/1.99  epr:                                    10
% 11.24/1.99  horn:                                   40
% 11.24/1.99  ground:                                 13
% 11.24/1.99  unary:                                  19
% 11.24/1.99  binary:                                 4
% 11.24/1.99  lits:                                   154
% 11.24/1.99  lits_eq:                                37
% 11.24/1.99  fd_pure:                                0
% 11.24/1.99  fd_pseudo:                              0
% 11.24/1.99  fd_cond:                                4
% 11.24/1.99  fd_pseudo_cond:                         2
% 11.24/1.99  ac_symbols:                             0
% 11.24/1.99  
% 11.24/1.99  ------ Propositional Solver
% 11.24/1.99  
% 11.24/1.99  prop_solver_calls:                      32
% 11.24/1.99  prop_fast_solver_calls:                 3167
% 11.24/1.99  smt_solver_calls:                       0
% 11.24/1.99  smt_fast_solver_calls:                  0
% 11.24/1.99  prop_num_of_clauses:                    13682
% 11.24/1.99  prop_preprocess_simplified:             24706
% 11.24/1.99  prop_fo_subsumed:                       419
% 11.24/1.99  prop_solver_time:                       0.
% 11.24/1.99  smt_solver_time:                        0.
% 11.24/1.99  smt_fast_solver_time:                   0.
% 11.24/1.99  prop_fast_solver_time:                  0.
% 11.24/1.99  prop_unsat_core_time:                   0.002
% 11.24/1.99  
% 11.24/1.99  ------ QBF
% 11.24/1.99  
% 11.24/1.99  qbf_q_res:                              0
% 11.24/1.99  qbf_num_tautologies:                    0
% 11.24/1.99  qbf_prep_cycles:                        0
% 11.24/1.99  
% 11.24/1.99  ------ BMC1
% 11.24/1.99  
% 11.24/1.99  bmc1_current_bound:                     -1
% 11.24/1.99  bmc1_last_solved_bound:                 -1
% 11.24/1.99  bmc1_unsat_core_size:                   -1
% 11.24/1.99  bmc1_unsat_core_parents_size:           -1
% 11.24/1.99  bmc1_merge_next_fun:                    0
% 11.24/1.99  bmc1_unsat_core_clauses_time:           0.
% 11.24/1.99  
% 11.24/1.99  ------ Instantiation
% 11.24/1.99  
% 11.24/1.99  inst_num_of_clauses:                    3262
% 11.24/1.99  inst_num_in_passive:                    276
% 11.24/1.99  inst_num_in_active:                     1694
% 11.24/1.99  inst_num_in_unprocessed:                1292
% 11.24/1.99  inst_num_of_loops:                      1790
% 11.24/1.99  inst_num_of_learning_restarts:          0
% 11.24/1.99  inst_num_moves_active_passive:          94
% 11.24/1.99  inst_lit_activity:                      0
% 11.24/1.99  inst_lit_activity_moves:                1
% 11.24/1.99  inst_num_tautologies:                   0
% 11.24/1.99  inst_num_prop_implied:                  0
% 11.24/1.99  inst_num_existing_simplified:           0
% 11.24/1.99  inst_num_eq_res_simplified:             0
% 11.24/1.99  inst_num_child_elim:                    0
% 11.24/1.99  inst_num_of_dismatching_blockings:      561
% 11.24/1.99  inst_num_of_non_proper_insts:           3505
% 11.24/1.99  inst_num_of_duplicates:                 0
% 11.24/1.99  inst_inst_num_from_inst_to_res:         0
% 11.24/1.99  inst_dismatching_checking_time:         0.
% 11.24/1.99  
% 11.24/1.99  ------ Resolution
% 11.24/1.99  
% 11.24/1.99  res_num_of_clauses:                     0
% 11.24/1.99  res_num_in_passive:                     0
% 11.24/1.99  res_num_in_active:                      0
% 11.24/1.99  res_num_of_loops:                       217
% 11.24/1.99  res_forward_subset_subsumed:            154
% 11.24/1.99  res_backward_subset_subsumed:           0
% 11.24/1.99  res_forward_subsumed:                   0
% 11.24/1.99  res_backward_subsumed:                  0
% 11.24/1.99  res_forward_subsumption_resolution:     2
% 11.24/1.99  res_backward_subsumption_resolution:    0
% 11.24/1.99  res_clause_to_clause_subsumption:       2097
% 11.24/1.99  res_orphan_elimination:                 0
% 11.24/1.99  res_tautology_del:                      83
% 11.24/1.99  res_num_eq_res_simplified:              1
% 11.24/1.99  res_num_sel_changes:                    0
% 11.24/1.99  res_moves_from_active_to_pass:          0
% 11.24/1.99  
% 11.24/1.99  ------ Superposition
% 11.24/1.99  
% 11.24/1.99  sup_time_total:                         0.
% 11.24/1.99  sup_time_generating:                    0.
% 11.24/1.99  sup_time_sim_full:                      0.
% 11.24/1.99  sup_time_sim_immed:                     0.
% 11.24/1.99  
% 11.24/1.99  sup_num_of_clauses:                     880
% 11.24/1.99  sup_num_in_active:                      333
% 11.24/1.99  sup_num_in_passive:                     547
% 11.24/1.99  sup_num_of_loops:                       357
% 11.24/1.99  sup_fw_superposition:                   482
% 11.24/1.99  sup_bw_superposition:                   580
% 11.24/1.99  sup_immediate_simplified:               346
% 11.24/1.99  sup_given_eliminated:                   0
% 11.24/1.99  comparisons_done:                       0
% 11.24/1.99  comparisons_avoided:                    0
% 11.24/1.99  
% 11.24/1.99  ------ Simplifications
% 11.24/1.99  
% 11.24/1.99  
% 11.24/1.99  sim_fw_subset_subsumed:                 27
% 11.24/1.99  sim_bw_subset_subsumed:                 41
% 11.24/1.99  sim_fw_subsumed:                        17
% 11.24/1.99  sim_bw_subsumed:                        0
% 11.24/1.99  sim_fw_subsumption_res:                 0
% 11.24/1.99  sim_bw_subsumption_res:                 0
% 11.24/1.99  sim_tautology_del:                      5
% 11.24/1.99  sim_eq_tautology_del:                   119
% 11.24/1.99  sim_eq_res_simp:                        28
% 11.24/1.99  sim_fw_demodulated:                     68
% 11.24/1.99  sim_bw_demodulated:                     12
% 11.24/1.99  sim_light_normalised:                   292
% 11.24/1.99  sim_joinable_taut:                      0
% 11.24/1.99  sim_joinable_simp:                      0
% 11.24/1.99  sim_ac_normalised:                      0
% 11.24/1.99  sim_smt_subsumption:                    0
% 11.24/1.99  
%------------------------------------------------------------------------------
