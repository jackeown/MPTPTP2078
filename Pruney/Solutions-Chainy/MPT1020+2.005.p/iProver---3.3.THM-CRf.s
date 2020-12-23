%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:05 EST 2020

% Result     : Theorem 55.77s
% Output     : CNFRefutation 55.77s
% Verified   : 
% Statistics : Number of formulae       :  231 (1145 expanded)
%              Number of clauses        :  133 ( 338 expanded)
%              Number of leaves         :   30 ( 295 expanded)
%              Depth                    :   20
%              Number of atoms          :  939 (8065 expanded)
%              Number of equality atoms :  349 ( 633 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f22,axiom,(
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

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_funct_1(X2) = X3
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0
          | ~ v2_funct_1(X2)
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | k2_relset_1(X0,X1,X2) != X1
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_funct_1(X2) = X3
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0
          | ~ v2_funct_1(X2)
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | k2_relset_1(X0,X1,X2) != X1
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f57])).

fof(f102,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_funct_1(X2) = X3
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ v2_funct_1(X2)
      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f24,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v3_funct_2(X2,X0,X0)
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
           => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v3_funct_2(X2,X0,X0)
              & v1_funct_2(X2,X0,X0)
              & v1_funct_1(X2) )
           => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
             => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f61,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f62,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f61])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
     => ( ~ r2_relset_1(X0,X0,sK4,k2_funct_2(X0,X1))
        & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,sK4),k6_partfun1(X0))
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(sK4,X0,X0)
        & v1_funct_2(sK4,X0,X0)
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
            & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v3_funct_2(X2,X0,X0)
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ? [X2] :
          ( ~ r2_relset_1(sK2,sK2,X2,k2_funct_2(sK2,sK3))
          & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK3,X2),k6_partfun1(sK2))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
          & v3_funct_2(X2,sK2,sK2)
          & v1_funct_2(X2,sK2,sK2)
          & v1_funct_1(X2) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      & v3_funct_2(sK3,sK2,sK2)
      & v1_funct_2(sK3,sK2,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,
    ( ~ r2_relset_1(sK2,sK2,sK4,k2_funct_2(sK2,sK3))
    & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK3,sK4),k6_partfun1(sK2))
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    & v3_funct_2(sK4,sK2,sK2)
    & v1_funct_2(sK4,sK2,sK2)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    & v3_funct_2(sK3,sK2,sK2)
    & v1_funct_2(sK3,sK2,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f62,f69,f68])).

fof(f112,plain,(
    r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK3,sK4),k6_partfun1(sK2)) ),
    inference(cnf_transformation,[],[f70])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f46,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f45])).

fof(f91,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f39])).

fof(f65,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f104,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f70])).

fof(f107,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f70])).

fof(f108,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f70])).

fof(f111,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f70])).

fof(f17,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f96,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( ( v2_funct_1(X4)
              & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 )
           => ( k2_relset_1(X0,X1,X3) = X1
              | k1_xboole_0 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k2_relset_1(X0,X1,X3) = X1
          | k1_xboole_0 = X2
          | ~ v2_funct_1(X4)
          | k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f54,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k2_relset_1(X0,X1,X3) = X1
          | k1_xboole_0 = X2
          | ~ v2_funct_1(X4)
          | k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f53])).

fof(f99,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X3) = X1
      | k1_xboole_0 = X2
      | ~ v2_funct_1(X4)
      | k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f105,plain,(
    v1_funct_2(sK3,sK2,sK2) ),
    inference(cnf_transformation,[],[f70])).

fof(f106,plain,(
    v3_funct_2(sK3,sK2,sK2) ),
    inference(cnf_transformation,[],[f70])).

fof(f109,plain,(
    v1_funct_2(sK4,sK2,sK2) ),
    inference(cnf_transformation,[],[f70])).

fof(f110,plain,(
    v3_funct_2(sK4,sK2,sK2) ),
    inference(cnf_transformation,[],[f70])).

fof(f2,axiom,(
    ! [X0] :
    ? [X1] :
      ( v1_xboole_0(X1)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( v1_xboole_0(sK0(X0))
        & m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X0] :
      ( v1_xboole_0(sK0(X0))
      & m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f2,f63])).

fof(f73,plain,(
    ! [X0] : v1_xboole_0(sK0(X0)) ),
    inference(cnf_transformation,[],[f64])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
         => ( ! [X3] :
                ( r2_hidden(X3,X0)
               => k11_relat_1(X1,X3) = k11_relat_1(X2,X3) )
           => r2_relset_1(X0,X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_relset_1(X0,X0,X1,X2)
          | ? [X3] :
              ( k11_relat_1(X1,X3) != k11_relat_1(X2,X3)
              & r2_hidden(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_relset_1(X0,X0,X1,X2)
          | ? [X3] :
              ( k11_relat_1(X1,X3) != k11_relat_1(X2,X3)
              & r2_hidden(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(flattening,[],[f41])).

fof(f66,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k11_relat_1(X1,X3) != k11_relat_1(X2,X3)
          & r2_hidden(X3,X0) )
     => ( k11_relat_1(X1,sK1(X0,X1,X2)) != k11_relat_1(X2,sK1(X0,X1,X2))
        & r2_hidden(sK1(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_relset_1(X0,X0,X1,X2)
          | ( k11_relat_1(X1,sK1(X0,X1,X2)) != k11_relat_1(X2,sK1(X0,X1,X2))
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f42,f66])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( r2_relset_1(X0,X0,X1,X2)
      | r2_hidden(sK1(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f113,plain,(
    ~ r2_relset_1(sK2,sK2,sK4,k2_funct_2(sK2,sK3)) ),
    inference(cnf_transformation,[],[f70])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f47])).

fof(f95,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f75,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f59])).

fof(f103,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f43])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f21,axiom,(
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
    inference(ennf_transformation,[],[f21])).

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

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f19,axiom,(
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
    inference(ennf_transformation,[],[f19])).

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

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f34,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f79,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f114,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f85])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_1(X1) = k2_funct_2(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f49])).

fof(f97,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_31,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X3,X1,X0)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | ~ v2_funct_1(X2)
    | k2_relset_1(X0,X1,X2) != X1
    | k2_funct_1(X2) = X3
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f102])).

cnf(c_84745,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,sK3,X2),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X1,X0)
    | ~ v1_funct_2(sK3,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | k2_relset_1(X0,X1,sK3) != X1
    | k2_funct_1(sK3) = X2
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_129058,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,sK3,sK4),k6_partfun1(X0))
    | ~ v1_funct_2(sK3,X0,X1)
    | ~ v1_funct_2(sK4,X1,X0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK4)
    | ~ v2_funct_1(sK3)
    | k2_relset_1(X0,X1,sK3) != X1
    | k2_funct_1(sK3) = sK4
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(instantiation,[status(thm)],[c_84745])).

cnf(c_129060,plain,
    ( ~ r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK3,sK4),k6_partfun1(sK2))
    | ~ v1_funct_2(sK3,sK2,sK2)
    | ~ v1_funct_2(sK4,sK2,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK4)
    | ~ v2_funct_1(sK3)
    | k2_relset_1(sK2,sK2,sK3) != sK2
    | k2_funct_1(sK3) = sK4
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_129058])).

cnf(c_34,negated_conjecture,
    ( r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK3,sK4),k6_partfun1(sK2)) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_2863,plain,
    ( r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK3,sK4),k6_partfun1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_2878,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_14,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2882,plain,
    ( X0 = X1
    | r2_relset_1(X2,X3,X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_8543,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = X6
    | r2_relset_1(X0,X3,k1_partfun1(X0,X1,X2,X3,X4,X5),X6) != iProver_top
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2878,c_2882])).

cnf(c_78528,plain,
    ( k1_partfun1(sK2,sK2,sK2,sK2,sK3,sK4) = k6_partfun1(sK2)
    | m1_subset_1(k6_partfun1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2863,c_8543])).

cnf(c_42,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_43,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_39,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_46,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_38,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_47,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_50,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_25,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_74,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_76,plain,
    ( m1_subset_1(k6_partfun1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_74])).

cnf(c_79828,plain,
    ( k1_partfun1(sK2,sK2,sK2,sK2,sK3,sK4) = k6_partfun1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_78528,c_43,c_46,c_47,c_50,c_76])).

cnf(c_2858,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_2862,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2884,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_8535,plain,
    ( k2_relset_1(X0,X1,k1_partfun1(X0,X2,X3,X1,X4,X5)) = k2_relat_1(k1_partfun1(X0,X2,X3,X1,X4,X5))
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2878,c_2884])).

cnf(c_67937,plain,
    ( k2_relset_1(X0,sK2,k1_partfun1(X0,X1,sK2,sK2,X2,sK4)) = k2_relat_1(k1_partfun1(X0,X1,sK2,sK2,X2,sK4))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2862,c_8535])).

cnf(c_68344,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k2_relset_1(X0,sK2,k1_partfun1(X0,X1,sK2,sK2,X2,sK4)) = k2_relat_1(k1_partfun1(X0,X1,sK2,sK2,X2,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_67937,c_47])).

cnf(c_68345,plain,
    ( k2_relset_1(X0,sK2,k1_partfun1(X0,X1,sK2,sK2,X2,sK4)) = k2_relat_1(k1_partfun1(X0,X1,sK2,sK2,X2,sK4))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_68344])).

cnf(c_68357,plain,
    ( k2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK3,sK4)) = k2_relat_1(k1_partfun1(sK2,sK2,sK2,sK2,sK3,sK4))
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2858,c_68345])).

cnf(c_68486,plain,
    ( k2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK3,sK4)) = k2_relat_1(k1_partfun1(sK2,sK2,sK2,sK2,sK3,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_68357,c_43])).

cnf(c_28,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X4,X1,X3) = X1
    | k2_relset_1(X4,X2,k1_partfun1(X4,X1,X1,X2,X3,X0)) != X2
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_2869,plain,
    ( k2_relset_1(X0,X1,X2) = X1
    | k2_relset_1(X0,X3,k1_partfun1(X0,X1,X1,X3,X2,X4)) != X3
    | k1_xboole_0 = X3
    | v1_funct_2(X4,X1,X3) != iProver_top
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_68491,plain,
    ( k2_relset_1(sK2,sK2,sK3) = sK2
    | k2_relat_1(k1_partfun1(sK2,sK2,sK2,sK2,sK3,sK4)) != sK2
    | sK2 = k1_xboole_0
    | v1_funct_2(sK3,sK2,sK2) != iProver_top
    | v1_funct_2(sK4,sK2,sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_68486,c_2869])).

cnf(c_3991,plain,
    ( k2_relset_1(sK2,sK2,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2858,c_2884])).

cnf(c_68492,plain,
    ( k2_relat_1(k1_partfun1(sK2,sK2,sK2,sK2,sK3,sK4)) != sK2
    | k2_relat_1(sK3) = sK2
    | sK2 = k1_xboole_0
    | v1_funct_2(sK3,sK2,sK2) != iProver_top
    | v1_funct_2(sK4,sK2,sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_funct_1(sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_68491,c_3991])).

cnf(c_41,negated_conjecture,
    ( v1_funct_2(sK3,sK2,sK2) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_40,negated_conjecture,
    ( v3_funct_2(sK3,sK2,sK2) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_37,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK2) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_36,negated_conjecture,
    ( v3_funct_2(sK4,sK2,sK2) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_1,plain,
    ( v1_xboole_0(sK0(X0)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_16,plain,
    ( r2_relset_1(X0,X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | r2_hidden(sK1(X0,X1,X2),X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_33,negated_conjecture,
    ( ~ r2_relset_1(sK2,sK2,sK4,k2_funct_2(sK2,sK3)) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_1036,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | r2_hidden(sK1(X1,X2,X0),X1)
    | k2_funct_2(sK2,sK3) != X0
    | sK4 != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_33])).

cnf(c_1037,plain,
    ( ~ m1_subset_1(k2_funct_2(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | r2_hidden(sK1(sK2,sK4,k2_funct_2(sK2,sK3)),sK2) ),
    inference(unflattening,[status(thm)],[c_1036])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_2977,plain,
    ( ~ v1_funct_2(sK3,sK2,sK2)
    | ~ v3_funct_2(sK3,sK2,sK2)
    | m1_subset_1(k2_funct_2(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_3030,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
    | ~ r2_hidden(sK1(sK2,sK4,k2_funct_2(sK2,sK3)),sK2)
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_3032,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK2))
    | ~ r2_hidden(sK1(sK2,sK4,k2_funct_2(sK2,sK3)),sK2)
    | ~ v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_3030])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_3076,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0(X1)))
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(sK0(X1)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3429,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0(X0)))
    | ~ v1_xboole_0(sK0(X0))
    | v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3076])).

cnf(c_3,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_4751,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0(X0))) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_32,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(X1,X1,X0) = X1 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_2865,plain,
    ( k1_relset_1(X0,X0,X1) = X0
    | v1_funct_2(X1,X0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_3874,plain,
    ( k1_relset_1(sK2,sK2,sK4) = sK2
    | v1_funct_2(sK4,sK2,sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2862,c_2865])).

cnf(c_48,plain,
    ( v1_funct_2(sK4,sK2,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_5541,plain,
    ( k1_relset_1(sK2,sK2,sK4) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3874,c_47,c_48])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2886,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_5544,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5541,c_2886])).

cnf(c_5545,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | m1_subset_1(sK2,k1_zfmisc_1(sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5544])).

cnf(c_17,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2879,plain,
    ( v3_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_5828,plain,
    ( v3_funct_2(sK4,sK2,sK2) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2862,c_2879])).

cnf(c_5842,plain,
    ( ~ v3_funct_2(sK4,sK2,sK2)
    | ~ v1_funct_1(sK4)
    | v2_funct_1(sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5828])).

cnf(c_2172,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_26064,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(k1_xboole_0)
    | X0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2172])).

cnf(c_26072,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_26064])).

cnf(c_68498,plain,
    ( ~ v1_funct_2(sK3,sK2,sK2)
    | ~ v1_funct_2(sK4,sK2,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK4)
    | ~ v2_funct_1(sK4)
    | k2_relat_1(k1_partfun1(sK2,sK2,sK2,sK2,sK3,sK4)) != sK2
    | k2_relat_1(sK3) = sK2
    | sK2 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_68492])).

cnf(c_78090,plain,
    ( k2_relat_1(k1_partfun1(sK2,sK2,sK2,sK2,sK3,sK4)) != sK2
    | k2_relat_1(sK3) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_68492,c_42,c_41,c_40,c_39,c_38,c_37,c_36,c_35,c_1,c_1037,c_2977,c_3032,c_3429,c_4751,c_5545,c_5842,c_26072,c_68498])).

cnf(c_79830,plain,
    ( k2_relat_1(k6_partfun1(sK2)) != sK2
    | k2_relat_1(sK3) = sK2 ),
    inference(demodulation,[status(thm)],[c_79828,c_78090])).

cnf(c_3990,plain,
    ( k2_relset_1(sK2,sK2,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_2862,c_2884])).

cnf(c_30,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_2867,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_5663,plain,
    ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(sK2)
    | k2_relat_1(sK4) != sK2
    | sK2 = k1_xboole_0
    | v1_funct_2(sK4,sK2,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3990,c_2867])).

cnf(c_49,plain,
    ( v3_funct_2(sK4,sK2,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_27,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_2870,plain,
    ( k2_relset_1(X0,X1,X2) = X1
    | r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) != iProver_top
    | v1_funct_2(X2,X0,X1) != iProver_top
    | v1_funct_2(X3,X1,X0) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_9024,plain,
    ( k2_relset_1(sK2,sK2,sK4) = sK2
    | v1_funct_2(sK3,sK2,sK2) != iProver_top
    | v1_funct_2(sK4,sK2,sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2863,c_2870])).

cnf(c_9025,plain,
    ( k2_relat_1(sK4) = sK2
    | v1_funct_2(sK3,sK2,sK2) != iProver_top
    | v1_funct_2(sK4,sK2,sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9024,c_3990])).

cnf(c_44,plain,
    ( v1_funct_2(sK3,sK2,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_10582,plain,
    ( k2_relat_1(sK4) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9025,c_43,c_44,c_46,c_47,c_48,c_50])).

cnf(c_10584,plain,
    ( k2_relset_1(sK2,sK2,sK4) = sK2 ),
    inference(demodulation,[status(thm)],[c_10582,c_3990])).

cnf(c_10586,plain,
    ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(sK2)
    | sK2 = k1_xboole_0
    | v1_funct_2(sK4,sK2,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_10584,c_2867])).

cnf(c_12350,plain,
    ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(sK2)
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5663,c_47,c_48,c_49,c_50,c_5828,c_10586])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2887,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3636,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2862,c_2887])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2889,plain,
    ( k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_5810,plain,
    ( k2_relat_1(k5_relat_1(sK4,k2_funct_1(sK4))) = k1_relat_1(sK4)
    | v1_funct_1(sK4) != iProver_top
    | v2_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3636,c_2889])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2885,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3999,plain,
    ( k1_relset_1(sK2,sK2,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_2862,c_2885])).

cnf(c_5543,plain,
    ( k1_relat_1(sK4) = sK2 ),
    inference(demodulation,[status(thm)],[c_5541,c_3999])).

cnf(c_5813,plain,
    ( k2_relat_1(k5_relat_1(sK4,k2_funct_1(sK4))) = sK2
    | v1_funct_1(sK4) != iProver_top
    | v2_funct_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5810,c_5543])).

cnf(c_15463,plain,
    ( k2_relat_1(k5_relat_1(sK4,k2_funct_1(sK4))) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5813,c_47,c_49,c_5828])).

cnf(c_15465,plain,
    ( k2_relat_1(k6_partfun1(sK2)) = sK2
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_12350,c_15463])).

cnf(c_80638,plain,
    ( k2_relat_1(sK3) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_79830,c_42,c_41,c_40,c_39,c_35,c_1,c_1037,c_2977,c_3032,c_3429,c_4751,c_5545,c_15465,c_26072])).

cnf(c_80644,plain,
    ( k2_relset_1(sK2,sK2,sK3) = sK2 ),
    inference(demodulation,[status(thm)],[c_80638,c_3991])).

cnf(c_2179,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | r2_relset_1(X4,X5,X6,X7)
    | X4 != X0
    | X5 != X1
    | X6 != X2
    | X7 != X3 ),
    theory(equality)).

cnf(c_3507,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | r2_relset_1(X4,X5,sK4,k2_funct_1(sK3))
    | X4 != X0
    | X5 != X1
    | k2_funct_1(sK3) != X3
    | sK4 != X2 ),
    inference(instantiation,[status(thm)],[c_2179])).

cnf(c_4317,plain,
    ( ~ r2_relset_1(X0,X1,sK4,X2)
    | r2_relset_1(X3,X4,sK4,k2_funct_1(sK3))
    | X3 != X0
    | X4 != X1
    | k2_funct_1(sK3) != X2
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_3507])).

cnf(c_21313,plain,
    ( r2_relset_1(X0,X1,sK4,k2_funct_1(sK3))
    | ~ r2_relset_1(X2,X3,sK4,sK4)
    | X0 != X2
    | X1 != X3
    | k2_funct_1(sK3) != sK4
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_4317])).

cnf(c_21316,plain,
    ( r2_relset_1(sK2,sK2,sK4,k2_funct_1(sK3))
    | ~ r2_relset_1(sK2,sK2,sK4,sK4)
    | k2_funct_1(sK3) != sK4
    | sK4 != sK4
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_21313])).

cnf(c_5829,plain,
    ( v3_funct_2(sK3,sK2,sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2858,c_2879])).

cnf(c_5843,plain,
    ( ~ v3_funct_2(sK3,sK2,sK2)
    | ~ v1_funct_1(sK3)
    | v2_funct_1(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5829])).

cnf(c_2168,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_4657,plain,
    ( sK2 != X0
    | sK2 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_2168])).

cnf(c_4658,plain,
    ( sK2 != sK2
    | sK2 = k1_xboole_0
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_4657])).

cnf(c_13,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_2883,plain,
    ( r2_relset_1(X0,X1,X2,X2) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3857,plain,
    ( r2_relset_1(sK2,sK2,sK4,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2862,c_2883])).

cnf(c_3868,plain,
    ( r2_relset_1(sK2,sK2,sK4,sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3857])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_3199,plain,
    ( ~ v1_funct_2(sK3,sK2,sK2)
    | ~ v3_funct_2(sK3,sK2,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK3)
    | k2_funct_2(sK2,sK3) = k2_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_2955,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | r2_relset_1(sK2,sK2,sK4,k2_funct_2(sK2,sK3))
    | k2_funct_2(sK2,sK3) != X3
    | sK4 != X2
    | sK2 != X1
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_2179])).

cnf(c_3005,plain,
    ( ~ r2_relset_1(X0,X1,sK4,X2)
    | r2_relset_1(sK2,sK2,sK4,k2_funct_2(sK2,sK3))
    | k2_funct_2(sK2,sK3) != X2
    | sK4 != sK4
    | sK2 != X1
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_2955])).

cnf(c_3119,plain,
    ( ~ r2_relset_1(X0,X1,sK4,k2_funct_1(sK3))
    | r2_relset_1(sK2,sK2,sK4,k2_funct_2(sK2,sK3))
    | k2_funct_2(sK2,sK3) != k2_funct_1(sK3)
    | sK4 != sK4
    | sK2 != X1
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_3005])).

cnf(c_3121,plain,
    ( r2_relset_1(sK2,sK2,sK4,k2_funct_2(sK2,sK3))
    | ~ r2_relset_1(sK2,sK2,sK4,k2_funct_1(sK3))
    | k2_funct_2(sK2,sK3) != k2_funct_1(sK3)
    | sK4 != sK4
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_3119])).

cnf(c_2167,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3058,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_2167])).

cnf(c_2204,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_2167])).

cnf(c_129061,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0(sK2))) ),
    inference(grounding,[status(thm)],[c_4751:[bind(X0,$fot(sK2))]])).

cnf(c_129062,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0(sK2)))
    | ~ v1_xboole_0(sK0(sK2))
    | v1_xboole_0(k1_xboole_0) ),
    inference(grounding,[status(thm)],[c_3429:[bind(X0,$fot(sK2))]])).

cnf(c_129063,plain,
    ( v1_xboole_0(sK0(sK2)) ),
    inference(grounding,[status(thm)],[c_1:[bind(X0,$fot(sK2))]])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_129060,c_80644,c_26072,c_21316,c_5843,c_5545,c_129061,c_4658,c_3868,c_129062,c_3199,c_3121,c_3058,c_3032,c_2977,c_2204,c_1037,c_129063,c_33,c_34,c_35,c_37,c_38,c_39,c_40,c_41,c_42])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:40:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 55.77/7.52  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 55.77/7.52  
% 55.77/7.52  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 55.77/7.52  
% 55.77/7.52  ------  iProver source info
% 55.77/7.52  
% 55.77/7.52  git: date: 2020-06-30 10:37:57 +0100
% 55.77/7.52  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 55.77/7.52  git: non_committed_changes: false
% 55.77/7.52  git: last_make_outside_of_git: false
% 55.77/7.52  
% 55.77/7.52  ------ 
% 55.77/7.52  
% 55.77/7.52  ------ Input Options
% 55.77/7.52  
% 55.77/7.52  --out_options                           all
% 55.77/7.52  --tptp_safe_out                         true
% 55.77/7.52  --problem_path                          ""
% 55.77/7.52  --include_path                          ""
% 55.77/7.52  --clausifier                            res/vclausify_rel
% 55.77/7.52  --clausifier_options                    ""
% 55.77/7.52  --stdin                                 false
% 55.77/7.52  --stats_out                             all
% 55.77/7.52  
% 55.77/7.52  ------ General Options
% 55.77/7.52  
% 55.77/7.52  --fof                                   false
% 55.77/7.52  --time_out_real                         305.
% 55.77/7.52  --time_out_virtual                      -1.
% 55.77/7.52  --symbol_type_check                     false
% 55.77/7.52  --clausify_out                          false
% 55.77/7.52  --sig_cnt_out                           false
% 55.77/7.52  --trig_cnt_out                          false
% 55.77/7.52  --trig_cnt_out_tolerance                1.
% 55.77/7.52  --trig_cnt_out_sk_spl                   false
% 55.77/7.52  --abstr_cl_out                          false
% 55.77/7.52  
% 55.77/7.52  ------ Global Options
% 55.77/7.52  
% 55.77/7.52  --schedule                              default
% 55.77/7.52  --add_important_lit                     false
% 55.77/7.52  --prop_solver_per_cl                    1000
% 55.77/7.52  --min_unsat_core                        false
% 55.77/7.52  --soft_assumptions                      false
% 55.77/7.52  --soft_lemma_size                       3
% 55.77/7.52  --prop_impl_unit_size                   0
% 55.77/7.52  --prop_impl_unit                        []
% 55.77/7.52  --share_sel_clauses                     true
% 55.77/7.52  --reset_solvers                         false
% 55.77/7.52  --bc_imp_inh                            [conj_cone]
% 55.77/7.52  --conj_cone_tolerance                   3.
% 55.77/7.52  --extra_neg_conj                        none
% 55.77/7.52  --large_theory_mode                     true
% 55.77/7.52  --prolific_symb_bound                   200
% 55.77/7.52  --lt_threshold                          2000
% 55.77/7.52  --clause_weak_htbl                      true
% 55.77/7.52  --gc_record_bc_elim                     false
% 55.77/7.52  
% 55.77/7.52  ------ Preprocessing Options
% 55.77/7.52  
% 55.77/7.52  --preprocessing_flag                    true
% 55.77/7.52  --time_out_prep_mult                    0.1
% 55.77/7.52  --splitting_mode                        input
% 55.77/7.52  --splitting_grd                         true
% 55.77/7.52  --splitting_cvd                         false
% 55.77/7.52  --splitting_cvd_svl                     false
% 55.77/7.52  --splitting_nvd                         32
% 55.77/7.52  --sub_typing                            true
% 55.77/7.52  --prep_gs_sim                           true
% 55.77/7.52  --prep_unflatten                        true
% 55.77/7.52  --prep_res_sim                          true
% 55.77/7.52  --prep_upred                            true
% 55.77/7.52  --prep_sem_filter                       exhaustive
% 55.77/7.52  --prep_sem_filter_out                   false
% 55.77/7.52  --pred_elim                             true
% 55.77/7.52  --res_sim_input                         true
% 55.77/7.52  --eq_ax_congr_red                       true
% 55.77/7.52  --pure_diseq_elim                       true
% 55.77/7.52  --brand_transform                       false
% 55.77/7.52  --non_eq_to_eq                          false
% 55.77/7.52  --prep_def_merge                        true
% 55.77/7.52  --prep_def_merge_prop_impl              false
% 55.77/7.52  --prep_def_merge_mbd                    true
% 55.77/7.52  --prep_def_merge_tr_red                 false
% 55.77/7.52  --prep_def_merge_tr_cl                  false
% 55.77/7.52  --smt_preprocessing                     true
% 55.77/7.52  --smt_ac_axioms                         fast
% 55.77/7.52  --preprocessed_out                      false
% 55.77/7.52  --preprocessed_stats                    false
% 55.77/7.52  
% 55.77/7.52  ------ Abstraction refinement Options
% 55.77/7.52  
% 55.77/7.52  --abstr_ref                             []
% 55.77/7.52  --abstr_ref_prep                        false
% 55.77/7.52  --abstr_ref_until_sat                   false
% 55.77/7.52  --abstr_ref_sig_restrict                funpre
% 55.77/7.52  --abstr_ref_af_restrict_to_split_sk     false
% 55.77/7.52  --abstr_ref_under                       []
% 55.77/7.52  
% 55.77/7.52  ------ SAT Options
% 55.77/7.52  
% 55.77/7.52  --sat_mode                              false
% 55.77/7.52  --sat_fm_restart_options                ""
% 55.77/7.52  --sat_gr_def                            false
% 55.77/7.52  --sat_epr_types                         true
% 55.77/7.52  --sat_non_cyclic_types                  false
% 55.77/7.52  --sat_finite_models                     false
% 55.77/7.52  --sat_fm_lemmas                         false
% 55.77/7.52  --sat_fm_prep                           false
% 55.77/7.52  --sat_fm_uc_incr                        true
% 55.77/7.52  --sat_out_model                         small
% 55.77/7.52  --sat_out_clauses                       false
% 55.77/7.52  
% 55.77/7.52  ------ QBF Options
% 55.77/7.52  
% 55.77/7.52  --qbf_mode                              false
% 55.77/7.52  --qbf_elim_univ                         false
% 55.77/7.52  --qbf_dom_inst                          none
% 55.77/7.52  --qbf_dom_pre_inst                      false
% 55.77/7.52  --qbf_sk_in                             false
% 55.77/7.52  --qbf_pred_elim                         true
% 55.77/7.52  --qbf_split                             512
% 55.77/7.52  
% 55.77/7.52  ------ BMC1 Options
% 55.77/7.52  
% 55.77/7.52  --bmc1_incremental                      false
% 55.77/7.52  --bmc1_axioms                           reachable_all
% 55.77/7.52  --bmc1_min_bound                        0
% 55.77/7.52  --bmc1_max_bound                        -1
% 55.77/7.52  --bmc1_max_bound_default                -1
% 55.77/7.52  --bmc1_symbol_reachability              true
% 55.77/7.52  --bmc1_property_lemmas                  false
% 55.77/7.52  --bmc1_k_induction                      false
% 55.77/7.52  --bmc1_non_equiv_states                 false
% 55.77/7.52  --bmc1_deadlock                         false
% 55.77/7.52  --bmc1_ucm                              false
% 55.77/7.52  --bmc1_add_unsat_core                   none
% 55.77/7.52  --bmc1_unsat_core_children              false
% 55.77/7.52  --bmc1_unsat_core_extrapolate_axioms    false
% 55.77/7.52  --bmc1_out_stat                         full
% 55.77/7.52  --bmc1_ground_init                      false
% 55.77/7.52  --bmc1_pre_inst_next_state              false
% 55.77/7.52  --bmc1_pre_inst_state                   false
% 55.77/7.52  --bmc1_pre_inst_reach_state             false
% 55.77/7.52  --bmc1_out_unsat_core                   false
% 55.77/7.52  --bmc1_aig_witness_out                  false
% 55.77/7.52  --bmc1_verbose                          false
% 55.77/7.52  --bmc1_dump_clauses_tptp                false
% 55.77/7.52  --bmc1_dump_unsat_core_tptp             false
% 55.77/7.52  --bmc1_dump_file                        -
% 55.77/7.52  --bmc1_ucm_expand_uc_limit              128
% 55.77/7.52  --bmc1_ucm_n_expand_iterations          6
% 55.77/7.52  --bmc1_ucm_extend_mode                  1
% 55.77/7.52  --bmc1_ucm_init_mode                    2
% 55.77/7.52  --bmc1_ucm_cone_mode                    none
% 55.77/7.52  --bmc1_ucm_reduced_relation_type        0
% 55.77/7.52  --bmc1_ucm_relax_model                  4
% 55.77/7.52  --bmc1_ucm_full_tr_after_sat            true
% 55.77/7.52  --bmc1_ucm_expand_neg_assumptions       false
% 55.77/7.52  --bmc1_ucm_layered_model                none
% 55.77/7.52  --bmc1_ucm_max_lemma_size               10
% 55.77/7.52  
% 55.77/7.52  ------ AIG Options
% 55.77/7.52  
% 55.77/7.52  --aig_mode                              false
% 55.77/7.52  
% 55.77/7.52  ------ Instantiation Options
% 55.77/7.52  
% 55.77/7.52  --instantiation_flag                    true
% 55.77/7.52  --inst_sos_flag                         true
% 55.77/7.52  --inst_sos_phase                        true
% 55.77/7.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 55.77/7.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 55.77/7.52  --inst_lit_sel_side                     num_symb
% 55.77/7.52  --inst_solver_per_active                1400
% 55.77/7.52  --inst_solver_calls_frac                1.
% 55.77/7.52  --inst_passive_queue_type               priority_queues
% 55.77/7.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 55.77/7.52  --inst_passive_queues_freq              [25;2]
% 55.77/7.52  --inst_dismatching                      true
% 55.77/7.52  --inst_eager_unprocessed_to_passive     true
% 55.77/7.52  --inst_prop_sim_given                   true
% 55.77/7.52  --inst_prop_sim_new                     false
% 55.77/7.52  --inst_subs_new                         false
% 55.77/7.52  --inst_eq_res_simp                      false
% 55.77/7.52  --inst_subs_given                       false
% 55.77/7.52  --inst_orphan_elimination               true
% 55.77/7.52  --inst_learning_loop_flag               true
% 55.77/7.52  --inst_learning_start                   3000
% 55.77/7.52  --inst_learning_factor                  2
% 55.77/7.52  --inst_start_prop_sim_after_learn       3
% 55.77/7.52  --inst_sel_renew                        solver
% 55.77/7.52  --inst_lit_activity_flag                true
% 55.77/7.52  --inst_restr_to_given                   false
% 55.77/7.52  --inst_activity_threshold               500
% 55.77/7.52  --inst_out_proof                        true
% 55.77/7.52  
% 55.77/7.52  ------ Resolution Options
% 55.77/7.52  
% 55.77/7.52  --resolution_flag                       true
% 55.77/7.52  --res_lit_sel                           adaptive
% 55.77/7.52  --res_lit_sel_side                      none
% 55.77/7.52  --res_ordering                          kbo
% 55.77/7.52  --res_to_prop_solver                    active
% 55.77/7.52  --res_prop_simpl_new                    false
% 55.77/7.52  --res_prop_simpl_given                  true
% 55.77/7.52  --res_passive_queue_type                priority_queues
% 55.77/7.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 55.77/7.52  --res_passive_queues_freq               [15;5]
% 55.77/7.52  --res_forward_subs                      full
% 55.77/7.52  --res_backward_subs                     full
% 55.77/7.52  --res_forward_subs_resolution           true
% 55.77/7.52  --res_backward_subs_resolution          true
% 55.77/7.52  --res_orphan_elimination                true
% 55.77/7.52  --res_time_limit                        2.
% 55.77/7.52  --res_out_proof                         true
% 55.77/7.52  
% 55.77/7.52  ------ Superposition Options
% 55.77/7.52  
% 55.77/7.52  --superposition_flag                    true
% 55.77/7.52  --sup_passive_queue_type                priority_queues
% 55.77/7.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 55.77/7.52  --sup_passive_queues_freq               [8;1;4]
% 55.77/7.52  --demod_completeness_check              fast
% 55.77/7.52  --demod_use_ground                      true
% 55.77/7.52  --sup_to_prop_solver                    passive
% 55.77/7.52  --sup_prop_simpl_new                    true
% 55.77/7.52  --sup_prop_simpl_given                  true
% 55.77/7.52  --sup_fun_splitting                     true
% 55.77/7.52  --sup_smt_interval                      50000
% 55.77/7.52  
% 55.77/7.52  ------ Superposition Simplification Setup
% 55.77/7.52  
% 55.77/7.52  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 55.77/7.52  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 55.77/7.52  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 55.77/7.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 55.77/7.52  --sup_full_triv                         [TrivRules;PropSubs]
% 55.77/7.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 55.77/7.52  --sup_full_bw                           [BwDemod;BwSubsumption]
% 55.77/7.52  --sup_immed_triv                        [TrivRules]
% 55.77/7.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 55.77/7.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 55.77/7.52  --sup_immed_bw_main                     []
% 55.77/7.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 55.77/7.52  --sup_input_triv                        [Unflattening;TrivRules]
% 55.77/7.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 55.77/7.52  --sup_input_bw                          []
% 55.77/7.52  
% 55.77/7.52  ------ Combination Options
% 55.77/7.52  
% 55.77/7.52  --comb_res_mult                         3
% 55.77/7.52  --comb_sup_mult                         2
% 55.77/7.52  --comb_inst_mult                        10
% 55.77/7.52  
% 55.77/7.52  ------ Debug Options
% 55.77/7.52  
% 55.77/7.52  --dbg_backtrace                         false
% 55.77/7.52  --dbg_dump_prop_clauses                 false
% 55.77/7.52  --dbg_dump_prop_clauses_file            -
% 55.77/7.52  --dbg_out_stat                          false
% 55.77/7.52  ------ Parsing...
% 55.77/7.52  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 55.77/7.52  
% 55.77/7.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 55.77/7.52  
% 55.77/7.52  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 55.77/7.52  
% 55.77/7.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 55.77/7.52  ------ Proving...
% 55.77/7.52  ------ Problem Properties 
% 55.77/7.52  
% 55.77/7.52  
% 55.77/7.52  clauses                                 42
% 55.77/7.52  conjectures                             10
% 55.77/7.52  EPR                                     6
% 55.77/7.52  Horn                                    37
% 55.77/7.52  unary                                   14
% 55.77/7.52  binary                                  5
% 55.77/7.52  lits                                    143
% 55.77/7.52  lits eq                                 22
% 55.77/7.52  fd_pure                                 0
% 55.77/7.52  fd_pseudo                               0
% 55.77/7.52  fd_cond                                 2
% 55.77/7.52  fd_pseudo_cond                          2
% 55.77/7.52  AC symbols                              0
% 55.77/7.52  
% 55.77/7.52  ------ Schedule dynamic 5 is on 
% 55.77/7.52  
% 55.77/7.52  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 55.77/7.52  
% 55.77/7.52  
% 55.77/7.52  ------ 
% 55.77/7.52  Current options:
% 55.77/7.52  ------ 
% 55.77/7.52  
% 55.77/7.52  ------ Input Options
% 55.77/7.52  
% 55.77/7.52  --out_options                           all
% 55.77/7.52  --tptp_safe_out                         true
% 55.77/7.52  --problem_path                          ""
% 55.77/7.52  --include_path                          ""
% 55.77/7.52  --clausifier                            res/vclausify_rel
% 55.77/7.52  --clausifier_options                    ""
% 55.77/7.52  --stdin                                 false
% 55.77/7.52  --stats_out                             all
% 55.77/7.52  
% 55.77/7.52  ------ General Options
% 55.77/7.52  
% 55.77/7.52  --fof                                   false
% 55.77/7.52  --time_out_real                         305.
% 55.77/7.52  --time_out_virtual                      -1.
% 55.77/7.52  --symbol_type_check                     false
% 55.77/7.52  --clausify_out                          false
% 55.77/7.52  --sig_cnt_out                           false
% 55.77/7.52  --trig_cnt_out                          false
% 55.77/7.52  --trig_cnt_out_tolerance                1.
% 55.77/7.52  --trig_cnt_out_sk_spl                   false
% 55.77/7.52  --abstr_cl_out                          false
% 55.77/7.52  
% 55.77/7.52  ------ Global Options
% 55.77/7.52  
% 55.77/7.52  --schedule                              default
% 55.77/7.52  --add_important_lit                     false
% 55.77/7.52  --prop_solver_per_cl                    1000
% 55.77/7.52  --min_unsat_core                        false
% 55.77/7.52  --soft_assumptions                      false
% 55.77/7.52  --soft_lemma_size                       3
% 55.77/7.52  --prop_impl_unit_size                   0
% 55.77/7.52  --prop_impl_unit                        []
% 55.77/7.52  --share_sel_clauses                     true
% 55.77/7.52  --reset_solvers                         false
% 55.77/7.52  --bc_imp_inh                            [conj_cone]
% 55.77/7.52  --conj_cone_tolerance                   3.
% 55.77/7.52  --extra_neg_conj                        none
% 55.77/7.52  --large_theory_mode                     true
% 55.77/7.52  --prolific_symb_bound                   200
% 55.77/7.52  --lt_threshold                          2000
% 55.77/7.52  --clause_weak_htbl                      true
% 55.77/7.52  --gc_record_bc_elim                     false
% 55.77/7.52  
% 55.77/7.52  ------ Preprocessing Options
% 55.77/7.52  
% 55.77/7.52  --preprocessing_flag                    true
% 55.77/7.52  --time_out_prep_mult                    0.1
% 55.77/7.52  --splitting_mode                        input
% 55.77/7.52  --splitting_grd                         true
% 55.77/7.52  --splitting_cvd                         false
% 55.77/7.52  --splitting_cvd_svl                     false
% 55.77/7.52  --splitting_nvd                         32
% 55.77/7.52  --sub_typing                            true
% 55.77/7.52  --prep_gs_sim                           true
% 55.77/7.52  --prep_unflatten                        true
% 55.77/7.52  --prep_res_sim                          true
% 55.77/7.52  --prep_upred                            true
% 55.77/7.52  --prep_sem_filter                       exhaustive
% 55.77/7.52  --prep_sem_filter_out                   false
% 55.77/7.52  --pred_elim                             true
% 55.77/7.52  --res_sim_input                         true
% 55.77/7.52  --eq_ax_congr_red                       true
% 55.77/7.52  --pure_diseq_elim                       true
% 55.77/7.52  --brand_transform                       false
% 55.77/7.52  --non_eq_to_eq                          false
% 55.77/7.52  --prep_def_merge                        true
% 55.77/7.52  --prep_def_merge_prop_impl              false
% 55.77/7.52  --prep_def_merge_mbd                    true
% 55.77/7.52  --prep_def_merge_tr_red                 false
% 55.77/7.52  --prep_def_merge_tr_cl                  false
% 55.77/7.52  --smt_preprocessing                     true
% 55.77/7.52  --smt_ac_axioms                         fast
% 55.77/7.52  --preprocessed_out                      false
% 55.77/7.52  --preprocessed_stats                    false
% 55.77/7.52  
% 55.77/7.52  ------ Abstraction refinement Options
% 55.77/7.52  
% 55.77/7.52  --abstr_ref                             []
% 55.77/7.52  --abstr_ref_prep                        false
% 55.77/7.52  --abstr_ref_until_sat                   false
% 55.77/7.52  --abstr_ref_sig_restrict                funpre
% 55.77/7.52  --abstr_ref_af_restrict_to_split_sk     false
% 55.77/7.52  --abstr_ref_under                       []
% 55.77/7.52  
% 55.77/7.52  ------ SAT Options
% 55.77/7.52  
% 55.77/7.52  --sat_mode                              false
% 55.77/7.52  --sat_fm_restart_options                ""
% 55.77/7.52  --sat_gr_def                            false
% 55.77/7.52  --sat_epr_types                         true
% 55.77/7.52  --sat_non_cyclic_types                  false
% 55.77/7.52  --sat_finite_models                     false
% 55.77/7.52  --sat_fm_lemmas                         false
% 55.77/7.52  --sat_fm_prep                           false
% 55.77/7.52  --sat_fm_uc_incr                        true
% 55.77/7.52  --sat_out_model                         small
% 55.77/7.52  --sat_out_clauses                       false
% 55.77/7.52  
% 55.77/7.52  ------ QBF Options
% 55.77/7.52  
% 55.77/7.52  --qbf_mode                              false
% 55.77/7.52  --qbf_elim_univ                         false
% 55.77/7.52  --qbf_dom_inst                          none
% 55.77/7.52  --qbf_dom_pre_inst                      false
% 55.77/7.52  --qbf_sk_in                             false
% 55.77/7.52  --qbf_pred_elim                         true
% 55.77/7.52  --qbf_split                             512
% 55.77/7.52  
% 55.77/7.52  ------ BMC1 Options
% 55.77/7.52  
% 55.77/7.52  --bmc1_incremental                      false
% 55.77/7.52  --bmc1_axioms                           reachable_all
% 55.77/7.52  --bmc1_min_bound                        0
% 55.77/7.52  --bmc1_max_bound                        -1
% 55.77/7.52  --bmc1_max_bound_default                -1
% 55.77/7.52  --bmc1_symbol_reachability              true
% 55.77/7.52  --bmc1_property_lemmas                  false
% 55.77/7.52  --bmc1_k_induction                      false
% 55.77/7.52  --bmc1_non_equiv_states                 false
% 55.77/7.52  --bmc1_deadlock                         false
% 55.77/7.52  --bmc1_ucm                              false
% 55.77/7.52  --bmc1_add_unsat_core                   none
% 55.77/7.52  --bmc1_unsat_core_children              false
% 55.77/7.52  --bmc1_unsat_core_extrapolate_axioms    false
% 55.77/7.52  --bmc1_out_stat                         full
% 55.77/7.52  --bmc1_ground_init                      false
% 55.77/7.52  --bmc1_pre_inst_next_state              false
% 55.77/7.52  --bmc1_pre_inst_state                   false
% 55.77/7.52  --bmc1_pre_inst_reach_state             false
% 55.77/7.52  --bmc1_out_unsat_core                   false
% 55.77/7.52  --bmc1_aig_witness_out                  false
% 55.77/7.52  --bmc1_verbose                          false
% 55.77/7.52  --bmc1_dump_clauses_tptp                false
% 55.77/7.52  --bmc1_dump_unsat_core_tptp             false
% 55.77/7.52  --bmc1_dump_file                        -
% 55.77/7.52  --bmc1_ucm_expand_uc_limit              128
% 55.77/7.52  --bmc1_ucm_n_expand_iterations          6
% 55.77/7.52  --bmc1_ucm_extend_mode                  1
% 55.77/7.52  --bmc1_ucm_init_mode                    2
% 55.77/7.52  --bmc1_ucm_cone_mode                    none
% 55.77/7.52  --bmc1_ucm_reduced_relation_type        0
% 55.77/7.52  --bmc1_ucm_relax_model                  4
% 55.77/7.52  --bmc1_ucm_full_tr_after_sat            true
% 55.77/7.52  --bmc1_ucm_expand_neg_assumptions       false
% 55.77/7.52  --bmc1_ucm_layered_model                none
% 55.77/7.52  --bmc1_ucm_max_lemma_size               10
% 55.77/7.52  
% 55.77/7.52  ------ AIG Options
% 55.77/7.52  
% 55.77/7.52  --aig_mode                              false
% 55.77/7.52  
% 55.77/7.52  ------ Instantiation Options
% 55.77/7.52  
% 55.77/7.52  --instantiation_flag                    true
% 55.77/7.52  --inst_sos_flag                         true
% 55.77/7.52  --inst_sos_phase                        true
% 55.77/7.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 55.77/7.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 55.77/7.52  --inst_lit_sel_side                     none
% 55.77/7.52  --inst_solver_per_active                1400
% 55.77/7.52  --inst_solver_calls_frac                1.
% 55.77/7.52  --inst_passive_queue_type               priority_queues
% 55.77/7.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 55.77/7.52  --inst_passive_queues_freq              [25;2]
% 55.77/7.52  --inst_dismatching                      true
% 55.77/7.52  --inst_eager_unprocessed_to_passive     true
% 55.77/7.52  --inst_prop_sim_given                   true
% 55.77/7.52  --inst_prop_sim_new                     false
% 55.77/7.52  --inst_subs_new                         false
% 55.77/7.52  --inst_eq_res_simp                      false
% 55.77/7.52  --inst_subs_given                       false
% 55.77/7.52  --inst_orphan_elimination               true
% 55.77/7.52  --inst_learning_loop_flag               true
% 55.77/7.52  --inst_learning_start                   3000
% 55.77/7.52  --inst_learning_factor                  2
% 55.77/7.52  --inst_start_prop_sim_after_learn       3
% 55.77/7.52  --inst_sel_renew                        solver
% 55.77/7.52  --inst_lit_activity_flag                true
% 55.77/7.52  --inst_restr_to_given                   false
% 55.77/7.52  --inst_activity_threshold               500
% 55.77/7.52  --inst_out_proof                        true
% 55.77/7.52  
% 55.77/7.52  ------ Resolution Options
% 55.77/7.52  
% 55.77/7.52  --resolution_flag                       false
% 55.77/7.52  --res_lit_sel                           adaptive
% 55.77/7.52  --res_lit_sel_side                      none
% 55.77/7.52  --res_ordering                          kbo
% 55.77/7.52  --res_to_prop_solver                    active
% 55.77/7.52  --res_prop_simpl_new                    false
% 55.77/7.52  --res_prop_simpl_given                  true
% 55.77/7.52  --res_passive_queue_type                priority_queues
% 55.77/7.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 55.77/7.52  --res_passive_queues_freq               [15;5]
% 55.77/7.52  --res_forward_subs                      full
% 55.77/7.52  --res_backward_subs                     full
% 55.77/7.52  --res_forward_subs_resolution           true
% 55.77/7.52  --res_backward_subs_resolution          true
% 55.77/7.52  --res_orphan_elimination                true
% 55.77/7.52  --res_time_limit                        2.
% 55.77/7.52  --res_out_proof                         true
% 55.77/7.52  
% 55.77/7.52  ------ Superposition Options
% 55.77/7.52  
% 55.77/7.52  --superposition_flag                    true
% 55.77/7.52  --sup_passive_queue_type                priority_queues
% 55.77/7.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 55.77/7.52  --sup_passive_queues_freq               [8;1;4]
% 55.77/7.52  --demod_completeness_check              fast
% 55.77/7.52  --demod_use_ground                      true
% 55.77/7.52  --sup_to_prop_solver                    passive
% 55.77/7.52  --sup_prop_simpl_new                    true
% 55.77/7.52  --sup_prop_simpl_given                  true
% 55.77/7.52  --sup_fun_splitting                     true
% 55.77/7.52  --sup_smt_interval                      50000
% 55.77/7.52  
% 55.77/7.52  ------ Superposition Simplification Setup
% 55.77/7.52  
% 55.77/7.52  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 55.77/7.52  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 55.77/7.52  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 55.77/7.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 55.77/7.52  --sup_full_triv                         [TrivRules;PropSubs]
% 55.77/7.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 55.77/7.52  --sup_full_bw                           [BwDemod;BwSubsumption]
% 55.77/7.52  --sup_immed_triv                        [TrivRules]
% 55.77/7.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 55.77/7.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 55.77/7.52  --sup_immed_bw_main                     []
% 55.77/7.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 55.77/7.52  --sup_input_triv                        [Unflattening;TrivRules]
% 55.77/7.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 55.77/7.52  --sup_input_bw                          []
% 55.77/7.52  
% 55.77/7.52  ------ Combination Options
% 55.77/7.52  
% 55.77/7.52  --comb_res_mult                         3
% 55.77/7.52  --comb_sup_mult                         2
% 55.77/7.52  --comb_inst_mult                        10
% 55.77/7.52  
% 55.77/7.52  ------ Debug Options
% 55.77/7.52  
% 55.77/7.52  --dbg_backtrace                         false
% 55.77/7.52  --dbg_dump_prop_clauses                 false
% 55.77/7.52  --dbg_dump_prop_clauses_file            -
% 55.77/7.52  --dbg_out_stat                          false
% 55.77/7.52  
% 55.77/7.52  
% 55.77/7.52  
% 55.77/7.52  
% 55.77/7.52  ------ Proving...
% 55.77/7.52  
% 55.77/7.52  
% 55.77/7.52  % SZS status Theorem for theBenchmark.p
% 55.77/7.52  
% 55.77/7.52  % SZS output start CNFRefutation for theBenchmark.p
% 55.77/7.52  
% 55.77/7.52  fof(f22,axiom,(
% 55.77/7.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 55.77/7.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.77/7.52  
% 55.77/7.52  fof(f57,plain,(
% 55.77/7.52    ! [X0,X1,X2] : (! [X3] : (((k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | (~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 55.77/7.52    inference(ennf_transformation,[],[f22])).
% 55.77/7.52  
% 55.77/7.52  fof(f58,plain,(
% 55.77/7.52    ! [X0,X1,X2] : (! [X3] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 55.77/7.52    inference(flattening,[],[f57])).
% 55.77/7.52  
% 55.77/7.52  fof(f102,plain,(
% 55.77/7.52    ( ! [X2,X0,X3,X1] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 55.77/7.52    inference(cnf_transformation,[],[f58])).
% 55.77/7.52  
% 55.77/7.52  fof(f24,conjecture,(
% 55.77/7.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 55.77/7.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.77/7.52  
% 55.77/7.52  fof(f25,negated_conjecture,(
% 55.77/7.52    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 55.77/7.52    inference(negated_conjecture,[],[f24])).
% 55.77/7.52  
% 55.77/7.52  fof(f61,plain,(
% 55.77/7.52    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 55.77/7.52    inference(ennf_transformation,[],[f25])).
% 55.77/7.52  
% 55.77/7.52  fof(f62,plain,(
% 55.77/7.52    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 55.77/7.52    inference(flattening,[],[f61])).
% 55.77/7.52  
% 55.77/7.52  fof(f69,plain,(
% 55.77/7.52    ( ! [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (~r2_relset_1(X0,X0,sK4,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,sK4),k6_partfun1(X0)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(sK4,X0,X0) & v1_funct_2(sK4,X0,X0) & v1_funct_1(sK4))) )),
% 55.77/7.52    introduced(choice_axiom,[])).
% 55.77/7.52  
% 55.77/7.52  fof(f68,plain,(
% 55.77/7.52    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK2,sK2,X2,k2_funct_2(sK2,sK3)) & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK3,X2),k6_partfun1(sK2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v3_funct_2(X2,sK2,sK2) & v1_funct_2(X2,sK2,sK2) & v1_funct_1(X2)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v3_funct_2(sK3,sK2,sK2) & v1_funct_2(sK3,sK2,sK2) & v1_funct_1(sK3))),
% 55.77/7.52    introduced(choice_axiom,[])).
% 55.77/7.52  
% 55.77/7.52  fof(f70,plain,(
% 55.77/7.52    (~r2_relset_1(sK2,sK2,sK4,k2_funct_2(sK2,sK3)) & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK3,sK4),k6_partfun1(sK2)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v3_funct_2(sK4,sK2,sK2) & v1_funct_2(sK4,sK2,sK2) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v3_funct_2(sK3,sK2,sK2) & v1_funct_2(sK3,sK2,sK2) & v1_funct_1(sK3)),
% 55.77/7.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f62,f69,f68])).
% 55.77/7.52  
% 55.77/7.52  fof(f112,plain,(
% 55.77/7.52    r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK3,sK4),k6_partfun1(sK2))),
% 55.77/7.52    inference(cnf_transformation,[],[f70])).
% 55.77/7.52  
% 55.77/7.52  fof(f15,axiom,(
% 55.77/7.52    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 55.77/7.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.77/7.52  
% 55.77/7.52  fof(f45,plain,(
% 55.77/7.52    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 55.77/7.52    inference(ennf_transformation,[],[f15])).
% 55.77/7.52  
% 55.77/7.52  fof(f46,plain,(
% 55.77/7.52    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 55.77/7.52    inference(flattening,[],[f45])).
% 55.77/7.52  
% 55.77/7.52  fof(f91,plain,(
% 55.77/7.52    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 55.77/7.52    inference(cnf_transformation,[],[f46])).
% 55.77/7.52  
% 55.77/7.52  fof(f12,axiom,(
% 55.77/7.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 55.77/7.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.77/7.52  
% 55.77/7.52  fof(f39,plain,(
% 55.77/7.52    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 55.77/7.52    inference(ennf_transformation,[],[f12])).
% 55.77/7.52  
% 55.77/7.52  fof(f40,plain,(
% 55.77/7.52    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 55.77/7.52    inference(flattening,[],[f39])).
% 55.77/7.52  
% 55.77/7.52  fof(f65,plain,(
% 55.77/7.52    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 55.77/7.52    inference(nnf_transformation,[],[f40])).
% 55.77/7.52  
% 55.77/7.52  fof(f84,plain,(
% 55.77/7.52    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 55.77/7.52    inference(cnf_transformation,[],[f65])).
% 55.77/7.52  
% 55.77/7.52  fof(f104,plain,(
% 55.77/7.52    v1_funct_1(sK3)),
% 55.77/7.52    inference(cnf_transformation,[],[f70])).
% 55.77/7.52  
% 55.77/7.52  fof(f107,plain,(
% 55.77/7.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 55.77/7.52    inference(cnf_transformation,[],[f70])).
% 55.77/7.52  
% 55.77/7.52  fof(f108,plain,(
% 55.77/7.52    v1_funct_1(sK4)),
% 55.77/7.52    inference(cnf_transformation,[],[f70])).
% 55.77/7.52  
% 55.77/7.52  fof(f111,plain,(
% 55.77/7.52    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 55.77/7.52    inference(cnf_transformation,[],[f70])).
% 55.77/7.52  
% 55.77/7.52  fof(f17,axiom,(
% 55.77/7.52    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 55.77/7.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.77/7.52  
% 55.77/7.52  fof(f26,plain,(
% 55.77/7.52    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 55.77/7.52    inference(pure_predicate_removal,[],[f17])).
% 55.77/7.52  
% 55.77/7.52  fof(f96,plain,(
% 55.77/7.52    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 55.77/7.52    inference(cnf_transformation,[],[f26])).
% 55.77/7.52  
% 55.77/7.52  fof(f11,axiom,(
% 55.77/7.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 55.77/7.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.77/7.52  
% 55.77/7.52  fof(f38,plain,(
% 55.77/7.52    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 55.77/7.52    inference(ennf_transformation,[],[f11])).
% 55.77/7.52  
% 55.77/7.52  fof(f83,plain,(
% 55.77/7.52    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 55.77/7.52    inference(cnf_transformation,[],[f38])).
% 55.77/7.52  
% 55.77/7.52  fof(f20,axiom,(
% 55.77/7.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 55.77/7.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.77/7.52  
% 55.77/7.52  fof(f53,plain,(
% 55.77/7.52    ! [X0,X1,X2,X3] : (! [X4] : (((k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2) | (~v2_funct_1(X4) | k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 55.77/7.52    inference(ennf_transformation,[],[f20])).
% 55.77/7.52  
% 55.77/7.52  fof(f54,plain,(
% 55.77/7.52    ! [X0,X1,X2,X3] : (! [X4] : (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2 | ~v2_funct_1(X4) | k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2 | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 55.77/7.52    inference(flattening,[],[f53])).
% 55.77/7.52  
% 55.77/7.52  fof(f99,plain,(
% 55.77/7.52    ( ! [X4,X2,X0,X3,X1] : (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2 | ~v2_funct_1(X4) | k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2 | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 55.77/7.52    inference(cnf_transformation,[],[f54])).
% 55.77/7.52  
% 55.77/7.52  fof(f105,plain,(
% 55.77/7.52    v1_funct_2(sK3,sK2,sK2)),
% 55.77/7.52    inference(cnf_transformation,[],[f70])).
% 55.77/7.52  
% 55.77/7.52  fof(f106,plain,(
% 55.77/7.52    v3_funct_2(sK3,sK2,sK2)),
% 55.77/7.52    inference(cnf_transformation,[],[f70])).
% 55.77/7.52  
% 55.77/7.52  fof(f109,plain,(
% 55.77/7.52    v1_funct_2(sK4,sK2,sK2)),
% 55.77/7.52    inference(cnf_transformation,[],[f70])).
% 55.77/7.52  
% 55.77/7.52  fof(f110,plain,(
% 55.77/7.52    v3_funct_2(sK4,sK2,sK2)),
% 55.77/7.52    inference(cnf_transformation,[],[f70])).
% 55.77/7.52  
% 55.77/7.52  fof(f2,axiom,(
% 55.77/7.52    ! [X0] : ? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 55.77/7.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.77/7.52  
% 55.77/7.52  fof(f63,plain,(
% 55.77/7.52    ! [X0] : (? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (v1_xboole_0(sK0(X0)) & m1_subset_1(sK0(X0),k1_zfmisc_1(X0))))),
% 55.77/7.52    introduced(choice_axiom,[])).
% 55.77/7.52  
% 55.77/7.52  fof(f64,plain,(
% 55.77/7.52    ! [X0] : (v1_xboole_0(sK0(X0)) & m1_subset_1(sK0(X0),k1_zfmisc_1(X0)))),
% 55.77/7.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f2,f63])).
% 55.77/7.52  
% 55.77/7.52  fof(f73,plain,(
% 55.77/7.52    ( ! [X0] : (v1_xboole_0(sK0(X0))) )),
% 55.77/7.52    inference(cnf_transformation,[],[f64])).
% 55.77/7.52  
% 55.77/7.52  fof(f13,axiom,(
% 55.77/7.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => (! [X3] : (r2_hidden(X3,X0) => k11_relat_1(X1,X3) = k11_relat_1(X2,X3)) => r2_relset_1(X0,X0,X1,X2))))),
% 55.77/7.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.77/7.52  
% 55.77/7.52  fof(f41,plain,(
% 55.77/7.52    ! [X0,X1] : (! [X2] : ((r2_relset_1(X0,X0,X1,X2) | ? [X3] : (k11_relat_1(X1,X3) != k11_relat_1(X2,X3) & r2_hidden(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 55.77/7.52    inference(ennf_transformation,[],[f13])).
% 55.77/7.52  
% 55.77/7.52  fof(f42,plain,(
% 55.77/7.52    ! [X0,X1] : (! [X2] : (r2_relset_1(X0,X0,X1,X2) | ? [X3] : (k11_relat_1(X1,X3) != k11_relat_1(X2,X3) & r2_hidden(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 55.77/7.52    inference(flattening,[],[f41])).
% 55.77/7.52  
% 55.77/7.52  fof(f66,plain,(
% 55.77/7.52    ! [X2,X1,X0] : (? [X3] : (k11_relat_1(X1,X3) != k11_relat_1(X2,X3) & r2_hidden(X3,X0)) => (k11_relat_1(X1,sK1(X0,X1,X2)) != k11_relat_1(X2,sK1(X0,X1,X2)) & r2_hidden(sK1(X0,X1,X2),X0)))),
% 55.77/7.52    introduced(choice_axiom,[])).
% 55.77/7.52  
% 55.77/7.52  fof(f67,plain,(
% 55.77/7.52    ! [X0,X1] : (! [X2] : (r2_relset_1(X0,X0,X1,X2) | (k11_relat_1(X1,sK1(X0,X1,X2)) != k11_relat_1(X2,sK1(X0,X1,X2)) & r2_hidden(sK1(X0,X1,X2),X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 55.77/7.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f42,f66])).
% 55.77/7.52  
% 55.77/7.52  fof(f86,plain,(
% 55.77/7.52    ( ! [X2,X0,X1] : (r2_relset_1(X0,X0,X1,X2) | r2_hidden(sK1(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 55.77/7.52    inference(cnf_transformation,[],[f67])).
% 55.77/7.52  
% 55.77/7.52  fof(f113,plain,(
% 55.77/7.52    ~r2_relset_1(sK2,sK2,sK4,k2_funct_2(sK2,sK3))),
% 55.77/7.52    inference(cnf_transformation,[],[f70])).
% 55.77/7.52  
% 55.77/7.52  fof(f16,axiom,(
% 55.77/7.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 55.77/7.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.77/7.52  
% 55.77/7.52  fof(f47,plain,(
% 55.77/7.52    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 55.77/7.52    inference(ennf_transformation,[],[f16])).
% 55.77/7.52  
% 55.77/7.52  fof(f48,plain,(
% 55.77/7.52    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 55.77/7.52    inference(flattening,[],[f47])).
% 55.77/7.52  
% 55.77/7.52  fof(f95,plain,(
% 55.77/7.52    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 55.77/7.52    inference(cnf_transformation,[],[f48])).
% 55.77/7.52  
% 55.77/7.52  fof(f6,axiom,(
% 55.77/7.52    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 55.77/7.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.77/7.52  
% 55.77/7.52  fof(f32,plain,(
% 55.77/7.52    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 55.77/7.52    inference(ennf_transformation,[],[f6])).
% 55.77/7.52  
% 55.77/7.52  fof(f77,plain,(
% 55.77/7.52    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 55.77/7.52    inference(cnf_transformation,[],[f32])).
% 55.77/7.52  
% 55.77/7.52  fof(f4,axiom,(
% 55.77/7.52    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 55.77/7.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.77/7.52  
% 55.77/7.52  fof(f29,plain,(
% 55.77/7.52    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 55.77/7.52    inference(ennf_transformation,[],[f4])).
% 55.77/7.52  
% 55.77/7.52  fof(f75,plain,(
% 55.77/7.52    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 55.77/7.52    inference(cnf_transformation,[],[f29])).
% 55.77/7.52  
% 55.77/7.52  fof(f3,axiom,(
% 55.77/7.52    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 55.77/7.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.77/7.52  
% 55.77/7.52  fof(f74,plain,(
% 55.77/7.52    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 55.77/7.52    inference(cnf_transformation,[],[f3])).
% 55.77/7.52  
% 55.77/7.52  fof(f23,axiom,(
% 55.77/7.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 55.77/7.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.77/7.52  
% 55.77/7.52  fof(f59,plain,(
% 55.77/7.52    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 55.77/7.52    inference(ennf_transformation,[],[f23])).
% 55.77/7.52  
% 55.77/7.52  fof(f60,plain,(
% 55.77/7.52    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 55.77/7.52    inference(flattening,[],[f59])).
% 55.77/7.52  
% 55.77/7.52  fof(f103,plain,(
% 55.77/7.52    ( ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 55.77/7.52    inference(cnf_transformation,[],[f60])).
% 55.77/7.52  
% 55.77/7.52  fof(f9,axiom,(
% 55.77/7.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 55.77/7.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.77/7.52  
% 55.77/7.52  fof(f36,plain,(
% 55.77/7.52    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 55.77/7.52    inference(ennf_transformation,[],[f9])).
% 55.77/7.52  
% 55.77/7.52  fof(f81,plain,(
% 55.77/7.52    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 55.77/7.52    inference(cnf_transformation,[],[f36])).
% 55.77/7.52  
% 55.77/7.52  fof(f14,axiom,(
% 55.77/7.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 55.77/7.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.77/7.52  
% 55.77/7.52  fof(f27,plain,(
% 55.77/7.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_1(X2) & v1_funct_1(X2))))),
% 55.77/7.52    inference(pure_predicate_removal,[],[f14])).
% 55.77/7.52  
% 55.77/7.52  fof(f43,plain,(
% 55.77/7.52    ! [X0,X1,X2] : (((v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 55.77/7.52    inference(ennf_transformation,[],[f27])).
% 55.77/7.52  
% 55.77/7.52  fof(f44,plain,(
% 55.77/7.52    ! [X0,X1,X2] : ((v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 55.77/7.52    inference(flattening,[],[f43])).
% 55.77/7.52  
% 55.77/7.52  fof(f89,plain,(
% 55.77/7.52    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 55.77/7.52    inference(cnf_transformation,[],[f44])).
% 55.77/7.52  
% 55.77/7.52  fof(f21,axiom,(
% 55.77/7.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 55.77/7.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.77/7.52  
% 55.77/7.52  fof(f55,plain,(
% 55.77/7.52    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 55.77/7.52    inference(ennf_transformation,[],[f21])).
% 55.77/7.52  
% 55.77/7.52  fof(f56,plain,(
% 55.77/7.52    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 55.77/7.52    inference(flattening,[],[f55])).
% 55.77/7.52  
% 55.77/7.52  fof(f100,plain,(
% 55.77/7.52    ( ! [X2,X0,X1] : (k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 55.77/7.52    inference(cnf_transformation,[],[f56])).
% 55.77/7.52  
% 55.77/7.52  fof(f19,axiom,(
% 55.77/7.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 55.77/7.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.77/7.52  
% 55.77/7.52  fof(f51,plain,(
% 55.77/7.52    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 55.77/7.52    inference(ennf_transformation,[],[f19])).
% 55.77/7.52  
% 55.77/7.52  fof(f52,plain,(
% 55.77/7.52    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 55.77/7.52    inference(flattening,[],[f51])).
% 55.77/7.52  
% 55.77/7.52  fof(f98,plain,(
% 55.77/7.52    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 55.77/7.52    inference(cnf_transformation,[],[f52])).
% 55.77/7.52  
% 55.77/7.52  fof(f8,axiom,(
% 55.77/7.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 55.77/7.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.77/7.52  
% 55.77/7.52  fof(f35,plain,(
% 55.77/7.52    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 55.77/7.52    inference(ennf_transformation,[],[f8])).
% 55.77/7.52  
% 55.77/7.52  fof(f80,plain,(
% 55.77/7.52    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 55.77/7.52    inference(cnf_transformation,[],[f35])).
% 55.77/7.52  
% 55.77/7.52  fof(f7,axiom,(
% 55.77/7.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 55.77/7.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.77/7.52  
% 55.77/7.52  fof(f33,plain,(
% 55.77/7.52    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 55.77/7.52    inference(ennf_transformation,[],[f7])).
% 55.77/7.52  
% 55.77/7.52  fof(f34,plain,(
% 55.77/7.52    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 55.77/7.52    inference(flattening,[],[f33])).
% 55.77/7.52  
% 55.77/7.52  fof(f79,plain,(
% 55.77/7.52    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 55.77/7.52    inference(cnf_transformation,[],[f34])).
% 55.77/7.52  
% 55.77/7.52  fof(f10,axiom,(
% 55.77/7.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 55.77/7.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.77/7.52  
% 55.77/7.52  fof(f37,plain,(
% 55.77/7.52    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 55.77/7.52    inference(ennf_transformation,[],[f10])).
% 55.77/7.52  
% 55.77/7.52  fof(f82,plain,(
% 55.77/7.52    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 55.77/7.52    inference(cnf_transformation,[],[f37])).
% 55.77/7.52  
% 55.77/7.52  fof(f85,plain,(
% 55.77/7.52    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 55.77/7.52    inference(cnf_transformation,[],[f65])).
% 55.77/7.52  
% 55.77/7.52  fof(f114,plain,(
% 55.77/7.52    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 55.77/7.52    inference(equality_resolution,[],[f85])).
% 55.77/7.52  
% 55.77/7.52  fof(f18,axiom,(
% 55.77/7.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_1(X1) = k2_funct_2(X0,X1))),
% 55.77/7.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.77/7.52  
% 55.77/7.52  fof(f49,plain,(
% 55.77/7.52    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 55.77/7.52    inference(ennf_transformation,[],[f18])).
% 55.77/7.52  
% 55.77/7.52  fof(f50,plain,(
% 55.77/7.52    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 55.77/7.52    inference(flattening,[],[f49])).
% 55.77/7.52  
% 55.77/7.52  fof(f97,plain,(
% 55.77/7.52    ( ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 55.77/7.52    inference(cnf_transformation,[],[f50])).
% 55.77/7.52  
% 55.77/7.52  cnf(c_31,plain,
% 55.77/7.52      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 55.77/7.52      | ~ v1_funct_2(X3,X1,X0)
% 55.77/7.52      | ~ v1_funct_2(X2,X0,X1)
% 55.77/7.52      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 55.77/7.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 55.77/7.52      | ~ v1_funct_1(X2)
% 55.77/7.52      | ~ v1_funct_1(X3)
% 55.77/7.52      | ~ v2_funct_1(X2)
% 55.77/7.52      | k2_relset_1(X0,X1,X2) != X1
% 55.77/7.52      | k2_funct_1(X2) = X3
% 55.77/7.52      | k1_xboole_0 = X1
% 55.77/7.52      | k1_xboole_0 = X0 ),
% 55.77/7.52      inference(cnf_transformation,[],[f102]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_84745,plain,
% 55.77/7.52      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,sK3,X2),k6_partfun1(X0))
% 55.77/7.52      | ~ v1_funct_2(X2,X1,X0)
% 55.77/7.52      | ~ v1_funct_2(sK3,X0,X1)
% 55.77/7.52      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 55.77/7.52      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 55.77/7.52      | ~ v1_funct_1(X2)
% 55.77/7.52      | ~ v1_funct_1(sK3)
% 55.77/7.52      | ~ v2_funct_1(sK3)
% 55.77/7.52      | k2_relset_1(X0,X1,sK3) != X1
% 55.77/7.52      | k2_funct_1(sK3) = X2
% 55.77/7.52      | k1_xboole_0 = X0
% 55.77/7.52      | k1_xboole_0 = X1 ),
% 55.77/7.52      inference(instantiation,[status(thm)],[c_31]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_129058,plain,
% 55.77/7.52      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,sK3,sK4),k6_partfun1(X0))
% 55.77/7.52      | ~ v1_funct_2(sK3,X0,X1)
% 55.77/7.52      | ~ v1_funct_2(sK4,X1,X0)
% 55.77/7.52      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 55.77/7.52      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 55.77/7.52      | ~ v1_funct_1(sK3)
% 55.77/7.52      | ~ v1_funct_1(sK4)
% 55.77/7.52      | ~ v2_funct_1(sK3)
% 55.77/7.52      | k2_relset_1(X0,X1,sK3) != X1
% 55.77/7.52      | k2_funct_1(sK3) = sK4
% 55.77/7.52      | k1_xboole_0 = X0
% 55.77/7.52      | k1_xboole_0 = X1 ),
% 55.77/7.52      inference(instantiation,[status(thm)],[c_84745]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_129060,plain,
% 55.77/7.52      ( ~ r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK3,sK4),k6_partfun1(sK2))
% 55.77/7.52      | ~ v1_funct_2(sK3,sK2,sK2)
% 55.77/7.52      | ~ v1_funct_2(sK4,sK2,sK2)
% 55.77/7.52      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 55.77/7.52      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 55.77/7.52      | ~ v1_funct_1(sK3)
% 55.77/7.52      | ~ v1_funct_1(sK4)
% 55.77/7.52      | ~ v2_funct_1(sK3)
% 55.77/7.52      | k2_relset_1(sK2,sK2,sK3) != sK2
% 55.77/7.52      | k2_funct_1(sK3) = sK4
% 55.77/7.52      | k1_xboole_0 = sK2 ),
% 55.77/7.52      inference(instantiation,[status(thm)],[c_129058]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_34,negated_conjecture,
% 55.77/7.52      ( r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK3,sK4),k6_partfun1(sK2)) ),
% 55.77/7.52      inference(cnf_transformation,[],[f112]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_2863,plain,
% 55.77/7.52      ( r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK3,sK4),k6_partfun1(sK2)) = iProver_top ),
% 55.77/7.52      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_19,plain,
% 55.77/7.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 55.77/7.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 55.77/7.52      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 55.77/7.52      | ~ v1_funct_1(X0)
% 55.77/7.52      | ~ v1_funct_1(X3) ),
% 55.77/7.52      inference(cnf_transformation,[],[f91]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_2878,plain,
% 55.77/7.52      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 55.77/7.52      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 55.77/7.52      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 55.77/7.52      | v1_funct_1(X0) != iProver_top
% 55.77/7.52      | v1_funct_1(X3) != iProver_top ),
% 55.77/7.52      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_14,plain,
% 55.77/7.52      ( ~ r2_relset_1(X0,X1,X2,X3)
% 55.77/7.52      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 55.77/7.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 55.77/7.52      | X3 = X2 ),
% 55.77/7.52      inference(cnf_transformation,[],[f84]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_2882,plain,
% 55.77/7.52      ( X0 = X1
% 55.77/7.52      | r2_relset_1(X2,X3,X1,X0) != iProver_top
% 55.77/7.52      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 55.77/7.52      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top ),
% 55.77/7.52      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_8543,plain,
% 55.77/7.52      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = X6
% 55.77/7.52      | r2_relset_1(X0,X3,k1_partfun1(X0,X1,X2,X3,X4,X5),X6) != iProver_top
% 55.77/7.52      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 55.77/7.52      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 55.77/7.52      | m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) != iProver_top
% 55.77/7.52      | v1_funct_1(X5) != iProver_top
% 55.77/7.52      | v1_funct_1(X4) != iProver_top ),
% 55.77/7.52      inference(superposition,[status(thm)],[c_2878,c_2882]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_78528,plain,
% 55.77/7.52      ( k1_partfun1(sK2,sK2,sK2,sK2,sK3,sK4) = k6_partfun1(sK2)
% 55.77/7.52      | m1_subset_1(k6_partfun1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
% 55.77/7.52      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
% 55.77/7.52      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
% 55.77/7.52      | v1_funct_1(sK3) != iProver_top
% 55.77/7.52      | v1_funct_1(sK4) != iProver_top ),
% 55.77/7.52      inference(superposition,[status(thm)],[c_2863,c_8543]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_42,negated_conjecture,
% 55.77/7.52      ( v1_funct_1(sK3) ),
% 55.77/7.52      inference(cnf_transformation,[],[f104]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_43,plain,
% 55.77/7.52      ( v1_funct_1(sK3) = iProver_top ),
% 55.77/7.52      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_39,negated_conjecture,
% 55.77/7.52      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
% 55.77/7.52      inference(cnf_transformation,[],[f107]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_46,plain,
% 55.77/7.52      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
% 55.77/7.52      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_38,negated_conjecture,
% 55.77/7.52      ( v1_funct_1(sK4) ),
% 55.77/7.52      inference(cnf_transformation,[],[f108]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_47,plain,
% 55.77/7.52      ( v1_funct_1(sK4) = iProver_top ),
% 55.77/7.52      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_35,negated_conjecture,
% 55.77/7.52      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
% 55.77/7.52      inference(cnf_transformation,[],[f111]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_50,plain,
% 55.77/7.52      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
% 55.77/7.52      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_25,plain,
% 55.77/7.52      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 55.77/7.52      inference(cnf_transformation,[],[f96]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_74,plain,
% 55.77/7.52      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 55.77/7.52      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_76,plain,
% 55.77/7.52      ( m1_subset_1(k6_partfun1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
% 55.77/7.52      inference(instantiation,[status(thm)],[c_74]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_79828,plain,
% 55.77/7.52      ( k1_partfun1(sK2,sK2,sK2,sK2,sK3,sK4) = k6_partfun1(sK2) ),
% 55.77/7.52      inference(global_propositional_subsumption,
% 55.77/7.52                [status(thm)],
% 55.77/7.52                [c_78528,c_43,c_46,c_47,c_50,c_76]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_2858,plain,
% 55.77/7.52      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
% 55.77/7.52      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_2862,plain,
% 55.77/7.52      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
% 55.77/7.52      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_12,plain,
% 55.77/7.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 55.77/7.52      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 55.77/7.52      inference(cnf_transformation,[],[f83]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_2884,plain,
% 55.77/7.52      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 55.77/7.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 55.77/7.52      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_8535,plain,
% 55.77/7.52      ( k2_relset_1(X0,X1,k1_partfun1(X0,X2,X3,X1,X4,X5)) = k2_relat_1(k1_partfun1(X0,X2,X3,X1,X4,X5))
% 55.77/7.52      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
% 55.77/7.52      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) != iProver_top
% 55.77/7.52      | v1_funct_1(X5) != iProver_top
% 55.77/7.52      | v1_funct_1(X4) != iProver_top ),
% 55.77/7.52      inference(superposition,[status(thm)],[c_2878,c_2884]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_67937,plain,
% 55.77/7.52      ( k2_relset_1(X0,sK2,k1_partfun1(X0,X1,sK2,sK2,X2,sK4)) = k2_relat_1(k1_partfun1(X0,X1,sK2,sK2,X2,sK4))
% 55.77/7.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 55.77/7.52      | v1_funct_1(X2) != iProver_top
% 55.77/7.52      | v1_funct_1(sK4) != iProver_top ),
% 55.77/7.52      inference(superposition,[status(thm)],[c_2862,c_8535]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_68344,plain,
% 55.77/7.52      ( v1_funct_1(X2) != iProver_top
% 55.77/7.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 55.77/7.52      | k2_relset_1(X0,sK2,k1_partfun1(X0,X1,sK2,sK2,X2,sK4)) = k2_relat_1(k1_partfun1(X0,X1,sK2,sK2,X2,sK4)) ),
% 55.77/7.52      inference(global_propositional_subsumption,
% 55.77/7.52                [status(thm)],
% 55.77/7.52                [c_67937,c_47]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_68345,plain,
% 55.77/7.52      ( k2_relset_1(X0,sK2,k1_partfun1(X0,X1,sK2,sK2,X2,sK4)) = k2_relat_1(k1_partfun1(X0,X1,sK2,sK2,X2,sK4))
% 55.77/7.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 55.77/7.52      | v1_funct_1(X2) != iProver_top ),
% 55.77/7.52      inference(renaming,[status(thm)],[c_68344]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_68357,plain,
% 55.77/7.52      ( k2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK3,sK4)) = k2_relat_1(k1_partfun1(sK2,sK2,sK2,sK2,sK3,sK4))
% 55.77/7.52      | v1_funct_1(sK3) != iProver_top ),
% 55.77/7.52      inference(superposition,[status(thm)],[c_2858,c_68345]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_68486,plain,
% 55.77/7.52      ( k2_relset_1(sK2,sK2,k1_partfun1(sK2,sK2,sK2,sK2,sK3,sK4)) = k2_relat_1(k1_partfun1(sK2,sK2,sK2,sK2,sK3,sK4)) ),
% 55.77/7.52      inference(global_propositional_subsumption,
% 55.77/7.52                [status(thm)],
% 55.77/7.52                [c_68357,c_43]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_28,plain,
% 55.77/7.52      ( ~ v1_funct_2(X0,X1,X2)
% 55.77/7.52      | ~ v1_funct_2(X3,X4,X1)
% 55.77/7.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 55.77/7.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 55.77/7.52      | ~ v1_funct_1(X0)
% 55.77/7.52      | ~ v1_funct_1(X3)
% 55.77/7.52      | ~ v2_funct_1(X0)
% 55.77/7.52      | k2_relset_1(X4,X1,X3) = X1
% 55.77/7.52      | k2_relset_1(X4,X2,k1_partfun1(X4,X1,X1,X2,X3,X0)) != X2
% 55.77/7.52      | k1_xboole_0 = X2 ),
% 55.77/7.52      inference(cnf_transformation,[],[f99]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_2869,plain,
% 55.77/7.52      ( k2_relset_1(X0,X1,X2) = X1
% 55.77/7.52      | k2_relset_1(X0,X3,k1_partfun1(X0,X1,X1,X3,X2,X4)) != X3
% 55.77/7.52      | k1_xboole_0 = X3
% 55.77/7.52      | v1_funct_2(X4,X1,X3) != iProver_top
% 55.77/7.52      | v1_funct_2(X2,X0,X1) != iProver_top
% 55.77/7.52      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
% 55.77/7.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 55.77/7.52      | v1_funct_1(X4) != iProver_top
% 55.77/7.52      | v1_funct_1(X2) != iProver_top
% 55.77/7.52      | v2_funct_1(X4) != iProver_top ),
% 55.77/7.52      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_68491,plain,
% 55.77/7.52      ( k2_relset_1(sK2,sK2,sK3) = sK2
% 55.77/7.52      | k2_relat_1(k1_partfun1(sK2,sK2,sK2,sK2,sK3,sK4)) != sK2
% 55.77/7.52      | sK2 = k1_xboole_0
% 55.77/7.52      | v1_funct_2(sK3,sK2,sK2) != iProver_top
% 55.77/7.52      | v1_funct_2(sK4,sK2,sK2) != iProver_top
% 55.77/7.52      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
% 55.77/7.52      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
% 55.77/7.52      | v1_funct_1(sK3) != iProver_top
% 55.77/7.52      | v1_funct_1(sK4) != iProver_top
% 55.77/7.52      | v2_funct_1(sK4) != iProver_top ),
% 55.77/7.52      inference(superposition,[status(thm)],[c_68486,c_2869]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_3991,plain,
% 55.77/7.52      ( k2_relset_1(sK2,sK2,sK3) = k2_relat_1(sK3) ),
% 55.77/7.52      inference(superposition,[status(thm)],[c_2858,c_2884]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_68492,plain,
% 55.77/7.52      ( k2_relat_1(k1_partfun1(sK2,sK2,sK2,sK2,sK3,sK4)) != sK2
% 55.77/7.52      | k2_relat_1(sK3) = sK2
% 55.77/7.52      | sK2 = k1_xboole_0
% 55.77/7.52      | v1_funct_2(sK3,sK2,sK2) != iProver_top
% 55.77/7.52      | v1_funct_2(sK4,sK2,sK2) != iProver_top
% 55.77/7.52      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
% 55.77/7.52      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
% 55.77/7.52      | v1_funct_1(sK3) != iProver_top
% 55.77/7.52      | v1_funct_1(sK4) != iProver_top
% 55.77/7.52      | v2_funct_1(sK4) != iProver_top ),
% 55.77/7.52      inference(demodulation,[status(thm)],[c_68491,c_3991]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_41,negated_conjecture,
% 55.77/7.52      ( v1_funct_2(sK3,sK2,sK2) ),
% 55.77/7.52      inference(cnf_transformation,[],[f105]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_40,negated_conjecture,
% 55.77/7.52      ( v3_funct_2(sK3,sK2,sK2) ),
% 55.77/7.52      inference(cnf_transformation,[],[f106]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_37,negated_conjecture,
% 55.77/7.52      ( v1_funct_2(sK4,sK2,sK2) ),
% 55.77/7.52      inference(cnf_transformation,[],[f109]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_36,negated_conjecture,
% 55.77/7.52      ( v3_funct_2(sK4,sK2,sK2) ),
% 55.77/7.52      inference(cnf_transformation,[],[f110]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_1,plain,
% 55.77/7.52      ( v1_xboole_0(sK0(X0)) ),
% 55.77/7.52      inference(cnf_transformation,[],[f73]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_16,plain,
% 55.77/7.52      ( r2_relset_1(X0,X0,X1,X2)
% 55.77/7.52      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 55.77/7.52      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 55.77/7.52      | r2_hidden(sK1(X0,X1,X2),X0) ),
% 55.77/7.52      inference(cnf_transformation,[],[f86]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_33,negated_conjecture,
% 55.77/7.52      ( ~ r2_relset_1(sK2,sK2,sK4,k2_funct_2(sK2,sK3)) ),
% 55.77/7.52      inference(cnf_transformation,[],[f113]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_1036,plain,
% 55.77/7.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 55.77/7.52      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 55.77/7.52      | r2_hidden(sK1(X1,X2,X0),X1)
% 55.77/7.52      | k2_funct_2(sK2,sK3) != X0
% 55.77/7.52      | sK4 != X2
% 55.77/7.52      | sK2 != X1 ),
% 55.77/7.52      inference(resolution_lifted,[status(thm)],[c_16,c_33]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_1037,plain,
% 55.77/7.52      ( ~ m1_subset_1(k2_funct_2(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 55.77/7.52      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 55.77/7.52      | r2_hidden(sK1(sK2,sK4,k2_funct_2(sK2,sK3)),sK2) ),
% 55.77/7.52      inference(unflattening,[status(thm)],[c_1036]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_21,plain,
% 55.77/7.52      ( ~ v1_funct_2(X0,X1,X1)
% 55.77/7.52      | ~ v3_funct_2(X0,X1,X1)
% 55.77/7.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 55.77/7.52      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 55.77/7.52      | ~ v1_funct_1(X0) ),
% 55.77/7.52      inference(cnf_transformation,[],[f95]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_2977,plain,
% 55.77/7.52      ( ~ v1_funct_2(sK3,sK2,sK2)
% 55.77/7.52      | ~ v3_funct_2(sK3,sK2,sK2)
% 55.77/7.52      | m1_subset_1(k2_funct_2(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 55.77/7.52      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 55.77/7.52      | ~ v1_funct_1(sK3) ),
% 55.77/7.52      inference(instantiation,[status(thm)],[c_21]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_6,plain,
% 55.77/7.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 55.77/7.52      | ~ r2_hidden(X2,X0)
% 55.77/7.52      | ~ v1_xboole_0(X1) ),
% 55.77/7.52      inference(cnf_transformation,[],[f77]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_3030,plain,
% 55.77/7.52      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
% 55.77/7.52      | ~ r2_hidden(sK1(sK2,sK4,k2_funct_2(sK2,sK3)),sK2)
% 55.77/7.52      | ~ v1_xboole_0(X0) ),
% 55.77/7.52      inference(instantiation,[status(thm)],[c_6]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_3032,plain,
% 55.77/7.52      ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK2))
% 55.77/7.52      | ~ r2_hidden(sK1(sK2,sK4,k2_funct_2(sK2,sK3)),sK2)
% 55.77/7.52      | ~ v1_xboole_0(sK2) ),
% 55.77/7.52      inference(instantiation,[status(thm)],[c_3030]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_4,plain,
% 55.77/7.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 55.77/7.52      | ~ v1_xboole_0(X1)
% 55.77/7.52      | v1_xboole_0(X0) ),
% 55.77/7.52      inference(cnf_transformation,[],[f75]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_3076,plain,
% 55.77/7.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0(X1)))
% 55.77/7.52      | v1_xboole_0(X0)
% 55.77/7.52      | ~ v1_xboole_0(sK0(X1)) ),
% 55.77/7.52      inference(instantiation,[status(thm)],[c_4]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_3429,plain,
% 55.77/7.52      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0(X0)))
% 55.77/7.52      | ~ v1_xboole_0(sK0(X0))
% 55.77/7.52      | v1_xboole_0(k1_xboole_0) ),
% 55.77/7.52      inference(instantiation,[status(thm)],[c_3076]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_3,plain,
% 55.77/7.52      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 55.77/7.52      inference(cnf_transformation,[],[f74]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_4751,plain,
% 55.77/7.52      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0(X0))) ),
% 55.77/7.52      inference(instantiation,[status(thm)],[c_3]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_32,plain,
% 55.77/7.52      ( ~ v1_funct_2(X0,X1,X1)
% 55.77/7.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 55.77/7.52      | ~ v1_funct_1(X0)
% 55.77/7.52      | k1_relset_1(X1,X1,X0) = X1 ),
% 55.77/7.52      inference(cnf_transformation,[],[f103]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_2865,plain,
% 55.77/7.52      ( k1_relset_1(X0,X0,X1) = X0
% 55.77/7.52      | v1_funct_2(X1,X0,X0) != iProver_top
% 55.77/7.52      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 55.77/7.52      | v1_funct_1(X1) != iProver_top ),
% 55.77/7.52      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_3874,plain,
% 55.77/7.52      ( k1_relset_1(sK2,sK2,sK4) = sK2
% 55.77/7.52      | v1_funct_2(sK4,sK2,sK2) != iProver_top
% 55.77/7.52      | v1_funct_1(sK4) != iProver_top ),
% 55.77/7.52      inference(superposition,[status(thm)],[c_2862,c_2865]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_48,plain,
% 55.77/7.52      ( v1_funct_2(sK4,sK2,sK2) = iProver_top ),
% 55.77/7.52      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_5541,plain,
% 55.77/7.52      ( k1_relset_1(sK2,sK2,sK4) = sK2 ),
% 55.77/7.52      inference(global_propositional_subsumption,
% 55.77/7.52                [status(thm)],
% 55.77/7.52                [c_3874,c_47,c_48]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_10,plain,
% 55.77/7.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 55.77/7.52      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 55.77/7.52      inference(cnf_transformation,[],[f81]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_2886,plain,
% 55.77/7.52      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 55.77/7.52      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 55.77/7.52      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_5544,plain,
% 55.77/7.52      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
% 55.77/7.52      | m1_subset_1(sK2,k1_zfmisc_1(sK2)) = iProver_top ),
% 55.77/7.52      inference(superposition,[status(thm)],[c_5541,c_2886]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_5545,plain,
% 55.77/7.52      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 55.77/7.52      | m1_subset_1(sK2,k1_zfmisc_1(sK2)) ),
% 55.77/7.52      inference(predicate_to_equality_rev,[status(thm)],[c_5544]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_17,plain,
% 55.77/7.52      ( ~ v3_funct_2(X0,X1,X2)
% 55.77/7.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 55.77/7.52      | ~ v1_funct_1(X0)
% 55.77/7.52      | v2_funct_1(X0) ),
% 55.77/7.52      inference(cnf_transformation,[],[f89]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_2879,plain,
% 55.77/7.52      ( v3_funct_2(X0,X1,X2) != iProver_top
% 55.77/7.52      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 55.77/7.52      | v1_funct_1(X0) != iProver_top
% 55.77/7.52      | v2_funct_1(X0) = iProver_top ),
% 55.77/7.52      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_5828,plain,
% 55.77/7.52      ( v3_funct_2(sK4,sK2,sK2) != iProver_top
% 55.77/7.52      | v1_funct_1(sK4) != iProver_top
% 55.77/7.52      | v2_funct_1(sK4) = iProver_top ),
% 55.77/7.52      inference(superposition,[status(thm)],[c_2862,c_2879]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_5842,plain,
% 55.77/7.52      ( ~ v3_funct_2(sK4,sK2,sK2) | ~ v1_funct_1(sK4) | v2_funct_1(sK4) ),
% 55.77/7.52      inference(predicate_to_equality_rev,[status(thm)],[c_5828]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_2172,plain,
% 55.77/7.52      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 55.77/7.52      theory(equality) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_26064,plain,
% 55.77/7.52      ( v1_xboole_0(X0)
% 55.77/7.52      | ~ v1_xboole_0(k1_xboole_0)
% 55.77/7.52      | X0 != k1_xboole_0 ),
% 55.77/7.52      inference(instantiation,[status(thm)],[c_2172]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_26072,plain,
% 55.77/7.52      ( v1_xboole_0(sK2)
% 55.77/7.52      | ~ v1_xboole_0(k1_xboole_0)
% 55.77/7.52      | sK2 != k1_xboole_0 ),
% 55.77/7.52      inference(instantiation,[status(thm)],[c_26064]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_68498,plain,
% 55.77/7.52      ( ~ v1_funct_2(sK3,sK2,sK2)
% 55.77/7.52      | ~ v1_funct_2(sK4,sK2,sK2)
% 55.77/7.52      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 55.77/7.52      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 55.77/7.52      | ~ v1_funct_1(sK3)
% 55.77/7.52      | ~ v1_funct_1(sK4)
% 55.77/7.52      | ~ v2_funct_1(sK4)
% 55.77/7.52      | k2_relat_1(k1_partfun1(sK2,sK2,sK2,sK2,sK3,sK4)) != sK2
% 55.77/7.52      | k2_relat_1(sK3) = sK2
% 55.77/7.52      | sK2 = k1_xboole_0 ),
% 55.77/7.52      inference(predicate_to_equality_rev,[status(thm)],[c_68492]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_78090,plain,
% 55.77/7.52      ( k2_relat_1(k1_partfun1(sK2,sK2,sK2,sK2,sK3,sK4)) != sK2
% 55.77/7.52      | k2_relat_1(sK3) = sK2 ),
% 55.77/7.52      inference(global_propositional_subsumption,
% 55.77/7.52                [status(thm)],
% 55.77/7.52                [c_68492,c_42,c_41,c_40,c_39,c_38,c_37,c_36,c_35,c_1,
% 55.77/7.52                 c_1037,c_2977,c_3032,c_3429,c_4751,c_5545,c_5842,
% 55.77/7.52                 c_26072,c_68498]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_79830,plain,
% 55.77/7.52      ( k2_relat_1(k6_partfun1(sK2)) != sK2 | k2_relat_1(sK3) = sK2 ),
% 55.77/7.52      inference(demodulation,[status(thm)],[c_79828,c_78090]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_3990,plain,
% 55.77/7.52      ( k2_relset_1(sK2,sK2,sK4) = k2_relat_1(sK4) ),
% 55.77/7.52      inference(superposition,[status(thm)],[c_2862,c_2884]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_30,plain,
% 55.77/7.52      ( ~ v1_funct_2(X0,X1,X2)
% 55.77/7.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 55.77/7.52      | ~ v1_funct_1(X0)
% 55.77/7.52      | ~ v2_funct_1(X0)
% 55.77/7.52      | k2_relset_1(X1,X2,X0) != X2
% 55.77/7.52      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 55.77/7.52      | k1_xboole_0 = X2 ),
% 55.77/7.52      inference(cnf_transformation,[],[f100]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_2867,plain,
% 55.77/7.52      ( k2_relset_1(X0,X1,X2) != X1
% 55.77/7.52      | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
% 55.77/7.52      | k1_xboole_0 = X1
% 55.77/7.52      | v1_funct_2(X2,X0,X1) != iProver_top
% 55.77/7.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 55.77/7.52      | v1_funct_1(X2) != iProver_top
% 55.77/7.52      | v2_funct_1(X2) != iProver_top ),
% 55.77/7.52      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_5663,plain,
% 55.77/7.52      ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(sK2)
% 55.77/7.52      | k2_relat_1(sK4) != sK2
% 55.77/7.52      | sK2 = k1_xboole_0
% 55.77/7.52      | v1_funct_2(sK4,sK2,sK2) != iProver_top
% 55.77/7.52      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
% 55.77/7.52      | v1_funct_1(sK4) != iProver_top
% 55.77/7.52      | v2_funct_1(sK4) != iProver_top ),
% 55.77/7.52      inference(superposition,[status(thm)],[c_3990,c_2867]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_49,plain,
% 55.77/7.52      ( v3_funct_2(sK4,sK2,sK2) = iProver_top ),
% 55.77/7.52      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_27,plain,
% 55.77/7.52      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 55.77/7.52      | ~ v1_funct_2(X2,X0,X1)
% 55.77/7.52      | ~ v1_funct_2(X3,X1,X0)
% 55.77/7.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 55.77/7.52      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 55.77/7.52      | ~ v1_funct_1(X3)
% 55.77/7.52      | ~ v1_funct_1(X2)
% 55.77/7.52      | k2_relset_1(X1,X0,X3) = X0 ),
% 55.77/7.52      inference(cnf_transformation,[],[f98]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_2870,plain,
% 55.77/7.52      ( k2_relset_1(X0,X1,X2) = X1
% 55.77/7.52      | r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) != iProver_top
% 55.77/7.52      | v1_funct_2(X2,X0,X1) != iProver_top
% 55.77/7.52      | v1_funct_2(X3,X1,X0) != iProver_top
% 55.77/7.52      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
% 55.77/7.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 55.77/7.52      | v1_funct_1(X3) != iProver_top
% 55.77/7.52      | v1_funct_1(X2) != iProver_top ),
% 55.77/7.52      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_9024,plain,
% 55.77/7.52      ( k2_relset_1(sK2,sK2,sK4) = sK2
% 55.77/7.52      | v1_funct_2(sK3,sK2,sK2) != iProver_top
% 55.77/7.52      | v1_funct_2(sK4,sK2,sK2) != iProver_top
% 55.77/7.52      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
% 55.77/7.52      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
% 55.77/7.52      | v1_funct_1(sK3) != iProver_top
% 55.77/7.52      | v1_funct_1(sK4) != iProver_top ),
% 55.77/7.52      inference(superposition,[status(thm)],[c_2863,c_2870]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_9025,plain,
% 55.77/7.52      ( k2_relat_1(sK4) = sK2
% 55.77/7.52      | v1_funct_2(sK3,sK2,sK2) != iProver_top
% 55.77/7.52      | v1_funct_2(sK4,sK2,sK2) != iProver_top
% 55.77/7.52      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
% 55.77/7.52      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
% 55.77/7.52      | v1_funct_1(sK3) != iProver_top
% 55.77/7.52      | v1_funct_1(sK4) != iProver_top ),
% 55.77/7.52      inference(demodulation,[status(thm)],[c_9024,c_3990]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_44,plain,
% 55.77/7.52      ( v1_funct_2(sK3,sK2,sK2) = iProver_top ),
% 55.77/7.52      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_10582,plain,
% 55.77/7.52      ( k2_relat_1(sK4) = sK2 ),
% 55.77/7.52      inference(global_propositional_subsumption,
% 55.77/7.52                [status(thm)],
% 55.77/7.52                [c_9025,c_43,c_44,c_46,c_47,c_48,c_50]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_10584,plain,
% 55.77/7.52      ( k2_relset_1(sK2,sK2,sK4) = sK2 ),
% 55.77/7.52      inference(demodulation,[status(thm)],[c_10582,c_3990]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_10586,plain,
% 55.77/7.52      ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(sK2)
% 55.77/7.52      | sK2 = k1_xboole_0
% 55.77/7.52      | v1_funct_2(sK4,sK2,sK2) != iProver_top
% 55.77/7.52      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
% 55.77/7.52      | v1_funct_1(sK4) != iProver_top
% 55.77/7.52      | v2_funct_1(sK4) != iProver_top ),
% 55.77/7.52      inference(superposition,[status(thm)],[c_10584,c_2867]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_12350,plain,
% 55.77/7.52      ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(sK2)
% 55.77/7.52      | sK2 = k1_xboole_0 ),
% 55.77/7.52      inference(global_propositional_subsumption,
% 55.77/7.52                [status(thm)],
% 55.77/7.52                [c_5663,c_47,c_48,c_49,c_50,c_5828,c_10586]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_9,plain,
% 55.77/7.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 55.77/7.52      | v1_relat_1(X0) ),
% 55.77/7.52      inference(cnf_transformation,[],[f80]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_2887,plain,
% 55.77/7.52      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 55.77/7.52      | v1_relat_1(X0) = iProver_top ),
% 55.77/7.52      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_3636,plain,
% 55.77/7.52      ( v1_relat_1(sK4) = iProver_top ),
% 55.77/7.52      inference(superposition,[status(thm)],[c_2862,c_2887]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_7,plain,
% 55.77/7.52      ( ~ v1_relat_1(X0)
% 55.77/7.52      | ~ v1_funct_1(X0)
% 55.77/7.52      | ~ v2_funct_1(X0)
% 55.77/7.52      | k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) ),
% 55.77/7.52      inference(cnf_transformation,[],[f79]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_2889,plain,
% 55.77/7.52      ( k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
% 55.77/7.52      | v1_relat_1(X0) != iProver_top
% 55.77/7.52      | v1_funct_1(X0) != iProver_top
% 55.77/7.52      | v2_funct_1(X0) != iProver_top ),
% 55.77/7.52      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_5810,plain,
% 55.77/7.52      ( k2_relat_1(k5_relat_1(sK4,k2_funct_1(sK4))) = k1_relat_1(sK4)
% 55.77/7.52      | v1_funct_1(sK4) != iProver_top
% 55.77/7.52      | v2_funct_1(sK4) != iProver_top ),
% 55.77/7.52      inference(superposition,[status(thm)],[c_3636,c_2889]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_11,plain,
% 55.77/7.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 55.77/7.52      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 55.77/7.52      inference(cnf_transformation,[],[f82]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_2885,plain,
% 55.77/7.52      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 55.77/7.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 55.77/7.52      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_3999,plain,
% 55.77/7.52      ( k1_relset_1(sK2,sK2,sK4) = k1_relat_1(sK4) ),
% 55.77/7.52      inference(superposition,[status(thm)],[c_2862,c_2885]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_5543,plain,
% 55.77/7.52      ( k1_relat_1(sK4) = sK2 ),
% 55.77/7.52      inference(demodulation,[status(thm)],[c_5541,c_3999]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_5813,plain,
% 55.77/7.52      ( k2_relat_1(k5_relat_1(sK4,k2_funct_1(sK4))) = sK2
% 55.77/7.52      | v1_funct_1(sK4) != iProver_top
% 55.77/7.52      | v2_funct_1(sK4) != iProver_top ),
% 55.77/7.52      inference(light_normalisation,[status(thm)],[c_5810,c_5543]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_15463,plain,
% 55.77/7.52      ( k2_relat_1(k5_relat_1(sK4,k2_funct_1(sK4))) = sK2 ),
% 55.77/7.52      inference(global_propositional_subsumption,
% 55.77/7.52                [status(thm)],
% 55.77/7.52                [c_5813,c_47,c_49,c_5828]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_15465,plain,
% 55.77/7.52      ( k2_relat_1(k6_partfun1(sK2)) = sK2 | sK2 = k1_xboole_0 ),
% 55.77/7.52      inference(superposition,[status(thm)],[c_12350,c_15463]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_80638,plain,
% 55.77/7.52      ( k2_relat_1(sK3) = sK2 ),
% 55.77/7.52      inference(global_propositional_subsumption,
% 55.77/7.52                [status(thm)],
% 55.77/7.52                [c_79830,c_42,c_41,c_40,c_39,c_35,c_1,c_1037,c_2977,
% 55.77/7.52                 c_3032,c_3429,c_4751,c_5545,c_15465,c_26072]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_80644,plain,
% 55.77/7.52      ( k2_relset_1(sK2,sK2,sK3) = sK2 ),
% 55.77/7.52      inference(demodulation,[status(thm)],[c_80638,c_3991]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_2179,plain,
% 55.77/7.52      ( ~ r2_relset_1(X0,X1,X2,X3)
% 55.77/7.52      | r2_relset_1(X4,X5,X6,X7)
% 55.77/7.52      | X4 != X0
% 55.77/7.52      | X5 != X1
% 55.77/7.52      | X6 != X2
% 55.77/7.52      | X7 != X3 ),
% 55.77/7.52      theory(equality) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_3507,plain,
% 55.77/7.52      ( ~ r2_relset_1(X0,X1,X2,X3)
% 55.77/7.52      | r2_relset_1(X4,X5,sK4,k2_funct_1(sK3))
% 55.77/7.52      | X4 != X0
% 55.77/7.52      | X5 != X1
% 55.77/7.52      | k2_funct_1(sK3) != X3
% 55.77/7.52      | sK4 != X2 ),
% 55.77/7.52      inference(instantiation,[status(thm)],[c_2179]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_4317,plain,
% 55.77/7.52      ( ~ r2_relset_1(X0,X1,sK4,X2)
% 55.77/7.52      | r2_relset_1(X3,X4,sK4,k2_funct_1(sK3))
% 55.77/7.52      | X3 != X0
% 55.77/7.52      | X4 != X1
% 55.77/7.52      | k2_funct_1(sK3) != X2
% 55.77/7.52      | sK4 != sK4 ),
% 55.77/7.52      inference(instantiation,[status(thm)],[c_3507]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_21313,plain,
% 55.77/7.52      ( r2_relset_1(X0,X1,sK4,k2_funct_1(sK3))
% 55.77/7.52      | ~ r2_relset_1(X2,X3,sK4,sK4)
% 55.77/7.52      | X0 != X2
% 55.77/7.52      | X1 != X3
% 55.77/7.52      | k2_funct_1(sK3) != sK4
% 55.77/7.52      | sK4 != sK4 ),
% 55.77/7.52      inference(instantiation,[status(thm)],[c_4317]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_21316,plain,
% 55.77/7.52      ( r2_relset_1(sK2,sK2,sK4,k2_funct_1(sK3))
% 55.77/7.52      | ~ r2_relset_1(sK2,sK2,sK4,sK4)
% 55.77/7.52      | k2_funct_1(sK3) != sK4
% 55.77/7.52      | sK4 != sK4
% 55.77/7.52      | sK2 != sK2 ),
% 55.77/7.52      inference(instantiation,[status(thm)],[c_21313]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_5829,plain,
% 55.77/7.52      ( v3_funct_2(sK3,sK2,sK2) != iProver_top
% 55.77/7.52      | v1_funct_1(sK3) != iProver_top
% 55.77/7.52      | v2_funct_1(sK3) = iProver_top ),
% 55.77/7.52      inference(superposition,[status(thm)],[c_2858,c_2879]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_5843,plain,
% 55.77/7.52      ( ~ v3_funct_2(sK3,sK2,sK2) | ~ v1_funct_1(sK3) | v2_funct_1(sK3) ),
% 55.77/7.52      inference(predicate_to_equality_rev,[status(thm)],[c_5829]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_2168,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_4657,plain,
% 55.77/7.52      ( sK2 != X0 | sK2 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 55.77/7.52      inference(instantiation,[status(thm)],[c_2168]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_4658,plain,
% 55.77/7.52      ( sK2 != sK2 | sK2 = k1_xboole_0 | k1_xboole_0 != sK2 ),
% 55.77/7.52      inference(instantiation,[status(thm)],[c_4657]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_13,plain,
% 55.77/7.52      ( r2_relset_1(X0,X1,X2,X2)
% 55.77/7.52      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 55.77/7.52      inference(cnf_transformation,[],[f114]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_2883,plain,
% 55.77/7.52      ( r2_relset_1(X0,X1,X2,X2) = iProver_top
% 55.77/7.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 55.77/7.52      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_3857,plain,
% 55.77/7.52      ( r2_relset_1(sK2,sK2,sK4,sK4) = iProver_top ),
% 55.77/7.52      inference(superposition,[status(thm)],[c_2862,c_2883]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_3868,plain,
% 55.77/7.52      ( r2_relset_1(sK2,sK2,sK4,sK4) ),
% 55.77/7.52      inference(predicate_to_equality_rev,[status(thm)],[c_3857]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_26,plain,
% 55.77/7.52      ( ~ v1_funct_2(X0,X1,X1)
% 55.77/7.52      | ~ v3_funct_2(X0,X1,X1)
% 55.77/7.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 55.77/7.52      | ~ v1_funct_1(X0)
% 55.77/7.52      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 55.77/7.52      inference(cnf_transformation,[],[f97]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_3199,plain,
% 55.77/7.52      ( ~ v1_funct_2(sK3,sK2,sK2)
% 55.77/7.52      | ~ v3_funct_2(sK3,sK2,sK2)
% 55.77/7.52      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 55.77/7.52      | ~ v1_funct_1(sK3)
% 55.77/7.52      | k2_funct_2(sK2,sK3) = k2_funct_1(sK3) ),
% 55.77/7.52      inference(instantiation,[status(thm)],[c_26]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_2955,plain,
% 55.77/7.52      ( ~ r2_relset_1(X0,X1,X2,X3)
% 55.77/7.52      | r2_relset_1(sK2,sK2,sK4,k2_funct_2(sK2,sK3))
% 55.77/7.52      | k2_funct_2(sK2,sK3) != X3
% 55.77/7.52      | sK4 != X2
% 55.77/7.52      | sK2 != X1
% 55.77/7.52      | sK2 != X0 ),
% 55.77/7.52      inference(instantiation,[status(thm)],[c_2179]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_3005,plain,
% 55.77/7.52      ( ~ r2_relset_1(X0,X1,sK4,X2)
% 55.77/7.52      | r2_relset_1(sK2,sK2,sK4,k2_funct_2(sK2,sK3))
% 55.77/7.52      | k2_funct_2(sK2,sK3) != X2
% 55.77/7.52      | sK4 != sK4
% 55.77/7.52      | sK2 != X1
% 55.77/7.52      | sK2 != X0 ),
% 55.77/7.52      inference(instantiation,[status(thm)],[c_2955]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_3119,plain,
% 55.77/7.52      ( ~ r2_relset_1(X0,X1,sK4,k2_funct_1(sK3))
% 55.77/7.52      | r2_relset_1(sK2,sK2,sK4,k2_funct_2(sK2,sK3))
% 55.77/7.52      | k2_funct_2(sK2,sK3) != k2_funct_1(sK3)
% 55.77/7.52      | sK4 != sK4
% 55.77/7.52      | sK2 != X1
% 55.77/7.52      | sK2 != X0 ),
% 55.77/7.52      inference(instantiation,[status(thm)],[c_3005]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_3121,plain,
% 55.77/7.52      ( r2_relset_1(sK2,sK2,sK4,k2_funct_2(sK2,sK3))
% 55.77/7.52      | ~ r2_relset_1(sK2,sK2,sK4,k2_funct_1(sK3))
% 55.77/7.52      | k2_funct_2(sK2,sK3) != k2_funct_1(sK3)
% 55.77/7.52      | sK4 != sK4
% 55.77/7.52      | sK2 != sK2 ),
% 55.77/7.52      inference(instantiation,[status(thm)],[c_3119]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_2167,plain,( X0 = X0 ),theory(equality) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_3058,plain,
% 55.77/7.52      ( sK4 = sK4 ),
% 55.77/7.52      inference(instantiation,[status(thm)],[c_2167]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_2204,plain,
% 55.77/7.52      ( sK2 = sK2 ),
% 55.77/7.52      inference(instantiation,[status(thm)],[c_2167]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_129061,plain,
% 55.77/7.52      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0(sK2))) ),
% 55.77/7.52      inference(grounding,[status(thm)],[c_4751:[bind(X0,$fot(sK2))]]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_129062,plain,
% 55.77/7.52      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0(sK2)))
% 55.77/7.52      | ~ v1_xboole_0(sK0(sK2))
% 55.77/7.52      | v1_xboole_0(k1_xboole_0) ),
% 55.77/7.52      inference(grounding,[status(thm)],[c_3429:[bind(X0,$fot(sK2))]]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(c_129063,plain,
% 55.77/7.52      ( v1_xboole_0(sK0(sK2)) ),
% 55.77/7.52      inference(grounding,[status(thm)],[c_1:[bind(X0,$fot(sK2))]]) ).
% 55.77/7.52  
% 55.77/7.52  cnf(contradiction,plain,
% 55.77/7.52      ( $false ),
% 55.77/7.52      inference(minisat,
% 55.77/7.52                [status(thm)],
% 55.77/7.52                [c_129060,c_80644,c_26072,c_21316,c_5843,c_5545,c_129061,
% 55.77/7.52                 c_4658,c_3868,c_129062,c_3199,c_3121,c_3058,c_3032,
% 55.77/7.52                 c_2977,c_2204,c_1037,c_129063,c_33,c_34,c_35,c_37,c_38,
% 55.77/7.52                 c_39,c_40,c_41,c_42]) ).
% 55.77/7.52  
% 55.77/7.52  
% 55.77/7.52  % SZS output end CNFRefutation for theBenchmark.p
% 55.77/7.52  
% 55.77/7.52  ------                               Statistics
% 55.77/7.52  
% 55.77/7.52  ------ General
% 55.77/7.52  
% 55.77/7.52  abstr_ref_over_cycles:                  0
% 55.77/7.52  abstr_ref_under_cycles:                 0
% 55.77/7.52  gc_basic_clause_elim:                   0
% 55.77/7.52  forced_gc_time:                         0
% 55.77/7.52  parsing_time:                           0.011
% 55.77/7.52  unif_index_cands_time:                  0.
% 55.77/7.52  unif_index_add_time:                    0.
% 55.77/7.52  orderings_time:                         0.
% 55.77/7.52  out_proof_time:                         0.053
% 55.77/7.52  total_time:                             7.008
% 55.77/7.52  num_of_symbols:                         58
% 55.77/7.52  num_of_terms:                           149198
% 55.77/7.52  
% 55.77/7.52  ------ Preprocessing
% 55.77/7.52  
% 55.77/7.52  num_of_splits:                          0
% 55.77/7.52  num_of_split_atoms:                     0
% 55.77/7.52  num_of_reused_defs:                     0
% 55.77/7.52  num_eq_ax_congr_red:                    42
% 55.77/7.52  num_of_sem_filtered_clauses:            1
% 55.77/7.52  num_of_subtypes:                        0
% 55.77/7.52  monotx_restored_types:                  0
% 55.77/7.52  sat_num_of_epr_types:                   0
% 55.77/7.52  sat_num_of_non_cyclic_types:            0
% 55.77/7.52  sat_guarded_non_collapsed_types:        0
% 55.77/7.52  num_pure_diseq_elim:                    0
% 55.77/7.52  simp_replaced_by:                       0
% 55.77/7.52  res_preprocessed:                       207
% 55.77/7.52  prep_upred:                             0
% 55.77/7.52  prep_unflattend:                        92
% 55.77/7.52  smt_new_axioms:                         0
% 55.77/7.52  pred_elim_cands:                        9
% 55.77/7.52  pred_elim:                              0
% 55.77/7.52  pred_elim_cl:                           0
% 55.77/7.52  pred_elim_cycles:                       6
% 55.77/7.52  merged_defs:                            0
% 55.77/7.52  merged_defs_ncl:                        0
% 55.77/7.52  bin_hyper_res:                          0
% 55.77/7.52  prep_cycles:                            4
% 55.77/7.52  pred_elim_time:                         0.039
% 55.77/7.52  splitting_time:                         0.
% 55.77/7.52  sem_filter_time:                        0.
% 55.77/7.52  monotx_time:                            0.001
% 55.77/7.52  subtype_inf_time:                       0.
% 55.77/7.52  
% 55.77/7.52  ------ Problem properties
% 55.77/7.52  
% 55.77/7.52  clauses:                                42
% 55.77/7.52  conjectures:                            10
% 55.77/7.52  epr:                                    6
% 55.77/7.52  horn:                                   37
% 55.77/7.52  ground:                                 10
% 55.77/7.52  unary:                                  14
% 55.77/7.52  binary:                                 5
% 55.77/7.52  lits:                                   143
% 55.77/7.52  lits_eq:                                22
% 55.77/7.52  fd_pure:                                0
% 55.77/7.52  fd_pseudo:                              0
% 55.77/7.52  fd_cond:                                2
% 55.77/7.52  fd_pseudo_cond:                         2
% 55.77/7.52  ac_symbols:                             0
% 55.77/7.52  
% 55.77/7.52  ------ Propositional Solver
% 55.77/7.52  
% 55.77/7.52  prop_solver_calls:                      54
% 55.77/7.52  prop_fast_solver_calls:                 6495
% 55.77/7.52  smt_solver_calls:                       0
% 55.77/7.52  smt_fast_solver_calls:                  0
% 55.77/7.52  prop_num_of_clauses:                    53476
% 55.77/7.52  prop_preprocess_simplified:             132776
% 55.77/7.52  prop_fo_subsumed:                       810
% 55.77/7.52  prop_solver_time:                       0.
% 55.77/7.52  smt_solver_time:                        0.
% 55.77/7.52  smt_fast_solver_time:                   0.
% 55.77/7.52  prop_fast_solver_time:                  0.
% 55.77/7.52  prop_unsat_core_time:                   0.008
% 55.77/7.52  
% 55.77/7.52  ------ QBF
% 55.77/7.52  
% 55.77/7.52  qbf_q_res:                              0
% 55.77/7.52  qbf_num_tautologies:                    0
% 55.77/7.52  qbf_prep_cycles:                        0
% 55.77/7.52  
% 55.77/7.52  ------ BMC1
% 55.77/7.52  
% 55.77/7.52  bmc1_current_bound:                     -1
% 55.77/7.52  bmc1_last_solved_bound:                 -1
% 55.77/7.52  bmc1_unsat_core_size:                   -1
% 55.77/7.52  bmc1_unsat_core_parents_size:           -1
% 55.77/7.52  bmc1_merge_next_fun:                    0
% 55.77/7.52  bmc1_unsat_core_clauses_time:           0.
% 55.77/7.52  
% 55.77/7.52  ------ Instantiation
% 55.77/7.52  
% 55.77/7.52  inst_num_of_clauses:                    9305
% 55.77/7.52  inst_num_in_passive:                    4630
% 55.77/7.52  inst_num_in_active:                     5359
% 55.77/7.52  inst_num_in_unprocessed:                1907
% 55.77/7.52  inst_num_of_loops:                      6066
% 55.77/7.52  inst_num_of_learning_restarts:          1
% 55.77/7.52  inst_num_moves_active_passive:          702
% 55.77/7.52  inst_lit_activity:                      0
% 55.77/7.52  inst_lit_activity_moves:                1
% 55.77/7.52  inst_num_tautologies:                   0
% 55.77/7.52  inst_num_prop_implied:                  0
% 55.77/7.52  inst_num_existing_simplified:           0
% 55.77/7.52  inst_num_eq_res_simplified:             0
% 55.77/7.52  inst_num_child_elim:                    0
% 55.77/7.52  inst_num_of_dismatching_blockings:      15063
% 55.77/7.52  inst_num_of_non_proper_insts:           17328
% 55.77/7.52  inst_num_of_duplicates:                 0
% 55.77/7.52  inst_inst_num_from_inst_to_res:         0
% 55.77/7.52  inst_dismatching_checking_time:         0.
% 55.77/7.52  
% 55.77/7.52  ------ Resolution
% 55.77/7.52  
% 55.77/7.52  res_num_of_clauses:                     61
% 55.77/7.52  res_num_in_passive:                     61
% 55.77/7.52  res_num_in_active:                      0
% 55.77/7.52  res_num_of_loops:                       211
% 55.77/7.52  res_forward_subset_subsumed:            444
% 55.77/7.52  res_backward_subset_subsumed:           0
% 55.77/7.52  res_forward_subsumed:                   0
% 55.77/7.52  res_backward_subsumed:                  0
% 55.77/7.52  res_forward_subsumption_resolution:     20
% 55.77/7.52  res_backward_subsumption_resolution:    0
% 55.77/7.52  res_clause_to_clause_subsumption:       8740
% 55.77/7.52  res_orphan_elimination:                 0
% 55.77/7.52  res_tautology_del:                      769
% 55.77/7.52  res_num_eq_res_simplified:              0
% 55.77/7.52  res_num_sel_changes:                    0
% 55.77/7.52  res_moves_from_active_to_pass:          0
% 55.77/7.52  
% 55.77/7.52  ------ Superposition
% 55.77/7.52  
% 55.77/7.52  sup_time_total:                         0.
% 55.77/7.52  sup_time_generating:                    0.
% 55.77/7.52  sup_time_sim_full:                      0.
% 55.77/7.52  sup_time_sim_immed:                     0.
% 55.77/7.52  
% 55.77/7.52  sup_num_of_clauses:                     3024
% 55.77/7.52  sup_num_in_active:                      1122
% 55.77/7.52  sup_num_in_passive:                     1902
% 55.77/7.52  sup_num_of_loops:                       1212
% 55.77/7.52  sup_fw_superposition:                   2362
% 55.77/7.52  sup_bw_superposition:                   1308
% 55.77/7.52  sup_immediate_simplified:               936
% 55.77/7.52  sup_given_eliminated:                   0
% 55.77/7.52  comparisons_done:                       0
% 55.77/7.52  comparisons_avoided:                    6
% 55.77/7.52  
% 55.77/7.52  ------ Simplifications
% 55.77/7.52  
% 55.77/7.52  
% 55.77/7.52  sim_fw_subset_subsumed:                 231
% 55.77/7.52  sim_bw_subset_subsumed:                 69
% 55.77/7.52  sim_fw_subsumed:                        161
% 55.77/7.52  sim_bw_subsumed:                        9
% 55.77/7.52  sim_fw_subsumption_res:                 0
% 55.77/7.52  sim_bw_subsumption_res:                 0
% 55.77/7.52  sim_tautology_del:                      17
% 55.77/7.52  sim_eq_tautology_del:                   94
% 55.77/7.52  sim_eq_res_simp:                        3
% 55.77/7.52  sim_fw_demodulated:                     396
% 55.77/7.52  sim_bw_demodulated:                     70
% 55.77/7.52  sim_light_normalised:                   279
% 55.77/7.52  sim_joinable_taut:                      0
% 55.77/7.52  sim_joinable_simp:                      0
% 55.77/7.52  sim_ac_normalised:                      0
% 55.77/7.52  sim_smt_subsumption:                    0
% 55.77/7.52  
%------------------------------------------------------------------------------
