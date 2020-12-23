%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:44 EST 2020

% Result     : Theorem 4.05s
% Output     : CNFRefutation 4.05s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 276 expanded)
%              Number of clauses        :   58 (  79 expanded)
%              Number of leaves         :   14 (  71 expanded)
%              Depth                    :   17
%              Number of atoms          :  371 (1726 expanded)
%              Number of equality atoms :  144 ( 288 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f32,conjecture,(
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

fof(f33,negated_conjecture,(
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
    inference(negated_conjecture,[],[f32])).

fof(f59,plain,(
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
    inference(ennf_transformation,[],[f33])).

fof(f60,plain,(
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
    inference(flattening,[],[f59])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
     => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK7),k6_partfun1(X0))
        & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(sK7,X1,X0)
        & v1_funct_1(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f73,plain,
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
   => ( ~ v2_funct_1(sK6)
      & ? [X3] :
          ( r2_relset_1(sK4,sK4,k1_partfun1(sK4,sK5,sK5,sK4,sK6,X3),k6_partfun1(sK4))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
          & v1_funct_2(X3,sK5,sK4)
          & v1_funct_1(X3) )
      & k1_xboole_0 != sK5
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
      & v1_funct_2(sK6,sK4,sK5)
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f75,plain,
    ( ~ v2_funct_1(sK6)
    & r2_relset_1(sK4,sK4,k1_partfun1(sK4,sK5,sK5,sK4,sK6,sK7),k6_partfun1(sK4))
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
    & v1_funct_2(sK7,sK5,sK4)
    & v1_funct_1(sK7)
    & k1_xboole_0 != sK5
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    & v1_funct_2(sK6,sK4,sK5)
    & v1_funct_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f60,f74,f73])).

fof(f127,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) ),
    inference(cnf_transformation,[],[f75])).

fof(f123,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f75])).

fof(f29,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f56,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f55])).

fof(f117,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f121,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f75])).

fof(f25,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f50,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f49])).

fof(f71,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f50])).

fof(f106,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f128,plain,(
    r2_relset_1(sK4,sK4,k1_partfun1(sK4,sK5,sK5,sK4,sK6,sK7),k6_partfun1(sK4)) ),
    inference(cnf_transformation,[],[f75])).

fof(f28,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f28])).

fof(f116,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f36])).

fof(f125,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f75])).

fof(f27,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f54,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f53])).

fof(f115,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f22,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( ? [X1] :
            ( k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,X1)
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
       => v2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ! [X1] :
          ( k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f46,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ! [X1] :
          ( k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f45])).

fof(f103,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X0)
      | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f30,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f118,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f30])).

fof(f146,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X0)
      | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f103,f118])).

fof(f129,plain,(
    ~ v2_funct_1(sK6) ),
    inference(cnf_transformation,[],[f75])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f26,axiom,(
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

fof(f51,plain,(
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
    inference(ennf_transformation,[],[f26])).

fof(f52,plain,(
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
    inference(flattening,[],[f51])).

fof(f72,plain,(
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
    inference(nnf_transformation,[],[f52])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f122,plain,(
    v1_funct_2(sK6,sK4,sK5) ),
    inference(cnf_transformation,[],[f75])).

fof(f124,plain,(
    k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_38,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_1429,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_42,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_1426,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_33,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k1_partfun1(X1,X2,X4,X5,X0,X3) = k5_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_1433,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_4196,plain,
    ( k1_partfun1(sK4,sK5,X0,X1,sK6,X2) = k5_relat_1(sK6,X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1426,c_1433])).

cnf(c_44,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_45,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_4917,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(sK4,sK5,X0,X1,sK6,X2) = k5_relat_1(sK6,X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4196,c_45])).

cnf(c_4918,plain,
    ( k1_partfun1(sK4,sK5,X0,X1,sK6,X2) = k5_relat_1(sK6,X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_4917])).

cnf(c_4925,plain,
    ( k1_partfun1(sK4,sK5,sK5,sK4,sK6,sK7) = k5_relat_1(sK6,sK7)
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1429,c_4918])).

cnf(c_23,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f106])).

cnf(c_37,negated_conjecture,
    ( r2_relset_1(sK4,sK4,k1_partfun1(sK4,sK5,sK5,sK4,sK6,sK7),k6_partfun1(sK4)) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_491,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK4,sK5,sK5,sK4,sK6,sK7) != X0
    | k6_partfun1(sK4) != X3
    | sK4 != X2
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_37])).

cnf(c_492,plain,
    ( ~ m1_subset_1(k1_partfun1(sK4,sK5,sK5,sK4,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(sK4,sK4)))
    | ~ m1_subset_1(k6_partfun1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK4,sK4)))
    | k6_partfun1(sK4) = k1_partfun1(sK4,sK5,sK5,sK4,sK6,sK7) ),
    inference(unflattening,[status(thm)],[c_491])).

cnf(c_32,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_500,plain,
    ( ~ m1_subset_1(k1_partfun1(sK4,sK5,sK5,sK4,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(sK4,sK4)))
    | k6_partfun1(sK4) = k1_partfun1(sK4,sK5,sK5,sK4,sK6,sK7) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_492,c_32])).

cnf(c_1421,plain,
    ( k6_partfun1(sK4) = k1_partfun1(sK4,sK5,sK5,sK4,sK6,sK7)
    | m1_subset_1(k1_partfun1(sK4,sK5,sK5,sK4,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_500])).

cnf(c_40,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_30,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X1,X2,X4,X5,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X5)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_1728,plain,
    ( m1_subset_1(k1_partfun1(sK4,sK5,sK5,sK4,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(sK4,sK4)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | ~ v1_funct_1(sK7)
    | ~ v1_funct_1(sK6) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_2254,plain,
    ( k6_partfun1(sK4) = k1_partfun1(sK4,sK5,sK5,sK4,sK6,sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1421,c_44,c_42,c_40,c_38,c_500,c_1728])).

cnf(c_4928,plain,
    ( k5_relat_1(sK6,sK7) = k6_partfun1(sK4)
    | v1_funct_1(sK7) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4925,c_2254])).

cnf(c_48,plain,
    ( v1_funct_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_5072,plain,
    ( k5_relat_1(sK6,sK7) = k6_partfun1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4928,c_48])).

cnf(c_19,plain,
    ( v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f146])).

cnf(c_1445,plain,
    ( k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
    | v2_funct_1(X0) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_6846,plain,
    ( k6_partfun1(k1_relat_1(sK6)) != k6_partfun1(sK4)
    | v2_funct_1(sK6) = iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_relat_1(sK7) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_5072,c_1445])).

cnf(c_47,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_50,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_36,negated_conjecture,
    ( ~ v2_funct_1(sK6) ),
    inference(cnf_transformation,[],[f129])).

cnf(c_52,plain,
    ( v2_funct_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1563,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_1760,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_1563])).

cnf(c_1761,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1760])).

cnf(c_2055,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
    | v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_2056,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) != iProver_top
    | v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2055])).

cnf(c_8165,plain,
    ( k6_partfun1(k1_relat_1(sK6)) != k6_partfun1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6846,c_45,c_47,c_48,c_50,c_52,c_1761,c_2056])).

cnf(c_29,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1437,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_6730,plain,
    ( k1_relset_1(sK4,sK5,sK6) = sK4
    | sK5 = k1_xboole_0
    | v1_funct_2(sK6,sK4,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1426,c_1437])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1443,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3748,plain,
    ( k1_relset_1(sK4,sK5,sK6) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_1426,c_1443])).

cnf(c_6733,plain,
    ( k1_relat_1(sK6) = sK4
    | sK5 = k1_xboole_0
    | v1_funct_2(sK6,sK4,sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6730,c_3748])).

cnf(c_43,negated_conjecture,
    ( v1_funct_2(sK6,sK4,sK5) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_46,plain,
    ( v1_funct_2(sK6,sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_41,negated_conjecture,
    ( k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f124])).

cnf(c_851,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_888,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_851])).

cnf(c_852,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1550,plain,
    ( sK5 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_852])).

cnf(c_1551,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1550])).

cnf(c_7870,plain,
    ( k1_relat_1(sK6) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6733,c_46,c_41,c_888,c_1551])).

cnf(c_8167,plain,
    ( k6_partfun1(sK4) != k6_partfun1(sK4) ),
    inference(light_normalisation,[status(thm)],[c_8165,c_7870])).

cnf(c_8168,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_8167])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:20:47 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 4.05/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.05/0.99  
% 4.05/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.05/0.99  
% 4.05/0.99  ------  iProver source info
% 4.05/0.99  
% 4.05/0.99  git: date: 2020-06-30 10:37:57 +0100
% 4.05/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.05/0.99  git: non_committed_changes: false
% 4.05/0.99  git: last_make_outside_of_git: false
% 4.05/0.99  
% 4.05/0.99  ------ 
% 4.05/0.99  
% 4.05/0.99  ------ Input Options
% 4.05/0.99  
% 4.05/0.99  --out_options                           all
% 4.05/0.99  --tptp_safe_out                         true
% 4.05/0.99  --problem_path                          ""
% 4.05/0.99  --include_path                          ""
% 4.05/0.99  --clausifier                            res/vclausify_rel
% 4.05/0.99  --clausifier_options                    ""
% 4.05/0.99  --stdin                                 false
% 4.05/0.99  --stats_out                             all
% 4.05/0.99  
% 4.05/0.99  ------ General Options
% 4.05/0.99  
% 4.05/0.99  --fof                                   false
% 4.05/0.99  --time_out_real                         305.
% 4.05/0.99  --time_out_virtual                      -1.
% 4.05/0.99  --symbol_type_check                     false
% 4.05/0.99  --clausify_out                          false
% 4.05/0.99  --sig_cnt_out                           false
% 4.05/0.99  --trig_cnt_out                          false
% 4.05/0.99  --trig_cnt_out_tolerance                1.
% 4.05/0.99  --trig_cnt_out_sk_spl                   false
% 4.05/0.99  --abstr_cl_out                          false
% 4.05/0.99  
% 4.05/0.99  ------ Global Options
% 4.05/0.99  
% 4.05/0.99  --schedule                              default
% 4.05/0.99  --add_important_lit                     false
% 4.05/0.99  --prop_solver_per_cl                    1000
% 4.05/0.99  --min_unsat_core                        false
% 4.05/0.99  --soft_assumptions                      false
% 4.05/0.99  --soft_lemma_size                       3
% 4.05/0.99  --prop_impl_unit_size                   0
% 4.05/0.99  --prop_impl_unit                        []
% 4.05/0.99  --share_sel_clauses                     true
% 4.05/0.99  --reset_solvers                         false
% 4.05/0.99  --bc_imp_inh                            [conj_cone]
% 4.05/0.99  --conj_cone_tolerance                   3.
% 4.05/0.99  --extra_neg_conj                        none
% 4.05/0.99  --large_theory_mode                     true
% 4.05/0.99  --prolific_symb_bound                   200
% 4.05/0.99  --lt_threshold                          2000
% 4.05/0.99  --clause_weak_htbl                      true
% 4.05/0.99  --gc_record_bc_elim                     false
% 4.05/0.99  
% 4.05/0.99  ------ Preprocessing Options
% 4.05/0.99  
% 4.05/0.99  --preprocessing_flag                    true
% 4.05/0.99  --time_out_prep_mult                    0.1
% 4.05/0.99  --splitting_mode                        input
% 4.05/0.99  --splitting_grd                         true
% 4.05/0.99  --splitting_cvd                         false
% 4.05/0.99  --splitting_cvd_svl                     false
% 4.05/0.99  --splitting_nvd                         32
% 4.05/0.99  --sub_typing                            true
% 4.05/0.99  --prep_gs_sim                           true
% 4.05/0.99  --prep_unflatten                        true
% 4.05/0.99  --prep_res_sim                          true
% 4.05/0.99  --prep_upred                            true
% 4.05/0.99  --prep_sem_filter                       exhaustive
% 4.05/0.99  --prep_sem_filter_out                   false
% 4.05/0.99  --pred_elim                             true
% 4.05/0.99  --res_sim_input                         true
% 4.05/0.99  --eq_ax_congr_red                       true
% 4.05/0.99  --pure_diseq_elim                       true
% 4.05/0.99  --brand_transform                       false
% 4.05/0.99  --non_eq_to_eq                          false
% 4.05/0.99  --prep_def_merge                        true
% 4.05/0.99  --prep_def_merge_prop_impl              false
% 4.05/0.99  --prep_def_merge_mbd                    true
% 4.05/0.99  --prep_def_merge_tr_red                 false
% 4.05/0.99  --prep_def_merge_tr_cl                  false
% 4.05/0.99  --smt_preprocessing                     true
% 4.05/0.99  --smt_ac_axioms                         fast
% 4.05/0.99  --preprocessed_out                      false
% 4.05/0.99  --preprocessed_stats                    false
% 4.05/0.99  
% 4.05/0.99  ------ Abstraction refinement Options
% 4.05/0.99  
% 4.05/0.99  --abstr_ref                             []
% 4.05/0.99  --abstr_ref_prep                        false
% 4.05/0.99  --abstr_ref_until_sat                   false
% 4.05/0.99  --abstr_ref_sig_restrict                funpre
% 4.05/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 4.05/0.99  --abstr_ref_under                       []
% 4.05/0.99  
% 4.05/0.99  ------ SAT Options
% 4.05/0.99  
% 4.05/0.99  --sat_mode                              false
% 4.05/0.99  --sat_fm_restart_options                ""
% 4.05/0.99  --sat_gr_def                            false
% 4.05/0.99  --sat_epr_types                         true
% 4.05/0.99  --sat_non_cyclic_types                  false
% 4.05/0.99  --sat_finite_models                     false
% 4.05/0.99  --sat_fm_lemmas                         false
% 4.05/0.99  --sat_fm_prep                           false
% 4.05/0.99  --sat_fm_uc_incr                        true
% 4.05/0.99  --sat_out_model                         small
% 4.05/0.99  --sat_out_clauses                       false
% 4.05/0.99  
% 4.05/0.99  ------ QBF Options
% 4.05/0.99  
% 4.05/0.99  --qbf_mode                              false
% 4.05/0.99  --qbf_elim_univ                         false
% 4.05/0.99  --qbf_dom_inst                          none
% 4.05/0.99  --qbf_dom_pre_inst                      false
% 4.05/0.99  --qbf_sk_in                             false
% 4.05/0.99  --qbf_pred_elim                         true
% 4.05/0.99  --qbf_split                             512
% 4.05/0.99  
% 4.05/0.99  ------ BMC1 Options
% 4.05/0.99  
% 4.05/0.99  --bmc1_incremental                      false
% 4.05/0.99  --bmc1_axioms                           reachable_all
% 4.05/0.99  --bmc1_min_bound                        0
% 4.05/0.99  --bmc1_max_bound                        -1
% 4.05/0.99  --bmc1_max_bound_default                -1
% 4.05/0.99  --bmc1_symbol_reachability              true
% 4.05/0.99  --bmc1_property_lemmas                  false
% 4.05/0.99  --bmc1_k_induction                      false
% 4.05/0.99  --bmc1_non_equiv_states                 false
% 4.05/0.99  --bmc1_deadlock                         false
% 4.05/0.99  --bmc1_ucm                              false
% 4.05/0.99  --bmc1_add_unsat_core                   none
% 4.05/0.99  --bmc1_unsat_core_children              false
% 4.05/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 4.05/0.99  --bmc1_out_stat                         full
% 4.05/0.99  --bmc1_ground_init                      false
% 4.05/0.99  --bmc1_pre_inst_next_state              false
% 4.05/0.99  --bmc1_pre_inst_state                   false
% 4.05/0.99  --bmc1_pre_inst_reach_state             false
% 4.05/0.99  --bmc1_out_unsat_core                   false
% 4.05/0.99  --bmc1_aig_witness_out                  false
% 4.05/0.99  --bmc1_verbose                          false
% 4.05/0.99  --bmc1_dump_clauses_tptp                false
% 4.05/0.99  --bmc1_dump_unsat_core_tptp             false
% 4.05/0.99  --bmc1_dump_file                        -
% 4.05/0.99  --bmc1_ucm_expand_uc_limit              128
% 4.05/0.99  --bmc1_ucm_n_expand_iterations          6
% 4.05/0.99  --bmc1_ucm_extend_mode                  1
% 4.05/0.99  --bmc1_ucm_init_mode                    2
% 4.05/0.99  --bmc1_ucm_cone_mode                    none
% 4.05/0.99  --bmc1_ucm_reduced_relation_type        0
% 4.05/0.99  --bmc1_ucm_relax_model                  4
% 4.05/0.99  --bmc1_ucm_full_tr_after_sat            true
% 4.05/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 4.05/0.99  --bmc1_ucm_layered_model                none
% 4.05/0.99  --bmc1_ucm_max_lemma_size               10
% 4.05/0.99  
% 4.05/0.99  ------ AIG Options
% 4.05/0.99  
% 4.05/0.99  --aig_mode                              false
% 4.05/0.99  
% 4.05/0.99  ------ Instantiation Options
% 4.05/0.99  
% 4.05/0.99  --instantiation_flag                    true
% 4.05/0.99  --inst_sos_flag                         true
% 4.05/0.99  --inst_sos_phase                        true
% 4.05/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.05/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.05/0.99  --inst_lit_sel_side                     num_symb
% 4.05/0.99  --inst_solver_per_active                1400
% 4.05/0.99  --inst_solver_calls_frac                1.
% 4.05/0.99  --inst_passive_queue_type               priority_queues
% 4.05/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.05/0.99  --inst_passive_queues_freq              [25;2]
% 4.05/0.99  --inst_dismatching                      true
% 4.05/0.99  --inst_eager_unprocessed_to_passive     true
% 4.05/0.99  --inst_prop_sim_given                   true
% 4.05/0.99  --inst_prop_sim_new                     false
% 4.05/0.99  --inst_subs_new                         false
% 4.05/0.99  --inst_eq_res_simp                      false
% 4.05/0.99  --inst_subs_given                       false
% 4.05/0.99  --inst_orphan_elimination               true
% 4.05/0.99  --inst_learning_loop_flag               true
% 4.05/0.99  --inst_learning_start                   3000
% 4.05/0.99  --inst_learning_factor                  2
% 4.05/0.99  --inst_start_prop_sim_after_learn       3
% 4.05/0.99  --inst_sel_renew                        solver
% 4.05/0.99  --inst_lit_activity_flag                true
% 4.05/0.99  --inst_restr_to_given                   false
% 4.05/0.99  --inst_activity_threshold               500
% 4.05/0.99  --inst_out_proof                        true
% 4.05/0.99  
% 4.05/0.99  ------ Resolution Options
% 4.05/0.99  
% 4.05/0.99  --resolution_flag                       true
% 4.05/0.99  --res_lit_sel                           adaptive
% 4.05/0.99  --res_lit_sel_side                      none
% 4.05/0.99  --res_ordering                          kbo
% 4.05/0.99  --res_to_prop_solver                    active
% 4.05/0.99  --res_prop_simpl_new                    false
% 4.05/0.99  --res_prop_simpl_given                  true
% 4.05/0.99  --res_passive_queue_type                priority_queues
% 4.05/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.05/0.99  --res_passive_queues_freq               [15;5]
% 4.05/0.99  --res_forward_subs                      full
% 4.05/0.99  --res_backward_subs                     full
% 4.05/0.99  --res_forward_subs_resolution           true
% 4.05/0.99  --res_backward_subs_resolution          true
% 4.05/0.99  --res_orphan_elimination                true
% 4.05/0.99  --res_time_limit                        2.
% 4.05/0.99  --res_out_proof                         true
% 4.05/0.99  
% 4.05/0.99  ------ Superposition Options
% 4.05/0.99  
% 4.05/0.99  --superposition_flag                    true
% 4.05/0.99  --sup_passive_queue_type                priority_queues
% 4.05/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.05/0.99  --sup_passive_queues_freq               [8;1;4]
% 4.05/0.99  --demod_completeness_check              fast
% 4.05/0.99  --demod_use_ground                      true
% 4.05/0.99  --sup_to_prop_solver                    passive
% 4.05/0.99  --sup_prop_simpl_new                    true
% 4.05/0.99  --sup_prop_simpl_given                  true
% 4.05/0.99  --sup_fun_splitting                     true
% 4.05/0.99  --sup_smt_interval                      50000
% 4.05/0.99  
% 4.05/0.99  ------ Superposition Simplification Setup
% 4.05/0.99  
% 4.05/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.05/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.05/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.05/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.05/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 4.05/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.05/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.05/0.99  --sup_immed_triv                        [TrivRules]
% 4.05/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.05/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.05/0.99  --sup_immed_bw_main                     []
% 4.05/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.05/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 4.05/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.05/0.99  --sup_input_bw                          []
% 4.05/0.99  
% 4.05/0.99  ------ Combination Options
% 4.05/0.99  
% 4.05/0.99  --comb_res_mult                         3
% 4.05/0.99  --comb_sup_mult                         2
% 4.05/0.99  --comb_inst_mult                        10
% 4.05/0.99  
% 4.05/0.99  ------ Debug Options
% 4.05/0.99  
% 4.05/0.99  --dbg_backtrace                         false
% 4.05/0.99  --dbg_dump_prop_clauses                 false
% 4.05/0.99  --dbg_dump_prop_clauses_file            -
% 4.05/0.99  --dbg_out_stat                          false
% 4.05/0.99  ------ Parsing...
% 4.05/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.05/0.99  
% 4.05/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 4.05/0.99  
% 4.05/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.05/0.99  
% 4.05/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.05/0.99  ------ Proving...
% 4.05/0.99  ------ Problem Properties 
% 4.05/0.99  
% 4.05/0.99  
% 4.05/0.99  clauses                                 41
% 4.05/0.99  conjectures                             8
% 4.05/0.99  EPR                                     6
% 4.05/0.99  Horn                                    35
% 4.05/0.99  unary                                   19
% 4.05/0.99  binary                                  5
% 4.05/0.99  lits                                    107
% 4.05/0.99  lits eq                                 28
% 4.05/0.99  fd_pure                                 0
% 4.05/0.99  fd_pseudo                               0
% 4.05/0.99  fd_cond                                 5
% 4.05/0.99  fd_pseudo_cond                          0
% 4.05/0.99  AC symbols                              0
% 4.05/0.99  
% 4.05/0.99  ------ Schedule dynamic 5 is on 
% 4.05/0.99  
% 4.05/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 4.05/0.99  
% 4.05/0.99  
% 4.05/0.99  ------ 
% 4.05/0.99  Current options:
% 4.05/0.99  ------ 
% 4.05/0.99  
% 4.05/0.99  ------ Input Options
% 4.05/0.99  
% 4.05/0.99  --out_options                           all
% 4.05/0.99  --tptp_safe_out                         true
% 4.05/0.99  --problem_path                          ""
% 4.05/0.99  --include_path                          ""
% 4.05/0.99  --clausifier                            res/vclausify_rel
% 4.05/0.99  --clausifier_options                    ""
% 4.05/0.99  --stdin                                 false
% 4.05/0.99  --stats_out                             all
% 4.05/0.99  
% 4.05/0.99  ------ General Options
% 4.05/0.99  
% 4.05/0.99  --fof                                   false
% 4.05/0.99  --time_out_real                         305.
% 4.05/0.99  --time_out_virtual                      -1.
% 4.05/0.99  --symbol_type_check                     false
% 4.05/0.99  --clausify_out                          false
% 4.05/0.99  --sig_cnt_out                           false
% 4.05/0.99  --trig_cnt_out                          false
% 4.05/0.99  --trig_cnt_out_tolerance                1.
% 4.05/0.99  --trig_cnt_out_sk_spl                   false
% 4.05/0.99  --abstr_cl_out                          false
% 4.05/0.99  
% 4.05/0.99  ------ Global Options
% 4.05/0.99  
% 4.05/0.99  --schedule                              default
% 4.05/0.99  --add_important_lit                     false
% 4.05/0.99  --prop_solver_per_cl                    1000
% 4.05/0.99  --min_unsat_core                        false
% 4.05/0.99  --soft_assumptions                      false
% 4.05/0.99  --soft_lemma_size                       3
% 4.05/0.99  --prop_impl_unit_size                   0
% 4.05/0.99  --prop_impl_unit                        []
% 4.05/0.99  --share_sel_clauses                     true
% 4.05/0.99  --reset_solvers                         false
% 4.05/0.99  --bc_imp_inh                            [conj_cone]
% 4.05/0.99  --conj_cone_tolerance                   3.
% 4.05/0.99  --extra_neg_conj                        none
% 4.05/0.99  --large_theory_mode                     true
% 4.05/0.99  --prolific_symb_bound                   200
% 4.05/0.99  --lt_threshold                          2000
% 4.05/0.99  --clause_weak_htbl                      true
% 4.05/0.99  --gc_record_bc_elim                     false
% 4.05/0.99  
% 4.05/0.99  ------ Preprocessing Options
% 4.05/0.99  
% 4.05/0.99  --preprocessing_flag                    true
% 4.05/0.99  --time_out_prep_mult                    0.1
% 4.05/0.99  --splitting_mode                        input
% 4.05/0.99  --splitting_grd                         true
% 4.05/0.99  --splitting_cvd                         false
% 4.05/0.99  --splitting_cvd_svl                     false
% 4.05/0.99  --splitting_nvd                         32
% 4.05/0.99  --sub_typing                            true
% 4.05/0.99  --prep_gs_sim                           true
% 4.05/0.99  --prep_unflatten                        true
% 4.05/0.99  --prep_res_sim                          true
% 4.05/0.99  --prep_upred                            true
% 4.05/0.99  --prep_sem_filter                       exhaustive
% 4.05/0.99  --prep_sem_filter_out                   false
% 4.05/0.99  --pred_elim                             true
% 4.05/0.99  --res_sim_input                         true
% 4.05/0.99  --eq_ax_congr_red                       true
% 4.05/0.99  --pure_diseq_elim                       true
% 4.05/0.99  --brand_transform                       false
% 4.05/0.99  --non_eq_to_eq                          false
% 4.05/0.99  --prep_def_merge                        true
% 4.05/0.99  --prep_def_merge_prop_impl              false
% 4.05/0.99  --prep_def_merge_mbd                    true
% 4.05/0.99  --prep_def_merge_tr_red                 false
% 4.05/0.99  --prep_def_merge_tr_cl                  false
% 4.05/0.99  --smt_preprocessing                     true
% 4.05/0.99  --smt_ac_axioms                         fast
% 4.05/0.99  --preprocessed_out                      false
% 4.05/0.99  --preprocessed_stats                    false
% 4.05/0.99  
% 4.05/0.99  ------ Abstraction refinement Options
% 4.05/0.99  
% 4.05/0.99  --abstr_ref                             []
% 4.05/0.99  --abstr_ref_prep                        false
% 4.05/0.99  --abstr_ref_until_sat                   false
% 4.05/0.99  --abstr_ref_sig_restrict                funpre
% 4.05/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 4.05/0.99  --abstr_ref_under                       []
% 4.05/0.99  
% 4.05/0.99  ------ SAT Options
% 4.05/0.99  
% 4.05/0.99  --sat_mode                              false
% 4.05/0.99  --sat_fm_restart_options                ""
% 4.05/0.99  --sat_gr_def                            false
% 4.05/0.99  --sat_epr_types                         true
% 4.05/0.99  --sat_non_cyclic_types                  false
% 4.05/0.99  --sat_finite_models                     false
% 4.05/0.99  --sat_fm_lemmas                         false
% 4.05/0.99  --sat_fm_prep                           false
% 4.05/0.99  --sat_fm_uc_incr                        true
% 4.05/0.99  --sat_out_model                         small
% 4.05/0.99  --sat_out_clauses                       false
% 4.05/0.99  
% 4.05/0.99  ------ QBF Options
% 4.05/0.99  
% 4.05/0.99  --qbf_mode                              false
% 4.05/0.99  --qbf_elim_univ                         false
% 4.05/0.99  --qbf_dom_inst                          none
% 4.05/0.99  --qbf_dom_pre_inst                      false
% 4.05/0.99  --qbf_sk_in                             false
% 4.05/0.99  --qbf_pred_elim                         true
% 4.05/0.99  --qbf_split                             512
% 4.05/0.99  
% 4.05/0.99  ------ BMC1 Options
% 4.05/0.99  
% 4.05/0.99  --bmc1_incremental                      false
% 4.05/0.99  --bmc1_axioms                           reachable_all
% 4.05/0.99  --bmc1_min_bound                        0
% 4.05/0.99  --bmc1_max_bound                        -1
% 4.05/0.99  --bmc1_max_bound_default                -1
% 4.05/0.99  --bmc1_symbol_reachability              true
% 4.05/0.99  --bmc1_property_lemmas                  false
% 4.05/0.99  --bmc1_k_induction                      false
% 4.05/0.99  --bmc1_non_equiv_states                 false
% 4.05/0.99  --bmc1_deadlock                         false
% 4.05/0.99  --bmc1_ucm                              false
% 4.05/0.99  --bmc1_add_unsat_core                   none
% 4.05/0.99  --bmc1_unsat_core_children              false
% 4.05/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 4.05/0.99  --bmc1_out_stat                         full
% 4.05/0.99  --bmc1_ground_init                      false
% 4.05/0.99  --bmc1_pre_inst_next_state              false
% 4.05/0.99  --bmc1_pre_inst_state                   false
% 4.05/0.99  --bmc1_pre_inst_reach_state             false
% 4.05/0.99  --bmc1_out_unsat_core                   false
% 4.05/0.99  --bmc1_aig_witness_out                  false
% 4.05/0.99  --bmc1_verbose                          false
% 4.05/0.99  --bmc1_dump_clauses_tptp                false
% 4.05/0.99  --bmc1_dump_unsat_core_tptp             false
% 4.05/0.99  --bmc1_dump_file                        -
% 4.05/0.99  --bmc1_ucm_expand_uc_limit              128
% 4.05/0.99  --bmc1_ucm_n_expand_iterations          6
% 4.05/0.99  --bmc1_ucm_extend_mode                  1
% 4.05/0.99  --bmc1_ucm_init_mode                    2
% 4.05/0.99  --bmc1_ucm_cone_mode                    none
% 4.05/0.99  --bmc1_ucm_reduced_relation_type        0
% 4.05/0.99  --bmc1_ucm_relax_model                  4
% 4.05/0.99  --bmc1_ucm_full_tr_after_sat            true
% 4.05/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 4.05/0.99  --bmc1_ucm_layered_model                none
% 4.05/0.99  --bmc1_ucm_max_lemma_size               10
% 4.05/0.99  
% 4.05/0.99  ------ AIG Options
% 4.05/0.99  
% 4.05/0.99  --aig_mode                              false
% 4.05/0.99  
% 4.05/0.99  ------ Instantiation Options
% 4.05/0.99  
% 4.05/0.99  --instantiation_flag                    true
% 4.05/0.99  --inst_sos_flag                         true
% 4.05/0.99  --inst_sos_phase                        true
% 4.05/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.05/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.05/0.99  --inst_lit_sel_side                     none
% 4.05/0.99  --inst_solver_per_active                1400
% 4.05/0.99  --inst_solver_calls_frac                1.
% 4.05/0.99  --inst_passive_queue_type               priority_queues
% 4.05/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.05/0.99  --inst_passive_queues_freq              [25;2]
% 4.05/0.99  --inst_dismatching                      true
% 4.05/0.99  --inst_eager_unprocessed_to_passive     true
% 4.05/0.99  --inst_prop_sim_given                   true
% 4.05/0.99  --inst_prop_sim_new                     false
% 4.05/0.99  --inst_subs_new                         false
% 4.05/0.99  --inst_eq_res_simp                      false
% 4.05/0.99  --inst_subs_given                       false
% 4.05/0.99  --inst_orphan_elimination               true
% 4.05/0.99  --inst_learning_loop_flag               true
% 4.05/0.99  --inst_learning_start                   3000
% 4.05/0.99  --inst_learning_factor                  2
% 4.05/0.99  --inst_start_prop_sim_after_learn       3
% 4.05/0.99  --inst_sel_renew                        solver
% 4.05/0.99  --inst_lit_activity_flag                true
% 4.05/0.99  --inst_restr_to_given                   false
% 4.05/0.99  --inst_activity_threshold               500
% 4.05/0.99  --inst_out_proof                        true
% 4.05/0.99  
% 4.05/0.99  ------ Resolution Options
% 4.05/0.99  
% 4.05/0.99  --resolution_flag                       false
% 4.05/0.99  --res_lit_sel                           adaptive
% 4.05/0.99  --res_lit_sel_side                      none
% 4.05/0.99  --res_ordering                          kbo
% 4.05/0.99  --res_to_prop_solver                    active
% 4.05/0.99  --res_prop_simpl_new                    false
% 4.05/0.99  --res_prop_simpl_given                  true
% 4.05/0.99  --res_passive_queue_type                priority_queues
% 4.05/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.05/0.99  --res_passive_queues_freq               [15;5]
% 4.05/0.99  --res_forward_subs                      full
% 4.05/0.99  --res_backward_subs                     full
% 4.05/0.99  --res_forward_subs_resolution           true
% 4.05/0.99  --res_backward_subs_resolution          true
% 4.05/0.99  --res_orphan_elimination                true
% 4.05/0.99  --res_time_limit                        2.
% 4.05/0.99  --res_out_proof                         true
% 4.05/0.99  
% 4.05/0.99  ------ Superposition Options
% 4.05/0.99  
% 4.05/0.99  --superposition_flag                    true
% 4.05/0.99  --sup_passive_queue_type                priority_queues
% 4.05/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.05/0.99  --sup_passive_queues_freq               [8;1;4]
% 4.05/0.99  --demod_completeness_check              fast
% 4.05/0.99  --demod_use_ground                      true
% 4.05/0.99  --sup_to_prop_solver                    passive
% 4.05/0.99  --sup_prop_simpl_new                    true
% 4.05/0.99  --sup_prop_simpl_given                  true
% 4.05/0.99  --sup_fun_splitting                     true
% 4.05/0.99  --sup_smt_interval                      50000
% 4.05/0.99  
% 4.05/0.99  ------ Superposition Simplification Setup
% 4.05/0.99  
% 4.05/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.05/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.05/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.05/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.05/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 4.05/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.05/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.05/0.99  --sup_immed_triv                        [TrivRules]
% 4.05/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.05/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.05/0.99  --sup_immed_bw_main                     []
% 4.05/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.05/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 4.05/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.05/0.99  --sup_input_bw                          []
% 4.05/0.99  
% 4.05/0.99  ------ Combination Options
% 4.05/0.99  
% 4.05/0.99  --comb_res_mult                         3
% 4.05/0.99  --comb_sup_mult                         2
% 4.05/0.99  --comb_inst_mult                        10
% 4.05/0.99  
% 4.05/0.99  ------ Debug Options
% 4.05/0.99  
% 4.05/0.99  --dbg_backtrace                         false
% 4.05/0.99  --dbg_dump_prop_clauses                 false
% 4.05/0.99  --dbg_dump_prop_clauses_file            -
% 4.05/0.99  --dbg_out_stat                          false
% 4.05/0.99  
% 4.05/0.99  
% 4.05/0.99  
% 4.05/0.99  
% 4.05/0.99  ------ Proving...
% 4.05/0.99  
% 4.05/0.99  
% 4.05/0.99  % SZS status Theorem for theBenchmark.p
% 4.05/0.99  
% 4.05/0.99   Resolution empty clause
% 4.05/0.99  
% 4.05/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 4.05/0.99  
% 4.05/0.99  fof(f32,conjecture,(
% 4.05/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ~(~v2_funct_1(X2) & ? [X3] : (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & k1_xboole_0 != X1))),
% 4.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.05/0.99  
% 4.05/0.99  fof(f33,negated_conjecture,(
% 4.05/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ~(~v2_funct_1(X2) & ? [X3] : (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & k1_xboole_0 != X1))),
% 4.05/0.99    inference(negated_conjecture,[],[f32])).
% 4.05/0.99  
% 4.05/0.99  fof(f59,plain,(
% 4.05/0.99    ? [X0,X1,X2] : ((~v2_funct_1(X2) & ? [X3] : (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 4.05/0.99    inference(ennf_transformation,[],[f33])).
% 4.05/0.99  
% 4.05/0.99  fof(f60,plain,(
% 4.05/0.99    ? [X0,X1,X2] : (~v2_funct_1(X2) & ? [X3] : (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 4.05/0.99    inference(flattening,[],[f59])).
% 4.05/0.99  
% 4.05/0.99  fof(f74,plain,(
% 4.05/0.99    ( ! [X2,X0,X1] : (? [X3] : (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK7),k6_partfun1(X0)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK7,X1,X0) & v1_funct_1(sK7))) )),
% 4.05/0.99    introduced(choice_axiom,[])).
% 4.05/0.99  
% 4.05/0.99  fof(f73,plain,(
% 4.05/0.99    ? [X0,X1,X2] : (~v2_funct_1(X2) & ? [X3] : (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (~v2_funct_1(sK6) & ? [X3] : (r2_relset_1(sK4,sK4,k1_partfun1(sK4,sK5,sK5,sK4,sK6,X3),k6_partfun1(sK4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) & v1_funct_2(X3,sK5,sK4) & v1_funct_1(X3)) & k1_xboole_0 != sK5 & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK6,sK4,sK5) & v1_funct_1(sK6))),
% 4.05/0.99    introduced(choice_axiom,[])).
% 4.05/0.99  
% 4.05/0.99  fof(f75,plain,(
% 4.05/0.99    ~v2_funct_1(sK6) & (r2_relset_1(sK4,sK4,k1_partfun1(sK4,sK5,sK5,sK4,sK6,sK7),k6_partfun1(sK4)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) & v1_funct_2(sK7,sK5,sK4) & v1_funct_1(sK7)) & k1_xboole_0 != sK5 & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK6,sK4,sK5) & v1_funct_1(sK6)),
% 4.05/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f60,f74,f73])).
% 4.05/0.99  
% 4.05/0.99  fof(f127,plain,(
% 4.05/0.99    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))),
% 4.05/0.99    inference(cnf_transformation,[],[f75])).
% 4.05/0.99  
% 4.05/0.99  fof(f123,plain,(
% 4.05/0.99    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 4.05/0.99    inference(cnf_transformation,[],[f75])).
% 4.05/0.99  
% 4.05/0.99  fof(f29,axiom,(
% 4.05/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 4.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.05/0.99  
% 4.05/0.99  fof(f55,plain,(
% 4.05/0.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 4.05/0.99    inference(ennf_transformation,[],[f29])).
% 4.05/0.99  
% 4.05/0.99  fof(f56,plain,(
% 4.05/0.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 4.05/0.99    inference(flattening,[],[f55])).
% 4.05/0.99  
% 4.05/0.99  fof(f117,plain,(
% 4.05/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 4.05/0.99    inference(cnf_transformation,[],[f56])).
% 4.05/0.99  
% 4.05/0.99  fof(f121,plain,(
% 4.05/0.99    v1_funct_1(sK6)),
% 4.05/0.99    inference(cnf_transformation,[],[f75])).
% 4.05/0.99  
% 4.05/0.99  fof(f25,axiom,(
% 4.05/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 4.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.05/0.99  
% 4.05/0.99  fof(f49,plain,(
% 4.05/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 4.05/0.99    inference(ennf_transformation,[],[f25])).
% 4.05/0.99  
% 4.05/0.99  fof(f50,plain,(
% 4.05/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.05/0.99    inference(flattening,[],[f49])).
% 4.05/0.99  
% 4.05/0.99  fof(f71,plain,(
% 4.05/0.99    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.05/0.99    inference(nnf_transformation,[],[f50])).
% 4.05/0.99  
% 4.05/0.99  fof(f106,plain,(
% 4.05/0.99    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.05/0.99    inference(cnf_transformation,[],[f71])).
% 4.05/0.99  
% 4.05/0.99  fof(f128,plain,(
% 4.05/0.99    r2_relset_1(sK4,sK4,k1_partfun1(sK4,sK5,sK5,sK4,sK6,sK7),k6_partfun1(sK4))),
% 4.05/0.99    inference(cnf_transformation,[],[f75])).
% 4.05/0.99  
% 4.05/0.99  fof(f28,axiom,(
% 4.05/0.99    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 4.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.05/0.99  
% 4.05/0.99  fof(f36,plain,(
% 4.05/0.99    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 4.05/0.99    inference(pure_predicate_removal,[],[f28])).
% 4.05/0.99  
% 4.05/0.99  fof(f116,plain,(
% 4.05/0.99    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 4.05/0.99    inference(cnf_transformation,[],[f36])).
% 4.05/0.99  
% 4.05/0.99  fof(f125,plain,(
% 4.05/0.99    v1_funct_1(sK7)),
% 4.05/0.99    inference(cnf_transformation,[],[f75])).
% 4.05/0.99  
% 4.05/0.99  fof(f27,axiom,(
% 4.05/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 4.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.05/0.99  
% 4.05/0.99  fof(f53,plain,(
% 4.05/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 4.05/0.99    inference(ennf_transformation,[],[f27])).
% 4.05/0.99  
% 4.05/0.99  fof(f54,plain,(
% 4.05/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 4.05/0.99    inference(flattening,[],[f53])).
% 4.05/0.99  
% 4.05/0.99  fof(f115,plain,(
% 4.05/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 4.05/0.99    inference(cnf_transformation,[],[f54])).
% 4.05/0.99  
% 4.05/0.99  fof(f22,axiom,(
% 4.05/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,X1) & v1_funct_1(X1) & v1_relat_1(X1)) => v2_funct_1(X0)))),
% 4.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.05/0.99  
% 4.05/0.99  fof(f45,plain,(
% 4.05/0.99    ! [X0] : ((v2_funct_1(X0) | ! [X1] : (k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 4.05/0.99    inference(ennf_transformation,[],[f22])).
% 4.05/0.99  
% 4.05/0.99  fof(f46,plain,(
% 4.05/0.99    ! [X0] : (v2_funct_1(X0) | ! [X1] : (k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.05/0.99    inference(flattening,[],[f45])).
% 4.05/0.99  
% 4.05/0.99  fof(f103,plain,(
% 4.05/0.99    ( ! [X0,X1] : (v2_funct_1(X0) | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.05/0.99    inference(cnf_transformation,[],[f46])).
% 4.05/0.99  
% 4.05/0.99  fof(f30,axiom,(
% 4.05/0.99    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 4.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.05/0.99  
% 4.05/0.99  fof(f118,plain,(
% 4.05/0.99    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 4.05/0.99    inference(cnf_transformation,[],[f30])).
% 4.05/0.99  
% 4.05/0.99  fof(f146,plain,(
% 4.05/0.99    ( ! [X0,X1] : (v2_funct_1(X0) | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.05/0.99    inference(definition_unfolding,[],[f103,f118])).
% 4.05/0.99  
% 4.05/0.99  fof(f129,plain,(
% 4.05/0.99    ~v2_funct_1(sK6)),
% 4.05/0.99    inference(cnf_transformation,[],[f75])).
% 4.05/0.99  
% 4.05/0.99  fof(f23,axiom,(
% 4.05/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 4.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.05/0.99  
% 4.05/0.99  fof(f47,plain,(
% 4.05/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.05/0.99    inference(ennf_transformation,[],[f23])).
% 4.05/0.99  
% 4.05/0.99  fof(f104,plain,(
% 4.05/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.05/0.99    inference(cnf_transformation,[],[f47])).
% 4.05/0.99  
% 4.05/0.99  fof(f26,axiom,(
% 4.05/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 4.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.05/0.99  
% 4.05/0.99  fof(f51,plain,(
% 4.05/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.05/0.99    inference(ennf_transformation,[],[f26])).
% 4.05/0.99  
% 4.05/0.99  fof(f52,plain,(
% 4.05/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.05/0.99    inference(flattening,[],[f51])).
% 4.05/0.99  
% 4.05/0.99  fof(f72,plain,(
% 4.05/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.05/0.99    inference(nnf_transformation,[],[f52])).
% 4.05/0.99  
% 4.05/0.99  fof(f108,plain,(
% 4.05/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.05/0.99    inference(cnf_transformation,[],[f72])).
% 4.05/0.99  
% 4.05/0.99  fof(f24,axiom,(
% 4.05/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 4.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.05/0.99  
% 4.05/0.99  fof(f48,plain,(
% 4.05/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.05/0.99    inference(ennf_transformation,[],[f24])).
% 4.05/0.99  
% 4.05/0.99  fof(f105,plain,(
% 4.05/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.05/0.99    inference(cnf_transformation,[],[f48])).
% 4.05/0.99  
% 4.05/0.99  fof(f122,plain,(
% 4.05/0.99    v1_funct_2(sK6,sK4,sK5)),
% 4.05/0.99    inference(cnf_transformation,[],[f75])).
% 4.05/0.99  
% 4.05/0.99  fof(f124,plain,(
% 4.05/0.99    k1_xboole_0 != sK5),
% 4.05/0.99    inference(cnf_transformation,[],[f75])).
% 4.05/0.99  
% 4.05/0.99  cnf(c_38,negated_conjecture,
% 4.05/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) ),
% 4.05/0.99      inference(cnf_transformation,[],[f127]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1429,plain,
% 4.05/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) = iProver_top ),
% 4.05/0.99      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_42,negated_conjecture,
% 4.05/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
% 4.05/0.99      inference(cnf_transformation,[],[f123]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1426,plain,
% 4.05/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 4.05/0.99      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_33,plain,
% 4.05/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.05/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 4.05/0.99      | ~ v1_funct_1(X3)
% 4.05/0.99      | ~ v1_funct_1(X0)
% 4.05/0.99      | k1_partfun1(X1,X2,X4,X5,X0,X3) = k5_relat_1(X0,X3) ),
% 4.05/0.99      inference(cnf_transformation,[],[f117]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1433,plain,
% 4.05/0.99      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 4.05/0.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 4.05/0.99      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 4.05/0.99      | v1_funct_1(X4) != iProver_top
% 4.05/0.99      | v1_funct_1(X5) != iProver_top ),
% 4.05/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_4196,plain,
% 4.05/0.99      ( k1_partfun1(sK4,sK5,X0,X1,sK6,X2) = k5_relat_1(sK6,X2)
% 4.05/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 4.05/0.99      | v1_funct_1(X2) != iProver_top
% 4.05/0.99      | v1_funct_1(sK6) != iProver_top ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_1426,c_1433]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_44,negated_conjecture,
% 4.05/0.99      ( v1_funct_1(sK6) ),
% 4.05/0.99      inference(cnf_transformation,[],[f121]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_45,plain,
% 4.05/0.99      ( v1_funct_1(sK6) = iProver_top ),
% 4.05/0.99      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_4917,plain,
% 4.05/0.99      ( v1_funct_1(X2) != iProver_top
% 4.05/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 4.05/0.99      | k1_partfun1(sK4,sK5,X0,X1,sK6,X2) = k5_relat_1(sK6,X2) ),
% 4.05/0.99      inference(global_propositional_subsumption,[status(thm)],[c_4196,c_45]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_4918,plain,
% 4.05/0.99      ( k1_partfun1(sK4,sK5,X0,X1,sK6,X2) = k5_relat_1(sK6,X2)
% 4.05/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 4.05/0.99      | v1_funct_1(X2) != iProver_top ),
% 4.05/0.99      inference(renaming,[status(thm)],[c_4917]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_4925,plain,
% 4.05/0.99      ( k1_partfun1(sK4,sK5,sK5,sK4,sK6,sK7) = k5_relat_1(sK6,sK7)
% 4.05/0.99      | v1_funct_1(sK7) != iProver_top ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_1429,c_4918]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_23,plain,
% 4.05/0.99      ( ~ r2_relset_1(X0,X1,X2,X3)
% 4.05/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 4.05/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 4.05/0.99      | X3 = X2 ),
% 4.05/0.99      inference(cnf_transformation,[],[f106]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_37,negated_conjecture,
% 4.05/0.99      ( r2_relset_1(sK4,sK4,k1_partfun1(sK4,sK5,sK5,sK4,sK6,sK7),k6_partfun1(sK4)) ),
% 4.05/0.99      inference(cnf_transformation,[],[f128]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_491,plain,
% 4.05/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.05/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.05/0.99      | X3 = X0
% 4.05/0.99      | k1_partfun1(sK4,sK5,sK5,sK4,sK6,sK7) != X0
% 4.05/0.99      | k6_partfun1(sK4) != X3
% 4.05/0.99      | sK4 != X2
% 4.05/0.99      | sK4 != X1 ),
% 4.05/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_37]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_492,plain,
% 4.05/0.99      ( ~ m1_subset_1(k1_partfun1(sK4,sK5,sK5,sK4,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(sK4,sK4)))
% 4.05/0.99      | ~ m1_subset_1(k6_partfun1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK4,sK4)))
% 4.05/0.99      | k6_partfun1(sK4) = k1_partfun1(sK4,sK5,sK5,sK4,sK6,sK7) ),
% 4.05/0.99      inference(unflattening,[status(thm)],[c_491]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_32,plain,
% 4.05/0.99      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 4.05/0.99      inference(cnf_transformation,[],[f116]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_500,plain,
% 4.05/0.99      ( ~ m1_subset_1(k1_partfun1(sK4,sK5,sK5,sK4,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(sK4,sK4)))
% 4.05/0.99      | k6_partfun1(sK4) = k1_partfun1(sK4,sK5,sK5,sK4,sK6,sK7) ),
% 4.05/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_492,c_32]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1421,plain,
% 4.05/0.99      ( k6_partfun1(sK4) = k1_partfun1(sK4,sK5,sK5,sK4,sK6,sK7)
% 4.05/0.99      | m1_subset_1(k1_partfun1(sK4,sK5,sK5,sK4,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(sK4,sK4))) != iProver_top ),
% 4.05/0.99      inference(predicate_to_equality,[status(thm)],[c_500]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_40,negated_conjecture,
% 4.05/0.99      ( v1_funct_1(sK7) ),
% 4.05/0.99      inference(cnf_transformation,[],[f125]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_30,plain,
% 4.05/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.05/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 4.05/0.99      | m1_subset_1(k1_partfun1(X1,X2,X4,X5,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X5)))
% 4.05/0.99      | ~ v1_funct_1(X3)
% 4.05/0.99      | ~ v1_funct_1(X0) ),
% 4.05/0.99      inference(cnf_transformation,[],[f115]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1728,plain,
% 4.05/0.99      ( m1_subset_1(k1_partfun1(sK4,sK5,sK5,sK4,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(sK4,sK4)))
% 4.05/0.99      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
% 4.05/0.99      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 4.05/0.99      | ~ v1_funct_1(sK7)
% 4.05/0.99      | ~ v1_funct_1(sK6) ),
% 4.05/0.99      inference(instantiation,[status(thm)],[c_30]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_2254,plain,
% 4.05/0.99      ( k6_partfun1(sK4) = k1_partfun1(sK4,sK5,sK5,sK4,sK6,sK7) ),
% 4.05/0.99      inference(global_propositional_subsumption,
% 4.05/0.99                [status(thm)],
% 4.05/0.99                [c_1421,c_44,c_42,c_40,c_38,c_500,c_1728]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_4928,plain,
% 4.05/0.99      ( k5_relat_1(sK6,sK7) = k6_partfun1(sK4)
% 4.05/0.99      | v1_funct_1(sK7) != iProver_top ),
% 4.05/0.99      inference(light_normalisation,[status(thm)],[c_4925,c_2254]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_48,plain,
% 4.05/0.99      ( v1_funct_1(sK7) = iProver_top ),
% 4.05/0.99      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_5072,plain,
% 4.05/0.99      ( k5_relat_1(sK6,sK7) = k6_partfun1(sK4) ),
% 4.05/0.99      inference(global_propositional_subsumption,[status(thm)],[c_4928,c_48]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_19,plain,
% 4.05/0.99      ( v2_funct_1(X0)
% 4.05/0.99      | ~ v1_funct_1(X0)
% 4.05/0.99      | ~ v1_funct_1(X1)
% 4.05/0.99      | ~ v1_relat_1(X0)
% 4.05/0.99      | ~ v1_relat_1(X1)
% 4.05/0.99      | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0)) ),
% 4.05/0.99      inference(cnf_transformation,[],[f146]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1445,plain,
% 4.05/0.99      ( k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
% 4.05/0.99      | v2_funct_1(X0) = iProver_top
% 4.05/0.99      | v1_funct_1(X0) != iProver_top
% 4.05/0.99      | v1_funct_1(X1) != iProver_top
% 4.05/0.99      | v1_relat_1(X0) != iProver_top
% 4.05/0.99      | v1_relat_1(X1) != iProver_top ),
% 4.05/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_6846,plain,
% 4.05/0.99      ( k6_partfun1(k1_relat_1(sK6)) != k6_partfun1(sK4)
% 4.05/0.99      | v2_funct_1(sK6) = iProver_top
% 4.05/0.99      | v1_funct_1(sK7) != iProver_top
% 4.05/0.99      | v1_funct_1(sK6) != iProver_top
% 4.05/0.99      | v1_relat_1(sK7) != iProver_top
% 4.05/0.99      | v1_relat_1(sK6) != iProver_top ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_5072,c_1445]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_47,plain,
% 4.05/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 4.05/0.99      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_50,plain,
% 4.05/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) = iProver_top ),
% 4.05/0.99      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_36,negated_conjecture,
% 4.05/0.99      ( ~ v2_funct_1(sK6) ),
% 4.05/0.99      inference(cnf_transformation,[],[f129]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_52,plain,
% 4.05/0.99      ( v2_funct_1(sK6) != iProver_top ),
% 4.05/0.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_20,plain,
% 4.05/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 4.05/0.99      inference(cnf_transformation,[],[f104]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1563,plain,
% 4.05/0.99      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(sK6) ),
% 4.05/0.99      inference(instantiation,[status(thm)],[c_20]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1760,plain,
% 4.05/0.99      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 4.05/0.99      | v1_relat_1(sK6) ),
% 4.05/0.99      inference(instantiation,[status(thm)],[c_1563]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1761,plain,
% 4.05/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
% 4.05/0.99      | v1_relat_1(sK6) = iProver_top ),
% 4.05/0.99      inference(predicate_to_equality,[status(thm)],[c_1760]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_2055,plain,
% 4.05/0.99      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
% 4.05/0.99      | v1_relat_1(sK7) ),
% 4.05/0.99      inference(instantiation,[status(thm)],[c_20]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_2056,plain,
% 4.05/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) != iProver_top
% 4.05/0.99      | v1_relat_1(sK7) = iProver_top ),
% 4.05/0.99      inference(predicate_to_equality,[status(thm)],[c_2055]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_8165,plain,
% 4.05/0.99      ( k6_partfun1(k1_relat_1(sK6)) != k6_partfun1(sK4) ),
% 4.05/0.99      inference(global_propositional_subsumption,
% 4.05/0.99                [status(thm)],
% 4.05/0.99                [c_6846,c_45,c_47,c_48,c_50,c_52,c_1761,c_2056]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_29,plain,
% 4.05/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 4.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.05/0.99      | k1_relset_1(X1,X2,X0) = X1
% 4.05/0.99      | k1_xboole_0 = X2 ),
% 4.05/0.99      inference(cnf_transformation,[],[f108]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1437,plain,
% 4.05/0.99      ( k1_relset_1(X0,X1,X2) = X0
% 4.05/0.99      | k1_xboole_0 = X1
% 4.05/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 4.05/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 4.05/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_6730,plain,
% 4.05/0.99      ( k1_relset_1(sK4,sK5,sK6) = sK4
% 4.05/0.99      | sK5 = k1_xboole_0
% 4.05/0.99      | v1_funct_2(sK6,sK4,sK5) != iProver_top ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_1426,c_1437]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_21,plain,
% 4.05/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.05/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 4.05/0.99      inference(cnf_transformation,[],[f105]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1443,plain,
% 4.05/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 4.05/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 4.05/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_3748,plain,
% 4.05/0.99      ( k1_relset_1(sK4,sK5,sK6) = k1_relat_1(sK6) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_1426,c_1443]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_6733,plain,
% 4.05/0.99      ( k1_relat_1(sK6) = sK4
% 4.05/0.99      | sK5 = k1_xboole_0
% 4.05/0.99      | v1_funct_2(sK6,sK4,sK5) != iProver_top ),
% 4.05/0.99      inference(demodulation,[status(thm)],[c_6730,c_3748]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_43,negated_conjecture,
% 4.05/0.99      ( v1_funct_2(sK6,sK4,sK5) ),
% 4.05/0.99      inference(cnf_transformation,[],[f122]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_46,plain,
% 4.05/0.99      ( v1_funct_2(sK6,sK4,sK5) = iProver_top ),
% 4.05/0.99      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_41,negated_conjecture,
% 4.05/0.99      ( k1_xboole_0 != sK5 ),
% 4.05/0.99      inference(cnf_transformation,[],[f124]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_851,plain,( X0 = X0 ),theory(equality) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_888,plain,
% 4.05/0.99      ( k1_xboole_0 = k1_xboole_0 ),
% 4.05/0.99      inference(instantiation,[status(thm)],[c_851]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_852,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1550,plain,
% 4.05/0.99      ( sK5 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK5 ),
% 4.05/0.99      inference(instantiation,[status(thm)],[c_852]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1551,plain,
% 4.05/0.99      ( sK5 != k1_xboole_0 | k1_xboole_0 = sK5 | k1_xboole_0 != k1_xboole_0 ),
% 4.05/0.99      inference(instantiation,[status(thm)],[c_1550]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_7870,plain,
% 4.05/0.99      ( k1_relat_1(sK6) = sK4 ),
% 4.05/0.99      inference(global_propositional_subsumption,
% 4.05/0.99                [status(thm)],
% 4.05/0.99                [c_6733,c_46,c_41,c_888,c_1551]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_8167,plain,
% 4.05/0.99      ( k6_partfun1(sK4) != k6_partfun1(sK4) ),
% 4.05/0.99      inference(light_normalisation,[status(thm)],[c_8165,c_7870]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_8168,plain,
% 4.05/0.99      ( $false ),
% 4.05/0.99      inference(equality_resolution_simp,[status(thm)],[c_8167]) ).
% 4.05/0.99  
% 4.05/0.99  
% 4.05/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 4.05/0.99  
% 4.05/0.99  ------                               Statistics
% 4.05/0.99  
% 4.05/0.99  ------ General
% 4.05/0.99  
% 4.05/0.99  abstr_ref_over_cycles:                  0
% 4.05/0.99  abstr_ref_under_cycles:                 0
% 4.05/0.99  gc_basic_clause_elim:                   0
% 4.05/0.99  forced_gc_time:                         0
% 4.05/0.99  parsing_time:                           0.012
% 4.05/0.99  unif_index_cands_time:                  0.
% 4.05/0.99  unif_index_add_time:                    0.
% 4.05/0.99  orderings_time:                         0.
% 4.05/0.99  out_proof_time:                         0.011
% 4.05/0.99  total_time:                             0.323
% 4.05/0.99  num_of_symbols:                         60
% 4.05/0.99  num_of_terms:                           13497
% 4.05/0.99  
% 4.05/0.99  ------ Preprocessing
% 4.05/0.99  
% 4.05/0.99  num_of_splits:                          0
% 4.05/0.99  num_of_split_atoms:                     0
% 4.05/0.99  num_of_reused_defs:                     0
% 4.05/0.99  num_eq_ax_congr_red:                    25
% 4.05/0.99  num_of_sem_filtered_clauses:            1
% 4.05/0.99  num_of_subtypes:                        0
% 4.05/0.99  monotx_restored_types:                  0
% 4.05/0.99  sat_num_of_epr_types:                   0
% 4.05/0.99  sat_num_of_non_cyclic_types:            0
% 4.05/0.99  sat_guarded_non_collapsed_types:        0
% 4.05/0.99  num_pure_diseq_elim:                    0
% 4.05/0.99  simp_replaced_by:                       0
% 4.05/0.99  res_preprocessed:                       207
% 4.05/0.99  prep_upred:                             0
% 4.05/0.99  prep_unflattend:                        18
% 4.05/0.99  smt_new_axioms:                         0
% 4.05/0.99  pred_elim_cands:                        6
% 4.05/0.99  pred_elim:                              3
% 4.05/0.99  pred_elim_cl:                           4
% 4.05/0.99  pred_elim_cycles:                       5
% 4.05/0.99  merged_defs:                            0
% 4.05/0.99  merged_defs_ncl:                        0
% 4.05/0.99  bin_hyper_res:                          0
% 4.05/0.99  prep_cycles:                            4
% 4.05/0.99  pred_elim_time:                         0.005
% 4.05/0.99  splitting_time:                         0.
% 4.05/0.99  sem_filter_time:                        0.
% 4.05/0.99  monotx_time:                            0.
% 4.05/0.99  subtype_inf_time:                       0.
% 4.05/0.99  
% 4.05/0.99  ------ Problem properties
% 4.05/0.99  
% 4.05/0.99  clauses:                                41
% 4.05/0.99  conjectures:                            8
% 4.05/0.99  epr:                                    6
% 4.05/0.99  horn:                                   35
% 4.05/0.99  ground:                                 10
% 4.05/0.99  unary:                                  19
% 4.05/0.99  binary:                                 5
% 4.05/0.99  lits:                                   107
% 4.05/0.99  lits_eq:                                28
% 4.05/0.99  fd_pure:                                0
% 4.05/0.99  fd_pseudo:                              0
% 4.05/0.99  fd_cond:                                5
% 4.05/0.99  fd_pseudo_cond:                         0
% 4.05/0.99  ac_symbols:                             0
% 4.05/0.99  
% 4.05/0.99  ------ Propositional Solver
% 4.05/0.99  
% 4.05/0.99  prop_solver_calls:                      28
% 4.05/0.99  prop_fast_solver_calls:                 1451
% 4.05/0.99  smt_solver_calls:                       0
% 4.05/0.99  smt_fast_solver_calls:                  0
% 4.05/0.99  prop_num_of_clauses:                    3919
% 4.05/0.99  prop_preprocess_simplified:             11499
% 4.05/0.99  prop_fo_subsumed:                       59
% 4.05/0.99  prop_solver_time:                       0.
% 4.05/0.99  smt_solver_time:                        0.
% 4.05/0.99  smt_fast_solver_time:                   0.
% 4.05/0.99  prop_fast_solver_time:                  0.
% 4.05/0.99  prop_unsat_core_time:                   0.
% 4.05/0.99  
% 4.05/0.99  ------ QBF
% 4.05/0.99  
% 4.05/0.99  qbf_q_res:                              0
% 4.05/0.99  qbf_num_tautologies:                    0
% 4.05/0.99  qbf_prep_cycles:                        0
% 4.05/0.99  
% 4.05/0.99  ------ BMC1
% 4.05/0.99  
% 4.05/0.99  bmc1_current_bound:                     -1
% 4.05/0.99  bmc1_last_solved_bound:                 -1
% 4.05/0.99  bmc1_unsat_core_size:                   -1
% 4.05/0.99  bmc1_unsat_core_parents_size:           -1
% 4.05/0.99  bmc1_merge_next_fun:                    0
% 4.05/0.99  bmc1_unsat_core_clauses_time:           0.
% 4.05/0.99  
% 4.05/0.99  ------ Instantiation
% 4.05/0.99  
% 4.05/0.99  inst_num_of_clauses:                    1081
% 4.05/0.99  inst_num_in_passive:                    323
% 4.05/0.99  inst_num_in_active:                     483
% 4.05/0.99  inst_num_in_unprocessed:                275
% 4.05/0.99  inst_num_of_loops:                      520
% 4.05/0.99  inst_num_of_learning_restarts:          0
% 4.05/0.99  inst_num_moves_active_passive:          37
% 4.05/0.99  inst_lit_activity:                      0
% 4.05/0.99  inst_lit_activity_moves:                0
% 4.05/0.99  inst_num_tautologies:                   0
% 4.05/0.99  inst_num_prop_implied:                  0
% 4.05/0.99  inst_num_existing_simplified:           0
% 4.05/0.99  inst_num_eq_res_simplified:             0
% 4.05/0.99  inst_num_child_elim:                    0
% 4.05/0.99  inst_num_of_dismatching_blockings:      291
% 4.05/0.99  inst_num_of_non_proper_insts:           1005
% 4.05/0.99  inst_num_of_duplicates:                 0
% 4.05/0.99  inst_inst_num_from_inst_to_res:         0
% 4.05/0.99  inst_dismatching_checking_time:         0.
% 4.05/0.99  
% 4.05/0.99  ------ Resolution
% 4.05/0.99  
% 4.05/0.99  res_num_of_clauses:                     0
% 4.05/0.99  res_num_in_passive:                     0
% 4.05/0.99  res_num_in_active:                      0
% 4.05/0.99  res_num_of_loops:                       211
% 4.05/0.99  res_forward_subset_subsumed:            119
% 4.05/0.99  res_backward_subset_subsumed:           4
% 4.05/0.99  res_forward_subsumed:                   0
% 4.05/0.99  res_backward_subsumed:                  0
% 4.05/0.99  res_forward_subsumption_resolution:     1
% 4.05/0.99  res_backward_subsumption_resolution:    0
% 4.05/0.99  res_clause_to_clause_subsumption:       348
% 4.05/0.99  res_orphan_elimination:                 0
% 4.05/0.99  res_tautology_del:                      21
% 4.05/0.99  res_num_eq_res_simplified:              0
% 4.05/0.99  res_num_sel_changes:                    0
% 4.05/0.99  res_moves_from_active_to_pass:          0
% 4.05/0.99  
% 4.05/0.99  ------ Superposition
% 4.05/0.99  
% 4.05/0.99  sup_time_total:                         0.
% 4.05/0.99  sup_time_generating:                    0.
% 4.05/0.99  sup_time_sim_full:                      0.
% 4.05/0.99  sup_time_sim_immed:                     0.
% 4.05/0.99  
% 4.05/0.99  sup_num_of_clauses:                     194
% 4.05/0.99  sup_num_in_active:                      97
% 4.05/0.99  sup_num_in_passive:                     97
% 4.05/0.99  sup_num_of_loops:                       103
% 4.05/0.99  sup_fw_superposition:                   125
% 4.05/0.99  sup_bw_superposition:                   82
% 4.05/0.99  sup_immediate_simplified:               70
% 4.05/0.99  sup_given_eliminated:                   2
% 4.05/0.99  comparisons_done:                       0
% 4.05/0.99  comparisons_avoided:                    3
% 4.05/0.99  
% 4.05/0.99  ------ Simplifications
% 4.05/0.99  
% 4.05/0.99  
% 4.05/0.99  sim_fw_subset_subsumed:                 4
% 4.05/0.99  sim_bw_subset_subsumed:                 7
% 4.05/0.99  sim_fw_subsumed:                        3
% 4.05/0.99  sim_bw_subsumed:                        1
% 4.05/0.99  sim_fw_subsumption_res:                 0
% 4.05/0.99  sim_bw_subsumption_res:                 0
% 4.05/0.99  sim_tautology_del:                      4
% 4.05/0.99  sim_eq_tautology_del:                   16
% 4.05/0.99  sim_eq_res_simp:                        1
% 4.05/0.99  sim_fw_demodulated:                     27
% 4.05/0.99  sim_bw_demodulated:                     3
% 4.05/0.99  sim_light_normalised:                   40
% 4.05/0.99  sim_joinable_taut:                      0
% 4.05/0.99  sim_joinable_simp:                      0
% 4.05/0.99  sim_ac_normalised:                      0
% 4.05/0.99  sim_smt_subsumption:                    0
% 4.05/0.99  
%------------------------------------------------------------------------------
