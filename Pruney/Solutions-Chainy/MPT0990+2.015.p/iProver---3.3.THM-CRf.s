%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:59 EST 2020

% Result     : Theorem 11.43s
% Output     : CNFRefutation 11.43s
% Verified   : 
% Statistics : Number of formulae       :  194 ( 974 expanded)
%              Number of clauses        :  105 ( 299 expanded)
%              Number of leaves         :   23 ( 232 expanded)
%              Depth                    :   18
%              Number of atoms          :  588 (6911 expanded)
%              Number of equality atoms :  256 (2411 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   24 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f28,conjecture,(
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

fof(f29,negated_conjecture,(
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
    inference(negated_conjecture,[],[f28])).

fof(f64,plain,(
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
    inference(ennf_transformation,[],[f29])).

fof(f65,plain,(
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
    inference(flattening,[],[f64])).

fof(f70,plain,(
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

fof(f69,plain,
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

fof(f71,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f65,f70,f69])).

fof(f114,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f71])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f111,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f71])).

fof(f109,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f71])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f42,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f41])).

fof(f86,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f117,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f71])).

fof(f17,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f50,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f49])).

fof(f96,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f26,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f107,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f26])).

fof(f127,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f96,f107])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f115,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f71])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f20])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f16,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f48,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f47])).

fof(f94,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f39])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f124,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_partfun1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f85,f107])).

fof(f25,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f61,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f60])).

fof(f106,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f112,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f71])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f57,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f56])).

fof(f68,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f57])).

fof(f101,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f116,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f71])).

fof(f24,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f24])).

fof(f105,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f30])).

fof(f23,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f59,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f58])).

fof(f104,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f43])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f9,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f82,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f122,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f82,f107])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f84,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f123,plain,(
    ! [X0] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f84,f107])).

fof(f120,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_42,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_2176,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_2183,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3543,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2176,c_2183])).

cnf(c_45,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_2173,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_3544,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2173,c_2183])).

cnf(c_47,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_2171,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_15,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_2194,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k5_relat_1(k5_relat_1(X1,X0),X2) = k5_relat_1(X1,k5_relat_1(X0,X2)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2198,plain,
    ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_8566,plain,
    ( k5_relat_1(k2_funct_1(X0),k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(k2_funct_1(X0),X1),X2)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2194,c_2198])).

cnf(c_33008,plain,
    ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2171,c_8566])).

cnf(c_33660,plain,
    ( v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_33008,c_3544])).

cnf(c_33661,plain,
    ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_33660])).

cnf(c_33669,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3544,c_33661])).

cnf(c_39,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_2177,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_23,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_2186,plain,
    ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_6774,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2177,c_2186])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_2182,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3692,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2173,c_2182])).

cnf(c_41,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f115])).

cnf(c_3694,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_3692,c_41])).

cnf(c_6775,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6774,c_3694])).

cnf(c_48,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_7628,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6775,c_48,c_3544])).

cnf(c_33675,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k6_partfun1(sK1),X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_33669,c_7628])).

cnf(c_34845,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
    inference(superposition,[status(thm)],[c_3543,c_33675])).

cnf(c_27,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_5,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_568,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_27,c_5])).

cnf(c_572,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_568,c_27,c_26,c_5])).

cnf(c_573,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(renaming,[status(thm)],[c_572])).

cnf(c_2169,plain,
    ( r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_573])).

cnf(c_3639,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2173,c_2169])).

cnf(c_21,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_2188,plain,
    ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_6292,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2177,c_2188])).

cnf(c_6397,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6292,c_48,c_3544])).

cnf(c_13,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_partfun1(X1)) = X0 ),
    inference(cnf_transformation,[],[f124])).

cnf(c_2196,plain,
    ( k5_relat_1(X0,k6_partfun1(X1)) = X0
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_6399,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0)) = k2_funct_1(sK2)
    | r1_tarski(k1_relat_1(sK2),X0) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6397,c_2196])).

cnf(c_5456,plain,
    ( ~ v1_funct_1(sK2)
    | v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_5457,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5456])).

cnf(c_6429,plain,
    ( r1_tarski(k1_relat_1(sK2),X0) != iProver_top
    | k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0)) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6399,c_48,c_3544,c_5457])).

cnf(c_6430,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0)) = k2_funct_1(sK2)
    | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6429])).

cnf(c_6435,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k2_funct_1(sK2) ),
    inference(superposition,[status(thm)],[c_3639,c_6430])).

cnf(c_34,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_2178,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_8629,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2176,c_2178])).

cnf(c_44,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_51,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_8727,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8629,c_51])).

cnf(c_8728,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_8727])).

cnf(c_8737,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2173,c_8728])).

cnf(c_30,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_40,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_647,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_40])).

cnf(c_648,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_647])).

cnf(c_33,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_63,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_650,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_648,c_63])).

cnf(c_2166,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_650])).

cnf(c_31,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_2262,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_2856,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2166,c_47,c_45,c_44,c_42,c_63,c_648,c_2262])).

cnf(c_8739,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8737,c_2856])).

cnf(c_8905,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8739,c_48])).

cnf(c_3638,plain,
    ( r1_tarski(k1_relat_1(sK3),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2176,c_2169])).

cnf(c_18,plain,
    ( ~ r1_tarski(X0,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_2191,plain,
    ( k9_relat_1(X0,k10_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_7223,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
    | r1_tarski(X0,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3694,c_2191])).

cnf(c_7867,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7223,c_48,c_3544])).

cnf(c_7874,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(sK3))) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_3638,c_7867])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X1,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2199,plain,
    ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4979,plain,
    ( k10_relat_1(sK2,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(sK2,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3544,c_2199])).

cnf(c_6098,plain,
    ( k10_relat_1(sK2,k1_relat_1(sK3)) = k1_relat_1(k5_relat_1(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_3543,c_4979])).

cnf(c_7875,plain,
    ( k9_relat_1(sK2,k1_relat_1(k5_relat_1(sK2,sK3))) = k1_relat_1(sK3) ),
    inference(light_normalisation,[status(thm)],[c_7874,c_6098])).

cnf(c_11918,plain,
    ( k9_relat_1(sK2,k1_relat_1(k6_partfun1(sK0))) = k1_relat_1(sK3) ),
    inference(light_normalisation,[status(thm)],[c_7875,c_7875,c_8905])).

cnf(c_11,plain,
    ( k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f122])).

cnf(c_8,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_551,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_27,c_8])).

cnf(c_555,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_551,c_27,c_26,c_8])).

cnf(c_2170,plain,
    ( k7_relat_1(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_555])).

cnf(c_4360,plain,
    ( k7_relat_1(sK2,sK0) = sK2 ),
    inference(superposition,[status(thm)],[c_2173,c_2170])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2200,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3707,plain,
    ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_3544,c_2200])).

cnf(c_5061,plain,
    ( k9_relat_1(sK2,sK0) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_4360,c_3707])).

cnf(c_5062,plain,
    ( k9_relat_1(sK2,sK0) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_5061,c_3694])).

cnf(c_11919,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(demodulation,[status(thm)],[c_11918,c_11,c_5062])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 ),
    inference(cnf_transformation,[],[f123])).

cnf(c_2197,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3634,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1(sK3)),sK3) = sK3 ),
    inference(superposition,[status(thm)],[c_3543,c_2197])).

cnf(c_11924,plain,
    ( k5_relat_1(k6_partfun1(sK1),sK3) = sK3 ),
    inference(demodulation,[status(thm)],[c_11919,c_3634])).

cnf(c_34854,plain,
    ( k2_funct_1(sK2) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_34845,c_6435,c_8905,c_11924])).

cnf(c_36,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f120])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_34854,c_36])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:48:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 11.43/1.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.43/1.99  
% 11.43/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.43/1.99  
% 11.43/1.99  ------  iProver source info
% 11.43/1.99  
% 11.43/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.43/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.43/1.99  git: non_committed_changes: false
% 11.43/1.99  git: last_make_outside_of_git: false
% 11.43/1.99  
% 11.43/1.99  ------ 
% 11.43/1.99  
% 11.43/1.99  ------ Input Options
% 11.43/1.99  
% 11.43/1.99  --out_options                           all
% 11.43/1.99  --tptp_safe_out                         true
% 11.43/1.99  --problem_path                          ""
% 11.43/1.99  --include_path                          ""
% 11.43/1.99  --clausifier                            res/vclausify_rel
% 11.43/1.99  --clausifier_options                    ""
% 11.43/1.99  --stdin                                 false
% 11.43/1.99  --stats_out                             all
% 11.43/1.99  
% 11.43/1.99  ------ General Options
% 11.43/1.99  
% 11.43/1.99  --fof                                   false
% 11.43/1.99  --time_out_real                         305.
% 11.43/1.99  --time_out_virtual                      -1.
% 11.43/1.99  --symbol_type_check                     false
% 11.43/1.99  --clausify_out                          false
% 11.43/1.99  --sig_cnt_out                           false
% 11.43/1.99  --trig_cnt_out                          false
% 11.43/1.99  --trig_cnt_out_tolerance                1.
% 11.43/1.99  --trig_cnt_out_sk_spl                   false
% 11.43/1.99  --abstr_cl_out                          false
% 11.43/1.99  
% 11.43/1.99  ------ Global Options
% 11.43/1.99  
% 11.43/1.99  --schedule                              default
% 11.43/1.99  --add_important_lit                     false
% 11.43/1.99  --prop_solver_per_cl                    1000
% 11.43/1.99  --min_unsat_core                        false
% 11.43/1.99  --soft_assumptions                      false
% 11.43/1.99  --soft_lemma_size                       3
% 11.43/1.99  --prop_impl_unit_size                   0
% 11.43/1.99  --prop_impl_unit                        []
% 11.43/1.99  --share_sel_clauses                     true
% 11.43/1.99  --reset_solvers                         false
% 11.43/1.99  --bc_imp_inh                            [conj_cone]
% 11.43/1.99  --conj_cone_tolerance                   3.
% 11.43/1.99  --extra_neg_conj                        none
% 11.43/1.99  --large_theory_mode                     true
% 11.43/1.99  --prolific_symb_bound                   200
% 11.43/1.99  --lt_threshold                          2000
% 11.43/1.99  --clause_weak_htbl                      true
% 11.43/1.99  --gc_record_bc_elim                     false
% 11.43/1.99  
% 11.43/1.99  ------ Preprocessing Options
% 11.43/1.99  
% 11.43/1.99  --preprocessing_flag                    true
% 11.43/1.99  --time_out_prep_mult                    0.1
% 11.43/1.99  --splitting_mode                        input
% 11.43/1.99  --splitting_grd                         true
% 11.43/1.99  --splitting_cvd                         false
% 11.43/1.99  --splitting_cvd_svl                     false
% 11.43/1.99  --splitting_nvd                         32
% 11.43/1.99  --sub_typing                            true
% 11.43/1.99  --prep_gs_sim                           true
% 11.43/1.99  --prep_unflatten                        true
% 11.43/1.99  --prep_res_sim                          true
% 11.43/1.99  --prep_upred                            true
% 11.43/1.99  --prep_sem_filter                       exhaustive
% 11.43/1.99  --prep_sem_filter_out                   false
% 11.43/1.99  --pred_elim                             true
% 11.43/1.99  --res_sim_input                         true
% 11.43/1.99  --eq_ax_congr_red                       true
% 11.43/1.99  --pure_diseq_elim                       true
% 11.43/1.99  --brand_transform                       false
% 11.43/1.99  --non_eq_to_eq                          false
% 11.43/1.99  --prep_def_merge                        true
% 11.43/1.99  --prep_def_merge_prop_impl              false
% 11.43/1.99  --prep_def_merge_mbd                    true
% 11.43/1.99  --prep_def_merge_tr_red                 false
% 11.43/1.99  --prep_def_merge_tr_cl                  false
% 11.43/1.99  --smt_preprocessing                     true
% 11.43/1.99  --smt_ac_axioms                         fast
% 11.43/1.99  --preprocessed_out                      false
% 11.43/1.99  --preprocessed_stats                    false
% 11.43/1.99  
% 11.43/1.99  ------ Abstraction refinement Options
% 11.43/1.99  
% 11.43/1.99  --abstr_ref                             []
% 11.43/1.99  --abstr_ref_prep                        false
% 11.43/1.99  --abstr_ref_until_sat                   false
% 11.43/1.99  --abstr_ref_sig_restrict                funpre
% 11.43/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.43/1.99  --abstr_ref_under                       []
% 11.43/1.99  
% 11.43/1.99  ------ SAT Options
% 11.43/1.99  
% 11.43/1.99  --sat_mode                              false
% 11.43/1.99  --sat_fm_restart_options                ""
% 11.43/1.99  --sat_gr_def                            false
% 11.43/1.99  --sat_epr_types                         true
% 11.43/1.99  --sat_non_cyclic_types                  false
% 11.43/1.99  --sat_finite_models                     false
% 11.43/1.99  --sat_fm_lemmas                         false
% 11.43/1.99  --sat_fm_prep                           false
% 11.43/1.99  --sat_fm_uc_incr                        true
% 11.43/1.99  --sat_out_model                         small
% 11.43/1.99  --sat_out_clauses                       false
% 11.43/1.99  
% 11.43/1.99  ------ QBF Options
% 11.43/1.99  
% 11.43/1.99  --qbf_mode                              false
% 11.43/1.99  --qbf_elim_univ                         false
% 11.43/1.99  --qbf_dom_inst                          none
% 11.43/1.99  --qbf_dom_pre_inst                      false
% 11.43/1.99  --qbf_sk_in                             false
% 11.43/1.99  --qbf_pred_elim                         true
% 11.43/1.99  --qbf_split                             512
% 11.43/1.99  
% 11.43/1.99  ------ BMC1 Options
% 11.43/1.99  
% 11.43/1.99  --bmc1_incremental                      false
% 11.43/1.99  --bmc1_axioms                           reachable_all
% 11.43/1.99  --bmc1_min_bound                        0
% 11.43/1.99  --bmc1_max_bound                        -1
% 11.43/1.99  --bmc1_max_bound_default                -1
% 11.43/1.99  --bmc1_symbol_reachability              true
% 11.43/1.99  --bmc1_property_lemmas                  false
% 11.43/1.99  --bmc1_k_induction                      false
% 11.43/1.99  --bmc1_non_equiv_states                 false
% 11.43/1.99  --bmc1_deadlock                         false
% 11.43/1.99  --bmc1_ucm                              false
% 11.43/1.99  --bmc1_add_unsat_core                   none
% 11.43/1.99  --bmc1_unsat_core_children              false
% 11.43/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.43/1.99  --bmc1_out_stat                         full
% 11.43/1.99  --bmc1_ground_init                      false
% 11.43/1.99  --bmc1_pre_inst_next_state              false
% 11.43/1.99  --bmc1_pre_inst_state                   false
% 11.43/1.99  --bmc1_pre_inst_reach_state             false
% 11.43/1.99  --bmc1_out_unsat_core                   false
% 11.43/1.99  --bmc1_aig_witness_out                  false
% 11.43/1.99  --bmc1_verbose                          false
% 11.43/1.99  --bmc1_dump_clauses_tptp                false
% 11.43/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.43/1.99  --bmc1_dump_file                        -
% 11.43/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.43/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.43/1.99  --bmc1_ucm_extend_mode                  1
% 11.43/1.99  --bmc1_ucm_init_mode                    2
% 11.43/1.99  --bmc1_ucm_cone_mode                    none
% 11.43/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.43/1.99  --bmc1_ucm_relax_model                  4
% 11.43/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.43/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.43/1.99  --bmc1_ucm_layered_model                none
% 11.43/1.99  --bmc1_ucm_max_lemma_size               10
% 11.43/1.99  
% 11.43/1.99  ------ AIG Options
% 11.43/1.99  
% 11.43/1.99  --aig_mode                              false
% 11.43/1.99  
% 11.43/1.99  ------ Instantiation Options
% 11.43/1.99  
% 11.43/1.99  --instantiation_flag                    true
% 11.43/1.99  --inst_sos_flag                         true
% 11.43/1.99  --inst_sos_phase                        true
% 11.43/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.43/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.43/1.99  --inst_lit_sel_side                     num_symb
% 11.43/1.99  --inst_solver_per_active                1400
% 11.43/1.99  --inst_solver_calls_frac                1.
% 11.43/1.99  --inst_passive_queue_type               priority_queues
% 11.43/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.43/1.99  --inst_passive_queues_freq              [25;2]
% 11.43/1.99  --inst_dismatching                      true
% 11.43/1.99  --inst_eager_unprocessed_to_passive     true
% 11.43/1.99  --inst_prop_sim_given                   true
% 11.43/1.99  --inst_prop_sim_new                     false
% 11.43/1.99  --inst_subs_new                         false
% 11.43/1.99  --inst_eq_res_simp                      false
% 11.43/1.99  --inst_subs_given                       false
% 11.43/1.99  --inst_orphan_elimination               true
% 11.43/1.99  --inst_learning_loop_flag               true
% 11.43/1.99  --inst_learning_start                   3000
% 11.43/1.99  --inst_learning_factor                  2
% 11.43/1.99  --inst_start_prop_sim_after_learn       3
% 11.43/1.99  --inst_sel_renew                        solver
% 11.43/1.99  --inst_lit_activity_flag                true
% 11.43/1.99  --inst_restr_to_given                   false
% 11.43/1.99  --inst_activity_threshold               500
% 11.43/1.99  --inst_out_proof                        true
% 11.43/1.99  
% 11.43/1.99  ------ Resolution Options
% 11.43/1.99  
% 11.43/1.99  --resolution_flag                       true
% 11.43/1.99  --res_lit_sel                           adaptive
% 11.43/1.99  --res_lit_sel_side                      none
% 11.43/1.99  --res_ordering                          kbo
% 11.43/1.99  --res_to_prop_solver                    active
% 11.43/1.99  --res_prop_simpl_new                    false
% 11.43/1.99  --res_prop_simpl_given                  true
% 11.43/1.99  --res_passive_queue_type                priority_queues
% 11.43/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.43/1.99  --res_passive_queues_freq               [15;5]
% 11.43/1.99  --res_forward_subs                      full
% 11.43/1.99  --res_backward_subs                     full
% 11.43/1.99  --res_forward_subs_resolution           true
% 11.43/1.99  --res_backward_subs_resolution          true
% 11.43/1.99  --res_orphan_elimination                true
% 11.43/1.99  --res_time_limit                        2.
% 11.43/1.99  --res_out_proof                         true
% 11.43/1.99  
% 11.43/1.99  ------ Superposition Options
% 11.43/1.99  
% 11.43/1.99  --superposition_flag                    true
% 11.43/1.99  --sup_passive_queue_type                priority_queues
% 11.43/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.43/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.43/1.99  --demod_completeness_check              fast
% 11.43/1.99  --demod_use_ground                      true
% 11.43/1.99  --sup_to_prop_solver                    passive
% 11.43/1.99  --sup_prop_simpl_new                    true
% 11.43/1.99  --sup_prop_simpl_given                  true
% 11.43/1.99  --sup_fun_splitting                     true
% 11.43/1.99  --sup_smt_interval                      50000
% 11.43/1.99  
% 11.43/1.99  ------ Superposition Simplification Setup
% 11.43/1.99  
% 11.43/1.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.43/1.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.43/1.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.43/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.43/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.43/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.43/1.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.43/1.99  --sup_immed_triv                        [TrivRules]
% 11.43/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.43/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.43/1.99  --sup_immed_bw_main                     []
% 11.43/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.43/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.43/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.43/1.99  --sup_input_bw                          []
% 11.43/1.99  
% 11.43/1.99  ------ Combination Options
% 11.43/1.99  
% 11.43/1.99  --comb_res_mult                         3
% 11.43/1.99  --comb_sup_mult                         2
% 11.43/1.99  --comb_inst_mult                        10
% 11.43/1.99  
% 11.43/1.99  ------ Debug Options
% 11.43/1.99  
% 11.43/1.99  --dbg_backtrace                         false
% 11.43/1.99  --dbg_dump_prop_clauses                 false
% 11.43/1.99  --dbg_dump_prop_clauses_file            -
% 11.43/1.99  --dbg_out_stat                          false
% 11.43/1.99  ------ Parsing...
% 11.43/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.43/1.99  
% 11.43/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 11.43/1.99  
% 11.43/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.43/1.99  
% 11.43/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.43/1.99  ------ Proving...
% 11.43/1.99  ------ Problem Properties 
% 11.43/1.99  
% 11.43/1.99  
% 11.43/1.99  clauses                                 46
% 11.43/1.99  conjectures                             11
% 11.43/1.99  EPR                                     7
% 11.43/1.99  Horn                                    46
% 11.43/1.99  unary                                   18
% 11.43/1.99  binary                                  9
% 11.43/1.99  lits                                    124
% 11.43/1.99  lits eq                                 29
% 11.43/1.99  fd_pure                                 0
% 11.43/1.99  fd_pseudo                               0
% 11.43/1.99  fd_cond                                 0
% 11.43/1.99  fd_pseudo_cond                          0
% 11.43/1.99  AC symbols                              0
% 11.43/1.99  
% 11.43/1.99  ------ Schedule dynamic 5 is on 
% 11.43/1.99  
% 11.43/1.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.43/1.99  
% 11.43/1.99  
% 11.43/1.99  ------ 
% 11.43/1.99  Current options:
% 11.43/1.99  ------ 
% 11.43/1.99  
% 11.43/1.99  ------ Input Options
% 11.43/1.99  
% 11.43/1.99  --out_options                           all
% 11.43/1.99  --tptp_safe_out                         true
% 11.43/1.99  --problem_path                          ""
% 11.43/1.99  --include_path                          ""
% 11.43/1.99  --clausifier                            res/vclausify_rel
% 11.43/1.99  --clausifier_options                    ""
% 11.43/1.99  --stdin                                 false
% 11.43/1.99  --stats_out                             all
% 11.43/1.99  
% 11.43/1.99  ------ General Options
% 11.43/1.99  
% 11.43/1.99  --fof                                   false
% 11.43/1.99  --time_out_real                         305.
% 11.43/1.99  --time_out_virtual                      -1.
% 11.43/1.99  --symbol_type_check                     false
% 11.43/1.99  --clausify_out                          false
% 11.43/1.99  --sig_cnt_out                           false
% 11.43/1.99  --trig_cnt_out                          false
% 11.43/1.99  --trig_cnt_out_tolerance                1.
% 11.43/1.99  --trig_cnt_out_sk_spl                   false
% 11.43/1.99  --abstr_cl_out                          false
% 11.43/1.99  
% 11.43/1.99  ------ Global Options
% 11.43/1.99  
% 11.43/1.99  --schedule                              default
% 11.43/1.99  --add_important_lit                     false
% 11.43/1.99  --prop_solver_per_cl                    1000
% 11.43/1.99  --min_unsat_core                        false
% 11.43/1.99  --soft_assumptions                      false
% 11.43/1.99  --soft_lemma_size                       3
% 11.43/1.99  --prop_impl_unit_size                   0
% 11.43/1.99  --prop_impl_unit                        []
% 11.43/1.99  --share_sel_clauses                     true
% 11.43/1.99  --reset_solvers                         false
% 11.43/1.99  --bc_imp_inh                            [conj_cone]
% 11.43/1.99  --conj_cone_tolerance                   3.
% 11.43/1.99  --extra_neg_conj                        none
% 11.43/1.99  --large_theory_mode                     true
% 11.43/1.99  --prolific_symb_bound                   200
% 11.43/1.99  --lt_threshold                          2000
% 11.43/1.99  --clause_weak_htbl                      true
% 11.43/1.99  --gc_record_bc_elim                     false
% 11.43/1.99  
% 11.43/1.99  ------ Preprocessing Options
% 11.43/1.99  
% 11.43/1.99  --preprocessing_flag                    true
% 11.43/1.99  --time_out_prep_mult                    0.1
% 11.43/1.99  --splitting_mode                        input
% 11.43/1.99  --splitting_grd                         true
% 11.43/1.99  --splitting_cvd                         false
% 11.43/1.99  --splitting_cvd_svl                     false
% 11.43/1.99  --splitting_nvd                         32
% 11.43/1.99  --sub_typing                            true
% 11.43/1.99  --prep_gs_sim                           true
% 11.43/1.99  --prep_unflatten                        true
% 11.43/1.99  --prep_res_sim                          true
% 11.43/1.99  --prep_upred                            true
% 11.43/1.99  --prep_sem_filter                       exhaustive
% 11.43/1.99  --prep_sem_filter_out                   false
% 11.43/1.99  --pred_elim                             true
% 11.43/1.99  --res_sim_input                         true
% 11.43/1.99  --eq_ax_congr_red                       true
% 11.43/1.99  --pure_diseq_elim                       true
% 11.43/1.99  --brand_transform                       false
% 11.43/1.99  --non_eq_to_eq                          false
% 11.43/1.99  --prep_def_merge                        true
% 11.43/1.99  --prep_def_merge_prop_impl              false
% 11.43/1.99  --prep_def_merge_mbd                    true
% 11.43/1.99  --prep_def_merge_tr_red                 false
% 11.43/1.99  --prep_def_merge_tr_cl                  false
% 11.43/1.99  --smt_preprocessing                     true
% 11.43/1.99  --smt_ac_axioms                         fast
% 11.43/1.99  --preprocessed_out                      false
% 11.43/1.99  --preprocessed_stats                    false
% 11.43/1.99  
% 11.43/1.99  ------ Abstraction refinement Options
% 11.43/1.99  
% 11.43/1.99  --abstr_ref                             []
% 11.43/1.99  --abstr_ref_prep                        false
% 11.43/1.99  --abstr_ref_until_sat                   false
% 11.43/1.99  --abstr_ref_sig_restrict                funpre
% 11.43/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.43/1.99  --abstr_ref_under                       []
% 11.43/1.99  
% 11.43/1.99  ------ SAT Options
% 11.43/1.99  
% 11.43/1.99  --sat_mode                              false
% 11.43/1.99  --sat_fm_restart_options                ""
% 11.43/1.99  --sat_gr_def                            false
% 11.43/1.99  --sat_epr_types                         true
% 11.43/1.99  --sat_non_cyclic_types                  false
% 11.43/1.99  --sat_finite_models                     false
% 11.43/1.99  --sat_fm_lemmas                         false
% 11.43/1.99  --sat_fm_prep                           false
% 11.43/1.99  --sat_fm_uc_incr                        true
% 11.43/1.99  --sat_out_model                         small
% 11.43/1.99  --sat_out_clauses                       false
% 11.43/1.99  
% 11.43/1.99  ------ QBF Options
% 11.43/1.99  
% 11.43/1.99  --qbf_mode                              false
% 11.43/1.99  --qbf_elim_univ                         false
% 11.43/1.99  --qbf_dom_inst                          none
% 11.43/1.99  --qbf_dom_pre_inst                      false
% 11.43/1.99  --qbf_sk_in                             false
% 11.43/1.99  --qbf_pred_elim                         true
% 11.43/1.99  --qbf_split                             512
% 11.43/1.99  
% 11.43/1.99  ------ BMC1 Options
% 11.43/1.99  
% 11.43/1.99  --bmc1_incremental                      false
% 11.43/1.99  --bmc1_axioms                           reachable_all
% 11.43/1.99  --bmc1_min_bound                        0
% 11.43/1.99  --bmc1_max_bound                        -1
% 11.43/1.99  --bmc1_max_bound_default                -1
% 11.43/1.99  --bmc1_symbol_reachability              true
% 11.43/1.99  --bmc1_property_lemmas                  false
% 11.43/1.99  --bmc1_k_induction                      false
% 11.43/1.99  --bmc1_non_equiv_states                 false
% 11.43/1.99  --bmc1_deadlock                         false
% 11.43/1.99  --bmc1_ucm                              false
% 11.43/1.99  --bmc1_add_unsat_core                   none
% 11.43/1.99  --bmc1_unsat_core_children              false
% 11.43/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.43/1.99  --bmc1_out_stat                         full
% 11.43/1.99  --bmc1_ground_init                      false
% 11.43/1.99  --bmc1_pre_inst_next_state              false
% 11.43/1.99  --bmc1_pre_inst_state                   false
% 11.43/1.99  --bmc1_pre_inst_reach_state             false
% 11.43/1.99  --bmc1_out_unsat_core                   false
% 11.43/1.99  --bmc1_aig_witness_out                  false
% 11.43/1.99  --bmc1_verbose                          false
% 11.43/1.99  --bmc1_dump_clauses_tptp                false
% 11.43/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.43/1.99  --bmc1_dump_file                        -
% 11.43/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.43/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.43/1.99  --bmc1_ucm_extend_mode                  1
% 11.43/1.99  --bmc1_ucm_init_mode                    2
% 11.43/1.99  --bmc1_ucm_cone_mode                    none
% 11.43/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.43/1.99  --bmc1_ucm_relax_model                  4
% 11.43/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.43/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.43/1.99  --bmc1_ucm_layered_model                none
% 11.43/1.99  --bmc1_ucm_max_lemma_size               10
% 11.43/1.99  
% 11.43/1.99  ------ AIG Options
% 11.43/1.99  
% 11.43/1.99  --aig_mode                              false
% 11.43/1.99  
% 11.43/1.99  ------ Instantiation Options
% 11.43/1.99  
% 11.43/1.99  --instantiation_flag                    true
% 11.43/1.99  --inst_sos_flag                         true
% 11.43/1.99  --inst_sos_phase                        true
% 11.43/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.43/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.43/1.99  --inst_lit_sel_side                     none
% 11.43/1.99  --inst_solver_per_active                1400
% 11.43/1.99  --inst_solver_calls_frac                1.
% 11.43/1.99  --inst_passive_queue_type               priority_queues
% 11.43/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.43/1.99  --inst_passive_queues_freq              [25;2]
% 11.43/1.99  --inst_dismatching                      true
% 11.43/1.99  --inst_eager_unprocessed_to_passive     true
% 11.43/1.99  --inst_prop_sim_given                   true
% 11.43/1.99  --inst_prop_sim_new                     false
% 11.43/1.99  --inst_subs_new                         false
% 11.43/1.99  --inst_eq_res_simp                      false
% 11.43/1.99  --inst_subs_given                       false
% 11.43/1.99  --inst_orphan_elimination               true
% 11.43/1.99  --inst_learning_loop_flag               true
% 11.43/1.99  --inst_learning_start                   3000
% 11.43/1.99  --inst_learning_factor                  2
% 11.43/1.99  --inst_start_prop_sim_after_learn       3
% 11.43/1.99  --inst_sel_renew                        solver
% 11.43/1.99  --inst_lit_activity_flag                true
% 11.43/1.99  --inst_restr_to_given                   false
% 11.43/1.99  --inst_activity_threshold               500
% 11.43/1.99  --inst_out_proof                        true
% 11.43/1.99  
% 11.43/1.99  ------ Resolution Options
% 11.43/1.99  
% 11.43/1.99  --resolution_flag                       false
% 11.43/1.99  --res_lit_sel                           adaptive
% 11.43/1.99  --res_lit_sel_side                      none
% 11.43/1.99  --res_ordering                          kbo
% 11.43/1.99  --res_to_prop_solver                    active
% 11.43/1.99  --res_prop_simpl_new                    false
% 11.43/1.99  --res_prop_simpl_given                  true
% 11.43/1.99  --res_passive_queue_type                priority_queues
% 11.43/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.43/1.99  --res_passive_queues_freq               [15;5]
% 11.43/1.99  --res_forward_subs                      full
% 11.43/1.99  --res_backward_subs                     full
% 11.43/1.99  --res_forward_subs_resolution           true
% 11.43/1.99  --res_backward_subs_resolution          true
% 11.43/1.99  --res_orphan_elimination                true
% 11.43/1.99  --res_time_limit                        2.
% 11.43/1.99  --res_out_proof                         true
% 11.43/1.99  
% 11.43/1.99  ------ Superposition Options
% 11.43/1.99  
% 11.43/1.99  --superposition_flag                    true
% 11.43/1.99  --sup_passive_queue_type                priority_queues
% 11.43/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.43/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.43/1.99  --demod_completeness_check              fast
% 11.43/1.99  --demod_use_ground                      true
% 11.43/1.99  --sup_to_prop_solver                    passive
% 11.43/1.99  --sup_prop_simpl_new                    true
% 11.43/1.99  --sup_prop_simpl_given                  true
% 11.43/1.99  --sup_fun_splitting                     true
% 11.43/1.99  --sup_smt_interval                      50000
% 11.43/1.99  
% 11.43/1.99  ------ Superposition Simplification Setup
% 11.43/1.99  
% 11.43/1.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.43/1.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.43/1.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.43/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.43/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.43/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.43/1.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.43/1.99  --sup_immed_triv                        [TrivRules]
% 11.43/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.43/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.43/1.99  --sup_immed_bw_main                     []
% 11.43/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.43/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.43/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.43/1.99  --sup_input_bw                          []
% 11.43/1.99  
% 11.43/1.99  ------ Combination Options
% 11.43/1.99  
% 11.43/1.99  --comb_res_mult                         3
% 11.43/1.99  --comb_sup_mult                         2
% 11.43/1.99  --comb_inst_mult                        10
% 11.43/1.99  
% 11.43/1.99  ------ Debug Options
% 11.43/1.99  
% 11.43/1.99  --dbg_backtrace                         false
% 11.43/1.99  --dbg_dump_prop_clauses                 false
% 11.43/1.99  --dbg_dump_prop_clauses_file            -
% 11.43/1.99  --dbg_out_stat                          false
% 11.43/1.99  
% 11.43/1.99  
% 11.43/1.99  
% 11.43/1.99  
% 11.43/1.99  ------ Proving...
% 11.43/1.99  
% 11.43/1.99  
% 11.43/1.99  % SZS status Theorem for theBenchmark.p
% 11.43/1.99  
% 11.43/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 11.43/1.99  
% 11.43/1.99  fof(f28,conjecture,(
% 11.43/1.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 11.43/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.43/1.99  
% 11.43/1.99  fof(f29,negated_conjecture,(
% 11.43/1.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 11.43/1.99    inference(negated_conjecture,[],[f28])).
% 11.43/1.99  
% 11.43/1.99  fof(f64,plain,(
% 11.43/1.99    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 11.43/1.99    inference(ennf_transformation,[],[f29])).
% 11.43/1.99  
% 11.43/1.99  fof(f65,plain,(
% 11.43/1.99    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 11.43/1.99    inference(flattening,[],[f64])).
% 11.43/1.99  
% 11.43/1.99  fof(f70,plain,(
% 11.43/1.99    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 11.43/1.99    introduced(choice_axiom,[])).
% 11.43/1.99  
% 11.43/1.99  fof(f69,plain,(
% 11.43/1.99    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 11.43/1.99    introduced(choice_axiom,[])).
% 11.43/1.99  
% 11.43/1.99  fof(f71,plain,(
% 11.43/1.99    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 11.43/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f65,f70,f69])).
% 11.43/1.99  
% 11.43/1.99  fof(f114,plain,(
% 11.43/1.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 11.43/1.99    inference(cnf_transformation,[],[f71])).
% 11.43/1.99  
% 11.43/1.99  fof(f19,axiom,(
% 11.43/1.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 11.43/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.43/1.99  
% 11.43/1.99  fof(f53,plain,(
% 11.43/1.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.43/1.99    inference(ennf_transformation,[],[f19])).
% 11.43/1.99  
% 11.43/1.99  fof(f98,plain,(
% 11.43/1.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.43/1.99    inference(cnf_transformation,[],[f53])).
% 11.43/1.99  
% 11.43/1.99  fof(f111,plain,(
% 11.43/1.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 11.43/1.99    inference(cnf_transformation,[],[f71])).
% 11.43/1.99  
% 11.43/1.99  fof(f109,plain,(
% 11.43/1.99    v1_funct_1(sK2)),
% 11.43/1.99    inference(cnf_transformation,[],[f71])).
% 11.43/1.99  
% 11.43/1.99  fof(f12,axiom,(
% 11.43/1.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 11.43/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.43/1.99  
% 11.43/1.99  fof(f41,plain,(
% 11.43/1.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.43/1.99    inference(ennf_transformation,[],[f12])).
% 11.43/1.99  
% 11.43/1.99  fof(f42,plain,(
% 11.43/1.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.43/1.99    inference(flattening,[],[f41])).
% 11.43/1.99  
% 11.43/1.99  fof(f86,plain,(
% 11.43/1.99    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.43/1.99    inference(cnf_transformation,[],[f42])).
% 11.43/1.99  
% 11.43/1.99  fof(f8,axiom,(
% 11.43/1.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2))))),
% 11.43/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.43/1.99  
% 11.43/1.99  fof(f37,plain,(
% 11.43/1.99    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 11.43/1.99    inference(ennf_transformation,[],[f8])).
% 11.43/1.99  
% 11.43/1.99  fof(f81,plain,(
% 11.43/1.99    ( ! [X2,X0,X1] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 11.43/1.99    inference(cnf_transformation,[],[f37])).
% 11.43/1.99  
% 11.43/1.99  fof(f117,plain,(
% 11.43/1.99    v2_funct_1(sK2)),
% 11.43/1.99    inference(cnf_transformation,[],[f71])).
% 11.43/1.99  
% 11.43/1.99  fof(f17,axiom,(
% 11.43/1.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 11.43/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.43/1.99  
% 11.43/1.99  fof(f49,plain,(
% 11.43/1.99    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.43/1.99    inference(ennf_transformation,[],[f17])).
% 11.43/1.99  
% 11.43/1.99  fof(f50,plain,(
% 11.43/1.99    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.43/1.99    inference(flattening,[],[f49])).
% 11.43/1.99  
% 11.43/1.99  fof(f96,plain,(
% 11.43/1.99    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.43/1.99    inference(cnf_transformation,[],[f50])).
% 11.43/1.99  
% 11.43/1.99  fof(f26,axiom,(
% 11.43/1.99    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 11.43/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.43/1.99  
% 11.43/1.99  fof(f107,plain,(
% 11.43/1.99    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 11.43/1.99    inference(cnf_transformation,[],[f26])).
% 11.43/1.99  
% 11.43/1.99  fof(f127,plain,(
% 11.43/1.99    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.43/1.99    inference(definition_unfolding,[],[f96,f107])).
% 11.43/1.99  
% 11.43/1.99  fof(f21,axiom,(
% 11.43/1.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 11.43/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.43/1.99  
% 11.43/1.99  fof(f55,plain,(
% 11.43/1.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.43/1.99    inference(ennf_transformation,[],[f21])).
% 11.43/1.99  
% 11.43/1.99  fof(f100,plain,(
% 11.43/1.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.43/1.99    inference(cnf_transformation,[],[f55])).
% 11.43/1.99  
% 11.43/1.99  fof(f115,plain,(
% 11.43/1.99    k2_relset_1(sK0,sK1,sK2) = sK1),
% 11.43/1.99    inference(cnf_transformation,[],[f71])).
% 11.43/1.99  
% 11.43/1.99  fof(f20,axiom,(
% 11.43/1.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 11.43/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.43/1.99  
% 11.43/1.99  fof(f31,plain,(
% 11.43/1.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 11.43/1.99    inference(pure_predicate_removal,[],[f20])).
% 11.43/1.99  
% 11.43/1.99  fof(f54,plain,(
% 11.43/1.99    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.43/1.99    inference(ennf_transformation,[],[f31])).
% 11.43/1.99  
% 11.43/1.99  fof(f99,plain,(
% 11.43/1.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.43/1.99    inference(cnf_transformation,[],[f54])).
% 11.43/1.99  
% 11.43/1.99  fof(f4,axiom,(
% 11.43/1.99    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 11.43/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.43/1.99  
% 11.43/1.99  fof(f32,plain,(
% 11.43/1.99    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 11.43/1.99    inference(ennf_transformation,[],[f4])).
% 11.43/1.99  
% 11.43/1.99  fof(f67,plain,(
% 11.43/1.99    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 11.43/1.99    inference(nnf_transformation,[],[f32])).
% 11.43/1.99  
% 11.43/1.99  fof(f76,plain,(
% 11.43/1.99    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.43/1.99    inference(cnf_transformation,[],[f67])).
% 11.43/1.99  
% 11.43/1.99  fof(f16,axiom,(
% 11.43/1.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 11.43/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.43/1.99  
% 11.43/1.99  fof(f47,plain,(
% 11.43/1.99    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.43/1.99    inference(ennf_transformation,[],[f16])).
% 11.43/1.99  
% 11.43/1.99  fof(f48,plain,(
% 11.43/1.99    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.43/1.99    inference(flattening,[],[f47])).
% 11.43/1.99  
% 11.43/1.99  fof(f94,plain,(
% 11.43/1.99    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.43/1.99    inference(cnf_transformation,[],[f48])).
% 11.43/1.99  
% 11.43/1.99  fof(f11,axiom,(
% 11.43/1.99    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 11.43/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.43/1.99  
% 11.43/1.99  fof(f39,plain,(
% 11.43/1.99    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 11.43/1.99    inference(ennf_transformation,[],[f11])).
% 11.43/1.99  
% 11.43/1.99  fof(f40,plain,(
% 11.43/1.99    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 11.43/1.99    inference(flattening,[],[f39])).
% 11.43/1.99  
% 11.43/1.99  fof(f85,plain,(
% 11.43/1.99    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 11.43/1.99    inference(cnf_transformation,[],[f40])).
% 11.43/1.99  
% 11.43/1.99  fof(f124,plain,(
% 11.43/1.99    ( ! [X0,X1] : (k5_relat_1(X1,k6_partfun1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 11.43/1.99    inference(definition_unfolding,[],[f85,f107])).
% 11.43/1.99  
% 11.43/1.99  fof(f25,axiom,(
% 11.43/1.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 11.43/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.43/1.99  
% 11.43/1.99  fof(f60,plain,(
% 11.43/1.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 11.43/1.99    inference(ennf_transformation,[],[f25])).
% 11.43/1.99  
% 11.43/1.99  fof(f61,plain,(
% 11.43/1.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 11.43/1.99    inference(flattening,[],[f60])).
% 11.43/1.99  
% 11.43/1.99  fof(f106,plain,(
% 11.43/1.99    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 11.43/1.99    inference(cnf_transformation,[],[f61])).
% 11.43/1.99  
% 11.43/1.99  fof(f112,plain,(
% 11.43/1.99    v1_funct_1(sK3)),
% 11.43/1.99    inference(cnf_transformation,[],[f71])).
% 11.43/1.99  
% 11.43/1.99  fof(f22,axiom,(
% 11.43/1.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 11.43/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.43/1.99  
% 11.43/1.99  fof(f56,plain,(
% 11.43/1.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 11.43/1.99    inference(ennf_transformation,[],[f22])).
% 11.43/1.99  
% 11.43/1.99  fof(f57,plain,(
% 11.43/1.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.43/1.99    inference(flattening,[],[f56])).
% 11.43/1.99  
% 11.43/1.99  fof(f68,plain,(
% 11.43/1.99    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.43/1.99    inference(nnf_transformation,[],[f57])).
% 11.43/1.99  
% 11.43/1.99  fof(f101,plain,(
% 11.43/1.99    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.43/1.99    inference(cnf_transformation,[],[f68])).
% 11.43/1.99  
% 11.43/1.99  fof(f116,plain,(
% 11.43/1.99    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 11.43/1.99    inference(cnf_transformation,[],[f71])).
% 11.43/1.99  
% 11.43/1.99  fof(f24,axiom,(
% 11.43/1.99    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 11.43/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.43/1.99  
% 11.43/1.99  fof(f30,plain,(
% 11.43/1.99    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 11.43/1.99    inference(pure_predicate_removal,[],[f24])).
% 11.43/1.99  
% 11.43/1.99  fof(f105,plain,(
% 11.43/1.99    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 11.43/1.99    inference(cnf_transformation,[],[f30])).
% 11.43/1.99  
% 11.43/1.99  fof(f23,axiom,(
% 11.43/1.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 11.43/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.43/1.99  
% 11.43/1.99  fof(f58,plain,(
% 11.43/1.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 11.43/1.99    inference(ennf_transformation,[],[f23])).
% 11.43/1.99  
% 11.43/1.99  fof(f59,plain,(
% 11.43/1.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 11.43/1.99    inference(flattening,[],[f58])).
% 11.43/1.99  
% 11.43/1.99  fof(f104,plain,(
% 11.43/1.99    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 11.43/1.99    inference(cnf_transformation,[],[f59])).
% 11.43/1.99  
% 11.43/1.99  fof(f14,axiom,(
% 11.43/1.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 11.43/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.43/1.99  
% 11.43/1.99  fof(f43,plain,(
% 11.43/1.99    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 11.43/1.99    inference(ennf_transformation,[],[f14])).
% 11.43/1.99  
% 11.43/1.99  fof(f44,plain,(
% 11.43/1.99    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 11.43/1.99    inference(flattening,[],[f43])).
% 11.43/1.99  
% 11.43/1.99  fof(f90,plain,(
% 11.43/1.99    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 11.43/1.99    inference(cnf_transformation,[],[f44])).
% 11.43/1.99  
% 11.43/1.99  fof(f6,axiom,(
% 11.43/1.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 11.43/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.43/1.99  
% 11.43/1.99  fof(f34,plain,(
% 11.43/1.99    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 11.43/1.99    inference(ennf_transformation,[],[f6])).
% 11.43/1.99  
% 11.43/1.99  fof(f79,plain,(
% 11.43/1.99    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 11.43/1.99    inference(cnf_transformation,[],[f34])).
% 11.43/1.99  
% 11.43/1.99  fof(f9,axiom,(
% 11.43/1.99    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 11.43/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.43/1.99  
% 11.43/1.99  fof(f82,plain,(
% 11.43/1.99    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 11.43/1.99    inference(cnf_transformation,[],[f9])).
% 11.43/1.99  
% 11.43/1.99  fof(f122,plain,(
% 11.43/1.99    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 11.43/1.99    inference(definition_unfolding,[],[f82,f107])).
% 11.43/1.99  
% 11.43/1.99  fof(f7,axiom,(
% 11.43/1.99    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 11.43/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.43/1.99  
% 11.43/1.99  fof(f35,plain,(
% 11.43/1.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 11.43/1.99    inference(ennf_transformation,[],[f7])).
% 11.43/1.99  
% 11.43/1.99  fof(f36,plain,(
% 11.43/1.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 11.43/1.99    inference(flattening,[],[f35])).
% 11.43/1.99  
% 11.43/1.99  fof(f80,plain,(
% 11.43/1.99    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.43/1.99    inference(cnf_transformation,[],[f36])).
% 11.43/1.99  
% 11.43/1.99  fof(f5,axiom,(
% 11.43/1.99    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 11.43/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.43/1.99  
% 11.43/1.99  fof(f33,plain,(
% 11.43/1.99    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 11.43/1.99    inference(ennf_transformation,[],[f5])).
% 11.43/1.99  
% 11.43/1.99  fof(f78,plain,(
% 11.43/1.99    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.43/1.99    inference(cnf_transformation,[],[f33])).
% 11.43/1.99  
% 11.43/1.99  fof(f10,axiom,(
% 11.43/1.99    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 11.43/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.43/1.99  
% 11.43/1.99  fof(f38,plain,(
% 11.43/1.99    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 11.43/1.99    inference(ennf_transformation,[],[f10])).
% 11.43/1.99  
% 11.43/1.99  fof(f84,plain,(
% 11.43/1.99    ( ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 11.43/1.99    inference(cnf_transformation,[],[f38])).
% 11.43/1.99  
% 11.43/1.99  fof(f123,plain,(
% 11.43/1.99    ( ! [X0] : (k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 11.43/1.99    inference(definition_unfolding,[],[f84,f107])).
% 11.43/1.99  
% 11.43/1.99  fof(f120,plain,(
% 11.43/1.99    k2_funct_1(sK2) != sK3),
% 11.43/1.99    inference(cnf_transformation,[],[f71])).
% 11.43/1.99  
% 11.43/1.99  cnf(c_42,negated_conjecture,
% 11.43/1.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 11.43/1.99      inference(cnf_transformation,[],[f114]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_2176,plain,
% 11.43/1.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 11.43/1.99      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_26,plain,
% 11.43/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.43/1.99      | v1_relat_1(X0) ),
% 11.43/1.99      inference(cnf_transformation,[],[f98]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_2183,plain,
% 11.43/1.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.43/1.99      | v1_relat_1(X0) = iProver_top ),
% 11.43/1.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_3543,plain,
% 11.43/1.99      ( v1_relat_1(sK3) = iProver_top ),
% 11.43/1.99      inference(superposition,[status(thm)],[c_2176,c_2183]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_45,negated_conjecture,
% 11.43/1.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 11.43/1.99      inference(cnf_transformation,[],[f111]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_2173,plain,
% 11.43/1.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 11.43/1.99      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_3544,plain,
% 11.43/1.99      ( v1_relat_1(sK2) = iProver_top ),
% 11.43/1.99      inference(superposition,[status(thm)],[c_2173,c_2183]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_47,negated_conjecture,
% 11.43/1.99      ( v1_funct_1(sK2) ),
% 11.43/1.99      inference(cnf_transformation,[],[f109]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_2171,plain,
% 11.43/1.99      ( v1_funct_1(sK2) = iProver_top ),
% 11.43/1.99      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_15,plain,
% 11.43/1.99      ( ~ v1_funct_1(X0)
% 11.43/1.99      | ~ v1_relat_1(X0)
% 11.43/1.99      | v1_relat_1(k2_funct_1(X0)) ),
% 11.43/1.99      inference(cnf_transformation,[],[f86]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_2194,plain,
% 11.43/1.99      ( v1_funct_1(X0) != iProver_top
% 11.43/1.99      | v1_relat_1(X0) != iProver_top
% 11.43/1.99      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 11.43/1.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_9,plain,
% 11.43/1.99      ( ~ v1_relat_1(X0)
% 11.43/1.99      | ~ v1_relat_1(X1)
% 11.43/1.99      | ~ v1_relat_1(X2)
% 11.43/1.99      | k5_relat_1(k5_relat_1(X1,X0),X2) = k5_relat_1(X1,k5_relat_1(X0,X2)) ),
% 11.43/1.99      inference(cnf_transformation,[],[f81]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_2198,plain,
% 11.43/1.99      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
% 11.43/1.99      | v1_relat_1(X1) != iProver_top
% 11.43/1.99      | v1_relat_1(X0) != iProver_top
% 11.43/1.99      | v1_relat_1(X2) != iProver_top ),
% 11.43/1.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_8566,plain,
% 11.43/1.99      ( k5_relat_1(k2_funct_1(X0),k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(k2_funct_1(X0),X1),X2)
% 11.43/1.99      | v1_funct_1(X0) != iProver_top
% 11.43/1.99      | v1_relat_1(X0) != iProver_top
% 11.43/1.99      | v1_relat_1(X1) != iProver_top
% 11.43/1.99      | v1_relat_1(X2) != iProver_top ),
% 11.43/1.99      inference(superposition,[status(thm)],[c_2194,c_2198]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_33008,plain,
% 11.43/1.99      ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1))
% 11.43/1.99      | v1_relat_1(X0) != iProver_top
% 11.43/1.99      | v1_relat_1(X1) != iProver_top
% 11.43/1.99      | v1_relat_1(sK2) != iProver_top ),
% 11.43/1.99      inference(superposition,[status(thm)],[c_2171,c_8566]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_33660,plain,
% 11.43/1.99      ( v1_relat_1(X1) != iProver_top
% 11.43/1.99      | v1_relat_1(X0) != iProver_top
% 11.43/1.99      | k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1)) ),
% 11.43/1.99      inference(global_propositional_subsumption,
% 11.43/1.99                [status(thm)],
% 11.43/1.99                [c_33008,c_3544]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_33661,plain,
% 11.43/1.99      ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1))
% 11.43/1.99      | v1_relat_1(X0) != iProver_top
% 11.43/1.99      | v1_relat_1(X1) != iProver_top ),
% 11.43/1.99      inference(renaming,[status(thm)],[c_33660]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_33669,plain,
% 11.43/1.99      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),X0)
% 11.43/1.99      | v1_relat_1(X0) != iProver_top ),
% 11.43/1.99      inference(superposition,[status(thm)],[c_3544,c_33661]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_39,negated_conjecture,
% 11.43/1.99      ( v2_funct_1(sK2) ),
% 11.43/1.99      inference(cnf_transformation,[],[f117]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_2177,plain,
% 11.43/1.99      ( v2_funct_1(sK2) = iProver_top ),
% 11.43/1.99      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_23,plain,
% 11.43/1.99      ( ~ v2_funct_1(X0)
% 11.43/1.99      | ~ v1_funct_1(X0)
% 11.43/1.99      | ~ v1_relat_1(X0)
% 11.43/1.99      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
% 11.43/1.99      inference(cnf_transformation,[],[f127]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_2186,plain,
% 11.43/1.99      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
% 11.43/1.99      | v2_funct_1(X0) != iProver_top
% 11.43/1.99      | v1_funct_1(X0) != iProver_top
% 11.43/1.99      | v1_relat_1(X0) != iProver_top ),
% 11.43/1.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_6774,plain,
% 11.43/1.99      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
% 11.43/1.99      | v1_funct_1(sK2) != iProver_top
% 11.43/1.99      | v1_relat_1(sK2) != iProver_top ),
% 11.43/1.99      inference(superposition,[status(thm)],[c_2177,c_2186]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_28,plain,
% 11.43/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.43/1.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 11.43/1.99      inference(cnf_transformation,[],[f100]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_2182,plain,
% 11.43/1.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 11.43/1.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 11.43/1.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_3692,plain,
% 11.43/1.99      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 11.43/1.99      inference(superposition,[status(thm)],[c_2173,c_2182]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_41,negated_conjecture,
% 11.43/1.99      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 11.43/1.99      inference(cnf_transformation,[],[f115]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_3694,plain,
% 11.43/1.99      ( k2_relat_1(sK2) = sK1 ),
% 11.43/1.99      inference(light_normalisation,[status(thm)],[c_3692,c_41]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_6775,plain,
% 11.43/1.99      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 11.43/1.99      | v1_funct_1(sK2) != iProver_top
% 11.43/1.99      | v1_relat_1(sK2) != iProver_top ),
% 11.43/1.99      inference(light_normalisation,[status(thm)],[c_6774,c_3694]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_48,plain,
% 11.43/1.99      ( v1_funct_1(sK2) = iProver_top ),
% 11.43/1.99      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_7628,plain,
% 11.43/1.99      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
% 11.43/1.99      inference(global_propositional_subsumption,
% 11.43/1.99                [status(thm)],
% 11.43/1.99                [c_6775,c_48,c_3544]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_33675,plain,
% 11.43/1.99      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k6_partfun1(sK1),X0)
% 11.43/1.99      | v1_relat_1(X0) != iProver_top ),
% 11.43/1.99      inference(light_normalisation,[status(thm)],[c_33669,c_7628]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_34845,plain,
% 11.43/1.99      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
% 11.43/1.99      inference(superposition,[status(thm)],[c_3543,c_33675]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_27,plain,
% 11.43/1.99      ( v4_relat_1(X0,X1)
% 11.43/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 11.43/1.99      inference(cnf_transformation,[],[f99]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_5,plain,
% 11.43/1.99      ( ~ v4_relat_1(X0,X1)
% 11.43/1.99      | r1_tarski(k1_relat_1(X0),X1)
% 11.43/1.99      | ~ v1_relat_1(X0) ),
% 11.43/1.99      inference(cnf_transformation,[],[f76]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_568,plain,
% 11.43/1.99      ( r1_tarski(k1_relat_1(X0),X1)
% 11.43/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.43/1.99      | ~ v1_relat_1(X0) ),
% 11.43/1.99      inference(resolution,[status(thm)],[c_27,c_5]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_572,plain,
% 11.43/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.43/1.99      | r1_tarski(k1_relat_1(X0),X1) ),
% 11.43/1.99      inference(global_propositional_subsumption,
% 11.43/1.99                [status(thm)],
% 11.43/1.99                [c_568,c_27,c_26,c_5]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_573,plain,
% 11.43/1.99      ( r1_tarski(k1_relat_1(X0),X1)
% 11.43/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 11.43/1.99      inference(renaming,[status(thm)],[c_572]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_2169,plain,
% 11.43/1.99      ( r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 11.43/1.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 11.43/1.99      inference(predicate_to_equality,[status(thm)],[c_573]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_3639,plain,
% 11.43/1.99      ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
% 11.43/1.99      inference(superposition,[status(thm)],[c_2173,c_2169]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_21,plain,
% 11.43/1.99      ( ~ v2_funct_1(X0)
% 11.43/1.99      | ~ v1_funct_1(X0)
% 11.43/1.99      | ~ v1_relat_1(X0)
% 11.43/1.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 11.43/1.99      inference(cnf_transformation,[],[f94]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_2188,plain,
% 11.43/1.99      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 11.43/1.99      | v2_funct_1(X0) != iProver_top
% 11.43/1.99      | v1_funct_1(X0) != iProver_top
% 11.43/1.99      | v1_relat_1(X0) != iProver_top ),
% 11.43/1.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_6292,plain,
% 11.43/1.99      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 11.43/1.99      | v1_funct_1(sK2) != iProver_top
% 11.43/1.99      | v1_relat_1(sK2) != iProver_top ),
% 11.43/1.99      inference(superposition,[status(thm)],[c_2177,c_2188]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_6397,plain,
% 11.43/1.99      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 11.43/1.99      inference(global_propositional_subsumption,
% 11.43/1.99                [status(thm)],
% 11.43/1.99                [c_6292,c_48,c_3544]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_13,plain,
% 11.43/1.99      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 11.43/1.99      | ~ v1_relat_1(X0)
% 11.43/1.99      | k5_relat_1(X0,k6_partfun1(X1)) = X0 ),
% 11.43/1.99      inference(cnf_transformation,[],[f124]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_2196,plain,
% 11.43/1.99      ( k5_relat_1(X0,k6_partfun1(X1)) = X0
% 11.43/1.99      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 11.43/1.99      | v1_relat_1(X0) != iProver_top ),
% 11.43/1.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_6399,plain,
% 11.43/1.99      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0)) = k2_funct_1(sK2)
% 11.43/1.99      | r1_tarski(k1_relat_1(sK2),X0) != iProver_top
% 11.43/1.99      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 11.43/1.99      inference(superposition,[status(thm)],[c_6397,c_2196]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_5456,plain,
% 11.43/1.99      ( ~ v1_funct_1(sK2)
% 11.43/1.99      | v1_relat_1(k2_funct_1(sK2))
% 11.43/1.99      | ~ v1_relat_1(sK2) ),
% 11.43/1.99      inference(instantiation,[status(thm)],[c_15]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_5457,plain,
% 11.43/1.99      ( v1_funct_1(sK2) != iProver_top
% 11.43/1.99      | v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 11.43/1.99      | v1_relat_1(sK2) != iProver_top ),
% 11.43/1.99      inference(predicate_to_equality,[status(thm)],[c_5456]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_6429,plain,
% 11.43/1.99      ( r1_tarski(k1_relat_1(sK2),X0) != iProver_top
% 11.43/1.99      | k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0)) = k2_funct_1(sK2) ),
% 11.43/1.99      inference(global_propositional_subsumption,
% 11.43/1.99                [status(thm)],
% 11.43/1.99                [c_6399,c_48,c_3544,c_5457]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_6430,plain,
% 11.43/1.99      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0)) = k2_funct_1(sK2)
% 11.43/1.99      | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
% 11.43/1.99      inference(renaming,[status(thm)],[c_6429]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_6435,plain,
% 11.43/1.99      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k2_funct_1(sK2) ),
% 11.43/1.99      inference(superposition,[status(thm)],[c_3639,c_6430]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_34,plain,
% 11.43/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.43/1.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 11.43/1.99      | ~ v1_funct_1(X0)
% 11.43/1.99      | ~ v1_funct_1(X3)
% 11.43/1.99      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 11.43/1.99      inference(cnf_transformation,[],[f106]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_2178,plain,
% 11.43/1.99      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 11.43/1.99      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 11.43/1.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.43/1.99      | v1_funct_1(X4) != iProver_top
% 11.43/1.99      | v1_funct_1(X5) != iProver_top ),
% 11.43/1.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_8629,plain,
% 11.43/1.99      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 11.43/1.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.43/1.99      | v1_funct_1(X2) != iProver_top
% 11.43/1.99      | v1_funct_1(sK3) != iProver_top ),
% 11.43/1.99      inference(superposition,[status(thm)],[c_2176,c_2178]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_44,negated_conjecture,
% 11.43/1.99      ( v1_funct_1(sK3) ),
% 11.43/1.99      inference(cnf_transformation,[],[f112]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_51,plain,
% 11.43/1.99      ( v1_funct_1(sK3) = iProver_top ),
% 11.43/1.99      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_8727,plain,
% 11.43/1.99      ( v1_funct_1(X2) != iProver_top
% 11.43/1.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.43/1.99      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 11.43/1.99      inference(global_propositional_subsumption,
% 11.43/1.99                [status(thm)],
% 11.43/1.99                [c_8629,c_51]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_8728,plain,
% 11.43/1.99      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 11.43/1.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.43/1.99      | v1_funct_1(X2) != iProver_top ),
% 11.43/1.99      inference(renaming,[status(thm)],[c_8727]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_8737,plain,
% 11.43/1.99      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 11.43/1.99      | v1_funct_1(sK2) != iProver_top ),
% 11.43/1.99      inference(superposition,[status(thm)],[c_2173,c_8728]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_30,plain,
% 11.43/1.99      ( ~ r2_relset_1(X0,X1,X2,X3)
% 11.43/1.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.43/1.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.43/1.99      | X3 = X2 ),
% 11.43/1.99      inference(cnf_transformation,[],[f101]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_40,negated_conjecture,
% 11.43/1.99      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 11.43/1.99      inference(cnf_transformation,[],[f116]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_647,plain,
% 11.43/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.43/1.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.43/1.99      | X3 = X0
% 11.43/1.99      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 11.43/1.99      | k6_partfun1(sK0) != X3
% 11.43/1.99      | sK0 != X2
% 11.43/1.99      | sK0 != X1 ),
% 11.43/1.99      inference(resolution_lifted,[status(thm)],[c_30,c_40]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_648,plain,
% 11.43/1.99      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.43/1.99      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.43/1.99      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 11.43/1.99      inference(unflattening,[status(thm)],[c_647]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_33,plain,
% 11.43/1.99      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 11.43/1.99      inference(cnf_transformation,[],[f105]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_63,plain,
% 11.43/1.99      ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 11.43/1.99      inference(instantiation,[status(thm)],[c_33]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_650,plain,
% 11.43/1.99      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.43/1.99      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 11.43/1.99      inference(global_propositional_subsumption,
% 11.43/1.99                [status(thm)],
% 11.43/1.99                [c_648,c_63]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_2166,plain,
% 11.43/1.99      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 11.43/1.99      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 11.43/1.99      inference(predicate_to_equality,[status(thm)],[c_650]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_31,plain,
% 11.43/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.43/1.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 11.43/1.99      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 11.43/1.99      | ~ v1_funct_1(X0)
% 11.43/1.99      | ~ v1_funct_1(X3) ),
% 11.43/1.99      inference(cnf_transformation,[],[f104]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_2262,plain,
% 11.43/1.99      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.43/1.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 11.43/1.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 11.43/1.99      | ~ v1_funct_1(sK3)
% 11.43/1.99      | ~ v1_funct_1(sK2) ),
% 11.43/1.99      inference(instantiation,[status(thm)],[c_31]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_2856,plain,
% 11.43/1.99      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 11.43/1.99      inference(global_propositional_subsumption,
% 11.43/1.99                [status(thm)],
% 11.43/1.99                [c_2166,c_47,c_45,c_44,c_42,c_63,c_648,c_2262]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_8739,plain,
% 11.43/1.99      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 11.43/1.99      | v1_funct_1(sK2) != iProver_top ),
% 11.43/1.99      inference(light_normalisation,[status(thm)],[c_8737,c_2856]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_8905,plain,
% 11.43/1.99      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 11.43/1.99      inference(global_propositional_subsumption,
% 11.43/1.99                [status(thm)],
% 11.43/1.99                [c_8739,c_48]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_3638,plain,
% 11.43/1.99      ( r1_tarski(k1_relat_1(sK3),sK1) = iProver_top ),
% 11.43/1.99      inference(superposition,[status(thm)],[c_2176,c_2169]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_18,plain,
% 11.43/1.99      ( ~ r1_tarski(X0,k2_relat_1(X1))
% 11.43/1.99      | ~ v1_funct_1(X1)
% 11.43/1.99      | ~ v1_relat_1(X1)
% 11.43/1.99      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
% 11.43/1.99      inference(cnf_transformation,[],[f90]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_2191,plain,
% 11.43/1.99      ( k9_relat_1(X0,k10_relat_1(X0,X1)) = X1
% 11.43/1.99      | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
% 11.43/1.99      | v1_funct_1(X0) != iProver_top
% 11.43/1.99      | v1_relat_1(X0) != iProver_top ),
% 11.43/1.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_7223,plain,
% 11.43/1.99      ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
% 11.43/1.99      | r1_tarski(X0,sK1) != iProver_top
% 11.43/1.99      | v1_funct_1(sK2) != iProver_top
% 11.43/1.99      | v1_relat_1(sK2) != iProver_top ),
% 11.43/1.99      inference(superposition,[status(thm)],[c_3694,c_2191]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_7867,plain,
% 11.43/1.99      ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
% 11.43/1.99      | r1_tarski(X0,sK1) != iProver_top ),
% 11.43/1.99      inference(global_propositional_subsumption,
% 11.43/1.99                [status(thm)],
% 11.43/1.99                [c_7223,c_48,c_3544]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_7874,plain,
% 11.43/1.99      ( k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(sK3))) = k1_relat_1(sK3) ),
% 11.43/1.99      inference(superposition,[status(thm)],[c_3638,c_7867]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_7,plain,
% 11.43/1.99      ( ~ v1_relat_1(X0)
% 11.43/1.99      | ~ v1_relat_1(X1)
% 11.43/1.99      | k10_relat_1(X1,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(X1,X0)) ),
% 11.43/1.99      inference(cnf_transformation,[],[f79]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_2199,plain,
% 11.43/1.99      ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
% 11.43/1.99      | v1_relat_1(X1) != iProver_top
% 11.43/1.99      | v1_relat_1(X0) != iProver_top ),
% 11.43/1.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_4979,plain,
% 11.43/1.99      ( k10_relat_1(sK2,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(sK2,X0))
% 11.43/1.99      | v1_relat_1(X0) != iProver_top ),
% 11.43/1.99      inference(superposition,[status(thm)],[c_3544,c_2199]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_6098,plain,
% 11.43/1.99      ( k10_relat_1(sK2,k1_relat_1(sK3)) = k1_relat_1(k5_relat_1(sK2,sK3)) ),
% 11.43/1.99      inference(superposition,[status(thm)],[c_3543,c_4979]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_7875,plain,
% 11.43/1.99      ( k9_relat_1(sK2,k1_relat_1(k5_relat_1(sK2,sK3))) = k1_relat_1(sK3) ),
% 11.43/1.99      inference(light_normalisation,[status(thm)],[c_7874,c_6098]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_11918,plain,
% 11.43/1.99      ( k9_relat_1(sK2,k1_relat_1(k6_partfun1(sK0))) = k1_relat_1(sK3) ),
% 11.43/1.99      inference(light_normalisation,[status(thm)],[c_7875,c_7875,c_8905]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_11,plain,
% 11.43/1.99      ( k1_relat_1(k6_partfun1(X0)) = X0 ),
% 11.43/1.99      inference(cnf_transformation,[],[f122]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_8,plain,
% 11.43/1.99      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 11.43/1.99      inference(cnf_transformation,[],[f80]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_551,plain,
% 11.43/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.43/1.99      | ~ v1_relat_1(X0)
% 11.43/1.99      | k7_relat_1(X0,X1) = X0 ),
% 11.43/1.99      inference(resolution,[status(thm)],[c_27,c_8]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_555,plain,
% 11.43/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.43/1.99      | k7_relat_1(X0,X1) = X0 ),
% 11.43/1.99      inference(global_propositional_subsumption,
% 11.43/1.99                [status(thm)],
% 11.43/1.99                [c_551,c_27,c_26,c_8]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_2170,plain,
% 11.43/1.99      ( k7_relat_1(X0,X1) = X0
% 11.43/1.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 11.43/1.99      inference(predicate_to_equality,[status(thm)],[c_555]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_4360,plain,
% 11.43/1.99      ( k7_relat_1(sK2,sK0) = sK2 ),
% 11.43/1.99      inference(superposition,[status(thm)],[c_2173,c_2170]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_6,plain,
% 11.43/1.99      ( ~ v1_relat_1(X0)
% 11.43/1.99      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 11.43/1.99      inference(cnf_transformation,[],[f78]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_2200,plain,
% 11.43/1.99      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 11.43/1.99      | v1_relat_1(X0) != iProver_top ),
% 11.43/1.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_3707,plain,
% 11.43/1.99      ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
% 11.43/1.99      inference(superposition,[status(thm)],[c_3544,c_2200]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_5061,plain,
% 11.43/1.99      ( k9_relat_1(sK2,sK0) = k2_relat_1(sK2) ),
% 11.43/1.99      inference(superposition,[status(thm)],[c_4360,c_3707]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_5062,plain,
% 11.43/1.99      ( k9_relat_1(sK2,sK0) = sK1 ),
% 11.43/1.99      inference(light_normalisation,[status(thm)],[c_5061,c_3694]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_11919,plain,
% 11.43/1.99      ( k1_relat_1(sK3) = sK1 ),
% 11.43/1.99      inference(demodulation,[status(thm)],[c_11918,c_11,c_5062]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_12,plain,
% 11.43/1.99      ( ~ v1_relat_1(X0)
% 11.43/1.99      | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 ),
% 11.43/1.99      inference(cnf_transformation,[],[f123]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_2197,plain,
% 11.43/1.99      ( k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0
% 11.43/1.99      | v1_relat_1(X0) != iProver_top ),
% 11.43/1.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_3634,plain,
% 11.43/1.99      ( k5_relat_1(k6_partfun1(k1_relat_1(sK3)),sK3) = sK3 ),
% 11.43/1.99      inference(superposition,[status(thm)],[c_3543,c_2197]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_11924,plain,
% 11.43/1.99      ( k5_relat_1(k6_partfun1(sK1),sK3) = sK3 ),
% 11.43/1.99      inference(demodulation,[status(thm)],[c_11919,c_3634]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_34854,plain,
% 11.43/1.99      ( k2_funct_1(sK2) = sK3 ),
% 11.43/1.99      inference(light_normalisation,
% 11.43/1.99                [status(thm)],
% 11.43/1.99                [c_34845,c_6435,c_8905,c_11924]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(c_36,negated_conjecture,
% 11.43/1.99      ( k2_funct_1(sK2) != sK3 ),
% 11.43/1.99      inference(cnf_transformation,[],[f120]) ).
% 11.43/1.99  
% 11.43/1.99  cnf(contradiction,plain,
% 11.43/1.99      ( $false ),
% 11.43/1.99      inference(minisat,[status(thm)],[c_34854,c_36]) ).
% 11.43/1.99  
% 11.43/1.99  
% 11.43/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.43/1.99  
% 11.43/1.99  ------                               Statistics
% 11.43/1.99  
% 11.43/1.99  ------ General
% 11.43/1.99  
% 11.43/1.99  abstr_ref_over_cycles:                  0
% 11.43/1.99  abstr_ref_under_cycles:                 0
% 11.43/1.99  gc_basic_clause_elim:                   0
% 11.43/1.99  forced_gc_time:                         0
% 11.43/1.99  parsing_time:                           0.007
% 11.43/1.99  unif_index_cands_time:                  0.
% 11.43/1.99  unif_index_add_time:                    0.
% 11.43/1.99  orderings_time:                         0.
% 11.43/1.99  out_proof_time:                         0.026
% 11.43/1.99  total_time:                             1.367
% 11.43/1.99  num_of_symbols:                         57
% 11.43/1.99  num_of_terms:                           55542
% 11.43/1.99  
% 11.43/1.99  ------ Preprocessing
% 11.43/1.99  
% 11.43/1.99  num_of_splits:                          0
% 11.43/1.99  num_of_split_atoms:                     0
% 11.43/1.99  num_of_reused_defs:                     0
% 11.43/1.99  num_eq_ax_congr_red:                    17
% 11.43/1.99  num_of_sem_filtered_clauses:            1
% 11.43/1.99  num_of_subtypes:                        0
% 11.43/1.99  monotx_restored_types:                  0
% 11.43/1.99  sat_num_of_epr_types:                   0
% 11.43/1.99  sat_num_of_non_cyclic_types:            0
% 11.43/1.99  sat_guarded_non_collapsed_types:        0
% 11.43/1.99  num_pure_diseq_elim:                    0
% 11.43/1.99  simp_replaced_by:                       0
% 11.43/1.99  res_preprocessed:                       225
% 11.43/1.99  prep_upred:                             0
% 11.43/1.99  prep_unflattend:                        34
% 11.43/1.99  smt_new_axioms:                         0
% 11.43/1.99  pred_elim_cands:                        6
% 11.43/1.99  pred_elim:                              2
% 11.43/1.99  pred_elim_cl:                           2
% 11.43/1.99  pred_elim_cycles:                       4
% 11.43/1.99  merged_defs:                            8
% 11.43/1.99  merged_defs_ncl:                        0
% 11.43/1.99  bin_hyper_res:                          8
% 11.43/1.99  prep_cycles:                            4
% 11.43/1.99  pred_elim_time:                         0.008
% 11.43/1.99  splitting_time:                         0.
% 11.43/1.99  sem_filter_time:                        0.
% 11.43/1.99  monotx_time:                            0.
% 11.43/1.99  subtype_inf_time:                       0.
% 11.43/1.99  
% 11.43/1.99  ------ Problem properties
% 11.43/1.99  
% 11.43/1.99  clauses:                                46
% 11.43/1.99  conjectures:                            11
% 11.43/1.99  epr:                                    7
% 11.43/1.99  horn:                                   46
% 11.43/1.99  ground:                                 12
% 11.43/1.99  unary:                                  18
% 11.43/1.99  binary:                                 9
% 11.43/1.99  lits:                                   124
% 11.43/1.99  lits_eq:                                29
% 11.43/1.99  fd_pure:                                0
% 11.43/1.99  fd_pseudo:                              0
% 11.43/1.99  fd_cond:                                0
% 11.43/1.99  fd_pseudo_cond:                         0
% 11.43/1.99  ac_symbols:                             0
% 11.43/1.99  
% 11.43/1.99  ------ Propositional Solver
% 11.43/1.99  
% 11.43/1.99  prop_solver_calls:                      34
% 11.43/1.99  prop_fast_solver_calls:                 2862
% 11.43/1.99  smt_solver_calls:                       0
% 11.43/1.99  smt_fast_solver_calls:                  0
% 11.43/1.99  prop_num_of_clauses:                    20433
% 11.43/1.99  prop_preprocess_simplified:             33524
% 11.43/1.99  prop_fo_subsumed:                       233
% 11.43/1.99  prop_solver_time:                       0.
% 11.43/1.99  smt_solver_time:                        0.
% 11.43/1.99  smt_fast_solver_time:                   0.
% 11.43/1.99  prop_fast_solver_time:                  0.
% 11.43/1.99  prop_unsat_core_time:                   0.004
% 11.43/1.99  
% 11.43/1.99  ------ QBF
% 11.43/1.99  
% 11.43/1.99  qbf_q_res:                              0
% 11.43/1.99  qbf_num_tautologies:                    0
% 11.43/1.99  qbf_prep_cycles:                        0
% 11.43/1.99  
% 11.43/1.99  ------ BMC1
% 11.43/1.99  
% 11.43/1.99  bmc1_current_bound:                     -1
% 11.43/1.99  bmc1_last_solved_bound:                 -1
% 11.43/1.99  bmc1_unsat_core_size:                   -1
% 11.43/1.99  bmc1_unsat_core_parents_size:           -1
% 11.43/1.99  bmc1_merge_next_fun:                    0
% 11.43/1.99  bmc1_unsat_core_clauses_time:           0.
% 11.43/1.99  
% 11.43/1.99  ------ Instantiation
% 11.43/1.99  
% 11.43/1.99  inst_num_of_clauses:                    5094
% 11.43/1.99  inst_num_in_passive:                    1980
% 11.43/1.99  inst_num_in_active:                     2236
% 11.43/1.99  inst_num_in_unprocessed:                879
% 11.43/1.99  inst_num_of_loops:                      2480
% 11.43/1.99  inst_num_of_learning_restarts:          0
% 11.43/1.99  inst_num_moves_active_passive:          239
% 11.43/1.99  inst_lit_activity:                      0
% 11.43/1.99  inst_lit_activity_moves:                1
% 11.43/1.99  inst_num_tautologies:                   0
% 11.43/1.99  inst_num_prop_implied:                  0
% 11.43/1.99  inst_num_existing_simplified:           0
% 11.43/1.99  inst_num_eq_res_simplified:             0
% 11.43/1.99  inst_num_child_elim:                    0
% 11.43/1.99  inst_num_of_dismatching_blockings:      976
% 11.43/1.99  inst_num_of_non_proper_insts:           5126
% 11.43/1.99  inst_num_of_duplicates:                 0
% 11.43/1.99  inst_inst_num_from_inst_to_res:         0
% 11.43/1.99  inst_dismatching_checking_time:         0.
% 11.43/1.99  
% 11.43/1.99  ------ Resolution
% 11.43/1.99  
% 11.43/1.99  res_num_of_clauses:                     0
% 11.43/1.99  res_num_in_passive:                     0
% 11.43/1.99  res_num_in_active:                      0
% 11.43/1.99  res_num_of_loops:                       229
% 11.43/1.99  res_forward_subset_subsumed:            219
% 11.43/1.99  res_backward_subset_subsumed:           2
% 11.43/1.99  res_forward_subsumed:                   2
% 11.43/1.99  res_backward_subsumed:                  0
% 11.43/1.99  res_forward_subsumption_resolution:     1
% 11.43/1.99  res_backward_subsumption_resolution:    0
% 11.43/1.99  res_clause_to_clause_subsumption:       2999
% 11.43/1.99  res_orphan_elimination:                 0
% 11.43/1.99  res_tautology_del:                      204
% 11.43/1.99  res_num_eq_res_simplified:              1
% 11.43/1.99  res_num_sel_changes:                    0
% 11.43/1.99  res_moves_from_active_to_pass:          0
% 11.43/1.99  
% 11.43/1.99  ------ Superposition
% 11.43/1.99  
% 11.43/1.99  sup_time_total:                         0.
% 11.43/1.99  sup_time_generating:                    0.
% 11.43/1.99  sup_time_sim_full:                      0.
% 11.43/1.99  sup_time_sim_immed:                     0.
% 11.43/1.99  
% 11.43/1.99  sup_num_of_clauses:                     1567
% 11.43/1.99  sup_num_in_active:                      456
% 11.43/1.99  sup_num_in_passive:                     1111
% 11.43/1.99  sup_num_of_loops:                       494
% 11.43/1.99  sup_fw_superposition:                   1130
% 11.43/1.99  sup_bw_superposition:                   675
% 11.43/1.99  sup_immediate_simplified:               420
% 11.43/1.99  sup_given_eliminated:                   1
% 11.43/1.99  comparisons_done:                       0
% 11.43/1.99  comparisons_avoided:                    0
% 11.43/1.99  
% 11.43/1.99  ------ Simplifications
% 11.43/1.99  
% 11.43/1.99  
% 11.43/1.99  sim_fw_subset_subsumed:                 30
% 11.43/1.99  sim_bw_subset_subsumed:                 34
% 11.43/1.99  sim_fw_subsumed:                        30
% 11.43/1.99  sim_bw_subsumed:                        6
% 11.43/1.99  sim_fw_subsumption_res:                 0
% 11.43/1.99  sim_bw_subsumption_res:                 0
% 11.43/1.99  sim_tautology_del:                      1
% 11.43/1.99  sim_eq_tautology_del:                   54
% 11.43/1.99  sim_eq_res_simp:                        1
% 11.43/1.99  sim_fw_demodulated:                     59
% 11.43/1.99  sim_bw_demodulated:                     34
% 11.43/1.99  sim_light_normalised:                   355
% 11.43/1.99  sim_joinable_taut:                      0
% 11.43/1.99  sim_joinable_simp:                      0
% 11.43/1.99  sim_ac_normalised:                      0
% 11.43/1.99  sim_smt_subsumption:                    0
% 11.43/1.99  
%------------------------------------------------------------------------------
