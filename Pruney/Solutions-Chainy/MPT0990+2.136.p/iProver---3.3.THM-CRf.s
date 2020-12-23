%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:26 EST 2020

% Result     : Theorem 15.78s
% Output     : CNFRefutation 15.78s
% Verified   : 
% Statistics : Number of formulae       :  255 (2496 expanded)
%              Number of clauses        :  152 ( 762 expanded)
%              Number of leaves         :   28 ( 617 expanded)
%              Depth                    :   22
%              Number of atoms          :  882 (19652 expanded)
%              Number of equality atoms :  424 (6953 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f34,conjecture,(
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

fof(f35,negated_conjecture,(
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
    inference(negated_conjecture,[],[f34])).

fof(f74,plain,(
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
    inference(ennf_transformation,[],[f35])).

fof(f75,plain,(
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
    inference(flattening,[],[f74])).

fof(f81,plain,(
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

fof(f80,plain,
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

fof(f82,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f75,f81,f80])).

fof(f134,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f82])).

fof(f137,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f82])).

fof(f28,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f65,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f64])).

fof(f120,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f135,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f82])).

fof(f25,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f61,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f60])).

fof(f79,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f61])).

fof(f115,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f139,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f82])).

fof(f27,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f27])).

fof(f119,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f36])).

fof(f132,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f82])).

fof(f26,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f63,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f62])).

fof(f118,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f21,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f56,plain,(
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
    inference(flattening,[],[f55])).

fof(f111,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f29,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f121,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f29])).

fof(f151,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f111,f121])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f138,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f82])).

fof(f30,axiom,(
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

fof(f66,plain,(
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
    inference(ennf_transformation,[],[f30])).

fof(f67,plain,(
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
    inference(flattening,[],[f66])).

fof(f122,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f133,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f82])).

fof(f136,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f82])).

fof(f31,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
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
    inference(ennf_transformation,[],[f31])).

fof(f69,plain,(
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
    inference(flattening,[],[f68])).

fof(f125,plain,(
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
    inference(cnf_transformation,[],[f69])).

fof(f141,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f82])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f76])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f77])).

fof(f153,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f83])).

fof(f85,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f18,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f107,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f149,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f107,f121])).

fof(f16,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f48,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f47])).

fof(f103,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f88,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f87,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f90,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f89,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f93,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f24,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f114,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f112,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f33,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
            & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f73,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f72])).

fof(f130,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f96,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f20,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f54,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f53])).

fof(f110,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f12,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f99,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f144,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f99,f121])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f91,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f140,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f82])).

fof(f143,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_57,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f134])).

cnf(c_2330,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_57])).

cnf(c_54,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f137])).

cnf(c_2333,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_54])).

cnf(c_37,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_2344,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_8724,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2333,c_2344])).

cnf(c_56,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f135])).

cnf(c_63,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_56])).

cnf(c_9244,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8724,c_63])).

cnf(c_9245,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_9244])).

cnf(c_9254,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2330,c_9245])).

cnf(c_33,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f115])).

cnf(c_52,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f139])).

cnf(c_736,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_52])).

cnf(c_737,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_736])).

cnf(c_36,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_745,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_737,c_36])).

cnf(c_2325,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_745])).

cnf(c_59,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f132])).

cnf(c_34,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_2715,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_34])).

cnf(c_3370,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2325,c_59,c_57,c_56,c_54,c_745,c_2715])).

cnf(c_9256,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9254,c_3370])).

cnf(c_60,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_59])).

cnf(c_10771,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9256,c_60])).

cnf(c_28,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
    | k2_funct_1(X0) = X1
    | k2_relat_1(X1) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f151])).

cnf(c_2351,plain,
    ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k2_relat_1(X0) != k1_relat_1(X1)
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_10773,plain,
    ( k2_funct_1(sK3) = sK2
    | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_10771,c_2351])).

cnf(c_30,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_2349,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_4298,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2330,c_2349])).

cnf(c_53,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f138])).

cnf(c_4299,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_4298,c_53])).

cnf(c_4297,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2333,c_2349])).

cnf(c_38,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f122])).

cnf(c_749,plain,
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
    inference(resolution_lifted,[status(thm)],[c_38,c_52])).

cnf(c_750,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0
    | k6_partfun1(sK0) != k6_partfun1(sK0) ),
    inference(unflattening,[status(thm)],[c_749])).

cnf(c_855,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_750])).

cnf(c_2324,plain,
    ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X0,sK0,X2) = sK0
    | v1_funct_2(X2,X0,sK0) != iProver_top
    | v1_funct_2(X1,sK0,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_855])).

cnf(c_2950,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2324])).

cnf(c_58,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f133])).

cnf(c_61,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_58])).

cnf(c_62,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_57])).

cnf(c_55,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f136])).

cnf(c_64,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_55])).

cnf(c_65,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_54])).

cnf(c_3377,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2950,c_60,c_61,c_62,c_63,c_64,c_65])).

cnf(c_4300,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_4297,c_3377])).

cnf(c_10779,plain,
    ( k2_funct_1(sK3) = sK2
    | k6_partfun1(sK0) != k6_partfun1(sK0)
    | k1_relat_1(sK3) != sK1
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10773,c_4299,c_4300])).

cnf(c_10780,plain,
    ( k2_funct_1(sK3) = sK2
    | k1_relat_1(sK3) != sK1
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_10779])).

cnf(c_40,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v2_funct_1(X0)
    | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
    | k2_relset_1(X4,X1,X3) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f125])).

cnf(c_2342,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k1_xboole_0 = X3
    | v1_funct_2(X4,X1,X3) != iProver_top
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X4) = iProver_top
    | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_9409,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_53,c_2342])).

cnf(c_9436,plain,
    ( v1_funct_1(X1) != iProver_top
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | k1_xboole_0 = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9409,c_60,c_61,c_62])).

cnf(c_9437,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_9436])).

cnf(c_9440,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3370,c_9437])).

cnf(c_50,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f141])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f153])).

cnf(c_192,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_196,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1248,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2487,plain,
    ( sK0 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_1248])).

cnf(c_2488,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2487])).

cnf(c_23,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f149])).

cnf(c_5340,plain,
    ( v2_funct_1(k6_partfun1(sK0)) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_5341,plain,
    ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5340])).

cnf(c_10545,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9440,c_63,c_64,c_65,c_50,c_192,c_196,c_2488,c_5341])).

cnf(c_2331,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_56])).

cnf(c_20,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_2359,plain,
    ( k2_funct_1(X0) = k4_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_7361,plain,
    ( k2_funct_1(sK3) = k4_relat_1(sK3)
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2331,c_2359])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_2371,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4115,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK1,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2333,c_2371])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_3,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_425,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_3])).

cnf(c_426,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_425])).

cnf(c_520,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_5,c_426])).

cnf(c_3466,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_520])).

cnf(c_4900,plain,
    ( ~ r1_tarski(sK3,k2_zfmisc_1(sK1,sK0))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_3466])).

cnf(c_4901,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4900])).

cnf(c_7,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_5279,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_5280,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5279])).

cnf(c_7708,plain,
    ( v2_funct_1(sK3) != iProver_top
    | k2_funct_1(sK3) = k4_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7361,c_4115,c_4901,c_5280])).

cnf(c_7709,plain,
    ( k2_funct_1(sK3) = k4_relat_1(sK3)
    | v2_funct_1(sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_7708])).

cnf(c_10551,plain,
    ( k2_funct_1(sK3) = k4_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_10545,c_7709])).

cnf(c_10781,plain,
    ( k1_relat_1(sK3) != sK1
    | k4_relat_1(sK3) = sK2
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10780,c_10551])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k4_relat_1(X0)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_10427,plain,
    ( v1_relat_1(k4_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_10435,plain,
    ( v1_relat_1(k4_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10427])).

cnf(c_2369,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4116,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2330,c_2371])).

cnf(c_2327,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_520])).

cnf(c_17469,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4116,c_2327])).

cnf(c_18066,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2369,c_17469])).

cnf(c_17468,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4115,c_2327])).

cnf(c_18022,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_17468,c_4115,c_4901,c_5280])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_2366,plain,
    ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_18039,plain,
    ( k10_relat_1(sK3,k2_relat_1(sK3)) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_18022,c_2366])).

cnf(c_18048,plain,
    ( k10_relat_1(sK3,sK0) = k1_relat_1(sK3) ),
    inference(light_normalisation,[status(thm)],[c_18039,c_4300])).

cnf(c_31,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_2348,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_5319,plain,
    ( k8_relset_1(sK1,sK0,sK3,X0) = k10_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_2333,c_2348])).

cnf(c_29,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k8_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_2350,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k8_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_5450,plain,
    ( m1_subset_1(k10_relat_1(sK3,X0),k1_zfmisc_1(sK1)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5319,c_2350])).

cnf(c_5568,plain,
    ( m1_subset_1(k10_relat_1(sK3,X0),k1_zfmisc_1(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5450,c_65])).

cnf(c_5574,plain,
    ( r1_tarski(k10_relat_1(sK3,X0),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_5568,c_2371])).

cnf(c_2374,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_5653,plain,
    ( k10_relat_1(sK3,X0) = sK1
    | r1_tarski(sK1,k10_relat_1(sK3,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5574,c_2374])).

cnf(c_22679,plain,
    ( k10_relat_1(sK3,sK0) = sK1
    | r1_tarski(sK1,k1_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_18048,c_5653])).

cnf(c_22682,plain,
    ( k1_relat_1(sK3) = sK1
    | r1_tarski(sK1,k1_relat_1(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_22679,c_18048])).

cnf(c_47,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f130])).

cnf(c_2335,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_4037,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3377,c_2335])).

cnf(c_4109,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | v2_funct_1(sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4037,c_63,c_64,c_65,c_50,c_192,c_196,c_2488])).

cnf(c_10553,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
    inference(superposition,[status(thm)],[c_10545,c_4109])).

cnf(c_10555,plain,
    ( k5_relat_1(sK3,k4_relat_1(sK3)) = k6_partfun1(sK1) ),
    inference(demodulation,[status(thm)],[c_10551,c_10553])).

cnf(c_13,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_2363,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_23257,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1(sK1)),k2_relat_1(k4_relat_1(sK3))) = iProver_top
    | v1_relat_1(k4_relat_1(sK3)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_10555,c_2363])).

cnf(c_26,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_2353,plain,
    ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_7989,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2331,c_2353])).

cnf(c_8744,plain,
    ( v2_funct_1(sK3) != iProver_top
    | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7989,c_4115,c_4901,c_5280])).

cnf(c_8745,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
    | v2_funct_1(sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_8744])).

cnf(c_10550,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_10545,c_8745])).

cnf(c_10556,plain,
    ( k2_relat_1(k4_relat_1(sK3)) = k1_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_10550,c_10551])).

cnf(c_23258,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1(sK1)),k1_relat_1(sK3)) = iProver_top
    | v1_relat_1(k4_relat_1(sK3)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_23257,c_10556])).

cnf(c_15,plain,
    ( k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f144])).

cnf(c_23259,plain,
    ( r1_tarski(sK1,k1_relat_1(sK3)) = iProver_top
    | v1_relat_1(k4_relat_1(sK3)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_23258,c_15])).

cnf(c_60283,plain,
    ( k4_relat_1(sK3) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10781,c_60,c_63,c_64,c_65,c_50,c_192,c_196,c_2488,c_4115,c_4901,c_5280,c_5341,c_9440,c_10435,c_18066,c_22682,c_23259])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k4_relat_1(k4_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_2368,plain,
    ( k4_relat_1(k4_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_18044,plain,
    ( k4_relat_1(k4_relat_1(sK3)) = sK3 ),
    inference(superposition,[status(thm)],[c_18022,c_2368])).

cnf(c_60334,plain,
    ( k4_relat_1(sK2) = sK3 ),
    inference(demodulation,[status(thm)],[c_60283,c_18044])).

cnf(c_2328,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_59])).

cnf(c_7362,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2328,c_2359])).

cnf(c_51,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f140])).

cnf(c_67,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_51])).

cnf(c_4307,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_4308,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4307])).

cnf(c_7713,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7362,c_60,c_67,c_4308])).

cnf(c_18811,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_18066,c_7713])).

cnf(c_48,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f143])).

cnf(c_19105,plain,
    ( k4_relat_1(sK2) != sK3 ),
    inference(demodulation,[status(thm)],[c_18811,c_48])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_60334,c_19105])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:20:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 15.78/2.51  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.78/2.51  
% 15.78/2.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.78/2.51  
% 15.78/2.51  ------  iProver source info
% 15.78/2.51  
% 15.78/2.51  git: date: 2020-06-30 10:37:57 +0100
% 15.78/2.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.78/2.51  git: non_committed_changes: false
% 15.78/2.51  git: last_make_outside_of_git: false
% 15.78/2.51  
% 15.78/2.51  ------ 
% 15.78/2.51  
% 15.78/2.51  ------ Input Options
% 15.78/2.51  
% 15.78/2.51  --out_options                           all
% 15.78/2.51  --tptp_safe_out                         true
% 15.78/2.51  --problem_path                          ""
% 15.78/2.51  --include_path                          ""
% 15.78/2.51  --clausifier                            res/vclausify_rel
% 15.78/2.51  --clausifier_options                    ""
% 15.78/2.51  --stdin                                 false
% 15.78/2.51  --stats_out                             all
% 15.78/2.51  
% 15.78/2.51  ------ General Options
% 15.78/2.51  
% 15.78/2.51  --fof                                   false
% 15.78/2.51  --time_out_real                         305.
% 15.78/2.51  --time_out_virtual                      -1.
% 15.78/2.51  --symbol_type_check                     false
% 15.78/2.51  --clausify_out                          false
% 15.78/2.51  --sig_cnt_out                           false
% 15.78/2.51  --trig_cnt_out                          false
% 15.78/2.51  --trig_cnt_out_tolerance                1.
% 15.78/2.51  --trig_cnt_out_sk_spl                   false
% 15.78/2.51  --abstr_cl_out                          false
% 15.78/2.51  
% 15.78/2.51  ------ Global Options
% 15.78/2.51  
% 15.78/2.51  --schedule                              default
% 15.78/2.51  --add_important_lit                     false
% 15.78/2.51  --prop_solver_per_cl                    1000
% 15.78/2.51  --min_unsat_core                        false
% 15.78/2.51  --soft_assumptions                      false
% 15.78/2.51  --soft_lemma_size                       3
% 15.78/2.51  --prop_impl_unit_size                   0
% 15.78/2.51  --prop_impl_unit                        []
% 15.78/2.51  --share_sel_clauses                     true
% 15.78/2.51  --reset_solvers                         false
% 15.78/2.51  --bc_imp_inh                            [conj_cone]
% 15.78/2.51  --conj_cone_tolerance                   3.
% 15.78/2.51  --extra_neg_conj                        none
% 15.78/2.51  --large_theory_mode                     true
% 15.78/2.51  --prolific_symb_bound                   200
% 15.78/2.51  --lt_threshold                          2000
% 15.78/2.51  --clause_weak_htbl                      true
% 15.78/2.51  --gc_record_bc_elim                     false
% 15.78/2.51  
% 15.78/2.51  ------ Preprocessing Options
% 15.78/2.51  
% 15.78/2.51  --preprocessing_flag                    true
% 15.78/2.51  --time_out_prep_mult                    0.1
% 15.78/2.51  --splitting_mode                        input
% 15.78/2.51  --splitting_grd                         true
% 15.78/2.51  --splitting_cvd                         false
% 15.78/2.51  --splitting_cvd_svl                     false
% 15.78/2.51  --splitting_nvd                         32
% 15.78/2.51  --sub_typing                            true
% 15.78/2.51  --prep_gs_sim                           true
% 15.78/2.51  --prep_unflatten                        true
% 15.78/2.51  --prep_res_sim                          true
% 15.78/2.51  --prep_upred                            true
% 15.78/2.51  --prep_sem_filter                       exhaustive
% 15.78/2.51  --prep_sem_filter_out                   false
% 15.78/2.51  --pred_elim                             true
% 15.78/2.51  --res_sim_input                         true
% 15.78/2.51  --eq_ax_congr_red                       true
% 15.78/2.51  --pure_diseq_elim                       true
% 15.78/2.51  --brand_transform                       false
% 15.78/2.51  --non_eq_to_eq                          false
% 15.78/2.51  --prep_def_merge                        true
% 15.78/2.51  --prep_def_merge_prop_impl              false
% 15.78/2.51  --prep_def_merge_mbd                    true
% 15.78/2.51  --prep_def_merge_tr_red                 false
% 15.78/2.51  --prep_def_merge_tr_cl                  false
% 15.78/2.51  --smt_preprocessing                     true
% 15.78/2.51  --smt_ac_axioms                         fast
% 15.78/2.51  --preprocessed_out                      false
% 15.78/2.51  --preprocessed_stats                    false
% 15.78/2.51  
% 15.78/2.51  ------ Abstraction refinement Options
% 15.78/2.51  
% 15.78/2.51  --abstr_ref                             []
% 15.78/2.51  --abstr_ref_prep                        false
% 15.78/2.51  --abstr_ref_until_sat                   false
% 15.78/2.51  --abstr_ref_sig_restrict                funpre
% 15.78/2.51  --abstr_ref_af_restrict_to_split_sk     false
% 15.78/2.51  --abstr_ref_under                       []
% 15.78/2.51  
% 15.78/2.51  ------ SAT Options
% 15.78/2.51  
% 15.78/2.51  --sat_mode                              false
% 15.78/2.51  --sat_fm_restart_options                ""
% 15.78/2.51  --sat_gr_def                            false
% 15.78/2.51  --sat_epr_types                         true
% 15.78/2.51  --sat_non_cyclic_types                  false
% 15.78/2.51  --sat_finite_models                     false
% 15.78/2.51  --sat_fm_lemmas                         false
% 15.78/2.51  --sat_fm_prep                           false
% 15.78/2.51  --sat_fm_uc_incr                        true
% 15.78/2.51  --sat_out_model                         small
% 15.78/2.51  --sat_out_clauses                       false
% 15.78/2.51  
% 15.78/2.51  ------ QBF Options
% 15.78/2.51  
% 15.78/2.51  --qbf_mode                              false
% 15.78/2.51  --qbf_elim_univ                         false
% 15.78/2.51  --qbf_dom_inst                          none
% 15.78/2.51  --qbf_dom_pre_inst                      false
% 15.78/2.51  --qbf_sk_in                             false
% 15.78/2.51  --qbf_pred_elim                         true
% 15.78/2.51  --qbf_split                             512
% 15.78/2.51  
% 15.78/2.51  ------ BMC1 Options
% 15.78/2.51  
% 15.78/2.51  --bmc1_incremental                      false
% 15.78/2.51  --bmc1_axioms                           reachable_all
% 15.78/2.51  --bmc1_min_bound                        0
% 15.78/2.51  --bmc1_max_bound                        -1
% 15.78/2.51  --bmc1_max_bound_default                -1
% 15.78/2.51  --bmc1_symbol_reachability              true
% 15.78/2.51  --bmc1_property_lemmas                  false
% 15.78/2.51  --bmc1_k_induction                      false
% 15.78/2.51  --bmc1_non_equiv_states                 false
% 15.78/2.51  --bmc1_deadlock                         false
% 15.78/2.51  --bmc1_ucm                              false
% 15.78/2.51  --bmc1_add_unsat_core                   none
% 15.78/2.51  --bmc1_unsat_core_children              false
% 15.78/2.51  --bmc1_unsat_core_extrapolate_axioms    false
% 15.78/2.51  --bmc1_out_stat                         full
% 15.78/2.51  --bmc1_ground_init                      false
% 15.78/2.51  --bmc1_pre_inst_next_state              false
% 15.78/2.51  --bmc1_pre_inst_state                   false
% 15.78/2.51  --bmc1_pre_inst_reach_state             false
% 15.78/2.51  --bmc1_out_unsat_core                   false
% 15.78/2.51  --bmc1_aig_witness_out                  false
% 15.78/2.51  --bmc1_verbose                          false
% 15.78/2.51  --bmc1_dump_clauses_tptp                false
% 15.78/2.51  --bmc1_dump_unsat_core_tptp             false
% 15.78/2.51  --bmc1_dump_file                        -
% 15.78/2.51  --bmc1_ucm_expand_uc_limit              128
% 15.78/2.51  --bmc1_ucm_n_expand_iterations          6
% 15.78/2.51  --bmc1_ucm_extend_mode                  1
% 15.78/2.51  --bmc1_ucm_init_mode                    2
% 15.78/2.51  --bmc1_ucm_cone_mode                    none
% 15.78/2.51  --bmc1_ucm_reduced_relation_type        0
% 15.78/2.51  --bmc1_ucm_relax_model                  4
% 15.78/2.51  --bmc1_ucm_full_tr_after_sat            true
% 15.78/2.51  --bmc1_ucm_expand_neg_assumptions       false
% 15.78/2.51  --bmc1_ucm_layered_model                none
% 15.78/2.51  --bmc1_ucm_max_lemma_size               10
% 15.78/2.51  
% 15.78/2.51  ------ AIG Options
% 15.78/2.51  
% 15.78/2.51  --aig_mode                              false
% 15.78/2.51  
% 15.78/2.51  ------ Instantiation Options
% 15.78/2.51  
% 15.78/2.51  --instantiation_flag                    true
% 15.78/2.51  --inst_sos_flag                         true
% 15.78/2.51  --inst_sos_phase                        true
% 15.78/2.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.78/2.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.78/2.51  --inst_lit_sel_side                     num_symb
% 15.78/2.51  --inst_solver_per_active                1400
% 15.78/2.51  --inst_solver_calls_frac                1.
% 15.78/2.51  --inst_passive_queue_type               priority_queues
% 15.78/2.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.78/2.51  --inst_passive_queues_freq              [25;2]
% 15.78/2.51  --inst_dismatching                      true
% 15.78/2.51  --inst_eager_unprocessed_to_passive     true
% 15.78/2.51  --inst_prop_sim_given                   true
% 15.78/2.51  --inst_prop_sim_new                     false
% 15.78/2.51  --inst_subs_new                         false
% 15.78/2.51  --inst_eq_res_simp                      false
% 15.78/2.51  --inst_subs_given                       false
% 15.78/2.51  --inst_orphan_elimination               true
% 15.78/2.51  --inst_learning_loop_flag               true
% 15.78/2.51  --inst_learning_start                   3000
% 15.78/2.51  --inst_learning_factor                  2
% 15.78/2.51  --inst_start_prop_sim_after_learn       3
% 15.78/2.51  --inst_sel_renew                        solver
% 15.78/2.51  --inst_lit_activity_flag                true
% 15.78/2.51  --inst_restr_to_given                   false
% 15.78/2.51  --inst_activity_threshold               500
% 15.78/2.51  --inst_out_proof                        true
% 15.78/2.51  
% 15.78/2.51  ------ Resolution Options
% 15.78/2.51  
% 15.78/2.51  --resolution_flag                       true
% 15.78/2.51  --res_lit_sel                           adaptive
% 15.78/2.51  --res_lit_sel_side                      none
% 15.78/2.51  --res_ordering                          kbo
% 15.78/2.51  --res_to_prop_solver                    active
% 15.78/2.51  --res_prop_simpl_new                    false
% 15.78/2.51  --res_prop_simpl_given                  true
% 15.78/2.51  --res_passive_queue_type                priority_queues
% 15.78/2.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.78/2.51  --res_passive_queues_freq               [15;5]
% 15.78/2.51  --res_forward_subs                      full
% 15.78/2.51  --res_backward_subs                     full
% 15.78/2.51  --res_forward_subs_resolution           true
% 15.78/2.51  --res_backward_subs_resolution          true
% 15.78/2.51  --res_orphan_elimination                true
% 15.78/2.51  --res_time_limit                        2.
% 15.78/2.51  --res_out_proof                         true
% 15.78/2.51  
% 15.78/2.51  ------ Superposition Options
% 15.78/2.51  
% 15.78/2.51  --superposition_flag                    true
% 15.78/2.51  --sup_passive_queue_type                priority_queues
% 15.78/2.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.78/2.51  --sup_passive_queues_freq               [8;1;4]
% 15.78/2.51  --demod_completeness_check              fast
% 15.78/2.51  --demod_use_ground                      true
% 15.78/2.51  --sup_to_prop_solver                    passive
% 15.78/2.51  --sup_prop_simpl_new                    true
% 15.78/2.51  --sup_prop_simpl_given                  true
% 15.78/2.51  --sup_fun_splitting                     true
% 15.78/2.51  --sup_smt_interval                      50000
% 15.78/2.51  
% 15.78/2.51  ------ Superposition Simplification Setup
% 15.78/2.51  
% 15.78/2.51  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.78/2.51  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.78/2.51  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.78/2.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.78/2.51  --sup_full_triv                         [TrivRules;PropSubs]
% 15.78/2.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.78/2.51  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.78/2.51  --sup_immed_triv                        [TrivRules]
% 15.78/2.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.78/2.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.78/2.51  --sup_immed_bw_main                     []
% 15.78/2.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.78/2.51  --sup_input_triv                        [Unflattening;TrivRules]
% 15.78/2.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.78/2.51  --sup_input_bw                          []
% 15.78/2.51  
% 15.78/2.51  ------ Combination Options
% 15.78/2.51  
% 15.78/2.51  --comb_res_mult                         3
% 15.78/2.51  --comb_sup_mult                         2
% 15.78/2.51  --comb_inst_mult                        10
% 15.78/2.51  
% 15.78/2.51  ------ Debug Options
% 15.78/2.51  
% 15.78/2.51  --dbg_backtrace                         false
% 15.78/2.51  --dbg_dump_prop_clauses                 false
% 15.78/2.51  --dbg_dump_prop_clauses_file            -
% 15.78/2.51  --dbg_out_stat                          false
% 15.78/2.51  ------ Parsing...
% 15.78/2.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.78/2.51  
% 15.78/2.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 15.78/2.51  
% 15.78/2.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.78/2.51  
% 15.78/2.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.78/2.51  ------ Proving...
% 15.78/2.51  ------ Problem Properties 
% 15.78/2.51  
% 15.78/2.51  
% 15.78/2.51  clauses                                 58
% 15.78/2.51  conjectures                             11
% 15.78/2.51  EPR                                     10
% 15.78/2.51  Horn                                    54
% 15.78/2.51  unary                                   19
% 15.78/2.51  binary                                  14
% 15.78/2.51  lits                                    190
% 15.78/2.51  lits eq                                 46
% 15.78/2.51  fd_pure                                 0
% 15.78/2.51  fd_pseudo                               0
% 15.78/2.51  fd_cond                                 4
% 15.78/2.51  fd_pseudo_cond                          2
% 15.78/2.51  AC symbols                              0
% 15.78/2.51  
% 15.78/2.51  ------ Schedule dynamic 5 is on 
% 15.78/2.51  
% 15.78/2.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 15.78/2.51  
% 15.78/2.51  
% 15.78/2.51  ------ 
% 15.78/2.51  Current options:
% 15.78/2.51  ------ 
% 15.78/2.51  
% 15.78/2.51  ------ Input Options
% 15.78/2.51  
% 15.78/2.51  --out_options                           all
% 15.78/2.51  --tptp_safe_out                         true
% 15.78/2.51  --problem_path                          ""
% 15.78/2.51  --include_path                          ""
% 15.78/2.51  --clausifier                            res/vclausify_rel
% 15.78/2.51  --clausifier_options                    ""
% 15.78/2.51  --stdin                                 false
% 15.78/2.51  --stats_out                             all
% 15.78/2.51  
% 15.78/2.51  ------ General Options
% 15.78/2.51  
% 15.78/2.51  --fof                                   false
% 15.78/2.51  --time_out_real                         305.
% 15.78/2.51  --time_out_virtual                      -1.
% 15.78/2.51  --symbol_type_check                     false
% 15.78/2.51  --clausify_out                          false
% 15.78/2.51  --sig_cnt_out                           false
% 15.78/2.51  --trig_cnt_out                          false
% 15.78/2.51  --trig_cnt_out_tolerance                1.
% 15.78/2.51  --trig_cnt_out_sk_spl                   false
% 15.78/2.51  --abstr_cl_out                          false
% 15.78/2.51  
% 15.78/2.51  ------ Global Options
% 15.78/2.51  
% 15.78/2.51  --schedule                              default
% 15.78/2.51  --add_important_lit                     false
% 15.78/2.51  --prop_solver_per_cl                    1000
% 15.78/2.51  --min_unsat_core                        false
% 15.78/2.51  --soft_assumptions                      false
% 15.78/2.51  --soft_lemma_size                       3
% 15.78/2.51  --prop_impl_unit_size                   0
% 15.78/2.51  --prop_impl_unit                        []
% 15.78/2.51  --share_sel_clauses                     true
% 15.78/2.51  --reset_solvers                         false
% 15.78/2.51  --bc_imp_inh                            [conj_cone]
% 15.78/2.51  --conj_cone_tolerance                   3.
% 15.78/2.51  --extra_neg_conj                        none
% 15.78/2.51  --large_theory_mode                     true
% 15.78/2.51  --prolific_symb_bound                   200
% 15.78/2.51  --lt_threshold                          2000
% 15.78/2.51  --clause_weak_htbl                      true
% 15.78/2.51  --gc_record_bc_elim                     false
% 15.78/2.51  
% 15.78/2.51  ------ Preprocessing Options
% 15.78/2.51  
% 15.78/2.51  --preprocessing_flag                    true
% 15.78/2.51  --time_out_prep_mult                    0.1
% 15.78/2.51  --splitting_mode                        input
% 15.78/2.51  --splitting_grd                         true
% 15.78/2.51  --splitting_cvd                         false
% 15.78/2.51  --splitting_cvd_svl                     false
% 15.78/2.51  --splitting_nvd                         32
% 15.78/2.51  --sub_typing                            true
% 15.78/2.51  --prep_gs_sim                           true
% 15.78/2.51  --prep_unflatten                        true
% 15.78/2.51  --prep_res_sim                          true
% 15.78/2.51  --prep_upred                            true
% 15.78/2.51  --prep_sem_filter                       exhaustive
% 15.78/2.51  --prep_sem_filter_out                   false
% 15.78/2.51  --pred_elim                             true
% 15.78/2.51  --res_sim_input                         true
% 15.78/2.51  --eq_ax_congr_red                       true
% 15.78/2.51  --pure_diseq_elim                       true
% 15.78/2.51  --brand_transform                       false
% 15.78/2.51  --non_eq_to_eq                          false
% 15.78/2.51  --prep_def_merge                        true
% 15.78/2.51  --prep_def_merge_prop_impl              false
% 15.78/2.51  --prep_def_merge_mbd                    true
% 15.78/2.51  --prep_def_merge_tr_red                 false
% 15.78/2.51  --prep_def_merge_tr_cl                  false
% 15.78/2.51  --smt_preprocessing                     true
% 15.78/2.51  --smt_ac_axioms                         fast
% 15.78/2.51  --preprocessed_out                      false
% 15.78/2.51  --preprocessed_stats                    false
% 15.78/2.51  
% 15.78/2.51  ------ Abstraction refinement Options
% 15.78/2.51  
% 15.78/2.51  --abstr_ref                             []
% 15.78/2.51  --abstr_ref_prep                        false
% 15.78/2.51  --abstr_ref_until_sat                   false
% 15.78/2.51  --abstr_ref_sig_restrict                funpre
% 15.78/2.51  --abstr_ref_af_restrict_to_split_sk     false
% 15.78/2.51  --abstr_ref_under                       []
% 15.78/2.51  
% 15.78/2.51  ------ SAT Options
% 15.78/2.51  
% 15.78/2.51  --sat_mode                              false
% 15.78/2.51  --sat_fm_restart_options                ""
% 15.78/2.51  --sat_gr_def                            false
% 15.78/2.51  --sat_epr_types                         true
% 15.78/2.51  --sat_non_cyclic_types                  false
% 15.78/2.51  --sat_finite_models                     false
% 15.78/2.51  --sat_fm_lemmas                         false
% 15.78/2.51  --sat_fm_prep                           false
% 15.78/2.51  --sat_fm_uc_incr                        true
% 15.78/2.51  --sat_out_model                         small
% 15.78/2.51  --sat_out_clauses                       false
% 15.78/2.51  
% 15.78/2.51  ------ QBF Options
% 15.78/2.51  
% 15.78/2.51  --qbf_mode                              false
% 15.78/2.51  --qbf_elim_univ                         false
% 15.78/2.51  --qbf_dom_inst                          none
% 15.78/2.51  --qbf_dom_pre_inst                      false
% 15.78/2.51  --qbf_sk_in                             false
% 15.78/2.51  --qbf_pred_elim                         true
% 15.78/2.51  --qbf_split                             512
% 15.78/2.51  
% 15.78/2.51  ------ BMC1 Options
% 15.78/2.51  
% 15.78/2.51  --bmc1_incremental                      false
% 15.78/2.51  --bmc1_axioms                           reachable_all
% 15.78/2.51  --bmc1_min_bound                        0
% 15.78/2.51  --bmc1_max_bound                        -1
% 15.78/2.51  --bmc1_max_bound_default                -1
% 15.78/2.51  --bmc1_symbol_reachability              true
% 15.78/2.51  --bmc1_property_lemmas                  false
% 15.78/2.51  --bmc1_k_induction                      false
% 15.78/2.51  --bmc1_non_equiv_states                 false
% 15.78/2.51  --bmc1_deadlock                         false
% 15.78/2.51  --bmc1_ucm                              false
% 15.78/2.51  --bmc1_add_unsat_core                   none
% 15.78/2.51  --bmc1_unsat_core_children              false
% 15.78/2.51  --bmc1_unsat_core_extrapolate_axioms    false
% 15.78/2.51  --bmc1_out_stat                         full
% 15.78/2.51  --bmc1_ground_init                      false
% 15.78/2.51  --bmc1_pre_inst_next_state              false
% 15.78/2.51  --bmc1_pre_inst_state                   false
% 15.78/2.51  --bmc1_pre_inst_reach_state             false
% 15.78/2.51  --bmc1_out_unsat_core                   false
% 15.78/2.51  --bmc1_aig_witness_out                  false
% 15.78/2.51  --bmc1_verbose                          false
% 15.78/2.51  --bmc1_dump_clauses_tptp                false
% 15.78/2.51  --bmc1_dump_unsat_core_tptp             false
% 15.78/2.51  --bmc1_dump_file                        -
% 15.78/2.51  --bmc1_ucm_expand_uc_limit              128
% 15.78/2.51  --bmc1_ucm_n_expand_iterations          6
% 15.78/2.51  --bmc1_ucm_extend_mode                  1
% 15.78/2.51  --bmc1_ucm_init_mode                    2
% 15.78/2.51  --bmc1_ucm_cone_mode                    none
% 15.78/2.51  --bmc1_ucm_reduced_relation_type        0
% 15.78/2.52  --bmc1_ucm_relax_model                  4
% 15.78/2.52  --bmc1_ucm_full_tr_after_sat            true
% 15.78/2.52  --bmc1_ucm_expand_neg_assumptions       false
% 15.78/2.52  --bmc1_ucm_layered_model                none
% 15.78/2.52  --bmc1_ucm_max_lemma_size               10
% 15.78/2.52  
% 15.78/2.52  ------ AIG Options
% 15.78/2.52  
% 15.78/2.52  --aig_mode                              false
% 15.78/2.52  
% 15.78/2.52  ------ Instantiation Options
% 15.78/2.52  
% 15.78/2.52  --instantiation_flag                    true
% 15.78/2.52  --inst_sos_flag                         true
% 15.78/2.52  --inst_sos_phase                        true
% 15.78/2.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.78/2.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.78/2.52  --inst_lit_sel_side                     none
% 15.78/2.52  --inst_solver_per_active                1400
% 15.78/2.52  --inst_solver_calls_frac                1.
% 15.78/2.52  --inst_passive_queue_type               priority_queues
% 15.78/2.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.78/2.52  --inst_passive_queues_freq              [25;2]
% 15.78/2.52  --inst_dismatching                      true
% 15.78/2.52  --inst_eager_unprocessed_to_passive     true
% 15.78/2.52  --inst_prop_sim_given                   true
% 15.78/2.52  --inst_prop_sim_new                     false
% 15.78/2.52  --inst_subs_new                         false
% 15.78/2.52  --inst_eq_res_simp                      false
% 15.78/2.52  --inst_subs_given                       false
% 15.78/2.52  --inst_orphan_elimination               true
% 15.78/2.52  --inst_learning_loop_flag               true
% 15.78/2.52  --inst_learning_start                   3000
% 15.78/2.52  --inst_learning_factor                  2
% 15.78/2.52  --inst_start_prop_sim_after_learn       3
% 15.78/2.52  --inst_sel_renew                        solver
% 15.78/2.52  --inst_lit_activity_flag                true
% 15.78/2.52  --inst_restr_to_given                   false
% 15.78/2.52  --inst_activity_threshold               500
% 15.78/2.52  --inst_out_proof                        true
% 15.78/2.52  
% 15.78/2.52  ------ Resolution Options
% 15.78/2.52  
% 15.78/2.52  --resolution_flag                       false
% 15.78/2.52  --res_lit_sel                           adaptive
% 15.78/2.52  --res_lit_sel_side                      none
% 15.78/2.52  --res_ordering                          kbo
% 15.78/2.52  --res_to_prop_solver                    active
% 15.78/2.52  --res_prop_simpl_new                    false
% 15.78/2.52  --res_prop_simpl_given                  true
% 15.78/2.52  --res_passive_queue_type                priority_queues
% 15.78/2.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.78/2.52  --res_passive_queues_freq               [15;5]
% 15.78/2.52  --res_forward_subs                      full
% 15.78/2.52  --res_backward_subs                     full
% 15.78/2.52  --res_forward_subs_resolution           true
% 15.78/2.52  --res_backward_subs_resolution          true
% 15.78/2.52  --res_orphan_elimination                true
% 15.78/2.52  --res_time_limit                        2.
% 15.78/2.52  --res_out_proof                         true
% 15.78/2.52  
% 15.78/2.52  ------ Superposition Options
% 15.78/2.52  
% 15.78/2.52  --superposition_flag                    true
% 15.78/2.52  --sup_passive_queue_type                priority_queues
% 15.78/2.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.78/2.52  --sup_passive_queues_freq               [8;1;4]
% 15.78/2.52  --demod_completeness_check              fast
% 15.78/2.52  --demod_use_ground                      true
% 15.78/2.52  --sup_to_prop_solver                    passive
% 15.78/2.52  --sup_prop_simpl_new                    true
% 15.78/2.52  --sup_prop_simpl_given                  true
% 15.78/2.52  --sup_fun_splitting                     true
% 15.78/2.52  --sup_smt_interval                      50000
% 15.78/2.52  
% 15.78/2.52  ------ Superposition Simplification Setup
% 15.78/2.52  
% 15.78/2.52  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.78/2.52  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.78/2.52  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.78/2.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.78/2.52  --sup_full_triv                         [TrivRules;PropSubs]
% 15.78/2.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.78/2.52  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.78/2.52  --sup_immed_triv                        [TrivRules]
% 15.78/2.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.78/2.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.78/2.52  --sup_immed_bw_main                     []
% 15.78/2.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.78/2.52  --sup_input_triv                        [Unflattening;TrivRules]
% 15.78/2.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.78/2.52  --sup_input_bw                          []
% 15.78/2.52  
% 15.78/2.52  ------ Combination Options
% 15.78/2.52  
% 15.78/2.52  --comb_res_mult                         3
% 15.78/2.52  --comb_sup_mult                         2
% 15.78/2.52  --comb_inst_mult                        10
% 15.78/2.52  
% 15.78/2.52  ------ Debug Options
% 15.78/2.52  
% 15.78/2.52  --dbg_backtrace                         false
% 15.78/2.52  --dbg_dump_prop_clauses                 false
% 15.78/2.52  --dbg_dump_prop_clauses_file            -
% 15.78/2.52  --dbg_out_stat                          false
% 15.78/2.52  
% 15.78/2.52  
% 15.78/2.52  
% 15.78/2.52  
% 15.78/2.52  ------ Proving...
% 15.78/2.52  
% 15.78/2.52  
% 15.78/2.52  % SZS status Theorem for theBenchmark.p
% 15.78/2.52  
% 15.78/2.52  % SZS output start CNFRefutation for theBenchmark.p
% 15.78/2.52  
% 15.78/2.52  fof(f34,conjecture,(
% 15.78/2.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 15.78/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.78/2.52  
% 15.78/2.52  fof(f35,negated_conjecture,(
% 15.78/2.52    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 15.78/2.52    inference(negated_conjecture,[],[f34])).
% 15.78/2.52  
% 15.78/2.52  fof(f74,plain,(
% 15.78/2.52    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 15.78/2.52    inference(ennf_transformation,[],[f35])).
% 15.78/2.52  
% 15.78/2.52  fof(f75,plain,(
% 15.78/2.52    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 15.78/2.52    inference(flattening,[],[f74])).
% 15.78/2.52  
% 15.78/2.52  fof(f81,plain,(
% 15.78/2.52    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 15.78/2.52    introduced(choice_axiom,[])).
% 15.78/2.52  
% 15.78/2.52  fof(f80,plain,(
% 15.78/2.52    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 15.78/2.52    introduced(choice_axiom,[])).
% 15.78/2.52  
% 15.78/2.52  fof(f82,plain,(
% 15.78/2.52    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 15.78/2.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f75,f81,f80])).
% 15.78/2.52  
% 15.78/2.52  fof(f134,plain,(
% 15.78/2.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 15.78/2.52    inference(cnf_transformation,[],[f82])).
% 15.78/2.52  
% 15.78/2.52  fof(f137,plain,(
% 15.78/2.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 15.78/2.52    inference(cnf_transformation,[],[f82])).
% 15.78/2.52  
% 15.78/2.52  fof(f28,axiom,(
% 15.78/2.52    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 15.78/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.78/2.52  
% 15.78/2.52  fof(f64,plain,(
% 15.78/2.52    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 15.78/2.52    inference(ennf_transformation,[],[f28])).
% 15.78/2.52  
% 15.78/2.52  fof(f65,plain,(
% 15.78/2.52    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 15.78/2.52    inference(flattening,[],[f64])).
% 15.78/2.52  
% 15.78/2.52  fof(f120,plain,(
% 15.78/2.52    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 15.78/2.52    inference(cnf_transformation,[],[f65])).
% 15.78/2.52  
% 15.78/2.52  fof(f135,plain,(
% 15.78/2.52    v1_funct_1(sK3)),
% 15.78/2.52    inference(cnf_transformation,[],[f82])).
% 15.78/2.52  
% 15.78/2.52  fof(f25,axiom,(
% 15.78/2.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 15.78/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.78/2.52  
% 15.78/2.52  fof(f60,plain,(
% 15.78/2.52    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 15.78/2.52    inference(ennf_transformation,[],[f25])).
% 15.78/2.52  
% 15.78/2.52  fof(f61,plain,(
% 15.78/2.52    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.78/2.52    inference(flattening,[],[f60])).
% 15.78/2.52  
% 15.78/2.52  fof(f79,plain,(
% 15.78/2.52    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.78/2.52    inference(nnf_transformation,[],[f61])).
% 15.78/2.52  
% 15.78/2.52  fof(f115,plain,(
% 15.78/2.52    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.78/2.52    inference(cnf_transformation,[],[f79])).
% 15.78/2.52  
% 15.78/2.52  fof(f139,plain,(
% 15.78/2.52    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 15.78/2.52    inference(cnf_transformation,[],[f82])).
% 15.78/2.52  
% 15.78/2.52  fof(f27,axiom,(
% 15.78/2.52    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 15.78/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.78/2.52  
% 15.78/2.52  fof(f36,plain,(
% 15.78/2.52    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 15.78/2.52    inference(pure_predicate_removal,[],[f27])).
% 15.78/2.52  
% 15.78/2.52  fof(f119,plain,(
% 15.78/2.52    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 15.78/2.52    inference(cnf_transformation,[],[f36])).
% 15.78/2.52  
% 15.78/2.52  fof(f132,plain,(
% 15.78/2.52    v1_funct_1(sK2)),
% 15.78/2.52    inference(cnf_transformation,[],[f82])).
% 15.78/2.52  
% 15.78/2.52  fof(f26,axiom,(
% 15.78/2.52    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 15.78/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.78/2.52  
% 15.78/2.52  fof(f62,plain,(
% 15.78/2.52    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 15.78/2.52    inference(ennf_transformation,[],[f26])).
% 15.78/2.52  
% 15.78/2.52  fof(f63,plain,(
% 15.78/2.52    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 15.78/2.52    inference(flattening,[],[f62])).
% 15.78/2.52  
% 15.78/2.52  fof(f118,plain,(
% 15.78/2.52    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 15.78/2.52    inference(cnf_transformation,[],[f63])).
% 15.78/2.52  
% 15.78/2.52  fof(f21,axiom,(
% 15.78/2.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 15.78/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.78/2.52  
% 15.78/2.52  fof(f55,plain,(
% 15.78/2.52    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 15.78/2.52    inference(ennf_transformation,[],[f21])).
% 15.78/2.52  
% 15.78/2.52  fof(f56,plain,(
% 15.78/2.52    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 15.78/2.52    inference(flattening,[],[f55])).
% 15.78/2.52  
% 15.78/2.52  fof(f111,plain,(
% 15.78/2.52    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 15.78/2.52    inference(cnf_transformation,[],[f56])).
% 15.78/2.52  
% 15.78/2.52  fof(f29,axiom,(
% 15.78/2.52    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 15.78/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.78/2.52  
% 15.78/2.52  fof(f121,plain,(
% 15.78/2.52    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 15.78/2.52    inference(cnf_transformation,[],[f29])).
% 15.78/2.52  
% 15.78/2.52  fof(f151,plain,(
% 15.78/2.52    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 15.78/2.52    inference(definition_unfolding,[],[f111,f121])).
% 15.78/2.52  
% 15.78/2.52  fof(f23,axiom,(
% 15.78/2.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 15.78/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.78/2.52  
% 15.78/2.52  fof(f58,plain,(
% 15.78/2.52    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.78/2.52    inference(ennf_transformation,[],[f23])).
% 15.78/2.52  
% 15.78/2.52  fof(f113,plain,(
% 15.78/2.52    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.78/2.52    inference(cnf_transformation,[],[f58])).
% 15.78/2.52  
% 15.78/2.52  fof(f138,plain,(
% 15.78/2.52    k2_relset_1(sK0,sK1,sK2) = sK1),
% 15.78/2.52    inference(cnf_transformation,[],[f82])).
% 15.78/2.52  
% 15.78/2.52  fof(f30,axiom,(
% 15.78/2.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 15.78/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.78/2.52  
% 15.78/2.52  fof(f66,plain,(
% 15.78/2.52    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 15.78/2.52    inference(ennf_transformation,[],[f30])).
% 15.78/2.52  
% 15.78/2.52  fof(f67,plain,(
% 15.78/2.52    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 15.78/2.52    inference(flattening,[],[f66])).
% 15.78/2.52  
% 15.78/2.52  fof(f122,plain,(
% 15.78/2.52    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 15.78/2.52    inference(cnf_transformation,[],[f67])).
% 15.78/2.52  
% 15.78/2.52  fof(f133,plain,(
% 15.78/2.52    v1_funct_2(sK2,sK0,sK1)),
% 15.78/2.52    inference(cnf_transformation,[],[f82])).
% 15.78/2.52  
% 15.78/2.52  fof(f136,plain,(
% 15.78/2.52    v1_funct_2(sK3,sK1,sK0)),
% 15.78/2.52    inference(cnf_transformation,[],[f82])).
% 15.78/2.52  
% 15.78/2.52  fof(f31,axiom,(
% 15.78/2.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 15.78/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.78/2.52  
% 15.78/2.52  fof(f68,plain,(
% 15.78/2.52    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 15.78/2.52    inference(ennf_transformation,[],[f31])).
% 15.78/2.52  
% 15.78/2.52  fof(f69,plain,(
% 15.78/2.52    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 15.78/2.52    inference(flattening,[],[f68])).
% 15.78/2.52  
% 15.78/2.52  fof(f125,plain,(
% 15.78/2.52    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X4) | k1_xboole_0 = X2 | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 15.78/2.52    inference(cnf_transformation,[],[f69])).
% 15.78/2.52  
% 15.78/2.52  fof(f141,plain,(
% 15.78/2.52    k1_xboole_0 != sK0),
% 15.78/2.52    inference(cnf_transformation,[],[f82])).
% 15.78/2.52  
% 15.78/2.52  fof(f1,axiom,(
% 15.78/2.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 15.78/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.78/2.52  
% 15.78/2.52  fof(f76,plain,(
% 15.78/2.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.78/2.52    inference(nnf_transformation,[],[f1])).
% 15.78/2.52  
% 15.78/2.52  fof(f77,plain,(
% 15.78/2.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.78/2.52    inference(flattening,[],[f76])).
% 15.78/2.52  
% 15.78/2.52  fof(f83,plain,(
% 15.78/2.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 15.78/2.52    inference(cnf_transformation,[],[f77])).
% 15.78/2.52  
% 15.78/2.52  fof(f153,plain,(
% 15.78/2.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 15.78/2.52    inference(equality_resolution,[],[f83])).
% 15.78/2.52  
% 15.78/2.52  fof(f85,plain,(
% 15.78/2.52    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 15.78/2.52    inference(cnf_transformation,[],[f77])).
% 15.78/2.52  
% 15.78/2.52  fof(f18,axiom,(
% 15.78/2.52    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 15.78/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.78/2.52  
% 15.78/2.52  fof(f107,plain,(
% 15.78/2.52    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 15.78/2.52    inference(cnf_transformation,[],[f18])).
% 15.78/2.52  
% 15.78/2.52  fof(f149,plain,(
% 15.78/2.52    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 15.78/2.52    inference(definition_unfolding,[],[f107,f121])).
% 15.78/2.52  
% 15.78/2.52  fof(f16,axiom,(
% 15.78/2.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 15.78/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.78/2.52  
% 15.78/2.52  fof(f47,plain,(
% 15.78/2.52    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 15.78/2.52    inference(ennf_transformation,[],[f16])).
% 15.78/2.52  
% 15.78/2.52  fof(f48,plain,(
% 15.78/2.52    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 15.78/2.52    inference(flattening,[],[f47])).
% 15.78/2.52  
% 15.78/2.52  fof(f103,plain,(
% 15.78/2.52    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 15.78/2.52    inference(cnf_transformation,[],[f48])).
% 15.78/2.52  
% 15.78/2.52  fof(f2,axiom,(
% 15.78/2.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 15.78/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.78/2.52  
% 15.78/2.52  fof(f78,plain,(
% 15.78/2.52    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 15.78/2.52    inference(nnf_transformation,[],[f2])).
% 15.78/2.52  
% 15.78/2.52  fof(f86,plain,(
% 15.78/2.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 15.78/2.52    inference(cnf_transformation,[],[f78])).
% 15.78/2.52  
% 15.78/2.52  fof(f3,axiom,(
% 15.78/2.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 15.78/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.78/2.52  
% 15.78/2.52  fof(f37,plain,(
% 15.78/2.52    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 15.78/2.52    inference(ennf_transformation,[],[f3])).
% 15.78/2.52  
% 15.78/2.52  fof(f88,plain,(
% 15.78/2.52    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 15.78/2.52    inference(cnf_transformation,[],[f37])).
% 15.78/2.52  
% 15.78/2.52  fof(f87,plain,(
% 15.78/2.52    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 15.78/2.52    inference(cnf_transformation,[],[f78])).
% 15.78/2.52  
% 15.78/2.52  fof(f5,axiom,(
% 15.78/2.52    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 15.78/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.78/2.52  
% 15.78/2.52  fof(f90,plain,(
% 15.78/2.52    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 15.78/2.52    inference(cnf_transformation,[],[f5])).
% 15.78/2.52  
% 15.78/2.52  fof(f4,axiom,(
% 15.78/2.52    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 15.78/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.78/2.52  
% 15.78/2.52  fof(f38,plain,(
% 15.78/2.52    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 15.78/2.52    inference(ennf_transformation,[],[f4])).
% 15.78/2.52  
% 15.78/2.52  fof(f89,plain,(
% 15.78/2.52    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 15.78/2.52    inference(cnf_transformation,[],[f38])).
% 15.78/2.52  
% 15.78/2.52  fof(f8,axiom,(
% 15.78/2.52    ! [X0] : (v1_relat_1(X0) => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)))),
% 15.78/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.78/2.52  
% 15.78/2.52  fof(f41,plain,(
% 15.78/2.52    ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 15.78/2.52    inference(ennf_transformation,[],[f8])).
% 15.78/2.52  
% 15.78/2.52  fof(f93,plain,(
% 15.78/2.52    ( ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 15.78/2.52    inference(cnf_transformation,[],[f41])).
% 15.78/2.52  
% 15.78/2.52  fof(f24,axiom,(
% 15.78/2.52    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 15.78/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.78/2.52  
% 15.78/2.52  fof(f59,plain,(
% 15.78/2.52    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.78/2.52    inference(ennf_transformation,[],[f24])).
% 15.78/2.52  
% 15.78/2.52  fof(f114,plain,(
% 15.78/2.52    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.78/2.52    inference(cnf_transformation,[],[f59])).
% 15.78/2.52  
% 15.78/2.52  fof(f22,axiom,(
% 15.78/2.52    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)))),
% 15.78/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.78/2.52  
% 15.78/2.52  fof(f57,plain,(
% 15.78/2.52    ! [X0,X1,X2,X3] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.78/2.52    inference(ennf_transformation,[],[f22])).
% 15.78/2.52  
% 15.78/2.52  fof(f112,plain,(
% 15.78/2.52    ( ! [X2,X0,X3,X1] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.78/2.52    inference(cnf_transformation,[],[f57])).
% 15.78/2.52  
% 15.78/2.52  fof(f33,axiom,(
% 15.78/2.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 15.78/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.78/2.52  
% 15.78/2.52  fof(f72,plain,(
% 15.78/2.52    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 15.78/2.52    inference(ennf_transformation,[],[f33])).
% 15.78/2.52  
% 15.78/2.52  fof(f73,plain,(
% 15.78/2.52    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 15.78/2.52    inference(flattening,[],[f72])).
% 15.78/2.52  
% 15.78/2.52  fof(f130,plain,(
% 15.78/2.52    ( ! [X2,X0,X1] : (k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 15.78/2.52    inference(cnf_transformation,[],[f73])).
% 15.78/2.52  
% 15.78/2.52  fof(f10,axiom,(
% 15.78/2.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 15.78/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.78/2.52  
% 15.78/2.52  fof(f43,plain,(
% 15.78/2.52    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 15.78/2.52    inference(ennf_transformation,[],[f10])).
% 15.78/2.52  
% 15.78/2.52  fof(f96,plain,(
% 15.78/2.52    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 15.78/2.52    inference(cnf_transformation,[],[f43])).
% 15.78/2.52  
% 15.78/2.52  fof(f20,axiom,(
% 15.78/2.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 15.78/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.78/2.52  
% 15.78/2.52  fof(f53,plain,(
% 15.78/2.52    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 15.78/2.52    inference(ennf_transformation,[],[f20])).
% 15.78/2.52  
% 15.78/2.52  fof(f54,plain,(
% 15.78/2.52    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 15.78/2.52    inference(flattening,[],[f53])).
% 15.78/2.52  
% 15.78/2.52  fof(f110,plain,(
% 15.78/2.52    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 15.78/2.52    inference(cnf_transformation,[],[f54])).
% 15.78/2.52  
% 15.78/2.52  fof(f12,axiom,(
% 15.78/2.52    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 15.78/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.78/2.52  
% 15.78/2.52  fof(f99,plain,(
% 15.78/2.52    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 15.78/2.52    inference(cnf_transformation,[],[f12])).
% 15.78/2.52  
% 15.78/2.52  fof(f144,plain,(
% 15.78/2.52    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 15.78/2.52    inference(definition_unfolding,[],[f99,f121])).
% 15.78/2.52  
% 15.78/2.52  fof(f6,axiom,(
% 15.78/2.52    ! [X0] : (v1_relat_1(X0) => k4_relat_1(k4_relat_1(X0)) = X0)),
% 15.78/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.78/2.52  
% 15.78/2.52  fof(f39,plain,(
% 15.78/2.52    ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 15.78/2.52    inference(ennf_transformation,[],[f6])).
% 15.78/2.52  
% 15.78/2.52  fof(f91,plain,(
% 15.78/2.52    ( ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 15.78/2.52    inference(cnf_transformation,[],[f39])).
% 15.78/2.52  
% 15.78/2.52  fof(f140,plain,(
% 15.78/2.52    v2_funct_1(sK2)),
% 15.78/2.52    inference(cnf_transformation,[],[f82])).
% 15.78/2.52  
% 15.78/2.52  fof(f143,plain,(
% 15.78/2.52    k2_funct_1(sK2) != sK3),
% 15.78/2.52    inference(cnf_transformation,[],[f82])).
% 15.78/2.52  
% 15.78/2.52  cnf(c_57,negated_conjecture,
% 15.78/2.52      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 15.78/2.52      inference(cnf_transformation,[],[f134]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_2330,plain,
% 15.78/2.52      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 15.78/2.52      inference(predicate_to_equality,[status(thm)],[c_57]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_54,negated_conjecture,
% 15.78/2.52      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 15.78/2.52      inference(cnf_transformation,[],[f137]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_2333,plain,
% 15.78/2.52      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 15.78/2.52      inference(predicate_to_equality,[status(thm)],[c_54]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_37,plain,
% 15.78/2.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.78/2.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 15.78/2.52      | ~ v1_funct_1(X0)
% 15.78/2.52      | ~ v1_funct_1(X3)
% 15.78/2.52      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 15.78/2.52      inference(cnf_transformation,[],[f120]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_2344,plain,
% 15.78/2.52      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 15.78/2.52      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 15.78/2.52      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.78/2.52      | v1_funct_1(X5) != iProver_top
% 15.78/2.52      | v1_funct_1(X4) != iProver_top ),
% 15.78/2.52      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_8724,plain,
% 15.78/2.52      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 15.78/2.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.78/2.52      | v1_funct_1(X2) != iProver_top
% 15.78/2.52      | v1_funct_1(sK3) != iProver_top ),
% 15.78/2.52      inference(superposition,[status(thm)],[c_2333,c_2344]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_56,negated_conjecture,
% 15.78/2.52      ( v1_funct_1(sK3) ),
% 15.78/2.52      inference(cnf_transformation,[],[f135]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_63,plain,
% 15.78/2.52      ( v1_funct_1(sK3) = iProver_top ),
% 15.78/2.52      inference(predicate_to_equality,[status(thm)],[c_56]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_9244,plain,
% 15.78/2.52      ( v1_funct_1(X2) != iProver_top
% 15.78/2.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.78/2.52      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 15.78/2.52      inference(global_propositional_subsumption,
% 15.78/2.52                [status(thm)],
% 15.78/2.52                [c_8724,c_63]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_9245,plain,
% 15.78/2.52      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 15.78/2.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.78/2.52      | v1_funct_1(X2) != iProver_top ),
% 15.78/2.52      inference(renaming,[status(thm)],[c_9244]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_9254,plain,
% 15.78/2.52      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 15.78/2.52      | v1_funct_1(sK2) != iProver_top ),
% 15.78/2.52      inference(superposition,[status(thm)],[c_2330,c_9245]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_33,plain,
% 15.78/2.52      ( ~ r2_relset_1(X0,X1,X2,X3)
% 15.78/2.52      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 15.78/2.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 15.78/2.52      | X3 = X2 ),
% 15.78/2.52      inference(cnf_transformation,[],[f115]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_52,negated_conjecture,
% 15.78/2.52      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 15.78/2.52      inference(cnf_transformation,[],[f139]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_736,plain,
% 15.78/2.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.78/2.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.78/2.52      | X3 = X0
% 15.78/2.52      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 15.78/2.52      | k6_partfun1(sK0) != X3
% 15.78/2.52      | sK0 != X2
% 15.78/2.52      | sK0 != X1 ),
% 15.78/2.52      inference(resolution_lifted,[status(thm)],[c_33,c_52]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_737,plain,
% 15.78/2.52      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 15.78/2.52      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 15.78/2.52      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 15.78/2.52      inference(unflattening,[status(thm)],[c_736]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_36,plain,
% 15.78/2.52      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 15.78/2.52      inference(cnf_transformation,[],[f119]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_745,plain,
% 15.78/2.52      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 15.78/2.52      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 15.78/2.52      inference(forward_subsumption_resolution,
% 15.78/2.52                [status(thm)],
% 15.78/2.52                [c_737,c_36]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_2325,plain,
% 15.78/2.52      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 15.78/2.52      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 15.78/2.52      inference(predicate_to_equality,[status(thm)],[c_745]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_59,negated_conjecture,
% 15.78/2.52      ( v1_funct_1(sK2) ),
% 15.78/2.52      inference(cnf_transformation,[],[f132]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_34,plain,
% 15.78/2.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.78/2.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 15.78/2.52      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 15.78/2.52      | ~ v1_funct_1(X0)
% 15.78/2.52      | ~ v1_funct_1(X3) ),
% 15.78/2.52      inference(cnf_transformation,[],[f118]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_2715,plain,
% 15.78/2.52      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 15.78/2.52      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 15.78/2.52      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 15.78/2.52      | ~ v1_funct_1(sK3)
% 15.78/2.52      | ~ v1_funct_1(sK2) ),
% 15.78/2.52      inference(instantiation,[status(thm)],[c_34]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_3370,plain,
% 15.78/2.52      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 15.78/2.52      inference(global_propositional_subsumption,
% 15.78/2.52                [status(thm)],
% 15.78/2.52                [c_2325,c_59,c_57,c_56,c_54,c_745,c_2715]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_9256,plain,
% 15.78/2.52      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 15.78/2.52      | v1_funct_1(sK2) != iProver_top ),
% 15.78/2.52      inference(light_normalisation,[status(thm)],[c_9254,c_3370]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_60,plain,
% 15.78/2.52      ( v1_funct_1(sK2) = iProver_top ),
% 15.78/2.52      inference(predicate_to_equality,[status(thm)],[c_59]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_10771,plain,
% 15.78/2.52      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 15.78/2.52      inference(global_propositional_subsumption,
% 15.78/2.52                [status(thm)],
% 15.78/2.52                [c_9256,c_60]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_28,plain,
% 15.78/2.52      ( ~ v1_funct_1(X0)
% 15.78/2.52      | ~ v1_funct_1(X1)
% 15.78/2.52      | ~ v2_funct_1(X0)
% 15.78/2.52      | ~ v1_relat_1(X0)
% 15.78/2.52      | ~ v1_relat_1(X1)
% 15.78/2.52      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
% 15.78/2.52      | k2_funct_1(X0) = X1
% 15.78/2.52      | k2_relat_1(X1) != k1_relat_1(X0) ),
% 15.78/2.52      inference(cnf_transformation,[],[f151]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_2351,plain,
% 15.78/2.52      ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 15.78/2.52      | k2_funct_1(X1) = X0
% 15.78/2.52      | k2_relat_1(X0) != k1_relat_1(X1)
% 15.78/2.52      | v1_funct_1(X1) != iProver_top
% 15.78/2.52      | v1_funct_1(X0) != iProver_top
% 15.78/2.52      | v2_funct_1(X1) != iProver_top
% 15.78/2.52      | v1_relat_1(X1) != iProver_top
% 15.78/2.52      | v1_relat_1(X0) != iProver_top ),
% 15.78/2.52      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_10773,plain,
% 15.78/2.52      ( k2_funct_1(sK3) = sK2
% 15.78/2.52      | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
% 15.78/2.52      | k2_relat_1(sK2) != k1_relat_1(sK3)
% 15.78/2.52      | v1_funct_1(sK3) != iProver_top
% 15.78/2.52      | v1_funct_1(sK2) != iProver_top
% 15.78/2.52      | v2_funct_1(sK3) != iProver_top
% 15.78/2.52      | v1_relat_1(sK3) != iProver_top
% 15.78/2.52      | v1_relat_1(sK2) != iProver_top ),
% 15.78/2.52      inference(superposition,[status(thm)],[c_10771,c_2351]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_30,plain,
% 15.78/2.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.78/2.52      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 15.78/2.52      inference(cnf_transformation,[],[f113]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_2349,plain,
% 15.78/2.52      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 15.78/2.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 15.78/2.52      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_4298,plain,
% 15.78/2.52      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 15.78/2.52      inference(superposition,[status(thm)],[c_2330,c_2349]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_53,negated_conjecture,
% 15.78/2.52      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 15.78/2.52      inference(cnf_transformation,[],[f138]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_4299,plain,
% 15.78/2.52      ( k2_relat_1(sK2) = sK1 ),
% 15.78/2.52      inference(light_normalisation,[status(thm)],[c_4298,c_53]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_4297,plain,
% 15.78/2.52      ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 15.78/2.52      inference(superposition,[status(thm)],[c_2333,c_2349]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_38,plain,
% 15.78/2.52      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 15.78/2.52      | ~ v1_funct_2(X2,X0,X1)
% 15.78/2.52      | ~ v1_funct_2(X3,X1,X0)
% 15.78/2.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 15.78/2.52      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 15.78/2.52      | ~ v1_funct_1(X2)
% 15.78/2.52      | ~ v1_funct_1(X3)
% 15.78/2.52      | k2_relset_1(X1,X0,X3) = X0 ),
% 15.78/2.52      inference(cnf_transformation,[],[f122]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_749,plain,
% 15.78/2.52      ( ~ v1_funct_2(X0,X1,X2)
% 15.78/2.52      | ~ v1_funct_2(X3,X2,X1)
% 15.78/2.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 15.78/2.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.78/2.52      | ~ v1_funct_1(X0)
% 15.78/2.52      | ~ v1_funct_1(X3)
% 15.78/2.52      | k1_partfun1(X2,X1,X1,X2,X3,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 15.78/2.52      | k2_relset_1(X1,X2,X0) = X2
% 15.78/2.52      | k6_partfun1(X2) != k6_partfun1(sK0)
% 15.78/2.52      | sK0 != X2 ),
% 15.78/2.52      inference(resolution_lifted,[status(thm)],[c_38,c_52]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_750,plain,
% 15.78/2.52      ( ~ v1_funct_2(X0,X1,sK0)
% 15.78/2.52      | ~ v1_funct_2(X2,sK0,X1)
% 15.78/2.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 15.78/2.52      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 15.78/2.52      | ~ v1_funct_1(X0)
% 15.78/2.52      | ~ v1_funct_1(X2)
% 15.78/2.52      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 15.78/2.52      | k2_relset_1(X1,sK0,X0) = sK0
% 15.78/2.52      | k6_partfun1(sK0) != k6_partfun1(sK0) ),
% 15.78/2.52      inference(unflattening,[status(thm)],[c_749]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_855,plain,
% 15.78/2.52      ( ~ v1_funct_2(X0,X1,sK0)
% 15.78/2.52      | ~ v1_funct_2(X2,sK0,X1)
% 15.78/2.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 15.78/2.52      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 15.78/2.52      | ~ v1_funct_1(X0)
% 15.78/2.52      | ~ v1_funct_1(X2)
% 15.78/2.52      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 15.78/2.52      | k2_relset_1(X1,sK0,X0) = sK0 ),
% 15.78/2.52      inference(equality_resolution_simp,[status(thm)],[c_750]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_2324,plain,
% 15.78/2.52      ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 15.78/2.52      | k2_relset_1(X0,sK0,X2) = sK0
% 15.78/2.52      | v1_funct_2(X2,X0,sK0) != iProver_top
% 15.78/2.52      | v1_funct_2(X1,sK0,X0) != iProver_top
% 15.78/2.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 15.78/2.52      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 15.78/2.52      | v1_funct_1(X2) != iProver_top
% 15.78/2.52      | v1_funct_1(X1) != iProver_top ),
% 15.78/2.52      inference(predicate_to_equality,[status(thm)],[c_855]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_2950,plain,
% 15.78/2.52      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 15.78/2.52      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 15.78/2.52      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 15.78/2.52      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 15.78/2.52      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 15.78/2.52      | v1_funct_1(sK3) != iProver_top
% 15.78/2.52      | v1_funct_1(sK2) != iProver_top ),
% 15.78/2.52      inference(equality_resolution,[status(thm)],[c_2324]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_58,negated_conjecture,
% 15.78/2.52      ( v1_funct_2(sK2,sK0,sK1) ),
% 15.78/2.52      inference(cnf_transformation,[],[f133]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_61,plain,
% 15.78/2.52      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 15.78/2.52      inference(predicate_to_equality,[status(thm)],[c_58]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_62,plain,
% 15.78/2.52      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 15.78/2.52      inference(predicate_to_equality,[status(thm)],[c_57]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_55,negated_conjecture,
% 15.78/2.52      ( v1_funct_2(sK3,sK1,sK0) ),
% 15.78/2.52      inference(cnf_transformation,[],[f136]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_64,plain,
% 15.78/2.52      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 15.78/2.52      inference(predicate_to_equality,[status(thm)],[c_55]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_65,plain,
% 15.78/2.52      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 15.78/2.52      inference(predicate_to_equality,[status(thm)],[c_54]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_3377,plain,
% 15.78/2.52      ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 15.78/2.52      inference(global_propositional_subsumption,
% 15.78/2.52                [status(thm)],
% 15.78/2.52                [c_2950,c_60,c_61,c_62,c_63,c_64,c_65]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_4300,plain,
% 15.78/2.52      ( k2_relat_1(sK3) = sK0 ),
% 15.78/2.52      inference(light_normalisation,[status(thm)],[c_4297,c_3377]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_10779,plain,
% 15.78/2.52      ( k2_funct_1(sK3) = sK2
% 15.78/2.52      | k6_partfun1(sK0) != k6_partfun1(sK0)
% 15.78/2.52      | k1_relat_1(sK3) != sK1
% 15.78/2.52      | v1_funct_1(sK3) != iProver_top
% 15.78/2.52      | v1_funct_1(sK2) != iProver_top
% 15.78/2.52      | v2_funct_1(sK3) != iProver_top
% 15.78/2.52      | v1_relat_1(sK3) != iProver_top
% 15.78/2.52      | v1_relat_1(sK2) != iProver_top ),
% 15.78/2.52      inference(light_normalisation,
% 15.78/2.52                [status(thm)],
% 15.78/2.52                [c_10773,c_4299,c_4300]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_10780,plain,
% 15.78/2.52      ( k2_funct_1(sK3) = sK2
% 15.78/2.52      | k1_relat_1(sK3) != sK1
% 15.78/2.52      | v1_funct_1(sK3) != iProver_top
% 15.78/2.52      | v1_funct_1(sK2) != iProver_top
% 15.78/2.52      | v2_funct_1(sK3) != iProver_top
% 15.78/2.52      | v1_relat_1(sK3) != iProver_top
% 15.78/2.52      | v1_relat_1(sK2) != iProver_top ),
% 15.78/2.52      inference(equality_resolution_simp,[status(thm)],[c_10779]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_40,plain,
% 15.78/2.52      ( ~ v1_funct_2(X0,X1,X2)
% 15.78/2.52      | ~ v1_funct_2(X3,X4,X1)
% 15.78/2.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 15.78/2.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.78/2.52      | ~ v1_funct_1(X0)
% 15.78/2.52      | ~ v1_funct_1(X3)
% 15.78/2.52      | v2_funct_1(X0)
% 15.78/2.52      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 15.78/2.52      | k2_relset_1(X4,X1,X3) != X1
% 15.78/2.52      | k1_xboole_0 = X2 ),
% 15.78/2.52      inference(cnf_transformation,[],[f125]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_2342,plain,
% 15.78/2.52      ( k2_relset_1(X0,X1,X2) != X1
% 15.78/2.52      | k1_xboole_0 = X3
% 15.78/2.52      | v1_funct_2(X4,X1,X3) != iProver_top
% 15.78/2.52      | v1_funct_2(X2,X0,X1) != iProver_top
% 15.78/2.52      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
% 15.78/2.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.78/2.52      | v1_funct_1(X4) != iProver_top
% 15.78/2.52      | v1_funct_1(X2) != iProver_top
% 15.78/2.52      | v2_funct_1(X4) = iProver_top
% 15.78/2.52      | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top ),
% 15.78/2.52      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_9409,plain,
% 15.78/2.52      ( k1_xboole_0 = X0
% 15.78/2.52      | v1_funct_2(X1,sK1,X0) != iProver_top
% 15.78/2.52      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 15.78/2.52      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 15.78/2.52      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 15.78/2.52      | v1_funct_1(X1) != iProver_top
% 15.78/2.52      | v1_funct_1(sK2) != iProver_top
% 15.78/2.52      | v2_funct_1(X1) = iProver_top
% 15.78/2.52      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
% 15.78/2.52      inference(superposition,[status(thm)],[c_53,c_2342]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_9436,plain,
% 15.78/2.52      ( v1_funct_1(X1) != iProver_top
% 15.78/2.52      | v1_funct_2(X1,sK1,X0) != iProver_top
% 15.78/2.52      | k1_xboole_0 = X0
% 15.78/2.52      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 15.78/2.52      | v2_funct_1(X1) = iProver_top
% 15.78/2.52      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
% 15.78/2.52      inference(global_propositional_subsumption,
% 15.78/2.52                [status(thm)],
% 15.78/2.52                [c_9409,c_60,c_61,c_62]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_9437,plain,
% 15.78/2.52      ( k1_xboole_0 = X0
% 15.78/2.52      | v1_funct_2(X1,sK1,X0) != iProver_top
% 15.78/2.52      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 15.78/2.52      | v1_funct_1(X1) != iProver_top
% 15.78/2.52      | v2_funct_1(X1) = iProver_top
% 15.78/2.52      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
% 15.78/2.52      inference(renaming,[status(thm)],[c_9436]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_9440,plain,
% 15.78/2.52      ( sK0 = k1_xboole_0
% 15.78/2.52      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 15.78/2.52      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 15.78/2.52      | v1_funct_1(sK3) != iProver_top
% 15.78/2.52      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 15.78/2.52      | v2_funct_1(sK3) = iProver_top ),
% 15.78/2.52      inference(superposition,[status(thm)],[c_3370,c_9437]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_50,negated_conjecture,
% 15.78/2.52      ( k1_xboole_0 != sK0 ),
% 15.78/2.52      inference(cnf_transformation,[],[f141]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_2,plain,
% 15.78/2.52      ( r1_tarski(X0,X0) ),
% 15.78/2.52      inference(cnf_transformation,[],[f153]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_192,plain,
% 15.78/2.52      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 15.78/2.52      inference(instantiation,[status(thm)],[c_2]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_0,plain,
% 15.78/2.52      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 15.78/2.52      inference(cnf_transformation,[],[f85]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_196,plain,
% 15.78/2.52      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 15.78/2.52      | k1_xboole_0 = k1_xboole_0 ),
% 15.78/2.52      inference(instantiation,[status(thm)],[c_0]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_1248,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_2487,plain,
% 15.78/2.52      ( sK0 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK0 ),
% 15.78/2.52      inference(instantiation,[status(thm)],[c_1248]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_2488,plain,
% 15.78/2.52      ( sK0 != k1_xboole_0
% 15.78/2.52      | k1_xboole_0 = sK0
% 15.78/2.52      | k1_xboole_0 != k1_xboole_0 ),
% 15.78/2.52      inference(instantiation,[status(thm)],[c_2487]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_23,plain,
% 15.78/2.52      ( v2_funct_1(k6_partfun1(X0)) ),
% 15.78/2.52      inference(cnf_transformation,[],[f149]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_5340,plain,
% 15.78/2.52      ( v2_funct_1(k6_partfun1(sK0)) ),
% 15.78/2.52      inference(instantiation,[status(thm)],[c_23]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_5341,plain,
% 15.78/2.52      ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
% 15.78/2.52      inference(predicate_to_equality,[status(thm)],[c_5340]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_10545,plain,
% 15.78/2.52      ( v2_funct_1(sK3) = iProver_top ),
% 15.78/2.52      inference(global_propositional_subsumption,
% 15.78/2.52                [status(thm)],
% 15.78/2.52                [c_9440,c_63,c_64,c_65,c_50,c_192,c_196,c_2488,c_5341]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_2331,plain,
% 15.78/2.52      ( v1_funct_1(sK3) = iProver_top ),
% 15.78/2.52      inference(predicate_to_equality,[status(thm)],[c_56]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_20,plain,
% 15.78/2.52      ( ~ v1_funct_1(X0)
% 15.78/2.52      | ~ v2_funct_1(X0)
% 15.78/2.52      | ~ v1_relat_1(X0)
% 15.78/2.52      | k2_funct_1(X0) = k4_relat_1(X0) ),
% 15.78/2.52      inference(cnf_transformation,[],[f103]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_2359,plain,
% 15.78/2.52      ( k2_funct_1(X0) = k4_relat_1(X0)
% 15.78/2.52      | v1_funct_1(X0) != iProver_top
% 15.78/2.52      | v2_funct_1(X0) != iProver_top
% 15.78/2.52      | v1_relat_1(X0) != iProver_top ),
% 15.78/2.52      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_7361,plain,
% 15.78/2.52      ( k2_funct_1(sK3) = k4_relat_1(sK3)
% 15.78/2.52      | v2_funct_1(sK3) != iProver_top
% 15.78/2.52      | v1_relat_1(sK3) != iProver_top ),
% 15.78/2.52      inference(superposition,[status(thm)],[c_2331,c_2359]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_4,plain,
% 15.78/2.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 15.78/2.52      inference(cnf_transformation,[],[f86]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_2371,plain,
% 15.78/2.52      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 15.78/2.52      | r1_tarski(X0,X1) = iProver_top ),
% 15.78/2.52      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_4115,plain,
% 15.78/2.52      ( r1_tarski(sK3,k2_zfmisc_1(sK1,sK0)) = iProver_top ),
% 15.78/2.52      inference(superposition,[status(thm)],[c_2333,c_2371]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_5,plain,
% 15.78/2.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.78/2.52      | ~ v1_relat_1(X1)
% 15.78/2.52      | v1_relat_1(X0) ),
% 15.78/2.52      inference(cnf_transformation,[],[f88]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_3,plain,
% 15.78/2.52      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 15.78/2.52      inference(cnf_transformation,[],[f87]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_425,plain,
% 15.78/2.52      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 15.78/2.52      inference(prop_impl,[status(thm)],[c_3]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_426,plain,
% 15.78/2.52      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 15.78/2.52      inference(renaming,[status(thm)],[c_425]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_520,plain,
% 15.78/2.52      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 15.78/2.52      inference(bin_hyper_res,[status(thm)],[c_5,c_426]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_3466,plain,
% 15.78/2.52      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 15.78/2.52      | v1_relat_1(X0)
% 15.78/2.52      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 15.78/2.52      inference(instantiation,[status(thm)],[c_520]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_4900,plain,
% 15.78/2.52      ( ~ r1_tarski(sK3,k2_zfmisc_1(sK1,sK0))
% 15.78/2.52      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
% 15.78/2.52      | v1_relat_1(sK3) ),
% 15.78/2.52      inference(instantiation,[status(thm)],[c_3466]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_4901,plain,
% 15.78/2.52      ( r1_tarski(sK3,k2_zfmisc_1(sK1,sK0)) != iProver_top
% 15.78/2.52      | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 15.78/2.52      | v1_relat_1(sK3) = iProver_top ),
% 15.78/2.52      inference(predicate_to_equality,[status(thm)],[c_4900]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_7,plain,
% 15.78/2.52      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 15.78/2.52      inference(cnf_transformation,[],[f90]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_5279,plain,
% 15.78/2.52      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
% 15.78/2.52      inference(instantiation,[status(thm)],[c_7]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_5280,plain,
% 15.78/2.52      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
% 15.78/2.52      inference(predicate_to_equality,[status(thm)],[c_5279]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_7708,plain,
% 15.78/2.52      ( v2_funct_1(sK3) != iProver_top
% 15.78/2.52      | k2_funct_1(sK3) = k4_relat_1(sK3) ),
% 15.78/2.52      inference(global_propositional_subsumption,
% 15.78/2.52                [status(thm)],
% 15.78/2.52                [c_7361,c_4115,c_4901,c_5280]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_7709,plain,
% 15.78/2.52      ( k2_funct_1(sK3) = k4_relat_1(sK3)
% 15.78/2.52      | v2_funct_1(sK3) != iProver_top ),
% 15.78/2.52      inference(renaming,[status(thm)],[c_7708]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_10551,plain,
% 15.78/2.52      ( k2_funct_1(sK3) = k4_relat_1(sK3) ),
% 15.78/2.52      inference(superposition,[status(thm)],[c_10545,c_7709]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_10781,plain,
% 15.78/2.52      ( k1_relat_1(sK3) != sK1
% 15.78/2.52      | k4_relat_1(sK3) = sK2
% 15.78/2.52      | v1_funct_1(sK3) != iProver_top
% 15.78/2.52      | v1_funct_1(sK2) != iProver_top
% 15.78/2.52      | v2_funct_1(sK3) != iProver_top
% 15.78/2.52      | v1_relat_1(sK3) != iProver_top
% 15.78/2.52      | v1_relat_1(sK2) != iProver_top ),
% 15.78/2.52      inference(demodulation,[status(thm)],[c_10780,c_10551]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_6,plain,
% 15.78/2.52      ( ~ v1_relat_1(X0) | v1_relat_1(k4_relat_1(X0)) ),
% 15.78/2.52      inference(cnf_transformation,[],[f89]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_10427,plain,
% 15.78/2.52      ( v1_relat_1(k4_relat_1(sK3)) | ~ v1_relat_1(sK3) ),
% 15.78/2.52      inference(instantiation,[status(thm)],[c_6]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_10435,plain,
% 15.78/2.52      ( v1_relat_1(k4_relat_1(sK3)) = iProver_top
% 15.78/2.52      | v1_relat_1(sK3) != iProver_top ),
% 15.78/2.52      inference(predicate_to_equality,[status(thm)],[c_10427]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_2369,plain,
% 15.78/2.52      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 15.78/2.52      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_4116,plain,
% 15.78/2.52      ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 15.78/2.52      inference(superposition,[status(thm)],[c_2330,c_2371]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_2327,plain,
% 15.78/2.52      ( r1_tarski(X0,X1) != iProver_top
% 15.78/2.52      | v1_relat_1(X1) != iProver_top
% 15.78/2.52      | v1_relat_1(X0) = iProver_top ),
% 15.78/2.52      inference(predicate_to_equality,[status(thm)],[c_520]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_17469,plain,
% 15.78/2.52      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 15.78/2.52      | v1_relat_1(sK2) = iProver_top ),
% 15.78/2.52      inference(superposition,[status(thm)],[c_4116,c_2327]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_18066,plain,
% 15.78/2.52      ( v1_relat_1(sK2) = iProver_top ),
% 15.78/2.52      inference(superposition,[status(thm)],[c_2369,c_17469]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_17468,plain,
% 15.78/2.52      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 15.78/2.52      | v1_relat_1(sK3) = iProver_top ),
% 15.78/2.52      inference(superposition,[status(thm)],[c_4115,c_2327]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_18022,plain,
% 15.78/2.52      ( v1_relat_1(sK3) = iProver_top ),
% 15.78/2.52      inference(global_propositional_subsumption,
% 15.78/2.52                [status(thm)],
% 15.78/2.52                [c_17468,c_4115,c_4901,c_5280]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_10,plain,
% 15.78/2.52      ( ~ v1_relat_1(X0)
% 15.78/2.52      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
% 15.78/2.52      inference(cnf_transformation,[],[f93]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_2366,plain,
% 15.78/2.52      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
% 15.78/2.52      | v1_relat_1(X0) != iProver_top ),
% 15.78/2.52      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_18039,plain,
% 15.78/2.52      ( k10_relat_1(sK3,k2_relat_1(sK3)) = k1_relat_1(sK3) ),
% 15.78/2.52      inference(superposition,[status(thm)],[c_18022,c_2366]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_18048,plain,
% 15.78/2.52      ( k10_relat_1(sK3,sK0) = k1_relat_1(sK3) ),
% 15.78/2.52      inference(light_normalisation,[status(thm)],[c_18039,c_4300]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_31,plain,
% 15.78/2.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.78/2.52      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 15.78/2.52      inference(cnf_transformation,[],[f114]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_2348,plain,
% 15.78/2.52      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 15.78/2.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 15.78/2.52      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_5319,plain,
% 15.78/2.52      ( k8_relset_1(sK1,sK0,sK3,X0) = k10_relat_1(sK3,X0) ),
% 15.78/2.52      inference(superposition,[status(thm)],[c_2333,c_2348]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_29,plain,
% 15.78/2.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.78/2.52      | m1_subset_1(k8_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X1)) ),
% 15.78/2.52      inference(cnf_transformation,[],[f112]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_2350,plain,
% 15.78/2.52      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 15.78/2.52      | m1_subset_1(k8_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X1)) = iProver_top ),
% 15.78/2.52      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_5450,plain,
% 15.78/2.52      ( m1_subset_1(k10_relat_1(sK3,X0),k1_zfmisc_1(sK1)) = iProver_top
% 15.78/2.52      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 15.78/2.52      inference(superposition,[status(thm)],[c_5319,c_2350]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_5568,plain,
% 15.78/2.52      ( m1_subset_1(k10_relat_1(sK3,X0),k1_zfmisc_1(sK1)) = iProver_top ),
% 15.78/2.52      inference(global_propositional_subsumption,
% 15.78/2.52                [status(thm)],
% 15.78/2.52                [c_5450,c_65]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_5574,plain,
% 15.78/2.52      ( r1_tarski(k10_relat_1(sK3,X0),sK1) = iProver_top ),
% 15.78/2.52      inference(superposition,[status(thm)],[c_5568,c_2371]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_2374,plain,
% 15.78/2.52      ( X0 = X1
% 15.78/2.52      | r1_tarski(X0,X1) != iProver_top
% 15.78/2.52      | r1_tarski(X1,X0) != iProver_top ),
% 15.78/2.52      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_5653,plain,
% 15.78/2.52      ( k10_relat_1(sK3,X0) = sK1
% 15.78/2.52      | r1_tarski(sK1,k10_relat_1(sK3,X0)) != iProver_top ),
% 15.78/2.52      inference(superposition,[status(thm)],[c_5574,c_2374]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_22679,plain,
% 15.78/2.52      ( k10_relat_1(sK3,sK0) = sK1
% 15.78/2.52      | r1_tarski(sK1,k1_relat_1(sK3)) != iProver_top ),
% 15.78/2.52      inference(superposition,[status(thm)],[c_18048,c_5653]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_22682,plain,
% 15.78/2.52      ( k1_relat_1(sK3) = sK1
% 15.78/2.52      | r1_tarski(sK1,k1_relat_1(sK3)) != iProver_top ),
% 15.78/2.52      inference(demodulation,[status(thm)],[c_22679,c_18048]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_47,plain,
% 15.78/2.52      ( ~ v1_funct_2(X0,X1,X2)
% 15.78/2.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.78/2.52      | ~ v1_funct_1(X0)
% 15.78/2.52      | ~ v2_funct_1(X0)
% 15.78/2.52      | k2_relset_1(X1,X2,X0) != X2
% 15.78/2.52      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 15.78/2.52      | k1_xboole_0 = X2 ),
% 15.78/2.52      inference(cnf_transformation,[],[f130]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_2335,plain,
% 15.78/2.52      ( k2_relset_1(X0,X1,X2) != X1
% 15.78/2.52      | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
% 15.78/2.52      | k1_xboole_0 = X1
% 15.78/2.52      | v1_funct_2(X2,X0,X1) != iProver_top
% 15.78/2.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.78/2.52      | v1_funct_1(X2) != iProver_top
% 15.78/2.52      | v2_funct_1(X2) != iProver_top ),
% 15.78/2.52      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_4037,plain,
% 15.78/2.52      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
% 15.78/2.52      | sK0 = k1_xboole_0
% 15.78/2.52      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 15.78/2.52      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 15.78/2.52      | v1_funct_1(sK3) != iProver_top
% 15.78/2.52      | v2_funct_1(sK3) != iProver_top ),
% 15.78/2.52      inference(superposition,[status(thm)],[c_3377,c_2335]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_4109,plain,
% 15.78/2.52      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
% 15.78/2.52      | v2_funct_1(sK3) != iProver_top ),
% 15.78/2.52      inference(global_propositional_subsumption,
% 15.78/2.52                [status(thm)],
% 15.78/2.52                [c_4037,c_63,c_64,c_65,c_50,c_192,c_196,c_2488]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_10553,plain,
% 15.78/2.52      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
% 15.78/2.52      inference(superposition,[status(thm)],[c_10545,c_4109]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_10555,plain,
% 15.78/2.52      ( k5_relat_1(sK3,k4_relat_1(sK3)) = k6_partfun1(sK1) ),
% 15.78/2.52      inference(demodulation,[status(thm)],[c_10551,c_10553]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_13,plain,
% 15.78/2.52      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
% 15.78/2.52      | ~ v1_relat_1(X0)
% 15.78/2.52      | ~ v1_relat_1(X1) ),
% 15.78/2.52      inference(cnf_transformation,[],[f96]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_2363,plain,
% 15.78/2.52      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
% 15.78/2.52      | v1_relat_1(X0) != iProver_top
% 15.78/2.52      | v1_relat_1(X1) != iProver_top ),
% 15.78/2.52      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_23257,plain,
% 15.78/2.52      ( r1_tarski(k2_relat_1(k6_partfun1(sK1)),k2_relat_1(k4_relat_1(sK3))) = iProver_top
% 15.78/2.52      | v1_relat_1(k4_relat_1(sK3)) != iProver_top
% 15.78/2.52      | v1_relat_1(sK3) != iProver_top ),
% 15.78/2.52      inference(superposition,[status(thm)],[c_10555,c_2363]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_26,plain,
% 15.78/2.52      ( ~ v1_funct_1(X0)
% 15.78/2.52      | ~ v2_funct_1(X0)
% 15.78/2.52      | ~ v1_relat_1(X0)
% 15.78/2.52      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 15.78/2.52      inference(cnf_transformation,[],[f110]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_2353,plain,
% 15.78/2.52      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 15.78/2.52      | v1_funct_1(X0) != iProver_top
% 15.78/2.52      | v2_funct_1(X0) != iProver_top
% 15.78/2.52      | v1_relat_1(X0) != iProver_top ),
% 15.78/2.52      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_7989,plain,
% 15.78/2.52      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
% 15.78/2.52      | v2_funct_1(sK3) != iProver_top
% 15.78/2.52      | v1_relat_1(sK3) != iProver_top ),
% 15.78/2.52      inference(superposition,[status(thm)],[c_2331,c_2353]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_8744,plain,
% 15.78/2.52      ( v2_funct_1(sK3) != iProver_top
% 15.78/2.52      | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 15.78/2.52      inference(global_propositional_subsumption,
% 15.78/2.52                [status(thm)],
% 15.78/2.52                [c_7989,c_4115,c_4901,c_5280]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_8745,plain,
% 15.78/2.52      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
% 15.78/2.52      | v2_funct_1(sK3) != iProver_top ),
% 15.78/2.52      inference(renaming,[status(thm)],[c_8744]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_10550,plain,
% 15.78/2.52      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 15.78/2.52      inference(superposition,[status(thm)],[c_10545,c_8745]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_10556,plain,
% 15.78/2.52      ( k2_relat_1(k4_relat_1(sK3)) = k1_relat_1(sK3) ),
% 15.78/2.52      inference(demodulation,[status(thm)],[c_10550,c_10551]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_23258,plain,
% 15.78/2.52      ( r1_tarski(k2_relat_1(k6_partfun1(sK1)),k1_relat_1(sK3)) = iProver_top
% 15.78/2.52      | v1_relat_1(k4_relat_1(sK3)) != iProver_top
% 15.78/2.52      | v1_relat_1(sK3) != iProver_top ),
% 15.78/2.52      inference(light_normalisation,[status(thm)],[c_23257,c_10556]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_15,plain,
% 15.78/2.52      ( k2_relat_1(k6_partfun1(X0)) = X0 ),
% 15.78/2.52      inference(cnf_transformation,[],[f144]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_23259,plain,
% 15.78/2.52      ( r1_tarski(sK1,k1_relat_1(sK3)) = iProver_top
% 15.78/2.52      | v1_relat_1(k4_relat_1(sK3)) != iProver_top
% 15.78/2.52      | v1_relat_1(sK3) != iProver_top ),
% 15.78/2.52      inference(demodulation,[status(thm)],[c_23258,c_15]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_60283,plain,
% 15.78/2.52      ( k4_relat_1(sK3) = sK2 ),
% 15.78/2.52      inference(global_propositional_subsumption,
% 15.78/2.52                [status(thm)],
% 15.78/2.52                [c_10781,c_60,c_63,c_64,c_65,c_50,c_192,c_196,c_2488,
% 15.78/2.52                 c_4115,c_4901,c_5280,c_5341,c_9440,c_10435,c_18066,
% 15.78/2.52                 c_22682,c_23259]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_8,plain,
% 15.78/2.52      ( ~ v1_relat_1(X0) | k4_relat_1(k4_relat_1(X0)) = X0 ),
% 15.78/2.52      inference(cnf_transformation,[],[f91]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_2368,plain,
% 15.78/2.52      ( k4_relat_1(k4_relat_1(X0)) = X0 | v1_relat_1(X0) != iProver_top ),
% 15.78/2.52      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_18044,plain,
% 15.78/2.52      ( k4_relat_1(k4_relat_1(sK3)) = sK3 ),
% 15.78/2.52      inference(superposition,[status(thm)],[c_18022,c_2368]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_60334,plain,
% 15.78/2.52      ( k4_relat_1(sK2) = sK3 ),
% 15.78/2.52      inference(demodulation,[status(thm)],[c_60283,c_18044]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_2328,plain,
% 15.78/2.52      ( v1_funct_1(sK2) = iProver_top ),
% 15.78/2.52      inference(predicate_to_equality,[status(thm)],[c_59]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_7362,plain,
% 15.78/2.52      ( k2_funct_1(sK2) = k4_relat_1(sK2)
% 15.78/2.52      | v2_funct_1(sK2) != iProver_top
% 15.78/2.52      | v1_relat_1(sK2) != iProver_top ),
% 15.78/2.52      inference(superposition,[status(thm)],[c_2328,c_2359]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_51,negated_conjecture,
% 15.78/2.52      ( v2_funct_1(sK2) ),
% 15.78/2.52      inference(cnf_transformation,[],[f140]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_67,plain,
% 15.78/2.52      ( v2_funct_1(sK2) = iProver_top ),
% 15.78/2.52      inference(predicate_to_equality,[status(thm)],[c_51]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_4307,plain,
% 15.78/2.52      ( ~ v1_funct_1(sK2)
% 15.78/2.52      | ~ v2_funct_1(sK2)
% 15.78/2.52      | ~ v1_relat_1(sK2)
% 15.78/2.52      | k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 15.78/2.52      inference(instantiation,[status(thm)],[c_20]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_4308,plain,
% 15.78/2.52      ( k2_funct_1(sK2) = k4_relat_1(sK2)
% 15.78/2.52      | v1_funct_1(sK2) != iProver_top
% 15.78/2.52      | v2_funct_1(sK2) != iProver_top
% 15.78/2.52      | v1_relat_1(sK2) != iProver_top ),
% 15.78/2.52      inference(predicate_to_equality,[status(thm)],[c_4307]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_7713,plain,
% 15.78/2.52      ( k2_funct_1(sK2) = k4_relat_1(sK2)
% 15.78/2.52      | v1_relat_1(sK2) != iProver_top ),
% 15.78/2.52      inference(global_propositional_subsumption,
% 15.78/2.52                [status(thm)],
% 15.78/2.52                [c_7362,c_60,c_67,c_4308]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_18811,plain,
% 15.78/2.52      ( k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 15.78/2.52      inference(superposition,[status(thm)],[c_18066,c_7713]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_48,negated_conjecture,
% 15.78/2.52      ( k2_funct_1(sK2) != sK3 ),
% 15.78/2.52      inference(cnf_transformation,[],[f143]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(c_19105,plain,
% 15.78/2.52      ( k4_relat_1(sK2) != sK3 ),
% 15.78/2.52      inference(demodulation,[status(thm)],[c_18811,c_48]) ).
% 15.78/2.52  
% 15.78/2.52  cnf(contradiction,plain,
% 15.78/2.52      ( $false ),
% 15.78/2.52      inference(minisat,[status(thm)],[c_60334,c_19105]) ).
% 15.78/2.52  
% 15.78/2.52  
% 15.78/2.52  % SZS output end CNFRefutation for theBenchmark.p
% 15.78/2.52  
% 15.78/2.52  ------                               Statistics
% 15.78/2.52  
% 15.78/2.52  ------ General
% 15.78/2.52  
% 15.78/2.52  abstr_ref_over_cycles:                  0
% 15.78/2.52  abstr_ref_under_cycles:                 0
% 15.78/2.52  gc_basic_clause_elim:                   0
% 15.78/2.52  forced_gc_time:                         0
% 15.78/2.52  parsing_time:                           0.008
% 15.78/2.52  unif_index_cands_time:                  0.
% 15.78/2.52  unif_index_add_time:                    0.
% 15.78/2.52  orderings_time:                         0.
% 15.78/2.52  out_proof_time:                         0.025
% 15.78/2.52  total_time:                             1.991
% 15.78/2.52  num_of_symbols:                         56
% 15.78/2.52  num_of_terms:                           75703
% 15.78/2.52  
% 15.78/2.52  ------ Preprocessing
% 15.78/2.52  
% 15.78/2.52  num_of_splits:                          0
% 15.78/2.52  num_of_split_atoms:                     0
% 15.78/2.52  num_of_reused_defs:                     0
% 15.78/2.52  num_eq_ax_congr_red:                    15
% 15.78/2.52  num_of_sem_filtered_clauses:            1
% 15.78/2.52  num_of_subtypes:                        0
% 15.78/2.52  monotx_restored_types:                  0
% 15.78/2.52  sat_num_of_epr_types:                   0
% 15.78/2.52  sat_num_of_non_cyclic_types:            0
% 15.78/2.52  sat_guarded_non_collapsed_types:        0
% 15.78/2.52  num_pure_diseq_elim:                    0
% 15.78/2.52  simp_replaced_by:                       0
% 15.78/2.52  res_preprocessed:                       274
% 15.78/2.52  prep_upred:                             0
% 15.78/2.52  prep_unflattend:                        12
% 15.78/2.52  smt_new_axioms:                         0
% 15.78/2.52  pred_elim_cands:                        6
% 15.78/2.52  pred_elim:                              1
% 15.78/2.52  pred_elim_cl:                           1
% 15.78/2.52  pred_elim_cycles:                       3
% 15.78/2.52  merged_defs:                            8
% 15.78/2.52  merged_defs_ncl:                        0
% 15.78/2.52  bin_hyper_res:                          9
% 15.78/2.52  prep_cycles:                            4
% 15.78/2.52  pred_elim_time:                         0.004
% 15.78/2.52  splitting_time:                         0.
% 15.78/2.52  sem_filter_time:                        0.
% 15.78/2.52  monotx_time:                            0.
% 15.78/2.52  subtype_inf_time:                       0.
% 15.78/2.52  
% 15.78/2.52  ------ Problem properties
% 15.78/2.52  
% 15.78/2.52  clauses:                                58
% 15.78/2.52  conjectures:                            11
% 15.78/2.52  epr:                                    10
% 15.78/2.52  horn:                                   54
% 15.78/2.52  ground:                                 12
% 15.78/2.52  unary:                                  19
% 15.78/2.52  binary:                                 14
% 15.78/2.52  lits:                                   190
% 15.78/2.52  lits_eq:                                46
% 15.78/2.52  fd_pure:                                0
% 15.78/2.52  fd_pseudo:                              0
% 15.78/2.52  fd_cond:                                4
% 15.78/2.52  fd_pseudo_cond:                         2
% 15.78/2.52  ac_symbols:                             0
% 15.78/2.52  
% 15.78/2.52  ------ Propositional Solver
% 15.78/2.52  
% 15.78/2.52  prop_solver_calls:                      42
% 15.78/2.52  prop_fast_solver_calls:                 4499
% 15.78/2.52  smt_solver_calls:                       0
% 15.78/2.52  smt_fast_solver_calls:                  0
% 15.78/2.52  prop_num_of_clauses:                    29264
% 15.78/2.52  prop_preprocess_simplified:             55507
% 15.78/2.52  prop_fo_subsumed:                       613
% 15.78/2.52  prop_solver_time:                       0.
% 15.78/2.52  smt_solver_time:                        0.
% 15.78/2.52  smt_fast_solver_time:                   0.
% 15.78/2.52  prop_fast_solver_time:                  0.
% 15.78/2.52  prop_unsat_core_time:                   0.004
% 15.78/2.52  
% 15.78/2.52  ------ QBF
% 15.78/2.52  
% 15.78/2.52  qbf_q_res:                              0
% 15.78/2.52  qbf_num_tautologies:                    0
% 15.78/2.52  qbf_prep_cycles:                        0
% 15.78/2.52  
% 15.78/2.52  ------ BMC1
% 15.78/2.52  
% 15.78/2.52  bmc1_current_bound:                     -1
% 15.78/2.52  bmc1_last_solved_bound:                 -1
% 15.78/2.52  bmc1_unsat_core_size:                   -1
% 15.78/2.52  bmc1_unsat_core_parents_size:           -1
% 15.78/2.52  bmc1_merge_next_fun:                    0
% 15.78/2.52  bmc1_unsat_core_clauses_time:           0.
% 15.78/2.52  
% 15.78/2.52  ------ Instantiation
% 15.78/2.52  
% 15.78/2.52  inst_num_of_clauses:                    1860
% 15.78/2.52  inst_num_in_passive:                    453
% 15.78/2.52  inst_num_in_active:                     3378
% 15.78/2.52  inst_num_in_unprocessed:                793
% 15.78/2.52  inst_num_of_loops:                      3619
% 15.78/2.52  inst_num_of_learning_restarts:          1
% 15.78/2.52  inst_num_moves_active_passive:          236
% 15.78/2.52  inst_lit_activity:                      0
% 15.78/2.52  inst_lit_activity_moves:                2
% 15.78/2.52  inst_num_tautologies:                   0
% 15.78/2.52  inst_num_prop_implied:                  0
% 15.78/2.52  inst_num_existing_simplified:           0
% 15.78/2.52  inst_num_eq_res_simplified:             0
% 15.78/2.52  inst_num_child_elim:                    0
% 15.78/2.52  inst_num_of_dismatching_blockings:      2639
% 15.78/2.52  inst_num_of_non_proper_insts:           8198
% 15.78/2.52  inst_num_of_duplicates:                 0
% 15.78/2.52  inst_inst_num_from_inst_to_res:         0
% 15.78/2.52  inst_dismatching_checking_time:         0.
% 15.78/2.52  
% 15.78/2.52  ------ Resolution
% 15.78/2.52  
% 15.78/2.52  res_num_of_clauses:                     78
% 15.78/2.52  res_num_in_passive:                     78
% 15.78/2.52  res_num_in_active:                      0
% 15.78/2.52  res_num_of_loops:                       278
% 15.78/2.52  res_forward_subset_subsumed:            530
% 15.78/2.52  res_backward_subset_subsumed:           0
% 15.78/2.52  res_forward_subsumed:                   0
% 15.78/2.52  res_backward_subsumed:                  0
% 15.78/2.52  res_forward_subsumption_resolution:     2
% 15.78/2.52  res_backward_subsumption_resolution:    0
% 15.78/2.52  res_clause_to_clause_subsumption:       6977
% 15.78/2.52  res_orphan_elimination:                 0
% 15.78/2.52  res_tautology_del:                      419
% 15.78/2.52  res_num_eq_res_simplified:              1
% 15.78/2.52  res_num_sel_changes:                    0
% 15.78/2.52  res_moves_from_active_to_pass:          0
% 15.78/2.52  
% 15.78/2.52  ------ Superposition
% 15.78/2.52  
% 15.78/2.52  sup_time_total:                         0.
% 15.78/2.52  sup_time_generating:                    0.
% 15.78/2.52  sup_time_sim_full:                      0.
% 15.78/2.52  sup_time_sim_immed:                     0.
% 15.78/2.52  
% 15.78/2.52  sup_num_of_clauses:                     1974
% 15.78/2.52  sup_num_in_active:                      547
% 15.78/2.52  sup_num_in_passive:                     1427
% 15.78/2.52  sup_num_of_loops:                       723
% 15.78/2.52  sup_fw_superposition:                   1711
% 15.78/2.52  sup_bw_superposition:                   1372
% 15.78/2.52  sup_immediate_simplified:               1133
% 15.78/2.52  sup_given_eliminated:                   1
% 15.78/2.52  comparisons_done:                       0
% 15.78/2.52  comparisons_avoided:                    4
% 15.78/2.52  
% 15.78/2.52  ------ Simplifications
% 15.78/2.52  
% 15.78/2.52  
% 15.78/2.52  sim_fw_subset_subsumed:                 90
% 15.78/2.52  sim_bw_subset_subsumed:                 66
% 15.78/2.52  sim_fw_subsumed:                        126
% 15.78/2.52  sim_bw_subsumed:                        8
% 15.78/2.52  sim_fw_subsumption_res:                 0
% 15.78/2.52  sim_bw_subsumption_res:                 0
% 15.78/2.52  sim_tautology_del:                      42
% 15.78/2.52  sim_eq_tautology_del:                   428
% 15.78/2.52  sim_eq_res_simp:                        27
% 15.78/2.52  sim_fw_demodulated:                     330
% 15.78/2.52  sim_bw_demodulated:                     159
% 15.78/2.52  sim_light_normalised:                   932
% 15.78/2.52  sim_joinable_taut:                      0
% 15.78/2.52  sim_joinable_simp:                      0
% 15.78/2.52  sim_ac_normalised:                      0
% 15.78/2.52  sim_smt_subsumption:                    0
% 15.78/2.52  
%------------------------------------------------------------------------------
