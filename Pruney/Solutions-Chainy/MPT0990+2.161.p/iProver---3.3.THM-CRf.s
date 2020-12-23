%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:31 EST 2020

% Result     : Theorem 4.01s
% Output     : CNFRefutation 4.01s
% Verified   : 
% Statistics : Number of formulae       :  182 (2006 expanded)
%              Number of clauses        :  108 ( 561 expanded)
%              Number of leaves         :   20 ( 535 expanded)
%              Depth                    :   23
%              Number of atoms          :  725 (17088 expanded)
%              Number of equality atoms :  370 (6311 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
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

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f42,plain,(
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

fof(f41,plain,
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

fof(f43,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f38,f42,f41])).

fof(f73,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f43])).

fof(f76,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f43])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f31])).

fof(f64,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f74,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f25])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f78,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f43])).

fof(f9,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f13,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f88,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f55,f65])).

fof(f71,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

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

fof(f63,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0)
              & k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f87,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f50,f65])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f77,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f43])).

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

fof(f33,plain,(
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

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f72,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f75,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f80,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f43])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f10,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f83,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f47,f65])).

fof(f15,axiom,(
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

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f69,plain,(
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
    inference(cnf_transformation,[],[f36])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f20,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f48,plain,(
    ! [X0] :
      ( k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f86,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f48,f65])).

fof(f81,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f43])).

fof(f82,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f43])).

fof(f79,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1241,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1244,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1250,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3705,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1244,c_1250])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_41,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_3821,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3705,c_41])).

cnf(c_3822,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_3821])).

cnf(c_3830,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1241,c_3822])).

cnf(c_10,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_30,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_413,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_30])).

cnf(c_414,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_413])).

cnf(c_11,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_422,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_414,c_11])).

cnf(c_1237,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_422])).

cnf(c_37,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1497,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_2092,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1237,c_37,c_35,c_34,c_32,c_422,c_1497])).

cnf(c_3831,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3830,c_2092])).

cnf(c_38,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_4079,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3831,c_38])).

cnf(c_6,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
    | k1_relat_1(X0) != k2_relat_1(X1)
    | k2_funct_1(X0) = X1 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1262,plain,
    ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
    | k1_relat_1(X1) != k2_relat_1(X0)
    | k2_funct_1(X1) = X0
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4186,plain,
    ( k1_relat_1(sK3) != k2_relat_1(sK2)
    | k2_funct_1(sK3) = sK2
    | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4079,c_1262])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1260,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2281,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1241,c_1260])).

cnf(c_31,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2282,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2281,c_31])).

cnf(c_2280,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1244,c_1260])).

cnf(c_21,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X3,X1,X0)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_426,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X2,X1,X1,X2,X3,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,X2,X0) = X2
    | k6_partfun1(X2) != k6_partfun1(sK0)
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_30])).

cnf(c_427,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0
    | k6_partfun1(sK0) != k6_partfun1(sK0) ),
    inference(unflattening,[status(thm)],[c_426])).

cnf(c_514,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_427])).

cnf(c_1236,plain,
    ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X0,sK0,X2) = sK0
    | v1_funct_2(X2,X0,sK0) != iProver_top
    | v1_funct_2(X1,sK0,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_514])).

cnf(c_1706,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1236])).

cnf(c_36,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_39,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_40,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_33,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_42,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_43,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_2183,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1706,c_38,c_39,c_40,c_41,c_42,c_43])).

cnf(c_2283,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_2280,c_2183])).

cnf(c_4187,plain,
    ( k1_relat_1(sK3) != sK1
    | k2_funct_1(sK3) = sK2
    | k6_partfun1(sK0) != k6_partfun1(sK0)
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4186,c_2282,c_2283])).

cnf(c_4188,plain,
    ( k1_relat_1(sK3) != sK1
    | k2_funct_1(sK3) = sK2
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4187])).

cnf(c_28,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_702,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_731,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_702])).

cnf(c_703,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1366,plain,
    ( sK0 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_703])).

cnf(c_1367,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1366])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1268,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2382,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1244,c_1268])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_2660,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2661,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2660])).

cnf(c_1267,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2383,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1241,c_1268])).

cnf(c_2828,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1267,c_2383])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1253,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3637,plain,
    ( k1_relset_1(sK1,sK0,sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1244,c_1253])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1261,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2377,plain,
    ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1244,c_1261])).

cnf(c_3640,plain,
    ( k1_relat_1(sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3637,c_2377])).

cnf(c_2,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1266,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X3)
    | ~ v2_funct_1(k1_partfun1(X1,X2,X2,X4,X0,X3))
    | k2_relset_1(X1,X2,X0) != X2
    | k1_xboole_0 = X4 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1248,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k1_xboole_0 = X3
    | v1_funct_2(X2,X0,X1) != iProver_top
    | v1_funct_2(X4,X1,X3) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X4) = iProver_top
    | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_4177,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_31,c_1248])).

cnf(c_4323,plain,
    ( v1_funct_1(X1) != iProver_top
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | k1_xboole_0 = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4177,c_38,c_39,c_40])).

cnf(c_4324,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4323])).

cnf(c_4327,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2092,c_4324])).

cnf(c_4416,plain,
    ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4327,c_41,c_42,c_43,c_28,c_731,c_1367])).

cnf(c_4420,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1266,c_4416])).

cnf(c_5498,plain,
    ( k2_funct_1(sK3) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4188,c_38,c_41,c_42,c_28,c_731,c_1367,c_2382,c_2661,c_2828,c_3640,c_4420])).

cnf(c_1242,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_5,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1263,plain,
    ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3079,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1242,c_1263])).

cnf(c_3233,plain,
    ( v2_funct_1(sK3) != iProver_top
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3079,c_2382,c_2661])).

cnf(c_3234,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
    | v2_funct_1(sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_3233])).

cnf(c_4445,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3)) ),
    inference(superposition,[status(thm)],[c_4420,c_3234])).

cnf(c_5500,plain,
    ( k5_relat_1(sK3,sK2) = k6_partfun1(k1_relat_1(sK3)) ),
    inference(demodulation,[status(thm)],[c_5498,c_4445])).

cnf(c_6816,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3640,c_42,c_28,c_731,c_1367])).

cnf(c_7186,plain,
    ( k5_relat_1(sK3,sK2) = k6_partfun1(sK1) ),
    inference(light_normalisation,[status(thm)],[c_5500,c_5500,c_6816])).

cnf(c_7190,plain,
    ( k1_relat_1(sK2) != k2_relat_1(sK3)
    | k2_funct_1(sK2) = sK3
    | k6_partfun1(k2_relat_1(sK2)) != k6_partfun1(sK1)
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_7186,c_1262])).

cnf(c_3638,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1241,c_1253])).

cnf(c_2378,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1241,c_1261])).

cnf(c_3639,plain,
    ( k1_relat_1(sK2) = sK0
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3638,c_2378])).

cnf(c_27,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1340,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_703])).

cnf(c_1341,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1340])).

cnf(c_6225,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3639,c_39,c_27,c_731,c_1341])).

cnf(c_7191,plain,
    ( k2_funct_1(sK2) = sK3
    | k6_partfun1(sK1) != k6_partfun1(sK1)
    | sK0 != sK0
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7190,c_2282,c_2283,c_6225])).

cnf(c_7192,plain,
    ( k2_funct_1(sK2) = sK3
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_7191])).

cnf(c_26,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_29,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_45,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7192,c_2828,c_2661,c_2382,c_26,c_45,c_41,c_38])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:28:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 4.01/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.01/1.01  
% 4.01/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.01/1.01  
% 4.01/1.01  ------  iProver source info
% 4.01/1.01  
% 4.01/1.01  git: date: 2020-06-30 10:37:57 +0100
% 4.01/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.01/1.01  git: non_committed_changes: false
% 4.01/1.01  git: last_make_outside_of_git: false
% 4.01/1.01  
% 4.01/1.01  ------ 
% 4.01/1.01  
% 4.01/1.01  ------ Input Options
% 4.01/1.01  
% 4.01/1.01  --out_options                           all
% 4.01/1.01  --tptp_safe_out                         true
% 4.01/1.01  --problem_path                          ""
% 4.01/1.01  --include_path                          ""
% 4.01/1.01  --clausifier                            res/vclausify_rel
% 4.01/1.01  --clausifier_options                    ""
% 4.01/1.01  --stdin                                 false
% 4.01/1.01  --stats_out                             all
% 4.01/1.01  
% 4.01/1.01  ------ General Options
% 4.01/1.01  
% 4.01/1.01  --fof                                   false
% 4.01/1.01  --time_out_real                         305.
% 4.01/1.01  --time_out_virtual                      -1.
% 4.01/1.01  --symbol_type_check                     false
% 4.01/1.01  --clausify_out                          false
% 4.01/1.01  --sig_cnt_out                           false
% 4.01/1.01  --trig_cnt_out                          false
% 4.01/1.01  --trig_cnt_out_tolerance                1.
% 4.01/1.01  --trig_cnt_out_sk_spl                   false
% 4.01/1.01  --abstr_cl_out                          false
% 4.01/1.01  
% 4.01/1.01  ------ Global Options
% 4.01/1.01  
% 4.01/1.01  --schedule                              default
% 4.01/1.01  --add_important_lit                     false
% 4.01/1.01  --prop_solver_per_cl                    1000
% 4.01/1.01  --min_unsat_core                        false
% 4.01/1.01  --soft_assumptions                      false
% 4.01/1.01  --soft_lemma_size                       3
% 4.01/1.01  --prop_impl_unit_size                   0
% 4.01/1.01  --prop_impl_unit                        []
% 4.01/1.01  --share_sel_clauses                     true
% 4.01/1.01  --reset_solvers                         false
% 4.01/1.01  --bc_imp_inh                            [conj_cone]
% 4.01/1.01  --conj_cone_tolerance                   3.
% 4.01/1.01  --extra_neg_conj                        none
% 4.01/1.01  --large_theory_mode                     true
% 4.01/1.01  --prolific_symb_bound                   200
% 4.01/1.01  --lt_threshold                          2000
% 4.01/1.01  --clause_weak_htbl                      true
% 4.01/1.01  --gc_record_bc_elim                     false
% 4.01/1.01  
% 4.01/1.01  ------ Preprocessing Options
% 4.01/1.01  
% 4.01/1.01  --preprocessing_flag                    true
% 4.01/1.01  --time_out_prep_mult                    0.1
% 4.01/1.01  --splitting_mode                        input
% 4.01/1.01  --splitting_grd                         true
% 4.01/1.01  --splitting_cvd                         false
% 4.01/1.01  --splitting_cvd_svl                     false
% 4.01/1.01  --splitting_nvd                         32
% 4.01/1.01  --sub_typing                            true
% 4.01/1.01  --prep_gs_sim                           true
% 4.01/1.01  --prep_unflatten                        true
% 4.01/1.01  --prep_res_sim                          true
% 4.01/1.01  --prep_upred                            true
% 4.01/1.01  --prep_sem_filter                       exhaustive
% 4.01/1.01  --prep_sem_filter_out                   false
% 4.01/1.01  --pred_elim                             true
% 4.01/1.01  --res_sim_input                         true
% 4.01/1.01  --eq_ax_congr_red                       true
% 4.01/1.01  --pure_diseq_elim                       true
% 4.01/1.01  --brand_transform                       false
% 4.01/1.01  --non_eq_to_eq                          false
% 4.01/1.01  --prep_def_merge                        true
% 4.01/1.01  --prep_def_merge_prop_impl              false
% 4.01/1.01  --prep_def_merge_mbd                    true
% 4.01/1.01  --prep_def_merge_tr_red                 false
% 4.01/1.01  --prep_def_merge_tr_cl                  false
% 4.01/1.01  --smt_preprocessing                     true
% 4.01/1.01  --smt_ac_axioms                         fast
% 4.01/1.01  --preprocessed_out                      false
% 4.01/1.01  --preprocessed_stats                    false
% 4.01/1.01  
% 4.01/1.01  ------ Abstraction refinement Options
% 4.01/1.01  
% 4.01/1.01  --abstr_ref                             []
% 4.01/1.01  --abstr_ref_prep                        false
% 4.01/1.01  --abstr_ref_until_sat                   false
% 4.01/1.01  --abstr_ref_sig_restrict                funpre
% 4.01/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 4.01/1.01  --abstr_ref_under                       []
% 4.01/1.01  
% 4.01/1.01  ------ SAT Options
% 4.01/1.01  
% 4.01/1.01  --sat_mode                              false
% 4.01/1.01  --sat_fm_restart_options                ""
% 4.01/1.01  --sat_gr_def                            false
% 4.01/1.01  --sat_epr_types                         true
% 4.01/1.01  --sat_non_cyclic_types                  false
% 4.01/1.01  --sat_finite_models                     false
% 4.01/1.01  --sat_fm_lemmas                         false
% 4.01/1.01  --sat_fm_prep                           false
% 4.01/1.01  --sat_fm_uc_incr                        true
% 4.01/1.01  --sat_out_model                         small
% 4.01/1.01  --sat_out_clauses                       false
% 4.01/1.01  
% 4.01/1.01  ------ QBF Options
% 4.01/1.01  
% 4.01/1.01  --qbf_mode                              false
% 4.01/1.01  --qbf_elim_univ                         false
% 4.01/1.01  --qbf_dom_inst                          none
% 4.01/1.01  --qbf_dom_pre_inst                      false
% 4.01/1.01  --qbf_sk_in                             false
% 4.01/1.01  --qbf_pred_elim                         true
% 4.01/1.01  --qbf_split                             512
% 4.01/1.01  
% 4.01/1.01  ------ BMC1 Options
% 4.01/1.01  
% 4.01/1.01  --bmc1_incremental                      false
% 4.01/1.01  --bmc1_axioms                           reachable_all
% 4.01/1.01  --bmc1_min_bound                        0
% 4.01/1.01  --bmc1_max_bound                        -1
% 4.01/1.01  --bmc1_max_bound_default                -1
% 4.01/1.01  --bmc1_symbol_reachability              true
% 4.01/1.01  --bmc1_property_lemmas                  false
% 4.01/1.01  --bmc1_k_induction                      false
% 4.01/1.01  --bmc1_non_equiv_states                 false
% 4.01/1.01  --bmc1_deadlock                         false
% 4.01/1.01  --bmc1_ucm                              false
% 4.01/1.01  --bmc1_add_unsat_core                   none
% 4.01/1.01  --bmc1_unsat_core_children              false
% 4.01/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 4.01/1.01  --bmc1_out_stat                         full
% 4.01/1.01  --bmc1_ground_init                      false
% 4.01/1.01  --bmc1_pre_inst_next_state              false
% 4.01/1.01  --bmc1_pre_inst_state                   false
% 4.01/1.01  --bmc1_pre_inst_reach_state             false
% 4.01/1.01  --bmc1_out_unsat_core                   false
% 4.01/1.01  --bmc1_aig_witness_out                  false
% 4.01/1.01  --bmc1_verbose                          false
% 4.01/1.01  --bmc1_dump_clauses_tptp                false
% 4.01/1.01  --bmc1_dump_unsat_core_tptp             false
% 4.01/1.01  --bmc1_dump_file                        -
% 4.01/1.01  --bmc1_ucm_expand_uc_limit              128
% 4.01/1.01  --bmc1_ucm_n_expand_iterations          6
% 4.01/1.01  --bmc1_ucm_extend_mode                  1
% 4.01/1.01  --bmc1_ucm_init_mode                    2
% 4.01/1.01  --bmc1_ucm_cone_mode                    none
% 4.01/1.01  --bmc1_ucm_reduced_relation_type        0
% 4.01/1.01  --bmc1_ucm_relax_model                  4
% 4.01/1.01  --bmc1_ucm_full_tr_after_sat            true
% 4.01/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 4.01/1.01  --bmc1_ucm_layered_model                none
% 4.01/1.01  --bmc1_ucm_max_lemma_size               10
% 4.01/1.01  
% 4.01/1.01  ------ AIG Options
% 4.01/1.01  
% 4.01/1.01  --aig_mode                              false
% 4.01/1.01  
% 4.01/1.01  ------ Instantiation Options
% 4.01/1.01  
% 4.01/1.01  --instantiation_flag                    true
% 4.01/1.01  --inst_sos_flag                         true
% 4.01/1.01  --inst_sos_phase                        true
% 4.01/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.01/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.01/1.01  --inst_lit_sel_side                     num_symb
% 4.01/1.01  --inst_solver_per_active                1400
% 4.01/1.01  --inst_solver_calls_frac                1.
% 4.01/1.01  --inst_passive_queue_type               priority_queues
% 4.01/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.01/1.01  --inst_passive_queues_freq              [25;2]
% 4.01/1.01  --inst_dismatching                      true
% 4.01/1.01  --inst_eager_unprocessed_to_passive     true
% 4.01/1.01  --inst_prop_sim_given                   true
% 4.01/1.01  --inst_prop_sim_new                     false
% 4.01/1.01  --inst_subs_new                         false
% 4.01/1.01  --inst_eq_res_simp                      false
% 4.01/1.01  --inst_subs_given                       false
% 4.01/1.01  --inst_orphan_elimination               true
% 4.01/1.01  --inst_learning_loop_flag               true
% 4.01/1.01  --inst_learning_start                   3000
% 4.01/1.01  --inst_learning_factor                  2
% 4.01/1.01  --inst_start_prop_sim_after_learn       3
% 4.01/1.01  --inst_sel_renew                        solver
% 4.01/1.01  --inst_lit_activity_flag                true
% 4.01/1.01  --inst_restr_to_given                   false
% 4.01/1.01  --inst_activity_threshold               500
% 4.01/1.01  --inst_out_proof                        true
% 4.01/1.01  
% 4.01/1.01  ------ Resolution Options
% 4.01/1.01  
% 4.01/1.01  --resolution_flag                       true
% 4.01/1.01  --res_lit_sel                           adaptive
% 4.01/1.01  --res_lit_sel_side                      none
% 4.01/1.01  --res_ordering                          kbo
% 4.01/1.01  --res_to_prop_solver                    active
% 4.01/1.01  --res_prop_simpl_new                    false
% 4.01/1.01  --res_prop_simpl_given                  true
% 4.01/1.01  --res_passive_queue_type                priority_queues
% 4.01/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.01/1.01  --res_passive_queues_freq               [15;5]
% 4.01/1.01  --res_forward_subs                      full
% 4.01/1.01  --res_backward_subs                     full
% 4.01/1.01  --res_forward_subs_resolution           true
% 4.01/1.01  --res_backward_subs_resolution          true
% 4.01/1.01  --res_orphan_elimination                true
% 4.01/1.01  --res_time_limit                        2.
% 4.01/1.01  --res_out_proof                         true
% 4.01/1.01  
% 4.01/1.01  ------ Superposition Options
% 4.01/1.01  
% 4.01/1.01  --superposition_flag                    true
% 4.01/1.01  --sup_passive_queue_type                priority_queues
% 4.01/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.01/1.01  --sup_passive_queues_freq               [8;1;4]
% 4.01/1.01  --demod_completeness_check              fast
% 4.01/1.01  --demod_use_ground                      true
% 4.01/1.01  --sup_to_prop_solver                    passive
% 4.01/1.01  --sup_prop_simpl_new                    true
% 4.01/1.01  --sup_prop_simpl_given                  true
% 4.01/1.01  --sup_fun_splitting                     true
% 4.01/1.01  --sup_smt_interval                      50000
% 4.01/1.01  
% 4.01/1.01  ------ Superposition Simplification Setup
% 4.01/1.01  
% 4.01/1.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.01/1.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.01/1.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.01/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.01/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 4.01/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.01/1.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.01/1.01  --sup_immed_triv                        [TrivRules]
% 4.01/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.01/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.01/1.01  --sup_immed_bw_main                     []
% 4.01/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.01/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 4.01/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.01/1.01  --sup_input_bw                          []
% 4.01/1.01  
% 4.01/1.01  ------ Combination Options
% 4.01/1.01  
% 4.01/1.01  --comb_res_mult                         3
% 4.01/1.01  --comb_sup_mult                         2
% 4.01/1.01  --comb_inst_mult                        10
% 4.01/1.01  
% 4.01/1.01  ------ Debug Options
% 4.01/1.01  
% 4.01/1.01  --dbg_backtrace                         false
% 4.01/1.01  --dbg_dump_prop_clauses                 false
% 4.01/1.01  --dbg_dump_prop_clauses_file            -
% 4.01/1.01  --dbg_out_stat                          false
% 4.01/1.01  ------ Parsing...
% 4.01/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.01/1.01  
% 4.01/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 4.01/1.01  
% 4.01/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.01/1.01  
% 4.01/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.01/1.01  ------ Proving...
% 4.01/1.01  ------ Problem Properties 
% 4.01/1.01  
% 4.01/1.01  
% 4.01/1.01  clauses                                 37
% 4.01/1.01  conjectures                             11
% 4.01/1.01  EPR                                     7
% 4.01/1.01  Horn                                    31
% 4.01/1.01  unary                                   15
% 4.01/1.01  binary                                  3
% 4.01/1.01  lits                                    130
% 4.01/1.01  lits eq                                 32
% 4.01/1.01  fd_pure                                 0
% 4.01/1.01  fd_pseudo                               0
% 4.01/1.01  fd_cond                                 5
% 4.01/1.01  fd_pseudo_cond                          1
% 4.01/1.01  AC symbols                              0
% 4.01/1.01  
% 4.01/1.01  ------ Schedule dynamic 5 is on 
% 4.01/1.01  
% 4.01/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 4.01/1.01  
% 4.01/1.01  
% 4.01/1.01  ------ 
% 4.01/1.01  Current options:
% 4.01/1.01  ------ 
% 4.01/1.01  
% 4.01/1.01  ------ Input Options
% 4.01/1.01  
% 4.01/1.01  --out_options                           all
% 4.01/1.01  --tptp_safe_out                         true
% 4.01/1.01  --problem_path                          ""
% 4.01/1.01  --include_path                          ""
% 4.01/1.01  --clausifier                            res/vclausify_rel
% 4.01/1.01  --clausifier_options                    ""
% 4.01/1.01  --stdin                                 false
% 4.01/1.01  --stats_out                             all
% 4.01/1.01  
% 4.01/1.01  ------ General Options
% 4.01/1.01  
% 4.01/1.01  --fof                                   false
% 4.01/1.01  --time_out_real                         305.
% 4.01/1.01  --time_out_virtual                      -1.
% 4.01/1.01  --symbol_type_check                     false
% 4.01/1.01  --clausify_out                          false
% 4.01/1.01  --sig_cnt_out                           false
% 4.01/1.01  --trig_cnt_out                          false
% 4.01/1.01  --trig_cnt_out_tolerance                1.
% 4.01/1.01  --trig_cnt_out_sk_spl                   false
% 4.01/1.01  --abstr_cl_out                          false
% 4.01/1.01  
% 4.01/1.01  ------ Global Options
% 4.01/1.01  
% 4.01/1.01  --schedule                              default
% 4.01/1.01  --add_important_lit                     false
% 4.01/1.01  --prop_solver_per_cl                    1000
% 4.01/1.01  --min_unsat_core                        false
% 4.01/1.01  --soft_assumptions                      false
% 4.01/1.01  --soft_lemma_size                       3
% 4.01/1.01  --prop_impl_unit_size                   0
% 4.01/1.01  --prop_impl_unit                        []
% 4.01/1.01  --share_sel_clauses                     true
% 4.01/1.01  --reset_solvers                         false
% 4.01/1.01  --bc_imp_inh                            [conj_cone]
% 4.01/1.01  --conj_cone_tolerance                   3.
% 4.01/1.01  --extra_neg_conj                        none
% 4.01/1.01  --large_theory_mode                     true
% 4.01/1.01  --prolific_symb_bound                   200
% 4.01/1.01  --lt_threshold                          2000
% 4.01/1.01  --clause_weak_htbl                      true
% 4.01/1.01  --gc_record_bc_elim                     false
% 4.01/1.01  
% 4.01/1.01  ------ Preprocessing Options
% 4.01/1.01  
% 4.01/1.01  --preprocessing_flag                    true
% 4.01/1.01  --time_out_prep_mult                    0.1
% 4.01/1.01  --splitting_mode                        input
% 4.01/1.01  --splitting_grd                         true
% 4.01/1.01  --splitting_cvd                         false
% 4.01/1.01  --splitting_cvd_svl                     false
% 4.01/1.01  --splitting_nvd                         32
% 4.01/1.01  --sub_typing                            true
% 4.01/1.01  --prep_gs_sim                           true
% 4.01/1.01  --prep_unflatten                        true
% 4.01/1.01  --prep_res_sim                          true
% 4.01/1.01  --prep_upred                            true
% 4.01/1.01  --prep_sem_filter                       exhaustive
% 4.01/1.01  --prep_sem_filter_out                   false
% 4.01/1.01  --pred_elim                             true
% 4.01/1.01  --res_sim_input                         true
% 4.01/1.01  --eq_ax_congr_red                       true
% 4.01/1.01  --pure_diseq_elim                       true
% 4.01/1.01  --brand_transform                       false
% 4.01/1.01  --non_eq_to_eq                          false
% 4.01/1.01  --prep_def_merge                        true
% 4.01/1.01  --prep_def_merge_prop_impl              false
% 4.01/1.01  --prep_def_merge_mbd                    true
% 4.01/1.01  --prep_def_merge_tr_red                 false
% 4.01/1.01  --prep_def_merge_tr_cl                  false
% 4.01/1.01  --smt_preprocessing                     true
% 4.01/1.01  --smt_ac_axioms                         fast
% 4.01/1.01  --preprocessed_out                      false
% 4.01/1.01  --preprocessed_stats                    false
% 4.01/1.01  
% 4.01/1.01  ------ Abstraction refinement Options
% 4.01/1.01  
% 4.01/1.01  --abstr_ref                             []
% 4.01/1.01  --abstr_ref_prep                        false
% 4.01/1.01  --abstr_ref_until_sat                   false
% 4.01/1.01  --abstr_ref_sig_restrict                funpre
% 4.01/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 4.01/1.01  --abstr_ref_under                       []
% 4.01/1.01  
% 4.01/1.01  ------ SAT Options
% 4.01/1.01  
% 4.01/1.01  --sat_mode                              false
% 4.01/1.01  --sat_fm_restart_options                ""
% 4.01/1.01  --sat_gr_def                            false
% 4.01/1.01  --sat_epr_types                         true
% 4.01/1.01  --sat_non_cyclic_types                  false
% 4.01/1.01  --sat_finite_models                     false
% 4.01/1.01  --sat_fm_lemmas                         false
% 4.01/1.01  --sat_fm_prep                           false
% 4.01/1.01  --sat_fm_uc_incr                        true
% 4.01/1.01  --sat_out_model                         small
% 4.01/1.01  --sat_out_clauses                       false
% 4.01/1.01  
% 4.01/1.01  ------ QBF Options
% 4.01/1.01  
% 4.01/1.01  --qbf_mode                              false
% 4.01/1.01  --qbf_elim_univ                         false
% 4.01/1.01  --qbf_dom_inst                          none
% 4.01/1.01  --qbf_dom_pre_inst                      false
% 4.01/1.01  --qbf_sk_in                             false
% 4.01/1.01  --qbf_pred_elim                         true
% 4.01/1.01  --qbf_split                             512
% 4.01/1.01  
% 4.01/1.01  ------ BMC1 Options
% 4.01/1.01  
% 4.01/1.01  --bmc1_incremental                      false
% 4.01/1.01  --bmc1_axioms                           reachable_all
% 4.01/1.01  --bmc1_min_bound                        0
% 4.01/1.01  --bmc1_max_bound                        -1
% 4.01/1.01  --bmc1_max_bound_default                -1
% 4.01/1.01  --bmc1_symbol_reachability              true
% 4.01/1.01  --bmc1_property_lemmas                  false
% 4.01/1.01  --bmc1_k_induction                      false
% 4.01/1.01  --bmc1_non_equiv_states                 false
% 4.01/1.01  --bmc1_deadlock                         false
% 4.01/1.01  --bmc1_ucm                              false
% 4.01/1.01  --bmc1_add_unsat_core                   none
% 4.01/1.01  --bmc1_unsat_core_children              false
% 4.01/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 4.01/1.01  --bmc1_out_stat                         full
% 4.01/1.01  --bmc1_ground_init                      false
% 4.01/1.01  --bmc1_pre_inst_next_state              false
% 4.01/1.01  --bmc1_pre_inst_state                   false
% 4.01/1.01  --bmc1_pre_inst_reach_state             false
% 4.01/1.01  --bmc1_out_unsat_core                   false
% 4.01/1.01  --bmc1_aig_witness_out                  false
% 4.01/1.01  --bmc1_verbose                          false
% 4.01/1.01  --bmc1_dump_clauses_tptp                false
% 4.01/1.01  --bmc1_dump_unsat_core_tptp             false
% 4.01/1.01  --bmc1_dump_file                        -
% 4.01/1.01  --bmc1_ucm_expand_uc_limit              128
% 4.01/1.01  --bmc1_ucm_n_expand_iterations          6
% 4.01/1.01  --bmc1_ucm_extend_mode                  1
% 4.01/1.01  --bmc1_ucm_init_mode                    2
% 4.01/1.01  --bmc1_ucm_cone_mode                    none
% 4.01/1.01  --bmc1_ucm_reduced_relation_type        0
% 4.01/1.01  --bmc1_ucm_relax_model                  4
% 4.01/1.01  --bmc1_ucm_full_tr_after_sat            true
% 4.01/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 4.01/1.01  --bmc1_ucm_layered_model                none
% 4.01/1.01  --bmc1_ucm_max_lemma_size               10
% 4.01/1.01  
% 4.01/1.01  ------ AIG Options
% 4.01/1.01  
% 4.01/1.01  --aig_mode                              false
% 4.01/1.01  
% 4.01/1.01  ------ Instantiation Options
% 4.01/1.01  
% 4.01/1.01  --instantiation_flag                    true
% 4.01/1.01  --inst_sos_flag                         true
% 4.01/1.01  --inst_sos_phase                        true
% 4.01/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.01/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.01/1.01  --inst_lit_sel_side                     none
% 4.01/1.01  --inst_solver_per_active                1400
% 4.01/1.01  --inst_solver_calls_frac                1.
% 4.01/1.01  --inst_passive_queue_type               priority_queues
% 4.01/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.01/1.01  --inst_passive_queues_freq              [25;2]
% 4.01/1.01  --inst_dismatching                      true
% 4.01/1.01  --inst_eager_unprocessed_to_passive     true
% 4.01/1.01  --inst_prop_sim_given                   true
% 4.01/1.01  --inst_prop_sim_new                     false
% 4.01/1.01  --inst_subs_new                         false
% 4.01/1.01  --inst_eq_res_simp                      false
% 4.01/1.01  --inst_subs_given                       false
% 4.01/1.01  --inst_orphan_elimination               true
% 4.01/1.01  --inst_learning_loop_flag               true
% 4.01/1.01  --inst_learning_start                   3000
% 4.01/1.01  --inst_learning_factor                  2
% 4.01/1.01  --inst_start_prop_sim_after_learn       3
% 4.01/1.01  --inst_sel_renew                        solver
% 4.01/1.01  --inst_lit_activity_flag                true
% 4.01/1.01  --inst_restr_to_given                   false
% 4.01/1.01  --inst_activity_threshold               500
% 4.01/1.01  --inst_out_proof                        true
% 4.01/1.01  
% 4.01/1.01  ------ Resolution Options
% 4.01/1.01  
% 4.01/1.01  --resolution_flag                       false
% 4.01/1.01  --res_lit_sel                           adaptive
% 4.01/1.01  --res_lit_sel_side                      none
% 4.01/1.01  --res_ordering                          kbo
% 4.01/1.01  --res_to_prop_solver                    active
% 4.01/1.01  --res_prop_simpl_new                    false
% 4.01/1.01  --res_prop_simpl_given                  true
% 4.01/1.01  --res_passive_queue_type                priority_queues
% 4.01/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.01/1.01  --res_passive_queues_freq               [15;5]
% 4.01/1.01  --res_forward_subs                      full
% 4.01/1.01  --res_backward_subs                     full
% 4.01/1.01  --res_forward_subs_resolution           true
% 4.01/1.01  --res_backward_subs_resolution          true
% 4.01/1.01  --res_orphan_elimination                true
% 4.01/1.01  --res_time_limit                        2.
% 4.01/1.01  --res_out_proof                         true
% 4.01/1.01  
% 4.01/1.01  ------ Superposition Options
% 4.01/1.01  
% 4.01/1.01  --superposition_flag                    true
% 4.01/1.01  --sup_passive_queue_type                priority_queues
% 4.01/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.01/1.01  --sup_passive_queues_freq               [8;1;4]
% 4.01/1.01  --demod_completeness_check              fast
% 4.01/1.01  --demod_use_ground                      true
% 4.01/1.01  --sup_to_prop_solver                    passive
% 4.01/1.01  --sup_prop_simpl_new                    true
% 4.01/1.01  --sup_prop_simpl_given                  true
% 4.01/1.01  --sup_fun_splitting                     true
% 4.01/1.01  --sup_smt_interval                      50000
% 4.01/1.01  
% 4.01/1.01  ------ Superposition Simplification Setup
% 4.01/1.01  
% 4.01/1.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.01/1.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.01/1.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.01/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.01/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 4.01/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.01/1.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.01/1.01  --sup_immed_triv                        [TrivRules]
% 4.01/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.01/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.01/1.01  --sup_immed_bw_main                     []
% 4.01/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.01/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 4.01/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.01/1.01  --sup_input_bw                          []
% 4.01/1.01  
% 4.01/1.01  ------ Combination Options
% 4.01/1.01  
% 4.01/1.01  --comb_res_mult                         3
% 4.01/1.01  --comb_sup_mult                         2
% 4.01/1.01  --comb_inst_mult                        10
% 4.01/1.01  
% 4.01/1.01  ------ Debug Options
% 4.01/1.01  
% 4.01/1.01  --dbg_backtrace                         false
% 4.01/1.01  --dbg_dump_prop_clauses                 false
% 4.01/1.01  --dbg_dump_prop_clauses_file            -
% 4.01/1.01  --dbg_out_stat                          false
% 4.01/1.01  
% 4.01/1.01  
% 4.01/1.01  
% 4.01/1.01  
% 4.01/1.01  ------ Proving...
% 4.01/1.01  
% 4.01/1.01  
% 4.01/1.01  % SZS status Theorem for theBenchmark.p
% 4.01/1.01  
% 4.01/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 4.01/1.01  
% 4.01/1.01  fof(f16,conjecture,(
% 4.01/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 4.01/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/1.01  
% 4.01/1.01  fof(f17,negated_conjecture,(
% 4.01/1.01    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 4.01/1.01    inference(negated_conjecture,[],[f16])).
% 4.01/1.01  
% 4.01/1.01  fof(f37,plain,(
% 4.01/1.01    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 4.01/1.01    inference(ennf_transformation,[],[f17])).
% 4.01/1.01  
% 4.01/1.01  fof(f38,plain,(
% 4.01/1.01    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 4.01/1.01    inference(flattening,[],[f37])).
% 4.01/1.01  
% 4.01/1.01  fof(f42,plain,(
% 4.01/1.01    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 4.01/1.01    introduced(choice_axiom,[])).
% 4.01/1.01  
% 4.01/1.01  fof(f41,plain,(
% 4.01/1.01    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 4.01/1.01    introduced(choice_axiom,[])).
% 4.01/1.01  
% 4.01/1.01  fof(f43,plain,(
% 4.01/1.01    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 4.01/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f38,f42,f41])).
% 4.01/1.01  
% 4.01/1.01  fof(f73,plain,(
% 4.01/1.01    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 4.01/1.01    inference(cnf_transformation,[],[f43])).
% 4.01/1.01  
% 4.01/1.01  fof(f76,plain,(
% 4.01/1.01    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 4.01/1.01    inference(cnf_transformation,[],[f43])).
% 4.01/1.01  
% 4.01/1.01  fof(f12,axiom,(
% 4.01/1.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 4.01/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/1.01  
% 4.01/1.01  fof(f31,plain,(
% 4.01/1.01    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 4.01/1.01    inference(ennf_transformation,[],[f12])).
% 4.01/1.01  
% 4.01/1.01  fof(f32,plain,(
% 4.01/1.01    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 4.01/1.01    inference(flattening,[],[f31])).
% 4.01/1.01  
% 4.01/1.01  fof(f64,plain,(
% 4.01/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 4.01/1.01    inference(cnf_transformation,[],[f32])).
% 4.01/1.01  
% 4.01/1.01  fof(f74,plain,(
% 4.01/1.01    v1_funct_1(sK3)),
% 4.01/1.01    inference(cnf_transformation,[],[f43])).
% 4.01/1.01  
% 4.01/1.01  fof(f8,axiom,(
% 4.01/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 4.01/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/1.01  
% 4.01/1.01  fof(f25,plain,(
% 4.01/1.01    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 4.01/1.01    inference(ennf_transformation,[],[f8])).
% 4.01/1.01  
% 4.01/1.01  fof(f26,plain,(
% 4.01/1.01    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.01/1.01    inference(flattening,[],[f25])).
% 4.01/1.01  
% 4.01/1.01  fof(f39,plain,(
% 4.01/1.01    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.01/1.01    inference(nnf_transformation,[],[f26])).
% 4.01/1.01  
% 4.01/1.01  fof(f53,plain,(
% 4.01/1.01    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.01/1.01    inference(cnf_transformation,[],[f39])).
% 4.01/1.01  
% 4.01/1.01  fof(f78,plain,(
% 4.01/1.01    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 4.01/1.01    inference(cnf_transformation,[],[f43])).
% 4.01/1.01  
% 4.01/1.01  fof(f9,axiom,(
% 4.01/1.01    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 4.01/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/1.01  
% 4.01/1.01  fof(f55,plain,(
% 4.01/1.01    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 4.01/1.01    inference(cnf_transformation,[],[f9])).
% 4.01/1.01  
% 4.01/1.01  fof(f13,axiom,(
% 4.01/1.01    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 4.01/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/1.01  
% 4.01/1.01  fof(f65,plain,(
% 4.01/1.01    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 4.01/1.01    inference(cnf_transformation,[],[f13])).
% 4.01/1.01  
% 4.01/1.01  fof(f88,plain,(
% 4.01/1.01    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 4.01/1.01    inference(definition_unfolding,[],[f55,f65])).
% 4.01/1.01  
% 4.01/1.01  fof(f71,plain,(
% 4.01/1.01    v1_funct_1(sK2)),
% 4.01/1.01    inference(cnf_transformation,[],[f43])).
% 4.01/1.01  
% 4.01/1.01  fof(f11,axiom,(
% 4.01/1.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 4.01/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/1.01  
% 4.01/1.01  fof(f29,plain,(
% 4.01/1.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 4.01/1.01    inference(ennf_transformation,[],[f11])).
% 4.01/1.01  
% 4.01/1.01  fof(f30,plain,(
% 4.01/1.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 4.01/1.01    inference(flattening,[],[f29])).
% 4.01/1.01  
% 4.01/1.01  fof(f63,plain,(
% 4.01/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 4.01/1.01    inference(cnf_transformation,[],[f30])).
% 4.01/1.01  
% 4.01/1.01  fof(f5,axiom,(
% 4.01/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 4.01/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/1.01  
% 4.01/1.01  fof(f21,plain,(
% 4.01/1.01    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 4.01/1.01    inference(ennf_transformation,[],[f5])).
% 4.01/1.01  
% 4.01/1.01  fof(f22,plain,(
% 4.01/1.01    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.01/1.01    inference(flattening,[],[f21])).
% 4.01/1.01  
% 4.01/1.01  fof(f50,plain,(
% 4.01/1.01    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.01/1.01    inference(cnf_transformation,[],[f22])).
% 4.01/1.01  
% 4.01/1.01  fof(f87,plain,(
% 4.01/1.01    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.01/1.01    inference(definition_unfolding,[],[f50,f65])).
% 4.01/1.01  
% 4.01/1.01  fof(f7,axiom,(
% 4.01/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 4.01/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/1.01  
% 4.01/1.01  fof(f24,plain,(
% 4.01/1.01    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.01/1.01    inference(ennf_transformation,[],[f7])).
% 4.01/1.01  
% 4.01/1.01  fof(f52,plain,(
% 4.01/1.01    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.01/1.01    inference(cnf_transformation,[],[f24])).
% 4.01/1.01  
% 4.01/1.01  fof(f77,plain,(
% 4.01/1.01    k2_relset_1(sK0,sK1,sK2) = sK1),
% 4.01/1.01    inference(cnf_transformation,[],[f43])).
% 4.01/1.01  
% 4.01/1.01  fof(f14,axiom,(
% 4.01/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 4.01/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/1.01  
% 4.01/1.01  fof(f33,plain,(
% 4.01/1.01    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 4.01/1.01    inference(ennf_transformation,[],[f14])).
% 4.01/1.01  
% 4.01/1.01  fof(f34,plain,(
% 4.01/1.01    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 4.01/1.01    inference(flattening,[],[f33])).
% 4.01/1.01  
% 4.01/1.01  fof(f66,plain,(
% 4.01/1.01    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 4.01/1.01    inference(cnf_transformation,[],[f34])).
% 4.01/1.01  
% 4.01/1.01  fof(f72,plain,(
% 4.01/1.01    v1_funct_2(sK2,sK0,sK1)),
% 4.01/1.01    inference(cnf_transformation,[],[f43])).
% 4.01/1.01  
% 4.01/1.01  fof(f75,plain,(
% 4.01/1.01    v1_funct_2(sK3,sK1,sK0)),
% 4.01/1.01    inference(cnf_transformation,[],[f43])).
% 4.01/1.01  
% 4.01/1.01  fof(f80,plain,(
% 4.01/1.01    k1_xboole_0 != sK0),
% 4.01/1.01    inference(cnf_transformation,[],[f43])).
% 4.01/1.01  
% 4.01/1.01  fof(f1,axiom,(
% 4.01/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 4.01/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/1.01  
% 4.01/1.01  fof(f18,plain,(
% 4.01/1.01    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 4.01/1.01    inference(ennf_transformation,[],[f1])).
% 4.01/1.01  
% 4.01/1.01  fof(f44,plain,(
% 4.01/1.01    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 4.01/1.01    inference(cnf_transformation,[],[f18])).
% 4.01/1.01  
% 4.01/1.01  fof(f2,axiom,(
% 4.01/1.01    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 4.01/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/1.01  
% 4.01/1.01  fof(f45,plain,(
% 4.01/1.01    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 4.01/1.01    inference(cnf_transformation,[],[f2])).
% 4.01/1.01  
% 4.01/1.01  fof(f10,axiom,(
% 4.01/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 4.01/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/1.01  
% 4.01/1.01  fof(f27,plain,(
% 4.01/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.01/1.01    inference(ennf_transformation,[],[f10])).
% 4.01/1.01  
% 4.01/1.01  fof(f28,plain,(
% 4.01/1.01    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.01/1.01    inference(flattening,[],[f27])).
% 4.01/1.01  
% 4.01/1.01  fof(f40,plain,(
% 4.01/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.01/1.01    inference(nnf_transformation,[],[f28])).
% 4.01/1.01  
% 4.01/1.01  fof(f56,plain,(
% 4.01/1.01    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.01/1.01    inference(cnf_transformation,[],[f40])).
% 4.01/1.01  
% 4.01/1.01  fof(f6,axiom,(
% 4.01/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 4.01/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/1.01  
% 4.01/1.01  fof(f23,plain,(
% 4.01/1.01    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.01/1.01    inference(ennf_transformation,[],[f6])).
% 4.01/1.01  
% 4.01/1.01  fof(f51,plain,(
% 4.01/1.01    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.01/1.01    inference(cnf_transformation,[],[f23])).
% 4.01/1.01  
% 4.01/1.01  fof(f3,axiom,(
% 4.01/1.01    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 4.01/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/1.01  
% 4.01/1.01  fof(f47,plain,(
% 4.01/1.01    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 4.01/1.01    inference(cnf_transformation,[],[f3])).
% 4.01/1.01  
% 4.01/1.01  fof(f83,plain,(
% 4.01/1.01    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 4.01/1.01    inference(definition_unfolding,[],[f47,f65])).
% 4.01/1.01  
% 4.01/1.01  fof(f15,axiom,(
% 4.01/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 4.01/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/1.01  
% 4.01/1.01  fof(f35,plain,(
% 4.01/1.01    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 4.01/1.01    inference(ennf_transformation,[],[f15])).
% 4.01/1.01  
% 4.01/1.01  fof(f36,plain,(
% 4.01/1.01    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 4.01/1.01    inference(flattening,[],[f35])).
% 4.01/1.01  
% 4.01/1.01  fof(f69,plain,(
% 4.01/1.01    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X4) | k1_xboole_0 = X2 | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 4.01/1.01    inference(cnf_transformation,[],[f36])).
% 4.01/1.01  
% 4.01/1.01  fof(f4,axiom,(
% 4.01/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)))))),
% 4.01/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/1.01  
% 4.01/1.01  fof(f19,plain,(
% 4.01/1.01    ! [X0] : (((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 4.01/1.01    inference(ennf_transformation,[],[f4])).
% 4.01/1.01  
% 4.01/1.01  fof(f20,plain,(
% 4.01/1.01    ! [X0] : ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.01/1.01    inference(flattening,[],[f19])).
% 4.01/1.01  
% 4.01/1.01  fof(f48,plain,(
% 4.01/1.01    ( ! [X0] : (k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.01/1.01    inference(cnf_transformation,[],[f20])).
% 4.01/1.01  
% 4.01/1.01  fof(f86,plain,(
% 4.01/1.01    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.01/1.01    inference(definition_unfolding,[],[f48,f65])).
% 4.01/1.01  
% 4.01/1.01  fof(f81,plain,(
% 4.01/1.01    k1_xboole_0 != sK1),
% 4.01/1.01    inference(cnf_transformation,[],[f43])).
% 4.01/1.01  
% 4.01/1.01  fof(f82,plain,(
% 4.01/1.01    k2_funct_1(sK2) != sK3),
% 4.01/1.01    inference(cnf_transformation,[],[f43])).
% 4.01/1.01  
% 4.01/1.01  fof(f79,plain,(
% 4.01/1.01    v2_funct_1(sK2)),
% 4.01/1.01    inference(cnf_transformation,[],[f43])).
% 4.01/1.01  
% 4.01/1.01  cnf(c_35,negated_conjecture,
% 4.01/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 4.01/1.01      inference(cnf_transformation,[],[f73]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_1241,plain,
% 4.01/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 4.01/1.01      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_32,negated_conjecture,
% 4.01/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 4.01/1.01      inference(cnf_transformation,[],[f76]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_1244,plain,
% 4.01/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 4.01/1.01      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_20,plain,
% 4.01/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.01/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 4.01/1.01      | ~ v1_funct_1(X0)
% 4.01/1.01      | ~ v1_funct_1(X3)
% 4.01/1.01      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 4.01/1.01      inference(cnf_transformation,[],[f64]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_1250,plain,
% 4.01/1.01      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 4.01/1.01      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 4.01/1.01      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 4.01/1.01      | v1_funct_1(X4) != iProver_top
% 4.01/1.01      | v1_funct_1(X5) != iProver_top ),
% 4.01/1.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_3705,plain,
% 4.01/1.01      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 4.01/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 4.01/1.01      | v1_funct_1(X2) != iProver_top
% 4.01/1.01      | v1_funct_1(sK3) != iProver_top ),
% 4.01/1.01      inference(superposition,[status(thm)],[c_1244,c_1250]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_34,negated_conjecture,
% 4.01/1.01      ( v1_funct_1(sK3) ),
% 4.01/1.01      inference(cnf_transformation,[],[f74]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_41,plain,
% 4.01/1.01      ( v1_funct_1(sK3) = iProver_top ),
% 4.01/1.01      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_3821,plain,
% 4.01/1.01      ( v1_funct_1(X2) != iProver_top
% 4.01/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 4.01/1.01      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 4.01/1.01      inference(global_propositional_subsumption,
% 4.01/1.01                [status(thm)],
% 4.01/1.01                [c_3705,c_41]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_3822,plain,
% 4.01/1.01      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 4.01/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 4.01/1.01      | v1_funct_1(X2) != iProver_top ),
% 4.01/1.01      inference(renaming,[status(thm)],[c_3821]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_3830,plain,
% 4.01/1.01      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 4.01/1.01      | v1_funct_1(sK2) != iProver_top ),
% 4.01/1.01      inference(superposition,[status(thm)],[c_1241,c_3822]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_10,plain,
% 4.01/1.01      ( ~ r2_relset_1(X0,X1,X2,X3)
% 4.01/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 4.01/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 4.01/1.01      | X3 = X2 ),
% 4.01/1.01      inference(cnf_transformation,[],[f53]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_30,negated_conjecture,
% 4.01/1.01      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 4.01/1.01      inference(cnf_transformation,[],[f78]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_413,plain,
% 4.01/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.01/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.01/1.01      | X3 = X0
% 4.01/1.01      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 4.01/1.01      | k6_partfun1(sK0) != X3
% 4.01/1.01      | sK0 != X2
% 4.01/1.01      | sK0 != X1 ),
% 4.01/1.01      inference(resolution_lifted,[status(thm)],[c_10,c_30]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_414,plain,
% 4.01/1.01      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 4.01/1.01      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 4.01/1.01      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 4.01/1.01      inference(unflattening,[status(thm)],[c_413]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_11,plain,
% 4.01/1.01      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 4.01/1.01      inference(cnf_transformation,[],[f88]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_422,plain,
% 4.01/1.01      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 4.01/1.01      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 4.01/1.01      inference(forward_subsumption_resolution,
% 4.01/1.01                [status(thm)],
% 4.01/1.01                [c_414,c_11]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_1237,plain,
% 4.01/1.01      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 4.01/1.01      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 4.01/1.01      inference(predicate_to_equality,[status(thm)],[c_422]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_37,negated_conjecture,
% 4.01/1.01      ( v1_funct_1(sK2) ),
% 4.01/1.01      inference(cnf_transformation,[],[f71]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_18,plain,
% 4.01/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.01/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 4.01/1.01      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 4.01/1.01      | ~ v1_funct_1(X0)
% 4.01/1.01      | ~ v1_funct_1(X3) ),
% 4.01/1.01      inference(cnf_transformation,[],[f63]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_1497,plain,
% 4.01/1.01      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 4.01/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 4.01/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 4.01/1.01      | ~ v1_funct_1(sK3)
% 4.01/1.01      | ~ v1_funct_1(sK2) ),
% 4.01/1.01      inference(instantiation,[status(thm)],[c_18]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_2092,plain,
% 4.01/1.01      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 4.01/1.01      inference(global_propositional_subsumption,
% 4.01/1.01                [status(thm)],
% 4.01/1.01                [c_1237,c_37,c_35,c_34,c_32,c_422,c_1497]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_3831,plain,
% 4.01/1.01      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 4.01/1.01      | v1_funct_1(sK2) != iProver_top ),
% 4.01/1.01      inference(light_normalisation,[status(thm)],[c_3830,c_2092]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_38,plain,
% 4.01/1.01      ( v1_funct_1(sK2) = iProver_top ),
% 4.01/1.01      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_4079,plain,
% 4.01/1.01      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 4.01/1.01      inference(global_propositional_subsumption,
% 4.01/1.01                [status(thm)],
% 4.01/1.01                [c_3831,c_38]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_6,plain,
% 4.01/1.01      ( ~ v1_funct_1(X0)
% 4.01/1.01      | ~ v1_funct_1(X1)
% 4.01/1.01      | ~ v2_funct_1(X0)
% 4.01/1.01      | ~ v1_relat_1(X0)
% 4.01/1.01      | ~ v1_relat_1(X1)
% 4.01/1.01      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
% 4.01/1.01      | k1_relat_1(X0) != k2_relat_1(X1)
% 4.01/1.01      | k2_funct_1(X0) = X1 ),
% 4.01/1.01      inference(cnf_transformation,[],[f87]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_1262,plain,
% 4.01/1.01      ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 4.01/1.01      | k1_relat_1(X1) != k2_relat_1(X0)
% 4.01/1.01      | k2_funct_1(X1) = X0
% 4.01/1.01      | v1_funct_1(X1) != iProver_top
% 4.01/1.01      | v1_funct_1(X0) != iProver_top
% 4.01/1.01      | v2_funct_1(X1) != iProver_top
% 4.01/1.01      | v1_relat_1(X1) != iProver_top
% 4.01/1.01      | v1_relat_1(X0) != iProver_top ),
% 4.01/1.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_4186,plain,
% 4.01/1.01      ( k1_relat_1(sK3) != k2_relat_1(sK2)
% 4.01/1.01      | k2_funct_1(sK3) = sK2
% 4.01/1.01      | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
% 4.01/1.01      | v1_funct_1(sK3) != iProver_top
% 4.01/1.01      | v1_funct_1(sK2) != iProver_top
% 4.01/1.01      | v2_funct_1(sK3) != iProver_top
% 4.01/1.01      | v1_relat_1(sK3) != iProver_top
% 4.01/1.01      | v1_relat_1(sK2) != iProver_top ),
% 4.01/1.01      inference(superposition,[status(thm)],[c_4079,c_1262]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_8,plain,
% 4.01/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.01/1.01      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 4.01/1.01      inference(cnf_transformation,[],[f52]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_1260,plain,
% 4.01/1.01      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 4.01/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 4.01/1.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_2281,plain,
% 4.01/1.01      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 4.01/1.01      inference(superposition,[status(thm)],[c_1241,c_1260]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_31,negated_conjecture,
% 4.01/1.01      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 4.01/1.01      inference(cnf_transformation,[],[f77]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_2282,plain,
% 4.01/1.01      ( k2_relat_1(sK2) = sK1 ),
% 4.01/1.01      inference(light_normalisation,[status(thm)],[c_2281,c_31]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_2280,plain,
% 4.01/1.01      ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 4.01/1.01      inference(superposition,[status(thm)],[c_1244,c_1260]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_21,plain,
% 4.01/1.01      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 4.01/1.01      | ~ v1_funct_2(X3,X1,X0)
% 4.01/1.01      | ~ v1_funct_2(X2,X0,X1)
% 4.01/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 4.01/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 4.01/1.01      | ~ v1_funct_1(X2)
% 4.01/1.01      | ~ v1_funct_1(X3)
% 4.01/1.01      | k2_relset_1(X1,X0,X3) = X0 ),
% 4.01/1.01      inference(cnf_transformation,[],[f66]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_426,plain,
% 4.01/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 4.01/1.01      | ~ v1_funct_2(X3,X2,X1)
% 4.01/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.01/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 4.01/1.01      | ~ v1_funct_1(X0)
% 4.01/1.01      | ~ v1_funct_1(X3)
% 4.01/1.01      | k1_partfun1(X2,X1,X1,X2,X3,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 4.01/1.01      | k2_relset_1(X1,X2,X0) = X2
% 4.01/1.01      | k6_partfun1(X2) != k6_partfun1(sK0)
% 4.01/1.01      | sK0 != X2 ),
% 4.01/1.01      inference(resolution_lifted,[status(thm)],[c_21,c_30]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_427,plain,
% 4.01/1.01      ( ~ v1_funct_2(X0,X1,sK0)
% 4.01/1.01      | ~ v1_funct_2(X2,sK0,X1)
% 4.01/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 4.01/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 4.01/1.01      | ~ v1_funct_1(X0)
% 4.01/1.01      | ~ v1_funct_1(X2)
% 4.01/1.01      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 4.01/1.01      | k2_relset_1(X1,sK0,X0) = sK0
% 4.01/1.01      | k6_partfun1(sK0) != k6_partfun1(sK0) ),
% 4.01/1.01      inference(unflattening,[status(thm)],[c_426]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_514,plain,
% 4.01/1.01      ( ~ v1_funct_2(X0,X1,sK0)
% 4.01/1.01      | ~ v1_funct_2(X2,sK0,X1)
% 4.01/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 4.01/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 4.01/1.01      | ~ v1_funct_1(X0)
% 4.01/1.01      | ~ v1_funct_1(X2)
% 4.01/1.01      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 4.01/1.01      | k2_relset_1(X1,sK0,X0) = sK0 ),
% 4.01/1.01      inference(equality_resolution_simp,[status(thm)],[c_427]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_1236,plain,
% 4.01/1.01      ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 4.01/1.01      | k2_relset_1(X0,sK0,X2) = sK0
% 4.01/1.01      | v1_funct_2(X2,X0,sK0) != iProver_top
% 4.01/1.01      | v1_funct_2(X1,sK0,X0) != iProver_top
% 4.01/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 4.01/1.01      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 4.01/1.01      | v1_funct_1(X2) != iProver_top
% 4.01/1.01      | v1_funct_1(X1) != iProver_top ),
% 4.01/1.01      inference(predicate_to_equality,[status(thm)],[c_514]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_1706,plain,
% 4.01/1.01      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 4.01/1.01      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 4.01/1.01      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 4.01/1.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 4.01/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 4.01/1.01      | v1_funct_1(sK3) != iProver_top
% 4.01/1.01      | v1_funct_1(sK2) != iProver_top ),
% 4.01/1.01      inference(equality_resolution,[status(thm)],[c_1236]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_36,negated_conjecture,
% 4.01/1.01      ( v1_funct_2(sK2,sK0,sK1) ),
% 4.01/1.01      inference(cnf_transformation,[],[f72]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_39,plain,
% 4.01/1.01      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 4.01/1.01      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_40,plain,
% 4.01/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 4.01/1.01      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_33,negated_conjecture,
% 4.01/1.01      ( v1_funct_2(sK3,sK1,sK0) ),
% 4.01/1.01      inference(cnf_transformation,[],[f75]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_42,plain,
% 4.01/1.01      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 4.01/1.01      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_43,plain,
% 4.01/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 4.01/1.01      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_2183,plain,
% 4.01/1.01      ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 4.01/1.01      inference(global_propositional_subsumption,
% 4.01/1.01                [status(thm)],
% 4.01/1.01                [c_1706,c_38,c_39,c_40,c_41,c_42,c_43]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_2283,plain,
% 4.01/1.01      ( k2_relat_1(sK3) = sK0 ),
% 4.01/1.01      inference(light_normalisation,[status(thm)],[c_2280,c_2183]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_4187,plain,
% 4.01/1.01      ( k1_relat_1(sK3) != sK1
% 4.01/1.01      | k2_funct_1(sK3) = sK2
% 4.01/1.01      | k6_partfun1(sK0) != k6_partfun1(sK0)
% 4.01/1.01      | v1_funct_1(sK3) != iProver_top
% 4.01/1.01      | v1_funct_1(sK2) != iProver_top
% 4.01/1.01      | v2_funct_1(sK3) != iProver_top
% 4.01/1.01      | v1_relat_1(sK3) != iProver_top
% 4.01/1.01      | v1_relat_1(sK2) != iProver_top ),
% 4.01/1.01      inference(light_normalisation,[status(thm)],[c_4186,c_2282,c_2283]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_4188,plain,
% 4.01/1.01      ( k1_relat_1(sK3) != sK1
% 4.01/1.01      | k2_funct_1(sK3) = sK2
% 4.01/1.01      | v1_funct_1(sK3) != iProver_top
% 4.01/1.01      | v1_funct_1(sK2) != iProver_top
% 4.01/1.01      | v2_funct_1(sK3) != iProver_top
% 4.01/1.01      | v1_relat_1(sK3) != iProver_top
% 4.01/1.01      | v1_relat_1(sK2) != iProver_top ),
% 4.01/1.01      inference(equality_resolution_simp,[status(thm)],[c_4187]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_28,negated_conjecture,
% 4.01/1.01      ( k1_xboole_0 != sK0 ),
% 4.01/1.01      inference(cnf_transformation,[],[f80]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_702,plain,( X0 = X0 ),theory(equality) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_731,plain,
% 4.01/1.01      ( k1_xboole_0 = k1_xboole_0 ),
% 4.01/1.01      inference(instantiation,[status(thm)],[c_702]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_703,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_1366,plain,
% 4.01/1.01      ( sK0 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK0 ),
% 4.01/1.01      inference(instantiation,[status(thm)],[c_703]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_1367,plain,
% 4.01/1.01      ( sK0 != k1_xboole_0
% 4.01/1.01      | k1_xboole_0 = sK0
% 4.01/1.01      | k1_xboole_0 != k1_xboole_0 ),
% 4.01/1.01      inference(instantiation,[status(thm)],[c_1366]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_0,plain,
% 4.01/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 4.01/1.01      | ~ v1_relat_1(X1)
% 4.01/1.01      | v1_relat_1(X0) ),
% 4.01/1.01      inference(cnf_transformation,[],[f44]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_1268,plain,
% 4.01/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 4.01/1.01      | v1_relat_1(X1) != iProver_top
% 4.01/1.01      | v1_relat_1(X0) = iProver_top ),
% 4.01/1.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_2382,plain,
% 4.01/1.01      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 4.01/1.01      | v1_relat_1(sK3) = iProver_top ),
% 4.01/1.01      inference(superposition,[status(thm)],[c_1244,c_1268]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_1,plain,
% 4.01/1.01      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 4.01/1.01      inference(cnf_transformation,[],[f45]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_2660,plain,
% 4.01/1.01      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
% 4.01/1.01      inference(instantiation,[status(thm)],[c_1]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_2661,plain,
% 4.01/1.01      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
% 4.01/1.01      inference(predicate_to_equality,[status(thm)],[c_2660]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_1267,plain,
% 4.01/1.01      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 4.01/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_2383,plain,
% 4.01/1.01      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 4.01/1.01      | v1_relat_1(sK2) = iProver_top ),
% 4.01/1.01      inference(superposition,[status(thm)],[c_1241,c_1268]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_2828,plain,
% 4.01/1.01      ( v1_relat_1(sK2) = iProver_top ),
% 4.01/1.01      inference(superposition,[status(thm)],[c_1267,c_2383]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_17,plain,
% 4.01/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 4.01/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.01/1.01      | k1_relset_1(X1,X2,X0) = X1
% 4.01/1.01      | k1_xboole_0 = X2 ),
% 4.01/1.01      inference(cnf_transformation,[],[f56]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_1253,plain,
% 4.01/1.01      ( k1_relset_1(X0,X1,X2) = X0
% 4.01/1.01      | k1_xboole_0 = X1
% 4.01/1.01      | v1_funct_2(X2,X0,X1) != iProver_top
% 4.01/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 4.01/1.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_3637,plain,
% 4.01/1.01      ( k1_relset_1(sK1,sK0,sK3) = sK1
% 4.01/1.01      | sK0 = k1_xboole_0
% 4.01/1.01      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 4.01/1.01      inference(superposition,[status(thm)],[c_1244,c_1253]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_7,plain,
% 4.01/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.01/1.01      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 4.01/1.01      inference(cnf_transformation,[],[f51]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_1261,plain,
% 4.01/1.01      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 4.01/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 4.01/1.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_2377,plain,
% 4.01/1.01      ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
% 4.01/1.01      inference(superposition,[status(thm)],[c_1244,c_1261]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_3640,plain,
% 4.01/1.01      ( k1_relat_1(sK3) = sK1
% 4.01/1.01      | sK0 = k1_xboole_0
% 4.01/1.01      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 4.01/1.01      inference(demodulation,[status(thm)],[c_3637,c_2377]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_2,plain,
% 4.01/1.01      ( v2_funct_1(k6_partfun1(X0)) ),
% 4.01/1.01      inference(cnf_transformation,[],[f83]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_1266,plain,
% 4.01/1.01      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 4.01/1.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_23,plain,
% 4.01/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 4.01/1.01      | ~ v1_funct_2(X3,X2,X4)
% 4.01/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.01/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
% 4.01/1.01      | ~ v1_funct_1(X3)
% 4.01/1.01      | ~ v1_funct_1(X0)
% 4.01/1.01      | v2_funct_1(X3)
% 4.01/1.01      | ~ v2_funct_1(k1_partfun1(X1,X2,X2,X4,X0,X3))
% 4.01/1.01      | k2_relset_1(X1,X2,X0) != X2
% 4.01/1.01      | k1_xboole_0 = X4 ),
% 4.01/1.01      inference(cnf_transformation,[],[f69]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_1248,plain,
% 4.01/1.01      ( k2_relset_1(X0,X1,X2) != X1
% 4.01/1.01      | k1_xboole_0 = X3
% 4.01/1.01      | v1_funct_2(X2,X0,X1) != iProver_top
% 4.01/1.01      | v1_funct_2(X4,X1,X3) != iProver_top
% 4.01/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 4.01/1.01      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
% 4.01/1.01      | v1_funct_1(X4) != iProver_top
% 4.01/1.01      | v1_funct_1(X2) != iProver_top
% 4.01/1.01      | v2_funct_1(X4) = iProver_top
% 4.01/1.01      | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top ),
% 4.01/1.01      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_4177,plain,
% 4.01/1.01      ( k1_xboole_0 = X0
% 4.01/1.01      | v1_funct_2(X1,sK1,X0) != iProver_top
% 4.01/1.01      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 4.01/1.01      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 4.01/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 4.01/1.01      | v1_funct_1(X1) != iProver_top
% 4.01/1.01      | v1_funct_1(sK2) != iProver_top
% 4.01/1.01      | v2_funct_1(X1) = iProver_top
% 4.01/1.01      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
% 4.01/1.01      inference(superposition,[status(thm)],[c_31,c_1248]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_4323,plain,
% 4.01/1.01      ( v1_funct_1(X1) != iProver_top
% 4.01/1.01      | v1_funct_2(X1,sK1,X0) != iProver_top
% 4.01/1.01      | k1_xboole_0 = X0
% 4.01/1.01      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 4.01/1.01      | v2_funct_1(X1) = iProver_top
% 4.01/1.01      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
% 4.01/1.01      inference(global_propositional_subsumption,
% 4.01/1.01                [status(thm)],
% 4.01/1.01                [c_4177,c_38,c_39,c_40]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_4324,plain,
% 4.01/1.01      ( k1_xboole_0 = X0
% 4.01/1.01      | v1_funct_2(X1,sK1,X0) != iProver_top
% 4.01/1.01      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 4.01/1.01      | v1_funct_1(X1) != iProver_top
% 4.01/1.01      | v2_funct_1(X1) = iProver_top
% 4.01/1.01      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
% 4.01/1.01      inference(renaming,[status(thm)],[c_4323]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_4327,plain,
% 4.01/1.01      ( sK0 = k1_xboole_0
% 4.01/1.01      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 4.01/1.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 4.01/1.01      | v1_funct_1(sK3) != iProver_top
% 4.01/1.01      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 4.01/1.01      | v2_funct_1(sK3) = iProver_top ),
% 4.01/1.01      inference(superposition,[status(thm)],[c_2092,c_4324]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_4416,plain,
% 4.01/1.01      ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 4.01/1.01      | v2_funct_1(sK3) = iProver_top ),
% 4.01/1.01      inference(global_propositional_subsumption,
% 4.01/1.01                [status(thm)],
% 4.01/1.01                [c_4327,c_41,c_42,c_43,c_28,c_731,c_1367]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_4420,plain,
% 4.01/1.01      ( v2_funct_1(sK3) = iProver_top ),
% 4.01/1.01      inference(superposition,[status(thm)],[c_1266,c_4416]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_5498,plain,
% 4.01/1.01      ( k2_funct_1(sK3) = sK2 ),
% 4.01/1.01      inference(global_propositional_subsumption,
% 4.01/1.01                [status(thm)],
% 4.01/1.01                [c_4188,c_38,c_41,c_42,c_28,c_731,c_1367,c_2382,c_2661,
% 4.01/1.01                 c_2828,c_3640,c_4420]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_1242,plain,
% 4.01/1.01      ( v1_funct_1(sK3) = iProver_top ),
% 4.01/1.01      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_5,plain,
% 4.01/1.01      ( ~ v1_funct_1(X0)
% 4.01/1.01      | ~ v2_funct_1(X0)
% 4.01/1.01      | ~ v1_relat_1(X0)
% 4.01/1.01      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
% 4.01/1.01      inference(cnf_transformation,[],[f86]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_1263,plain,
% 4.01/1.01      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
% 4.01/1.01      | v1_funct_1(X0) != iProver_top
% 4.01/1.01      | v2_funct_1(X0) != iProver_top
% 4.01/1.01      | v1_relat_1(X0) != iProver_top ),
% 4.01/1.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_3079,plain,
% 4.01/1.01      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
% 4.01/1.01      | v2_funct_1(sK3) != iProver_top
% 4.01/1.01      | v1_relat_1(sK3) != iProver_top ),
% 4.01/1.01      inference(superposition,[status(thm)],[c_1242,c_1263]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_3233,plain,
% 4.01/1.01      ( v2_funct_1(sK3) != iProver_top
% 4.01/1.01      | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3)) ),
% 4.01/1.01      inference(global_propositional_subsumption,
% 4.01/1.01                [status(thm)],
% 4.01/1.01                [c_3079,c_2382,c_2661]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_3234,plain,
% 4.01/1.01      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
% 4.01/1.01      | v2_funct_1(sK3) != iProver_top ),
% 4.01/1.01      inference(renaming,[status(thm)],[c_3233]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_4445,plain,
% 4.01/1.01      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3)) ),
% 4.01/1.01      inference(superposition,[status(thm)],[c_4420,c_3234]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_5500,plain,
% 4.01/1.01      ( k5_relat_1(sK3,sK2) = k6_partfun1(k1_relat_1(sK3)) ),
% 4.01/1.01      inference(demodulation,[status(thm)],[c_5498,c_4445]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_6816,plain,
% 4.01/1.01      ( k1_relat_1(sK3) = sK1 ),
% 4.01/1.01      inference(global_propositional_subsumption,
% 4.01/1.01                [status(thm)],
% 4.01/1.01                [c_3640,c_42,c_28,c_731,c_1367]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_7186,plain,
% 4.01/1.01      ( k5_relat_1(sK3,sK2) = k6_partfun1(sK1) ),
% 4.01/1.01      inference(light_normalisation,[status(thm)],[c_5500,c_5500,c_6816]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_7190,plain,
% 4.01/1.01      ( k1_relat_1(sK2) != k2_relat_1(sK3)
% 4.01/1.01      | k2_funct_1(sK2) = sK3
% 4.01/1.01      | k6_partfun1(k2_relat_1(sK2)) != k6_partfun1(sK1)
% 4.01/1.01      | v1_funct_1(sK3) != iProver_top
% 4.01/1.01      | v1_funct_1(sK2) != iProver_top
% 4.01/1.01      | v2_funct_1(sK2) != iProver_top
% 4.01/1.01      | v1_relat_1(sK3) != iProver_top
% 4.01/1.01      | v1_relat_1(sK2) != iProver_top ),
% 4.01/1.01      inference(superposition,[status(thm)],[c_7186,c_1262]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_3638,plain,
% 4.01/1.01      ( k1_relset_1(sK0,sK1,sK2) = sK0
% 4.01/1.01      | sK1 = k1_xboole_0
% 4.01/1.01      | v1_funct_2(sK2,sK0,sK1) != iProver_top ),
% 4.01/1.01      inference(superposition,[status(thm)],[c_1241,c_1253]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_2378,plain,
% 4.01/1.01      ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
% 4.01/1.01      inference(superposition,[status(thm)],[c_1241,c_1261]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_3639,plain,
% 4.01/1.01      ( k1_relat_1(sK2) = sK0
% 4.01/1.01      | sK1 = k1_xboole_0
% 4.01/1.01      | v1_funct_2(sK2,sK0,sK1) != iProver_top ),
% 4.01/1.01      inference(demodulation,[status(thm)],[c_3638,c_2378]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_27,negated_conjecture,
% 4.01/1.01      ( k1_xboole_0 != sK1 ),
% 4.01/1.01      inference(cnf_transformation,[],[f81]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_1340,plain,
% 4.01/1.01      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 4.01/1.01      inference(instantiation,[status(thm)],[c_703]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_1341,plain,
% 4.01/1.01      ( sK1 != k1_xboole_0
% 4.01/1.01      | k1_xboole_0 = sK1
% 4.01/1.01      | k1_xboole_0 != k1_xboole_0 ),
% 4.01/1.01      inference(instantiation,[status(thm)],[c_1340]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_6225,plain,
% 4.01/1.01      ( k1_relat_1(sK2) = sK0 ),
% 4.01/1.01      inference(global_propositional_subsumption,
% 4.01/1.01                [status(thm)],
% 4.01/1.01                [c_3639,c_39,c_27,c_731,c_1341]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_7191,plain,
% 4.01/1.01      ( k2_funct_1(sK2) = sK3
% 4.01/1.01      | k6_partfun1(sK1) != k6_partfun1(sK1)
% 4.01/1.01      | sK0 != sK0
% 4.01/1.01      | v1_funct_1(sK3) != iProver_top
% 4.01/1.01      | v1_funct_1(sK2) != iProver_top
% 4.01/1.01      | v2_funct_1(sK2) != iProver_top
% 4.01/1.01      | v1_relat_1(sK3) != iProver_top
% 4.01/1.01      | v1_relat_1(sK2) != iProver_top ),
% 4.01/1.01      inference(light_normalisation,
% 4.01/1.01                [status(thm)],
% 4.01/1.01                [c_7190,c_2282,c_2283,c_6225]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_7192,plain,
% 4.01/1.01      ( k2_funct_1(sK2) = sK3
% 4.01/1.01      | v1_funct_1(sK3) != iProver_top
% 4.01/1.01      | v1_funct_1(sK2) != iProver_top
% 4.01/1.01      | v2_funct_1(sK2) != iProver_top
% 4.01/1.01      | v1_relat_1(sK3) != iProver_top
% 4.01/1.01      | v1_relat_1(sK2) != iProver_top ),
% 4.01/1.01      inference(equality_resolution_simp,[status(thm)],[c_7191]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_26,negated_conjecture,
% 4.01/1.01      ( k2_funct_1(sK2) != sK3 ),
% 4.01/1.01      inference(cnf_transformation,[],[f82]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_29,negated_conjecture,
% 4.01/1.01      ( v2_funct_1(sK2) ),
% 4.01/1.01      inference(cnf_transformation,[],[f79]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(c_45,plain,
% 4.01/1.01      ( v2_funct_1(sK2) = iProver_top ),
% 4.01/1.01      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 4.01/1.01  
% 4.01/1.01  cnf(contradiction,plain,
% 4.01/1.01      ( $false ),
% 4.01/1.01      inference(minisat,
% 4.01/1.01                [status(thm)],
% 4.01/1.01                [c_7192,c_2828,c_2661,c_2382,c_26,c_45,c_41,c_38]) ).
% 4.01/1.01  
% 4.01/1.01  
% 4.01/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 4.01/1.01  
% 4.01/1.01  ------                               Statistics
% 4.01/1.01  
% 4.01/1.01  ------ General
% 4.01/1.01  
% 4.01/1.01  abstr_ref_over_cycles:                  0
% 4.01/1.01  abstr_ref_under_cycles:                 0
% 4.01/1.01  gc_basic_clause_elim:                   0
% 4.01/1.01  forced_gc_time:                         0
% 4.01/1.01  parsing_time:                           0.008
% 4.01/1.01  unif_index_cands_time:                  0.
% 4.01/1.01  unif_index_add_time:                    0.
% 4.01/1.01  orderings_time:                         0.
% 4.01/1.01  out_proof_time:                         0.012
% 4.01/1.01  total_time:                             0.274
% 4.01/1.01  num_of_symbols:                         52
% 4.01/1.01  num_of_terms:                           11806
% 4.01/1.01  
% 4.01/1.01  ------ Preprocessing
% 4.01/1.01  
% 4.01/1.01  num_of_splits:                          0
% 4.01/1.01  num_of_split_atoms:                     0
% 4.01/1.01  num_of_reused_defs:                     0
% 4.01/1.01  num_eq_ax_congr_red:                    12
% 4.01/1.01  num_of_sem_filtered_clauses:            1
% 4.01/1.01  num_of_subtypes:                        0
% 4.01/1.01  monotx_restored_types:                  0
% 4.01/1.01  sat_num_of_epr_types:                   0
% 4.01/1.01  sat_num_of_non_cyclic_types:            0
% 4.01/1.01  sat_guarded_non_collapsed_types:        0
% 4.01/1.01  num_pure_diseq_elim:                    0
% 4.01/1.01  simp_replaced_by:                       0
% 4.01/1.01  res_preprocessed:                       180
% 4.01/1.01  prep_upred:                             0
% 4.01/1.01  prep_unflattend:                        12
% 4.01/1.01  smt_new_axioms:                         0
% 4.01/1.01  pred_elim_cands:                        5
% 4.01/1.01  pred_elim:                              1
% 4.01/1.01  pred_elim_cl:                           1
% 4.01/1.01  pred_elim_cycles:                       3
% 4.01/1.01  merged_defs:                            0
% 4.01/1.01  merged_defs_ncl:                        0
% 4.01/1.01  bin_hyper_res:                          0
% 4.01/1.01  prep_cycles:                            4
% 4.01/1.01  pred_elim_time:                         0.003
% 4.01/1.01  splitting_time:                         0.
% 4.01/1.01  sem_filter_time:                        0.
% 4.01/1.01  monotx_time:                            0.
% 4.01/1.01  subtype_inf_time:                       0.
% 4.01/1.01  
% 4.01/1.01  ------ Problem properties
% 4.01/1.01  
% 4.01/1.01  clauses:                                37
% 4.01/1.01  conjectures:                            11
% 4.01/1.01  epr:                                    7
% 4.01/1.01  horn:                                   31
% 4.01/1.01  ground:                                 12
% 4.01/1.01  unary:                                  15
% 4.01/1.01  binary:                                 3
% 4.01/1.01  lits:                                   130
% 4.01/1.01  lits_eq:                                32
% 4.01/1.01  fd_pure:                                0
% 4.01/1.01  fd_pseudo:                              0
% 4.01/1.01  fd_cond:                                5
% 4.01/1.01  fd_pseudo_cond:                         1
% 4.01/1.01  ac_symbols:                             0
% 4.01/1.01  
% 4.01/1.01  ------ Propositional Solver
% 4.01/1.01  
% 4.01/1.01  prop_solver_calls:                      30
% 4.01/1.01  prop_fast_solver_calls:                 1702
% 4.01/1.01  smt_solver_calls:                       0
% 4.01/1.01  smt_fast_solver_calls:                  0
% 4.01/1.01  prop_num_of_clauses:                    3374
% 4.01/1.01  prop_preprocess_simplified:             8849
% 4.01/1.01  prop_fo_subsumed:                       89
% 4.01/1.01  prop_solver_time:                       0.
% 4.01/1.01  smt_solver_time:                        0.
% 4.01/1.01  smt_fast_solver_time:                   0.
% 4.01/1.01  prop_fast_solver_time:                  0.
% 4.01/1.01  prop_unsat_core_time:                   0.
% 4.01/1.01  
% 4.01/1.01  ------ QBF
% 4.01/1.01  
% 4.01/1.01  qbf_q_res:                              0
% 4.01/1.01  qbf_num_tautologies:                    0
% 4.01/1.01  qbf_prep_cycles:                        0
% 4.01/1.01  
% 4.01/1.01  ------ BMC1
% 4.01/1.01  
% 4.01/1.01  bmc1_current_bound:                     -1
% 4.01/1.01  bmc1_last_solved_bound:                 -1
% 4.01/1.01  bmc1_unsat_core_size:                   -1
% 4.01/1.01  bmc1_unsat_core_parents_size:           -1
% 4.01/1.01  bmc1_merge_next_fun:                    0
% 4.01/1.01  bmc1_unsat_core_clauses_time:           0.
% 4.01/1.01  
% 4.01/1.01  ------ Instantiation
% 4.01/1.01  
% 4.01/1.01  inst_num_of_clauses:                    979
% 4.01/1.01  inst_num_in_passive:                    426
% 4.01/1.01  inst_num_in_active:                     540
% 4.01/1.01  inst_num_in_unprocessed:                13
% 4.01/1.01  inst_num_of_loops:                      560
% 4.01/1.01  inst_num_of_learning_restarts:          0
% 4.01/1.01  inst_num_moves_active_passive:          17
% 4.01/1.01  inst_lit_activity:                      0
% 4.01/1.01  inst_lit_activity_moves:                0
% 4.01/1.01  inst_num_tautologies:                   0
% 4.01/1.01  inst_num_prop_implied:                  0
% 4.01/1.01  inst_num_existing_simplified:           0
% 4.01/1.01  inst_num_eq_res_simplified:             0
% 4.01/1.01  inst_num_child_elim:                    0
% 4.01/1.01  inst_num_of_dismatching_blockings:      335
% 4.01/1.01  inst_num_of_non_proper_insts:           972
% 4.01/1.01  inst_num_of_duplicates:                 0
% 4.01/1.01  inst_inst_num_from_inst_to_res:         0
% 4.01/1.01  inst_dismatching_checking_time:         0.
% 4.01/1.01  
% 4.01/1.01  ------ Resolution
% 4.01/1.01  
% 4.01/1.01  res_num_of_clauses:                     0
% 4.01/1.01  res_num_in_passive:                     0
% 4.01/1.01  res_num_in_active:                      0
% 4.01/1.01  res_num_of_loops:                       184
% 4.01/1.01  res_forward_subset_subsumed:            138
% 4.01/1.01  res_backward_subset_subsumed:           0
% 4.01/1.01  res_forward_subsumed:                   0
% 4.01/1.01  res_backward_subsumed:                  0
% 4.01/1.01  res_forward_subsumption_resolution:     2
% 4.01/1.01  res_backward_subsumption_resolution:    0
% 4.01/1.01  res_clause_to_clause_subsumption:       335
% 4.01/1.01  res_orphan_elimination:                 0
% 4.01/1.01  res_tautology_del:                      45
% 4.01/1.01  res_num_eq_res_simplified:              1
% 4.01/1.01  res_num_sel_changes:                    0
% 4.01/1.01  res_moves_from_active_to_pass:          0
% 4.01/1.01  
% 4.01/1.01  ------ Superposition
% 4.01/1.01  
% 4.01/1.01  sup_time_total:                         0.
% 4.01/1.01  sup_time_generating:                    0.
% 4.01/1.01  sup_time_sim_full:                      0.
% 4.01/1.01  sup_time_sim_immed:                     0.
% 4.01/1.01  
% 4.01/1.01  sup_num_of_clauses:                     154
% 4.01/1.01  sup_num_in_active:                      88
% 4.01/1.01  sup_num_in_passive:                     66
% 4.01/1.01  sup_num_of_loops:                       110
% 4.01/1.01  sup_fw_superposition:                   88
% 4.01/1.01  sup_bw_superposition:                   77
% 4.01/1.01  sup_immediate_simplified:               72
% 4.01/1.01  sup_given_eliminated:                   0
% 4.01/1.01  comparisons_done:                       0
% 4.01/1.01  comparisons_avoided:                    0
% 4.01/1.01  
% 4.01/1.01  ------ Simplifications
% 4.01/1.01  
% 4.01/1.01  
% 4.01/1.01  sim_fw_subset_subsumed:                 10
% 4.01/1.01  sim_bw_subset_subsumed:                 15
% 4.01/1.01  sim_fw_subsumed:                        12
% 4.01/1.01  sim_bw_subsumed:                        3
% 4.01/1.01  sim_fw_subsumption_res:                 0
% 4.01/1.01  sim_bw_subsumption_res:                 0
% 4.01/1.01  sim_tautology_del:                      0
% 4.01/1.01  sim_eq_tautology_del:                   9
% 4.01/1.01  sim_eq_res_simp:                        2
% 4.01/1.01  sim_fw_demodulated:                     11
% 4.01/1.01  sim_bw_demodulated:                     13
% 4.01/1.01  sim_light_normalised:                   45
% 4.01/1.01  sim_joinable_taut:                      0
% 4.01/1.01  sim_joinable_simp:                      0
% 4.01/1.01  sim_ac_normalised:                      0
% 4.01/1.01  sim_smt_subsumption:                    0
% 4.01/1.01  
%------------------------------------------------------------------------------
