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
% DateTime   : Thu Dec  3 12:03:24 EST 2020

% Result     : Theorem 3.37s
% Output     : CNFRefutation 3.37s
% Verified   : 
% Statistics : Number of formulae       :  199 ( 876 expanded)
%              Number of clauses        :  124 ( 301 expanded)
%              Number of leaves         :   19 ( 205 expanded)
%              Depth                    :   24
%              Number of atoms          :  615 (6552 expanded)
%              Number of equality atoms :  235 (2211 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   24 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,conjecture,(
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

fof(f18,negated_conjecture,(
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
    inference(negated_conjecture,[],[f17])).

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f44,plain,(
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

fof(f43,plain,
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

fof(f45,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f40,f44,f43])).

fof(f74,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f45])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f15,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_partfun1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f53,f65])).

fof(f71,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f45])).

fof(f75,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f45])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f77,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f69,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f70,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f28,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f55,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f83,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f55,f65])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f35])).

fof(f64,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f72,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f31])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f76,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f45])).

fof(f12,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f85,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f61,f65])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f33])).

fof(f63,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_partfun1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f52,f65])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f80,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_705,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_1170,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_705])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_718,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(X1_52))
    | ~ v1_relat_1(X1_52)
    | v1_relat_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1161,plain,
    ( m1_subset_1(X0_52,k1_zfmisc_1(X1_52)) != iProver_top
    | v1_relat_1(X1_52) != iProver_top
    | v1_relat_1(X0_52) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_718])).

cnf(c_1594,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1170,c_1161])).

cnf(c_39,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_1371,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | v1_relat_1(X0_52)
    | ~ v1_relat_1(k2_zfmisc_1(X0_53,X1_53)) ),
    inference(instantiation,[status(thm)],[c_718])).

cnf(c_1533,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1371])).

cnf(c_1534,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1533])).

cnf(c_3,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_717,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_53,X1_53)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1575,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_717])).

cnf(c_1576,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1575])).

cnf(c_1713,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1594,c_39,c_1534,c_1576])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_partfun1(X1),X0) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_715,plain,
    ( ~ v1_relat_1(X0_52)
    | k5_relat_1(k6_partfun1(X0_53),X0_52) = k7_relat_1(X0_52,X0_53) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1164,plain,
    ( k5_relat_1(k6_partfun1(X0_53),X0_52) = k7_relat_1(X0_52,X0_53)
    | v1_relat_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_715])).

cnf(c_2118,plain,
    ( k5_relat_1(k6_partfun1(X0_53),sK3) = k7_relat_1(sK3,X0_53) ),
    inference(superposition,[status(thm)],[c_1713,c_1164])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_702,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_31])).

cnf(c_1173,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_702])).

cnf(c_1598,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1173,c_1161])).

cnf(c_36,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_1536,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1371])).

cnf(c_1537,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1536])).

cnf(c_1578,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_717])).

cnf(c_1579,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1578])).

cnf(c_1766,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1598,c_36,c_1537,c_1579])).

cnf(c_27,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_706,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_25,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_460,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_25])).

cnf(c_461,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(unflattening,[status(thm)],[c_460])).

cnf(c_33,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_465,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_2(sK2,X0,X1)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_461,c_33])).

cnf(c_466,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(renaming,[status(thm)],[c_465])).

cnf(c_694,plain,
    ( ~ v1_funct_2(sK2,X0_53,X1_53)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1_53,X0_53)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | k2_relset_1(X0_53,X1_53,sK2) != X1_53 ),
    inference(subtyping,[status(esa)],[c_466])).

cnf(c_1181,plain,
    ( k2_relset_1(X0_53,X1_53,sK2) != X1_53
    | v1_funct_2(sK2,X0_53,X1_53) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1_53,X0_53))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_694])).

cnf(c_2712,plain,
    ( v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_706,c_1181])).

cnf(c_32,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_35,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_1363,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k2_relset_1(sK0,sK1,sK2) != sK1 ),
    inference(instantiation,[status(thm)],[c_694])).

cnf(c_1364,plain,
    ( k2_relset_1(sK0,sK1,sK2) != sK1
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1363])).

cnf(c_2715,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2712,c_35,c_36,c_706,c_1364])).

cnf(c_2721,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2715,c_1161])).

cnf(c_1544,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(k2_funct_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_1371])).

cnf(c_1545,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1544])).

cnf(c_3094,plain,
    ( v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2721,c_35,c_36,c_706,c_1364,c_1545,c_1576])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_716,plain,
    ( ~ v1_relat_1(X0_52)
    | ~ v1_relat_1(X1_52)
    | ~ v1_relat_1(X2_52)
    | k5_relat_1(k5_relat_1(X0_52,X1_52),X2_52) = k5_relat_1(X0_52,k5_relat_1(X1_52,X2_52)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1163,plain,
    ( k5_relat_1(k5_relat_1(X0_52,X1_52),X2_52) = k5_relat_1(X0_52,k5_relat_1(X1_52,X2_52))
    | v1_relat_1(X0_52) != iProver_top
    | v1_relat_1(X1_52) != iProver_top
    | v1_relat_1(X2_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_716])).

cnf(c_3099,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0_52,X1_52)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0_52),X1_52)
    | v1_relat_1(X0_52) != iProver_top
    | v1_relat_1(X1_52) != iProver_top ),
    inference(superposition,[status(thm)],[c_3094,c_1163])).

cnf(c_5360,plain,
    ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),X0_52) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0_52))
    | v1_relat_1(X0_52) != iProver_top ),
    inference(superposition,[status(thm)],[c_1766,c_3099])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_714,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | k2_relset_1(X0_53,X1_53,X0_52) = k2_relat_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1165,plain,
    ( k2_relset_1(X0_53,X1_53,X0_52) = k2_relat_1(X0_52)
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_714])).

cnf(c_2321,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1173,c_1165])).

cnf(c_2326,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2321,c_706])).

cnf(c_8,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_498,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_25])).

cnf(c_499,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(unflattening,[status(thm)],[c_498])).

cnf(c_501,plain,
    ( ~ v1_relat_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_499,c_33])).

cnf(c_692,plain,
    ( ~ v1_relat_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(subtyping,[status(esa)],[c_501])).

cnf(c_1183,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_692])).

cnf(c_1867,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1183,c_31,c_692,c_1536,c_1578])).

cnf(c_2332,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(demodulation,[status(thm)],[c_2326,c_1867])).

cnf(c_5383,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0_52)) = k5_relat_1(k6_partfun1(sK1),X0_52)
    | v1_relat_1(X0_52) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5360,c_2332])).

cnf(c_5451,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
    inference(superposition,[status(thm)],[c_1713,c_5383])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_710,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(X2_53,X3_53)))
    | ~ v1_funct_1(X0_52)
    | ~ v1_funct_1(X1_52)
    | k1_partfun1(X2_53,X3_53,X0_53,X1_53,X1_52,X0_52) = k5_relat_1(X1_52,X0_52) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1169,plain,
    ( k1_partfun1(X0_53,X1_53,X2_53,X3_53,X0_52,X1_52) = k5_relat_1(X0_52,X1_52)
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(X2_53,X3_53))) != iProver_top
    | v1_funct_1(X1_52) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_710])).

cnf(c_3495,plain,
    ( k1_partfun1(X0_53,X1_53,sK1,sK0,X0_52,sK3) = k5_relat_1(X0_52,sK3)
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1170,c_1169])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_37,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_3949,plain,
    ( v1_funct_1(X0_52) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | k1_partfun1(X0_53,X1_53,sK1,sK0,X0_52,sK3) = k5_relat_1(X0_52,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3495,c_37])).

cnf(c_3950,plain,
    ( k1_partfun1(X0_53,X1_53,sK1,sK0,X0_52,sK3) = k5_relat_1(X0_52,sK3)
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_3949])).

cnf(c_3959,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1173,c_3950])).

cnf(c_14,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_26,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_395,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_26])).

cnf(c_396,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_395])).

cnf(c_15,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_61,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_398,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_396,c_61])).

cnf(c_697,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_398])).

cnf(c_1178,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_697])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_712,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(X2_53,X3_53)))
    | m1_subset_1(k1_partfun1(X2_53,X3_53,X0_53,X1_53,X1_52,X0_52),k1_zfmisc_1(k2_zfmisc_1(X2_53,X1_53)))
    | ~ v1_funct_1(X0_52)
    | ~ v1_funct_1(X1_52) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1479,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | m1_subset_1(k1_partfun1(X0_53,X1_53,sK1,sK0,X0_52,sK3),k1_zfmisc_1(k2_zfmisc_1(X0_53,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(X0_52)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_712])).

cnf(c_1680,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1479])).

cnf(c_1871,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1178,c_33,c_31,c_30,c_28,c_697,c_1680])).

cnf(c_3986,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3959,c_1871])).

cnf(c_34,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_4598,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3986,c_34])).

cnf(c_10,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_356,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_10,c_2])).

cnf(c_6,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_partfun1(X1)) = X0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_375,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_partfun1(X2)) = X0 ),
    inference(resolution,[status(thm)],[c_356,c_6])).

cnf(c_698,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ v1_relat_1(X0_52)
    | k5_relat_1(X0_52,k6_partfun1(X1_53)) = X0_52 ),
    inference(subtyping,[status(esa)],[c_375])).

cnf(c_1177,plain,
    ( k5_relat_1(X0_52,k6_partfun1(X0_53)) = X0_52
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_53,X0_53))) != iProver_top
    | v1_relat_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_698])).

cnf(c_4837,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k2_funct_1(sK2)
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2715,c_1177])).

cnf(c_3760,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_698])).

cnf(c_4919,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4837,c_32,c_31,c_706,c_1363,c_1544,c_1575,c_3760])).

cnf(c_5462,plain,
    ( k5_relat_1(k6_partfun1(sK1),sK3) = k2_funct_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_5451,c_4598,c_4919])).

cnf(c_5473,plain,
    ( k7_relat_1(sK3,sK1) = k2_funct_1(sK2) ),
    inference(superposition,[status(thm)],[c_2118,c_5462])).

cnf(c_11,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_4,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_338,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_11,c_4])).

cnf(c_699,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ v1_relat_1(X0_52)
    | k7_relat_1(X0_52,X0_53) = X0_52 ),
    inference(subtyping,[status(esa)],[c_338])).

cnf(c_1176,plain,
    ( k7_relat_1(X0_52,X0_53) = X0_52
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_relat_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_699])).

cnf(c_756,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_53,X1_53)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_717])).

cnf(c_782,plain,
    ( k7_relat_1(X0_52,X0_53) = X0_52
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_relat_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_699])).

cnf(c_1372,plain,
    ( m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_relat_1(X0_52) = iProver_top
    | v1_relat_1(k2_zfmisc_1(X0_53,X1_53)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1371])).

cnf(c_4431,plain,
    ( m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | k7_relat_1(X0_52,X0_53) = X0_52 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1176,c_756,c_782,c_1372])).

cnf(c_4432,plain,
    ( k7_relat_1(X0_52,X0_53) = X0_52
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4431])).

cnf(c_4439,plain,
    ( k7_relat_1(sK3,sK1) = sK3 ),
    inference(superposition,[status(thm)],[c_1170,c_4432])).

cnf(c_5475,plain,
    ( k2_funct_1(sK2) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_5473,c_4439])).

cnf(c_22,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_709,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5475,c_709])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 12:08:14 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.37/0.91  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.37/0.91  
% 3.37/0.91  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.37/0.91  
% 3.37/0.91  ------  iProver source info
% 3.37/0.91  
% 3.37/0.91  git: date: 2020-06-30 10:37:57 +0100
% 3.37/0.91  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.37/0.91  git: non_committed_changes: false
% 3.37/0.91  git: last_make_outside_of_git: false
% 3.37/0.91  
% 3.37/0.91  ------ 
% 3.37/0.91  
% 3.37/0.91  ------ Input Options
% 3.37/0.91  
% 3.37/0.91  --out_options                           all
% 3.37/0.91  --tptp_safe_out                         true
% 3.37/0.91  --problem_path                          ""
% 3.37/0.91  --include_path                          ""
% 3.37/0.91  --clausifier                            res/vclausify_rel
% 3.37/0.91  --clausifier_options                    --mode clausify
% 3.37/0.91  --stdin                                 false
% 3.37/0.91  --stats_out                             all
% 3.37/0.91  
% 3.37/0.91  ------ General Options
% 3.37/0.91  
% 3.37/0.91  --fof                                   false
% 3.37/0.91  --time_out_real                         305.
% 3.37/0.91  --time_out_virtual                      -1.
% 3.37/0.91  --symbol_type_check                     false
% 3.37/0.91  --clausify_out                          false
% 3.37/0.91  --sig_cnt_out                           false
% 3.37/0.91  --trig_cnt_out                          false
% 3.37/0.91  --trig_cnt_out_tolerance                1.
% 3.37/0.91  --trig_cnt_out_sk_spl                   false
% 3.37/0.91  --abstr_cl_out                          false
% 3.37/0.91  
% 3.37/0.91  ------ Global Options
% 3.37/0.91  
% 3.37/0.91  --schedule                              default
% 3.37/0.91  --add_important_lit                     false
% 3.37/0.91  --prop_solver_per_cl                    1000
% 3.37/0.91  --min_unsat_core                        false
% 3.37/0.91  --soft_assumptions                      false
% 3.37/0.91  --soft_lemma_size                       3
% 3.37/0.91  --prop_impl_unit_size                   0
% 3.37/0.91  --prop_impl_unit                        []
% 3.37/0.91  --share_sel_clauses                     true
% 3.37/0.91  --reset_solvers                         false
% 3.37/0.91  --bc_imp_inh                            [conj_cone]
% 3.37/0.91  --conj_cone_tolerance                   3.
% 3.37/0.91  --extra_neg_conj                        none
% 3.37/0.91  --large_theory_mode                     true
% 3.37/0.91  --prolific_symb_bound                   200
% 3.37/0.91  --lt_threshold                          2000
% 3.37/0.91  --clause_weak_htbl                      true
% 3.37/0.91  --gc_record_bc_elim                     false
% 3.37/0.91  
% 3.37/0.91  ------ Preprocessing Options
% 3.37/0.91  
% 3.37/0.91  --preprocessing_flag                    true
% 3.37/0.91  --time_out_prep_mult                    0.1
% 3.37/0.91  --splitting_mode                        input
% 3.37/0.91  --splitting_grd                         true
% 3.37/0.91  --splitting_cvd                         false
% 3.37/0.91  --splitting_cvd_svl                     false
% 3.37/0.91  --splitting_nvd                         32
% 3.37/0.91  --sub_typing                            true
% 3.37/0.91  --prep_gs_sim                           true
% 3.37/0.91  --prep_unflatten                        true
% 3.37/0.91  --prep_res_sim                          true
% 3.37/0.91  --prep_upred                            true
% 3.37/0.91  --prep_sem_filter                       exhaustive
% 3.37/0.91  --prep_sem_filter_out                   false
% 3.37/0.91  --pred_elim                             true
% 3.37/0.91  --res_sim_input                         true
% 3.37/0.91  --eq_ax_congr_red                       true
% 3.37/0.91  --pure_diseq_elim                       true
% 3.37/0.91  --brand_transform                       false
% 3.37/0.91  --non_eq_to_eq                          false
% 3.37/0.91  --prep_def_merge                        true
% 3.37/0.91  --prep_def_merge_prop_impl              false
% 3.37/0.91  --prep_def_merge_mbd                    true
% 3.37/0.91  --prep_def_merge_tr_red                 false
% 3.37/0.91  --prep_def_merge_tr_cl                  false
% 3.37/0.91  --smt_preprocessing                     true
% 3.37/0.91  --smt_ac_axioms                         fast
% 3.37/0.91  --preprocessed_out                      false
% 3.37/0.91  --preprocessed_stats                    false
% 3.37/0.91  
% 3.37/0.91  ------ Abstraction refinement Options
% 3.37/0.91  
% 3.37/0.91  --abstr_ref                             []
% 3.37/0.91  --abstr_ref_prep                        false
% 3.37/0.91  --abstr_ref_until_sat                   false
% 3.37/0.91  --abstr_ref_sig_restrict                funpre
% 3.37/0.91  --abstr_ref_af_restrict_to_split_sk     false
% 3.37/0.91  --abstr_ref_under                       []
% 3.37/0.91  
% 3.37/0.91  ------ SAT Options
% 3.37/0.91  
% 3.37/0.91  --sat_mode                              false
% 3.37/0.91  --sat_fm_restart_options                ""
% 3.37/0.91  --sat_gr_def                            false
% 3.37/0.91  --sat_epr_types                         true
% 3.37/0.91  --sat_non_cyclic_types                  false
% 3.37/0.91  --sat_finite_models                     false
% 3.37/0.91  --sat_fm_lemmas                         false
% 3.37/0.91  --sat_fm_prep                           false
% 3.37/0.91  --sat_fm_uc_incr                        true
% 3.37/0.91  --sat_out_model                         small
% 3.37/0.91  --sat_out_clauses                       false
% 3.37/0.91  
% 3.37/0.91  ------ QBF Options
% 3.37/0.91  
% 3.37/0.91  --qbf_mode                              false
% 3.37/0.91  --qbf_elim_univ                         false
% 3.37/0.91  --qbf_dom_inst                          none
% 3.37/0.91  --qbf_dom_pre_inst                      false
% 3.37/0.91  --qbf_sk_in                             false
% 3.37/0.91  --qbf_pred_elim                         true
% 3.37/0.91  --qbf_split                             512
% 3.37/0.91  
% 3.37/0.91  ------ BMC1 Options
% 3.37/0.91  
% 3.37/0.91  --bmc1_incremental                      false
% 3.37/0.91  --bmc1_axioms                           reachable_all
% 3.37/0.91  --bmc1_min_bound                        0
% 3.37/0.91  --bmc1_max_bound                        -1
% 3.37/0.91  --bmc1_max_bound_default                -1
% 3.37/0.91  --bmc1_symbol_reachability              true
% 3.37/0.91  --bmc1_property_lemmas                  false
% 3.37/0.91  --bmc1_k_induction                      false
% 3.37/0.91  --bmc1_non_equiv_states                 false
% 3.37/0.91  --bmc1_deadlock                         false
% 3.37/0.91  --bmc1_ucm                              false
% 3.37/0.91  --bmc1_add_unsat_core                   none
% 3.37/0.91  --bmc1_unsat_core_children              false
% 3.37/0.91  --bmc1_unsat_core_extrapolate_axioms    false
% 3.37/0.91  --bmc1_out_stat                         full
% 3.37/0.91  --bmc1_ground_init                      false
% 3.37/0.91  --bmc1_pre_inst_next_state              false
% 3.37/0.91  --bmc1_pre_inst_state                   false
% 3.37/0.91  --bmc1_pre_inst_reach_state             false
% 3.37/0.91  --bmc1_out_unsat_core                   false
% 3.37/0.91  --bmc1_aig_witness_out                  false
% 3.37/0.91  --bmc1_verbose                          false
% 3.37/0.91  --bmc1_dump_clauses_tptp                false
% 3.37/0.91  --bmc1_dump_unsat_core_tptp             false
% 3.37/0.91  --bmc1_dump_file                        -
% 3.37/0.91  --bmc1_ucm_expand_uc_limit              128
% 3.37/0.91  --bmc1_ucm_n_expand_iterations          6
% 3.37/0.91  --bmc1_ucm_extend_mode                  1
% 3.37/0.91  --bmc1_ucm_init_mode                    2
% 3.37/0.91  --bmc1_ucm_cone_mode                    none
% 3.37/0.91  --bmc1_ucm_reduced_relation_type        0
% 3.37/0.91  --bmc1_ucm_relax_model                  4
% 3.37/0.91  --bmc1_ucm_full_tr_after_sat            true
% 3.37/0.91  --bmc1_ucm_expand_neg_assumptions       false
% 3.37/0.91  --bmc1_ucm_layered_model                none
% 3.37/0.92  --bmc1_ucm_max_lemma_size               10
% 3.37/0.92  
% 3.37/0.92  ------ AIG Options
% 3.37/0.92  
% 3.37/0.92  --aig_mode                              false
% 3.37/0.92  
% 3.37/0.92  ------ Instantiation Options
% 3.37/0.92  
% 3.37/0.92  --instantiation_flag                    true
% 3.37/0.92  --inst_sos_flag                         false
% 3.37/0.92  --inst_sos_phase                        true
% 3.37/0.92  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.37/0.92  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.37/0.92  --inst_lit_sel_side                     num_symb
% 3.37/0.92  --inst_solver_per_active                1400
% 3.37/0.92  --inst_solver_calls_frac                1.
% 3.37/0.92  --inst_passive_queue_type               priority_queues
% 3.37/0.92  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.37/0.92  --inst_passive_queues_freq              [25;2]
% 3.37/0.92  --inst_dismatching                      true
% 3.37/0.92  --inst_eager_unprocessed_to_passive     true
% 3.37/0.92  --inst_prop_sim_given                   true
% 3.37/0.92  --inst_prop_sim_new                     false
% 3.37/0.92  --inst_subs_new                         false
% 3.37/0.92  --inst_eq_res_simp                      false
% 3.37/0.92  --inst_subs_given                       false
% 3.37/0.92  --inst_orphan_elimination               true
% 3.37/0.92  --inst_learning_loop_flag               true
% 3.37/0.92  --inst_learning_start                   3000
% 3.37/0.92  --inst_learning_factor                  2
% 3.37/0.92  --inst_start_prop_sim_after_learn       3
% 3.37/0.92  --inst_sel_renew                        solver
% 3.37/0.92  --inst_lit_activity_flag                true
% 3.37/0.92  --inst_restr_to_given                   false
% 3.37/0.92  --inst_activity_threshold               500
% 3.37/0.92  --inst_out_proof                        true
% 3.37/0.92  
% 3.37/0.92  ------ Resolution Options
% 3.37/0.92  
% 3.37/0.92  --resolution_flag                       true
% 3.37/0.92  --res_lit_sel                           adaptive
% 3.37/0.92  --res_lit_sel_side                      none
% 3.37/0.92  --res_ordering                          kbo
% 3.37/0.92  --res_to_prop_solver                    active
% 3.37/0.92  --res_prop_simpl_new                    false
% 3.37/0.92  --res_prop_simpl_given                  true
% 3.37/0.92  --res_passive_queue_type                priority_queues
% 3.37/0.92  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.37/0.92  --res_passive_queues_freq               [15;5]
% 3.37/0.92  --res_forward_subs                      full
% 3.37/0.92  --res_backward_subs                     full
% 3.37/0.92  --res_forward_subs_resolution           true
% 3.37/0.92  --res_backward_subs_resolution          true
% 3.37/0.92  --res_orphan_elimination                true
% 3.37/0.92  --res_time_limit                        2.
% 3.37/0.92  --res_out_proof                         true
% 3.37/0.92  
% 3.37/0.92  ------ Superposition Options
% 3.37/0.92  
% 3.37/0.92  --superposition_flag                    true
% 3.37/0.92  --sup_passive_queue_type                priority_queues
% 3.37/0.92  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.37/0.92  --sup_passive_queues_freq               [8;1;4]
% 3.37/0.92  --demod_completeness_check              fast
% 3.37/0.92  --demod_use_ground                      true
% 3.37/0.92  --sup_to_prop_solver                    passive
% 3.37/0.92  --sup_prop_simpl_new                    true
% 3.37/0.92  --sup_prop_simpl_given                  true
% 3.37/0.92  --sup_fun_splitting                     false
% 3.37/0.92  --sup_smt_interval                      50000
% 3.37/0.92  
% 3.37/0.92  ------ Superposition Simplification Setup
% 3.37/0.92  
% 3.37/0.92  --sup_indices_passive                   []
% 3.37/0.92  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.37/0.92  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.37/0.92  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.37/0.92  --sup_full_triv                         [TrivRules;PropSubs]
% 3.37/0.92  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.37/0.92  --sup_full_bw                           [BwDemod]
% 3.37/0.92  --sup_immed_triv                        [TrivRules]
% 3.37/0.92  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.37/0.92  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.37/0.92  --sup_immed_bw_main                     []
% 3.37/0.92  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.37/0.92  --sup_input_triv                        [Unflattening;TrivRules]
% 3.37/0.92  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.37/0.92  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.37/0.92  
% 3.37/0.92  ------ Combination Options
% 3.37/0.92  
% 3.37/0.92  --comb_res_mult                         3
% 3.37/0.92  --comb_sup_mult                         2
% 3.37/0.92  --comb_inst_mult                        10
% 3.37/0.92  
% 3.37/0.92  ------ Debug Options
% 3.37/0.92  
% 3.37/0.92  --dbg_backtrace                         false
% 3.37/0.92  --dbg_dump_prop_clauses                 false
% 3.37/0.92  --dbg_dump_prop_clauses_file            -
% 3.37/0.92  --dbg_out_stat                          false
% 3.37/0.92  ------ Parsing...
% 3.37/0.92  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.37/0.92  
% 3.37/0.92  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.37/0.92  
% 3.37/0.92  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.37/0.92  
% 3.37/0.92  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.37/0.92  ------ Proving...
% 3.37/0.92  ------ Problem Properties 
% 3.37/0.92  
% 3.37/0.92  
% 3.37/0.92  clauses                                 27
% 3.37/0.92  conjectures                             10
% 3.37/0.92  EPR                                     6
% 3.37/0.92  Horn                                    27
% 3.37/0.92  unary                                   12
% 3.37/0.92  binary                                  5
% 3.37/0.92  lits                                    62
% 3.37/0.92  lits eq                                 16
% 3.37/0.92  fd_pure                                 0
% 3.37/0.92  fd_pseudo                               0
% 3.37/0.92  fd_cond                                 0
% 3.37/0.92  fd_pseudo_cond                          0
% 3.37/0.92  AC symbols                              0
% 3.37/0.92  
% 3.37/0.92  ------ Schedule dynamic 5 is on 
% 3.37/0.92  
% 3.37/0.92  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.37/0.92  
% 3.37/0.92  
% 3.37/0.92  ------ 
% 3.37/0.92  Current options:
% 3.37/0.92  ------ 
% 3.37/0.92  
% 3.37/0.92  ------ Input Options
% 3.37/0.92  
% 3.37/0.92  --out_options                           all
% 3.37/0.92  --tptp_safe_out                         true
% 3.37/0.92  --problem_path                          ""
% 3.37/0.92  --include_path                          ""
% 3.37/0.92  --clausifier                            res/vclausify_rel
% 3.37/0.92  --clausifier_options                    --mode clausify
% 3.37/0.92  --stdin                                 false
% 3.37/0.92  --stats_out                             all
% 3.37/0.92  
% 3.37/0.92  ------ General Options
% 3.37/0.92  
% 3.37/0.92  --fof                                   false
% 3.37/0.92  --time_out_real                         305.
% 3.37/0.92  --time_out_virtual                      -1.
% 3.37/0.92  --symbol_type_check                     false
% 3.37/0.92  --clausify_out                          false
% 3.37/0.92  --sig_cnt_out                           false
% 3.37/0.92  --trig_cnt_out                          false
% 3.37/0.92  --trig_cnt_out_tolerance                1.
% 3.37/0.92  --trig_cnt_out_sk_spl                   false
% 3.37/0.92  --abstr_cl_out                          false
% 3.37/0.92  
% 3.37/0.92  ------ Global Options
% 3.37/0.92  
% 3.37/0.92  --schedule                              default
% 3.37/0.92  --add_important_lit                     false
% 3.37/0.92  --prop_solver_per_cl                    1000
% 3.37/0.92  --min_unsat_core                        false
% 3.37/0.92  --soft_assumptions                      false
% 3.37/0.92  --soft_lemma_size                       3
% 3.37/0.92  --prop_impl_unit_size                   0
% 3.37/0.92  --prop_impl_unit                        []
% 3.37/0.92  --share_sel_clauses                     true
% 3.37/0.92  --reset_solvers                         false
% 3.37/0.92  --bc_imp_inh                            [conj_cone]
% 3.37/0.92  --conj_cone_tolerance                   3.
% 3.37/0.92  --extra_neg_conj                        none
% 3.37/0.92  --large_theory_mode                     true
% 3.37/0.92  --prolific_symb_bound                   200
% 3.37/0.92  --lt_threshold                          2000
% 3.37/0.92  --clause_weak_htbl                      true
% 3.37/0.92  --gc_record_bc_elim                     false
% 3.37/0.92  
% 3.37/0.92  ------ Preprocessing Options
% 3.37/0.92  
% 3.37/0.92  --preprocessing_flag                    true
% 3.37/0.92  --time_out_prep_mult                    0.1
% 3.37/0.92  --splitting_mode                        input
% 3.37/0.92  --splitting_grd                         true
% 3.37/0.92  --splitting_cvd                         false
% 3.37/0.92  --splitting_cvd_svl                     false
% 3.37/0.92  --splitting_nvd                         32
% 3.37/0.92  --sub_typing                            true
% 3.37/0.92  --prep_gs_sim                           true
% 3.37/0.92  --prep_unflatten                        true
% 3.37/0.92  --prep_res_sim                          true
% 3.37/0.92  --prep_upred                            true
% 3.37/0.92  --prep_sem_filter                       exhaustive
% 3.37/0.92  --prep_sem_filter_out                   false
% 3.37/0.92  --pred_elim                             true
% 3.37/0.92  --res_sim_input                         true
% 3.37/0.92  --eq_ax_congr_red                       true
% 3.37/0.92  --pure_diseq_elim                       true
% 3.37/0.92  --brand_transform                       false
% 3.37/0.92  --non_eq_to_eq                          false
% 3.37/0.92  --prep_def_merge                        true
% 3.37/0.92  --prep_def_merge_prop_impl              false
% 3.37/0.92  --prep_def_merge_mbd                    true
% 3.37/0.92  --prep_def_merge_tr_red                 false
% 3.37/0.92  --prep_def_merge_tr_cl                  false
% 3.37/0.92  --smt_preprocessing                     true
% 3.37/0.92  --smt_ac_axioms                         fast
% 3.37/0.92  --preprocessed_out                      false
% 3.37/0.92  --preprocessed_stats                    false
% 3.37/0.92  
% 3.37/0.92  ------ Abstraction refinement Options
% 3.37/0.92  
% 3.37/0.92  --abstr_ref                             []
% 3.37/0.92  --abstr_ref_prep                        false
% 3.37/0.92  --abstr_ref_until_sat                   false
% 3.37/0.92  --abstr_ref_sig_restrict                funpre
% 3.37/0.92  --abstr_ref_af_restrict_to_split_sk     false
% 3.37/0.92  --abstr_ref_under                       []
% 3.37/0.92  
% 3.37/0.92  ------ SAT Options
% 3.37/0.92  
% 3.37/0.92  --sat_mode                              false
% 3.37/0.92  --sat_fm_restart_options                ""
% 3.37/0.92  --sat_gr_def                            false
% 3.37/0.92  --sat_epr_types                         true
% 3.37/0.92  --sat_non_cyclic_types                  false
% 3.37/0.92  --sat_finite_models                     false
% 3.37/0.92  --sat_fm_lemmas                         false
% 3.37/0.92  --sat_fm_prep                           false
% 3.37/0.92  --sat_fm_uc_incr                        true
% 3.37/0.92  --sat_out_model                         small
% 3.37/0.92  --sat_out_clauses                       false
% 3.37/0.92  
% 3.37/0.92  ------ QBF Options
% 3.37/0.92  
% 3.37/0.92  --qbf_mode                              false
% 3.37/0.92  --qbf_elim_univ                         false
% 3.37/0.92  --qbf_dom_inst                          none
% 3.37/0.92  --qbf_dom_pre_inst                      false
% 3.37/0.92  --qbf_sk_in                             false
% 3.37/0.92  --qbf_pred_elim                         true
% 3.37/0.92  --qbf_split                             512
% 3.37/0.92  
% 3.37/0.92  ------ BMC1 Options
% 3.37/0.92  
% 3.37/0.92  --bmc1_incremental                      false
% 3.37/0.92  --bmc1_axioms                           reachable_all
% 3.37/0.92  --bmc1_min_bound                        0
% 3.37/0.92  --bmc1_max_bound                        -1
% 3.37/0.92  --bmc1_max_bound_default                -1
% 3.37/0.92  --bmc1_symbol_reachability              true
% 3.37/0.92  --bmc1_property_lemmas                  false
% 3.37/0.92  --bmc1_k_induction                      false
% 3.37/0.92  --bmc1_non_equiv_states                 false
% 3.37/0.92  --bmc1_deadlock                         false
% 3.37/0.92  --bmc1_ucm                              false
% 3.37/0.92  --bmc1_add_unsat_core                   none
% 3.37/0.92  --bmc1_unsat_core_children              false
% 3.37/0.92  --bmc1_unsat_core_extrapolate_axioms    false
% 3.37/0.92  --bmc1_out_stat                         full
% 3.37/0.92  --bmc1_ground_init                      false
% 3.37/0.92  --bmc1_pre_inst_next_state              false
% 3.37/0.92  --bmc1_pre_inst_state                   false
% 3.37/0.92  --bmc1_pre_inst_reach_state             false
% 3.37/0.92  --bmc1_out_unsat_core                   false
% 3.37/0.92  --bmc1_aig_witness_out                  false
% 3.37/0.92  --bmc1_verbose                          false
% 3.37/0.92  --bmc1_dump_clauses_tptp                false
% 3.37/0.92  --bmc1_dump_unsat_core_tptp             false
% 3.37/0.92  --bmc1_dump_file                        -
% 3.37/0.92  --bmc1_ucm_expand_uc_limit              128
% 3.37/0.92  --bmc1_ucm_n_expand_iterations          6
% 3.37/0.92  --bmc1_ucm_extend_mode                  1
% 3.37/0.92  --bmc1_ucm_init_mode                    2
% 3.37/0.92  --bmc1_ucm_cone_mode                    none
% 3.37/0.92  --bmc1_ucm_reduced_relation_type        0
% 3.37/0.92  --bmc1_ucm_relax_model                  4
% 3.37/0.92  --bmc1_ucm_full_tr_after_sat            true
% 3.37/0.92  --bmc1_ucm_expand_neg_assumptions       false
% 3.37/0.92  --bmc1_ucm_layered_model                none
% 3.37/0.92  --bmc1_ucm_max_lemma_size               10
% 3.37/0.92  
% 3.37/0.92  ------ AIG Options
% 3.37/0.92  
% 3.37/0.92  --aig_mode                              false
% 3.37/0.92  
% 3.37/0.92  ------ Instantiation Options
% 3.37/0.92  
% 3.37/0.92  --instantiation_flag                    true
% 3.37/0.92  --inst_sos_flag                         false
% 3.37/0.92  --inst_sos_phase                        true
% 3.37/0.92  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.37/0.92  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.37/0.92  --inst_lit_sel_side                     none
% 3.37/0.92  --inst_solver_per_active                1400
% 3.37/0.92  --inst_solver_calls_frac                1.
% 3.37/0.92  --inst_passive_queue_type               priority_queues
% 3.37/0.92  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.37/0.92  --inst_passive_queues_freq              [25;2]
% 3.37/0.92  --inst_dismatching                      true
% 3.37/0.92  --inst_eager_unprocessed_to_passive     true
% 3.37/0.92  --inst_prop_sim_given                   true
% 3.37/0.92  --inst_prop_sim_new                     false
% 3.37/0.92  --inst_subs_new                         false
% 3.37/0.92  --inst_eq_res_simp                      false
% 3.37/0.92  --inst_subs_given                       false
% 3.37/0.92  --inst_orphan_elimination               true
% 3.37/0.92  --inst_learning_loop_flag               true
% 3.37/0.92  --inst_learning_start                   3000
% 3.37/0.92  --inst_learning_factor                  2
% 3.37/0.92  --inst_start_prop_sim_after_learn       3
% 3.37/0.92  --inst_sel_renew                        solver
% 3.37/0.92  --inst_lit_activity_flag                true
% 3.37/0.92  --inst_restr_to_given                   false
% 3.37/0.92  --inst_activity_threshold               500
% 3.37/0.92  --inst_out_proof                        true
% 3.37/0.92  
% 3.37/0.92  ------ Resolution Options
% 3.37/0.92  
% 3.37/0.92  --resolution_flag                       false
% 3.37/0.92  --res_lit_sel                           adaptive
% 3.37/0.92  --res_lit_sel_side                      none
% 3.37/0.92  --res_ordering                          kbo
% 3.37/0.92  --res_to_prop_solver                    active
% 3.37/0.92  --res_prop_simpl_new                    false
% 3.37/0.92  --res_prop_simpl_given                  true
% 3.37/0.92  --res_passive_queue_type                priority_queues
% 3.37/0.92  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.37/0.92  --res_passive_queues_freq               [15;5]
% 3.37/0.92  --res_forward_subs                      full
% 3.37/0.92  --res_backward_subs                     full
% 3.37/0.92  --res_forward_subs_resolution           true
% 3.37/0.92  --res_backward_subs_resolution          true
% 3.37/0.92  --res_orphan_elimination                true
% 3.37/0.92  --res_time_limit                        2.
% 3.37/0.92  --res_out_proof                         true
% 3.37/0.92  
% 3.37/0.92  ------ Superposition Options
% 3.37/0.92  
% 3.37/0.92  --superposition_flag                    true
% 3.37/0.92  --sup_passive_queue_type                priority_queues
% 3.37/0.92  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.37/0.92  --sup_passive_queues_freq               [8;1;4]
% 3.37/0.92  --demod_completeness_check              fast
% 3.37/0.92  --demod_use_ground                      true
% 3.37/0.92  --sup_to_prop_solver                    passive
% 3.37/0.92  --sup_prop_simpl_new                    true
% 3.37/0.92  --sup_prop_simpl_given                  true
% 3.37/0.92  --sup_fun_splitting                     false
% 3.37/0.92  --sup_smt_interval                      50000
% 3.37/0.92  
% 3.37/0.92  ------ Superposition Simplification Setup
% 3.37/0.92  
% 3.37/0.92  --sup_indices_passive                   []
% 3.37/0.92  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.37/0.92  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.37/0.92  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.37/0.92  --sup_full_triv                         [TrivRules;PropSubs]
% 3.37/0.92  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.37/0.92  --sup_full_bw                           [BwDemod]
% 3.37/0.92  --sup_immed_triv                        [TrivRules]
% 3.37/0.92  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.37/0.92  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.37/0.92  --sup_immed_bw_main                     []
% 3.37/0.92  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.37/0.92  --sup_input_triv                        [Unflattening;TrivRules]
% 3.37/0.92  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.37/0.92  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.37/0.92  
% 3.37/0.92  ------ Combination Options
% 3.37/0.92  
% 3.37/0.92  --comb_res_mult                         3
% 3.37/0.92  --comb_sup_mult                         2
% 3.37/0.92  --comb_inst_mult                        10
% 3.37/0.92  
% 3.37/0.92  ------ Debug Options
% 3.37/0.92  
% 3.37/0.92  --dbg_backtrace                         false
% 3.37/0.92  --dbg_dump_prop_clauses                 false
% 3.37/0.92  --dbg_dump_prop_clauses_file            -
% 3.37/0.92  --dbg_out_stat                          false
% 3.37/0.92  
% 3.37/0.92  
% 3.37/0.92  
% 3.37/0.92  
% 3.37/0.92  ------ Proving...
% 3.37/0.92  
% 3.37/0.92  
% 3.37/0.92  % SZS status Theorem for theBenchmark.p
% 3.37/0.92  
% 3.37/0.92  % SZS output start CNFRefutation for theBenchmark.p
% 3.37/0.92  
% 3.37/0.92  fof(f17,conjecture,(
% 3.37/0.92    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 3.37/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/0.92  
% 3.37/0.92  fof(f18,negated_conjecture,(
% 3.37/0.92    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 3.37/0.92    inference(negated_conjecture,[],[f17])).
% 3.37/0.92  
% 3.37/0.92  fof(f39,plain,(
% 3.37/0.92    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.37/0.92    inference(ennf_transformation,[],[f18])).
% 3.37/0.92  
% 3.37/0.92  fof(f40,plain,(
% 3.37/0.92    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.37/0.92    inference(flattening,[],[f39])).
% 3.37/0.92  
% 3.37/0.92  fof(f44,plain,(
% 3.37/0.92    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 3.37/0.92    introduced(choice_axiom,[])).
% 3.37/0.92  
% 3.37/0.92  fof(f43,plain,(
% 3.37/0.92    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 3.37/0.92    introduced(choice_axiom,[])).
% 3.37/0.92  
% 3.37/0.92  fof(f45,plain,(
% 3.37/0.92    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 3.37/0.92    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f40,f44,f43])).
% 3.37/0.92  
% 3.37/0.92  fof(f74,plain,(
% 3.37/0.92    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 3.37/0.92    inference(cnf_transformation,[],[f45])).
% 3.37/0.92  
% 3.37/0.92  fof(f1,axiom,(
% 3.37/0.92    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.37/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/0.92  
% 3.37/0.92  fof(f19,plain,(
% 3.37/0.92    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.37/0.92    inference(ennf_transformation,[],[f1])).
% 3.37/0.92  
% 3.37/0.92  fof(f46,plain,(
% 3.37/0.92    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.37/0.92    inference(cnf_transformation,[],[f19])).
% 3.37/0.92  
% 3.37/0.92  fof(f3,axiom,(
% 3.37/0.92    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.37/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/0.92  
% 3.37/0.92  fof(f49,plain,(
% 3.37/0.92    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.37/0.92    inference(cnf_transformation,[],[f3])).
% 3.37/0.92  
% 3.37/0.92  fof(f7,axiom,(
% 3.37/0.92    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 3.37/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/0.92  
% 3.37/0.92  fof(f26,plain,(
% 3.37/0.92    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 3.37/0.92    inference(ennf_transformation,[],[f7])).
% 3.37/0.92  
% 3.37/0.92  fof(f53,plain,(
% 3.37/0.92    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 3.37/0.92    inference(cnf_transformation,[],[f26])).
% 3.37/0.92  
% 3.37/0.92  fof(f15,axiom,(
% 3.37/0.92    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.37/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/0.92  
% 3.37/0.92  fof(f65,plain,(
% 3.37/0.92    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.37/0.92    inference(cnf_transformation,[],[f15])).
% 3.37/0.92  
% 3.37/0.92  fof(f82,plain,(
% 3.37/0.92    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_partfun1(X0),X1) | ~v1_relat_1(X1)) )),
% 3.37/0.92    inference(definition_unfolding,[],[f53,f65])).
% 3.37/0.92  
% 3.37/0.92  fof(f71,plain,(
% 3.37/0.92    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.37/0.92    inference(cnf_transformation,[],[f45])).
% 3.37/0.92  
% 3.37/0.92  fof(f75,plain,(
% 3.37/0.92    k2_relset_1(sK0,sK1,sK2) = sK1),
% 3.37/0.92    inference(cnf_transformation,[],[f45])).
% 3.37/0.92  
% 3.37/0.92  fof(f16,axiom,(
% 3.37/0.92    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.37/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/0.92  
% 3.37/0.92  fof(f37,plain,(
% 3.37/0.92    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.37/0.92    inference(ennf_transformation,[],[f16])).
% 3.37/0.92  
% 3.37/0.92  fof(f38,plain,(
% 3.37/0.92    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.37/0.92    inference(flattening,[],[f37])).
% 3.37/0.92  
% 3.37/0.92  fof(f68,plain,(
% 3.37/0.92    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.37/0.92    inference(cnf_transformation,[],[f38])).
% 3.37/0.92  
% 3.37/0.92  fof(f77,plain,(
% 3.37/0.92    v2_funct_1(sK2)),
% 3.37/0.92    inference(cnf_transformation,[],[f45])).
% 3.37/0.92  
% 3.37/0.92  fof(f69,plain,(
% 3.37/0.92    v1_funct_1(sK2)),
% 3.37/0.92    inference(cnf_transformation,[],[f45])).
% 3.37/0.92  
% 3.37/0.92  fof(f70,plain,(
% 3.37/0.92    v1_funct_2(sK2,sK0,sK1)),
% 3.37/0.92    inference(cnf_transformation,[],[f45])).
% 3.37/0.92  
% 3.37/0.92  fof(f5,axiom,(
% 3.37/0.92    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2))))),
% 3.37/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/0.92  
% 3.37/0.92  fof(f23,plain,(
% 3.37/0.92    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.37/0.92    inference(ennf_transformation,[],[f5])).
% 3.37/0.92  
% 3.37/0.92  fof(f51,plain,(
% 3.37/0.92    ( ! [X2,X0,X1] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.37/0.92    inference(cnf_transformation,[],[f23])).
% 3.37/0.92  
% 3.37/0.92  fof(f10,axiom,(
% 3.37/0.92    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.37/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/0.92  
% 3.37/0.92  fof(f30,plain,(
% 3.37/0.92    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.37/0.92    inference(ennf_transformation,[],[f10])).
% 3.37/0.92  
% 3.37/0.92  fof(f58,plain,(
% 3.37/0.92    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.37/0.92    inference(cnf_transformation,[],[f30])).
% 3.37/0.92  
% 3.37/0.92  fof(f8,axiom,(
% 3.37/0.92    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 3.37/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/0.92  
% 3.37/0.92  fof(f27,plain,(
% 3.37/0.92    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.37/0.92    inference(ennf_transformation,[],[f8])).
% 3.37/0.92  
% 3.37/0.92  fof(f28,plain,(
% 3.37/0.92    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.37/0.92    inference(flattening,[],[f27])).
% 3.37/0.92  
% 3.37/0.92  fof(f55,plain,(
% 3.37/0.92    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.37/0.92    inference(cnf_transformation,[],[f28])).
% 3.37/0.92  
% 3.37/0.92  fof(f83,plain,(
% 3.37/0.92    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.37/0.92    inference(definition_unfolding,[],[f55,f65])).
% 3.37/0.92  
% 3.37/0.92  fof(f14,axiom,(
% 3.37/0.92    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.37/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/0.92  
% 3.37/0.92  fof(f35,plain,(
% 3.37/0.92    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.37/0.92    inference(ennf_transformation,[],[f14])).
% 3.37/0.92  
% 3.37/0.92  fof(f36,plain,(
% 3.37/0.92    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.37/0.92    inference(flattening,[],[f35])).
% 3.37/0.92  
% 3.37/0.92  fof(f64,plain,(
% 3.37/0.92    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.37/0.92    inference(cnf_transformation,[],[f36])).
% 3.37/0.92  
% 3.37/0.92  fof(f72,plain,(
% 3.37/0.92    v1_funct_1(sK3)),
% 3.37/0.92    inference(cnf_transformation,[],[f45])).
% 3.37/0.92  
% 3.37/0.92  fof(f11,axiom,(
% 3.37/0.92    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.37/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/0.92  
% 3.37/0.92  fof(f31,plain,(
% 3.37/0.92    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.37/0.92    inference(ennf_transformation,[],[f11])).
% 3.37/0.92  
% 3.37/0.92  fof(f32,plain,(
% 3.37/0.92    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.37/0.92    inference(flattening,[],[f31])).
% 3.37/0.92  
% 3.37/0.92  fof(f42,plain,(
% 3.37/0.92    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.37/0.92    inference(nnf_transformation,[],[f32])).
% 3.37/0.92  
% 3.37/0.92  fof(f59,plain,(
% 3.37/0.92    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.37/0.92    inference(cnf_transformation,[],[f42])).
% 3.37/0.92  
% 3.37/0.92  fof(f76,plain,(
% 3.37/0.92    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 3.37/0.92    inference(cnf_transformation,[],[f45])).
% 3.37/0.92  
% 3.37/0.92  fof(f12,axiom,(
% 3.37/0.92    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.37/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/0.92  
% 3.37/0.92  fof(f61,plain,(
% 3.37/0.92    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.37/0.92    inference(cnf_transformation,[],[f12])).
% 3.37/0.92  
% 3.37/0.92  fof(f85,plain,(
% 3.37/0.92    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.37/0.92    inference(definition_unfolding,[],[f61,f65])).
% 3.37/0.92  
% 3.37/0.92  fof(f13,axiom,(
% 3.37/0.92    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 3.37/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/0.92  
% 3.37/0.92  fof(f33,plain,(
% 3.37/0.92    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.37/0.92    inference(ennf_transformation,[],[f13])).
% 3.37/0.92  
% 3.37/0.92  fof(f34,plain,(
% 3.37/0.92    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.37/0.92    inference(flattening,[],[f33])).
% 3.37/0.92  
% 3.37/0.92  fof(f63,plain,(
% 3.37/0.92    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.37/0.92    inference(cnf_transformation,[],[f34])).
% 3.37/0.92  
% 3.37/0.92  fof(f9,axiom,(
% 3.37/0.92    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.37/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/0.92  
% 3.37/0.92  fof(f29,plain,(
% 3.37/0.92    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.37/0.92    inference(ennf_transformation,[],[f9])).
% 3.37/0.92  
% 3.37/0.92  fof(f57,plain,(
% 3.37/0.92    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.37/0.92    inference(cnf_transformation,[],[f29])).
% 3.37/0.92  
% 3.37/0.92  fof(f2,axiom,(
% 3.37/0.92    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.37/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/0.92  
% 3.37/0.92  fof(f20,plain,(
% 3.37/0.92    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.37/0.92    inference(ennf_transformation,[],[f2])).
% 3.37/0.92  
% 3.37/0.92  fof(f41,plain,(
% 3.37/0.92    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.37/0.92    inference(nnf_transformation,[],[f20])).
% 3.37/0.92  
% 3.37/0.92  fof(f47,plain,(
% 3.37/0.92    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.37/0.92    inference(cnf_transformation,[],[f41])).
% 3.37/0.92  
% 3.37/0.92  fof(f6,axiom,(
% 3.37/0.92    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 3.37/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/0.92  
% 3.37/0.92  fof(f24,plain,(
% 3.37/0.92    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.37/0.92    inference(ennf_transformation,[],[f6])).
% 3.37/0.92  
% 3.37/0.92  fof(f25,plain,(
% 3.37/0.92    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 3.37/0.92    inference(flattening,[],[f24])).
% 3.37/0.92  
% 3.37/0.92  fof(f52,plain,(
% 3.37/0.92    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.37/0.92    inference(cnf_transformation,[],[f25])).
% 3.37/0.92  
% 3.37/0.92  fof(f81,plain,(
% 3.37/0.92    ( ! [X0,X1] : (k5_relat_1(X1,k6_partfun1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.37/0.92    inference(definition_unfolding,[],[f52,f65])).
% 3.37/0.92  
% 3.37/0.92  fof(f56,plain,(
% 3.37/0.92    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.37/0.92    inference(cnf_transformation,[],[f29])).
% 3.37/0.92  
% 3.37/0.92  fof(f4,axiom,(
% 3.37/0.92    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 3.37/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/0.92  
% 3.37/0.92  fof(f21,plain,(
% 3.37/0.92    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.37/0.92    inference(ennf_transformation,[],[f4])).
% 3.37/0.92  
% 3.37/0.92  fof(f22,plain,(
% 3.37/0.92    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.37/0.92    inference(flattening,[],[f21])).
% 3.37/0.92  
% 3.37/0.92  fof(f50,plain,(
% 3.37/0.92    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.37/0.92    inference(cnf_transformation,[],[f22])).
% 3.37/0.92  
% 3.37/0.92  fof(f80,plain,(
% 3.37/0.92    k2_funct_1(sK2) != sK3),
% 3.37/0.92    inference(cnf_transformation,[],[f45])).
% 3.37/0.92  
% 3.37/0.92  cnf(c_28,negated_conjecture,
% 3.37/0.92      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 3.37/0.92      inference(cnf_transformation,[],[f74]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_705,negated_conjecture,
% 3.37/0.92      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 3.37/0.92      inference(subtyping,[status(esa)],[c_28]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_1170,plain,
% 3.37/0.92      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.37/0.92      inference(predicate_to_equality,[status(thm)],[c_705]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_0,plain,
% 3.37/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.37/0.92      | ~ v1_relat_1(X1)
% 3.37/0.92      | v1_relat_1(X0) ),
% 3.37/0.92      inference(cnf_transformation,[],[f46]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_718,plain,
% 3.37/0.92      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(X1_52))
% 3.37/0.92      | ~ v1_relat_1(X1_52)
% 3.37/0.92      | v1_relat_1(X0_52) ),
% 3.37/0.92      inference(subtyping,[status(esa)],[c_0]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_1161,plain,
% 3.37/0.92      ( m1_subset_1(X0_52,k1_zfmisc_1(X1_52)) != iProver_top
% 3.37/0.92      | v1_relat_1(X1_52) != iProver_top
% 3.37/0.92      | v1_relat_1(X0_52) = iProver_top ),
% 3.37/0.92      inference(predicate_to_equality,[status(thm)],[c_718]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_1594,plain,
% 3.37/0.92      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 3.37/0.92      | v1_relat_1(sK3) = iProver_top ),
% 3.37/0.92      inference(superposition,[status(thm)],[c_1170,c_1161]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_39,plain,
% 3.37/0.92      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.37/0.92      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_1371,plain,
% 3.37/0.92      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 3.37/0.92      | v1_relat_1(X0_52)
% 3.37/0.92      | ~ v1_relat_1(k2_zfmisc_1(X0_53,X1_53)) ),
% 3.37/0.92      inference(instantiation,[status(thm)],[c_718]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_1533,plain,
% 3.37/0.92      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.37/0.92      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
% 3.37/0.92      | v1_relat_1(sK3) ),
% 3.37/0.92      inference(instantiation,[status(thm)],[c_1371]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_1534,plain,
% 3.37/0.92      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.37/0.92      | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 3.37/0.92      | v1_relat_1(sK3) = iProver_top ),
% 3.37/0.92      inference(predicate_to_equality,[status(thm)],[c_1533]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_3,plain,
% 3.37/0.92      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.37/0.92      inference(cnf_transformation,[],[f49]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_717,plain,
% 3.37/0.92      ( v1_relat_1(k2_zfmisc_1(X0_53,X1_53)) ),
% 3.37/0.92      inference(subtyping,[status(esa)],[c_3]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_1575,plain,
% 3.37/0.92      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
% 3.37/0.92      inference(instantiation,[status(thm)],[c_717]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_1576,plain,
% 3.37/0.92      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
% 3.37/0.92      inference(predicate_to_equality,[status(thm)],[c_1575]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_1713,plain,
% 3.37/0.92      ( v1_relat_1(sK3) = iProver_top ),
% 3.37/0.92      inference(global_propositional_subsumption,
% 3.37/0.92                [status(thm)],
% 3.37/0.92                [c_1594,c_39,c_1534,c_1576]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_7,plain,
% 3.37/0.92      ( ~ v1_relat_1(X0)
% 3.37/0.92      | k5_relat_1(k6_partfun1(X1),X0) = k7_relat_1(X0,X1) ),
% 3.37/0.92      inference(cnf_transformation,[],[f82]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_715,plain,
% 3.37/0.92      ( ~ v1_relat_1(X0_52)
% 3.37/0.92      | k5_relat_1(k6_partfun1(X0_53),X0_52) = k7_relat_1(X0_52,X0_53) ),
% 3.37/0.92      inference(subtyping,[status(esa)],[c_7]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_1164,plain,
% 3.37/0.92      ( k5_relat_1(k6_partfun1(X0_53),X0_52) = k7_relat_1(X0_52,X0_53)
% 3.37/0.92      | v1_relat_1(X0_52) != iProver_top ),
% 3.37/0.92      inference(predicate_to_equality,[status(thm)],[c_715]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_2118,plain,
% 3.37/0.92      ( k5_relat_1(k6_partfun1(X0_53),sK3) = k7_relat_1(sK3,X0_53) ),
% 3.37/0.92      inference(superposition,[status(thm)],[c_1713,c_1164]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_31,negated_conjecture,
% 3.37/0.92      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.37/0.92      inference(cnf_transformation,[],[f71]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_702,negated_conjecture,
% 3.37/0.92      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.37/0.92      inference(subtyping,[status(esa)],[c_31]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_1173,plain,
% 3.37/0.92      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.37/0.92      inference(predicate_to_equality,[status(thm)],[c_702]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_1598,plain,
% 3.37/0.92      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 3.37/0.92      | v1_relat_1(sK2) = iProver_top ),
% 3.37/0.92      inference(superposition,[status(thm)],[c_1173,c_1161]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_36,plain,
% 3.37/0.92      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.37/0.92      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_1536,plain,
% 3.37/0.92      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.37/0.92      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
% 3.37/0.92      | v1_relat_1(sK2) ),
% 3.37/0.92      inference(instantiation,[status(thm)],[c_1371]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_1537,plain,
% 3.37/0.92      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.37/0.92      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 3.37/0.92      | v1_relat_1(sK2) = iProver_top ),
% 3.37/0.92      inference(predicate_to_equality,[status(thm)],[c_1536]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_1578,plain,
% 3.37/0.92      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 3.37/0.92      inference(instantiation,[status(thm)],[c_717]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_1579,plain,
% 3.37/0.92      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 3.37/0.92      inference(predicate_to_equality,[status(thm)],[c_1578]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_1766,plain,
% 3.37/0.92      ( v1_relat_1(sK2) = iProver_top ),
% 3.37/0.92      inference(global_propositional_subsumption,
% 3.37/0.92                [status(thm)],
% 3.37/0.92                [c_1598,c_36,c_1537,c_1579]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_27,negated_conjecture,
% 3.37/0.92      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 3.37/0.92      inference(cnf_transformation,[],[f75]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_706,negated_conjecture,
% 3.37/0.92      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 3.37/0.92      inference(subtyping,[status(esa)],[c_27]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_19,plain,
% 3.37/0.92      ( ~ v1_funct_2(X0,X1,X2)
% 3.37/0.92      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.37/0.92      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.37/0.92      | ~ v1_funct_1(X0)
% 3.37/0.92      | ~ v2_funct_1(X0)
% 3.37/0.92      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.37/0.92      inference(cnf_transformation,[],[f68]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_25,negated_conjecture,
% 3.37/0.92      ( v2_funct_1(sK2) ),
% 3.37/0.92      inference(cnf_transformation,[],[f77]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_460,plain,
% 3.37/0.92      ( ~ v1_funct_2(X0,X1,X2)
% 3.37/0.92      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.37/0.92      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.37/0.92      | ~ v1_funct_1(X0)
% 3.37/0.92      | k2_relset_1(X1,X2,X0) != X2
% 3.37/0.92      | sK2 != X0 ),
% 3.37/0.92      inference(resolution_lifted,[status(thm)],[c_19,c_25]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_461,plain,
% 3.37/0.92      ( ~ v1_funct_2(sK2,X0,X1)
% 3.37/0.92      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.37/0.92      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.37/0.92      | ~ v1_funct_1(sK2)
% 3.37/0.92      | k2_relset_1(X0,X1,sK2) != X1 ),
% 3.37/0.92      inference(unflattening,[status(thm)],[c_460]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_33,negated_conjecture,
% 3.37/0.92      ( v1_funct_1(sK2) ),
% 3.37/0.92      inference(cnf_transformation,[],[f69]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_465,plain,
% 3.37/0.92      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.37/0.92      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.37/0.92      | ~ v1_funct_2(sK2,X0,X1)
% 3.37/0.92      | k2_relset_1(X0,X1,sK2) != X1 ),
% 3.37/0.92      inference(global_propositional_subsumption,
% 3.37/0.92                [status(thm)],
% 3.37/0.92                [c_461,c_33]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_466,plain,
% 3.37/0.92      ( ~ v1_funct_2(sK2,X0,X1)
% 3.37/0.92      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.37/0.92      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.37/0.92      | k2_relset_1(X0,X1,sK2) != X1 ),
% 3.37/0.92      inference(renaming,[status(thm)],[c_465]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_694,plain,
% 3.37/0.92      ( ~ v1_funct_2(sK2,X0_53,X1_53)
% 3.37/0.92      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1_53,X0_53)))
% 3.37/0.92      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 3.37/0.92      | k2_relset_1(X0_53,X1_53,sK2) != X1_53 ),
% 3.37/0.92      inference(subtyping,[status(esa)],[c_466]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_1181,plain,
% 3.37/0.92      ( k2_relset_1(X0_53,X1_53,sK2) != X1_53
% 3.37/0.92      | v1_funct_2(sK2,X0_53,X1_53) != iProver_top
% 3.37/0.92      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1_53,X0_53))) = iProver_top
% 3.37/0.92      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
% 3.37/0.92      inference(predicate_to_equality,[status(thm)],[c_694]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_2712,plain,
% 3.37/0.92      ( v1_funct_2(sK2,sK0,sK1) != iProver_top
% 3.37/0.92      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
% 3.37/0.92      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 3.37/0.92      inference(superposition,[status(thm)],[c_706,c_1181]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_32,negated_conjecture,
% 3.37/0.92      ( v1_funct_2(sK2,sK0,sK1) ),
% 3.37/0.92      inference(cnf_transformation,[],[f70]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_35,plain,
% 3.37/0.92      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 3.37/0.92      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_1363,plain,
% 3.37/0.92      ( ~ v1_funct_2(sK2,sK0,sK1)
% 3.37/0.92      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.37/0.92      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.37/0.92      | k2_relset_1(sK0,sK1,sK2) != sK1 ),
% 3.37/0.92      inference(instantiation,[status(thm)],[c_694]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_1364,plain,
% 3.37/0.92      ( k2_relset_1(sK0,sK1,sK2) != sK1
% 3.37/0.92      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 3.37/0.92      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
% 3.37/0.92      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 3.37/0.92      inference(predicate_to_equality,[status(thm)],[c_1363]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_2715,plain,
% 3.37/0.92      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.37/0.92      inference(global_propositional_subsumption,
% 3.37/0.92                [status(thm)],
% 3.37/0.92                [c_2712,c_35,c_36,c_706,c_1364]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_2721,plain,
% 3.37/0.92      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 3.37/0.92      | v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
% 3.37/0.92      inference(superposition,[status(thm)],[c_2715,c_1161]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_1544,plain,
% 3.37/0.92      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.37/0.92      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
% 3.37/0.92      | v1_relat_1(k2_funct_1(sK2)) ),
% 3.37/0.92      inference(instantiation,[status(thm)],[c_1371]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_1545,plain,
% 3.37/0.92      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.37/0.92      | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 3.37/0.92      | v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
% 3.37/0.92      inference(predicate_to_equality,[status(thm)],[c_1544]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_3094,plain,
% 3.37/0.92      ( v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
% 3.37/0.92      inference(global_propositional_subsumption,
% 3.37/0.92                [status(thm)],
% 3.37/0.92                [c_2721,c_35,c_36,c_706,c_1364,c_1545,c_1576]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_5,plain,
% 3.37/0.92      ( ~ v1_relat_1(X0)
% 3.37/0.92      | ~ v1_relat_1(X1)
% 3.37/0.92      | ~ v1_relat_1(X2)
% 3.37/0.92      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ),
% 3.37/0.92      inference(cnf_transformation,[],[f51]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_716,plain,
% 3.37/0.92      ( ~ v1_relat_1(X0_52)
% 3.37/0.92      | ~ v1_relat_1(X1_52)
% 3.37/0.92      | ~ v1_relat_1(X2_52)
% 3.37/0.92      | k5_relat_1(k5_relat_1(X0_52,X1_52),X2_52) = k5_relat_1(X0_52,k5_relat_1(X1_52,X2_52)) ),
% 3.37/0.92      inference(subtyping,[status(esa)],[c_5]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_1163,plain,
% 3.37/0.92      ( k5_relat_1(k5_relat_1(X0_52,X1_52),X2_52) = k5_relat_1(X0_52,k5_relat_1(X1_52,X2_52))
% 3.37/0.92      | v1_relat_1(X0_52) != iProver_top
% 3.37/0.92      | v1_relat_1(X1_52) != iProver_top
% 3.37/0.92      | v1_relat_1(X2_52) != iProver_top ),
% 3.37/0.92      inference(predicate_to_equality,[status(thm)],[c_716]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_3099,plain,
% 3.37/0.92      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0_52,X1_52)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0_52),X1_52)
% 3.37/0.92      | v1_relat_1(X0_52) != iProver_top
% 3.37/0.92      | v1_relat_1(X1_52) != iProver_top ),
% 3.37/0.92      inference(superposition,[status(thm)],[c_3094,c_1163]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_5360,plain,
% 3.37/0.92      ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),X0_52) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0_52))
% 3.37/0.92      | v1_relat_1(X0_52) != iProver_top ),
% 3.37/0.92      inference(superposition,[status(thm)],[c_1766,c_3099]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_12,plain,
% 3.37/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.37/0.92      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.37/0.92      inference(cnf_transformation,[],[f58]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_714,plain,
% 3.37/0.92      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 3.37/0.92      | k2_relset_1(X0_53,X1_53,X0_52) = k2_relat_1(X0_52) ),
% 3.37/0.92      inference(subtyping,[status(esa)],[c_12]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_1165,plain,
% 3.37/0.92      ( k2_relset_1(X0_53,X1_53,X0_52) = k2_relat_1(X0_52)
% 3.37/0.92      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
% 3.37/0.92      inference(predicate_to_equality,[status(thm)],[c_714]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_2321,plain,
% 3.37/0.92      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 3.37/0.92      inference(superposition,[status(thm)],[c_1173,c_1165]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_2326,plain,
% 3.37/0.92      ( k2_relat_1(sK2) = sK1 ),
% 3.37/0.92      inference(light_normalisation,[status(thm)],[c_2321,c_706]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_8,plain,
% 3.37/0.92      ( ~ v1_funct_1(X0)
% 3.37/0.92      | ~ v2_funct_1(X0)
% 3.37/0.92      | ~ v1_relat_1(X0)
% 3.37/0.92      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
% 3.37/0.92      inference(cnf_transformation,[],[f83]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_498,plain,
% 3.37/0.92      ( ~ v1_funct_1(X0)
% 3.37/0.92      | ~ v1_relat_1(X0)
% 3.37/0.92      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
% 3.37/0.92      | sK2 != X0 ),
% 3.37/0.92      inference(resolution_lifted,[status(thm)],[c_8,c_25]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_499,plain,
% 3.37/0.92      ( ~ v1_funct_1(sK2)
% 3.37/0.92      | ~ v1_relat_1(sK2)
% 3.37/0.92      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 3.37/0.92      inference(unflattening,[status(thm)],[c_498]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_501,plain,
% 3.37/0.92      ( ~ v1_relat_1(sK2)
% 3.37/0.92      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 3.37/0.92      inference(global_propositional_subsumption,
% 3.37/0.92                [status(thm)],
% 3.37/0.92                [c_499,c_33]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_692,plain,
% 3.37/0.92      ( ~ v1_relat_1(sK2)
% 3.37/0.92      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 3.37/0.92      inference(subtyping,[status(esa)],[c_501]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_1183,plain,
% 3.37/0.92      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
% 3.37/0.92      | v1_relat_1(sK2) != iProver_top ),
% 3.37/0.92      inference(predicate_to_equality,[status(thm)],[c_692]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_1867,plain,
% 3.37/0.92      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 3.37/0.92      inference(global_propositional_subsumption,
% 3.37/0.92                [status(thm)],
% 3.37/0.92                [c_1183,c_31,c_692,c_1536,c_1578]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_2332,plain,
% 3.37/0.92      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
% 3.37/0.92      inference(demodulation,[status(thm)],[c_2326,c_1867]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_5383,plain,
% 3.37/0.92      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0_52)) = k5_relat_1(k6_partfun1(sK1),X0_52)
% 3.37/0.92      | v1_relat_1(X0_52) != iProver_top ),
% 3.37/0.92      inference(light_normalisation,[status(thm)],[c_5360,c_2332]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_5451,plain,
% 3.37/0.92      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
% 3.37/0.92      inference(superposition,[status(thm)],[c_1713,c_5383]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_18,plain,
% 3.37/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.37/0.92      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.37/0.92      | ~ v1_funct_1(X0)
% 3.37/0.92      | ~ v1_funct_1(X3)
% 3.37/0.92      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.37/0.92      inference(cnf_transformation,[],[f64]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_710,plain,
% 3.37/0.92      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 3.37/0.92      | ~ m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(X2_53,X3_53)))
% 3.37/0.92      | ~ v1_funct_1(X0_52)
% 3.37/0.92      | ~ v1_funct_1(X1_52)
% 3.37/0.92      | k1_partfun1(X2_53,X3_53,X0_53,X1_53,X1_52,X0_52) = k5_relat_1(X1_52,X0_52) ),
% 3.37/0.92      inference(subtyping,[status(esa)],[c_18]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_1169,plain,
% 3.37/0.92      ( k1_partfun1(X0_53,X1_53,X2_53,X3_53,X0_52,X1_52) = k5_relat_1(X0_52,X1_52)
% 3.37/0.92      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 3.37/0.92      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(X2_53,X3_53))) != iProver_top
% 3.37/0.92      | v1_funct_1(X1_52) != iProver_top
% 3.37/0.92      | v1_funct_1(X0_52) != iProver_top ),
% 3.37/0.92      inference(predicate_to_equality,[status(thm)],[c_710]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_3495,plain,
% 3.37/0.92      ( k1_partfun1(X0_53,X1_53,sK1,sK0,X0_52,sK3) = k5_relat_1(X0_52,sK3)
% 3.37/0.92      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 3.37/0.92      | v1_funct_1(X0_52) != iProver_top
% 3.37/0.92      | v1_funct_1(sK3) != iProver_top ),
% 3.37/0.92      inference(superposition,[status(thm)],[c_1170,c_1169]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_30,negated_conjecture,
% 3.37/0.92      ( v1_funct_1(sK3) ),
% 3.37/0.92      inference(cnf_transformation,[],[f72]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_37,plain,
% 3.37/0.92      ( v1_funct_1(sK3) = iProver_top ),
% 3.37/0.92      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_3949,plain,
% 3.37/0.92      ( v1_funct_1(X0_52) != iProver_top
% 3.37/0.92      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 3.37/0.92      | k1_partfun1(X0_53,X1_53,sK1,sK0,X0_52,sK3) = k5_relat_1(X0_52,sK3) ),
% 3.37/0.92      inference(global_propositional_subsumption,
% 3.37/0.92                [status(thm)],
% 3.37/0.92                [c_3495,c_37]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_3950,plain,
% 3.37/0.92      ( k1_partfun1(X0_53,X1_53,sK1,sK0,X0_52,sK3) = k5_relat_1(X0_52,sK3)
% 3.37/0.92      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 3.37/0.92      | v1_funct_1(X0_52) != iProver_top ),
% 3.37/0.92      inference(renaming,[status(thm)],[c_3949]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_3959,plain,
% 3.37/0.92      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 3.37/0.92      | v1_funct_1(sK2) != iProver_top ),
% 3.37/0.92      inference(superposition,[status(thm)],[c_1173,c_3950]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_14,plain,
% 3.37/0.92      ( ~ r2_relset_1(X0,X1,X2,X3)
% 3.37/0.92      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.37/0.92      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.37/0.92      | X3 = X2 ),
% 3.37/0.92      inference(cnf_transformation,[],[f59]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_26,negated_conjecture,
% 3.37/0.92      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 3.37/0.92      inference(cnf_transformation,[],[f76]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_395,plain,
% 3.37/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.37/0.92      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.37/0.92      | X3 = X0
% 3.37/0.92      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 3.37/0.92      | k6_partfun1(sK0) != X3
% 3.37/0.92      | sK0 != X2
% 3.37/0.92      | sK0 != X1 ),
% 3.37/0.92      inference(resolution_lifted,[status(thm)],[c_14,c_26]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_396,plain,
% 3.37/0.92      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.37/0.92      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.37/0.92      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.37/0.92      inference(unflattening,[status(thm)],[c_395]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_15,plain,
% 3.37/0.92      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.37/0.92      inference(cnf_transformation,[],[f85]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_61,plain,
% 3.37/0.92      ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.37/0.92      inference(instantiation,[status(thm)],[c_15]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_398,plain,
% 3.37/0.92      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.37/0.92      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.37/0.92      inference(global_propositional_subsumption,
% 3.37/0.92                [status(thm)],
% 3.37/0.92                [c_396,c_61]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_697,plain,
% 3.37/0.92      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.37/0.92      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.37/0.92      inference(subtyping,[status(esa)],[c_398]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_1178,plain,
% 3.37/0.92      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.37/0.92      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.37/0.92      inference(predicate_to_equality,[status(thm)],[c_697]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_16,plain,
% 3.37/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.37/0.92      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.37/0.92      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.37/0.92      | ~ v1_funct_1(X0)
% 3.37/0.92      | ~ v1_funct_1(X3) ),
% 3.37/0.92      inference(cnf_transformation,[],[f63]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_712,plain,
% 3.37/0.92      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 3.37/0.92      | ~ m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(X2_53,X3_53)))
% 3.37/0.92      | m1_subset_1(k1_partfun1(X2_53,X3_53,X0_53,X1_53,X1_52,X0_52),k1_zfmisc_1(k2_zfmisc_1(X2_53,X1_53)))
% 3.37/0.92      | ~ v1_funct_1(X0_52)
% 3.37/0.92      | ~ v1_funct_1(X1_52) ),
% 3.37/0.92      inference(subtyping,[status(esa)],[c_16]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_1479,plain,
% 3.37/0.92      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 3.37/0.92      | m1_subset_1(k1_partfun1(X0_53,X1_53,sK1,sK0,X0_52,sK3),k1_zfmisc_1(k2_zfmisc_1(X0_53,sK0)))
% 3.37/0.92      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.37/0.92      | ~ v1_funct_1(X0_52)
% 3.37/0.92      | ~ v1_funct_1(sK3) ),
% 3.37/0.92      inference(instantiation,[status(thm)],[c_712]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_1680,plain,
% 3.37/0.92      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.37/0.92      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.37/0.92      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.37/0.92      | ~ v1_funct_1(sK3)
% 3.37/0.92      | ~ v1_funct_1(sK2) ),
% 3.37/0.92      inference(instantiation,[status(thm)],[c_1479]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_1871,plain,
% 3.37/0.92      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.37/0.92      inference(global_propositional_subsumption,
% 3.37/0.92                [status(thm)],
% 3.37/0.92                [c_1178,c_33,c_31,c_30,c_28,c_697,c_1680]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_3986,plain,
% 3.37/0.92      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 3.37/0.92      | v1_funct_1(sK2) != iProver_top ),
% 3.37/0.92      inference(light_normalisation,[status(thm)],[c_3959,c_1871]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_34,plain,
% 3.37/0.92      ( v1_funct_1(sK2) = iProver_top ),
% 3.37/0.92      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_4598,plain,
% 3.37/0.92      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 3.37/0.92      inference(global_propositional_subsumption,
% 3.37/0.92                [status(thm)],
% 3.37/0.92                [c_3986,c_34]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_10,plain,
% 3.37/0.92      ( v5_relat_1(X0,X1)
% 3.37/0.92      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.37/0.92      inference(cnf_transformation,[],[f57]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_2,plain,
% 3.37/0.92      ( r1_tarski(k2_relat_1(X0),X1)
% 3.37/0.92      | ~ v5_relat_1(X0,X1)
% 3.37/0.92      | ~ v1_relat_1(X0) ),
% 3.37/0.92      inference(cnf_transformation,[],[f47]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_356,plain,
% 3.37/0.92      ( r1_tarski(k2_relat_1(X0),X1)
% 3.37/0.92      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.37/0.92      | ~ v1_relat_1(X0) ),
% 3.37/0.92      inference(resolution,[status(thm)],[c_10,c_2]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_6,plain,
% 3.37/0.92      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 3.37/0.92      | ~ v1_relat_1(X0)
% 3.37/0.92      | k5_relat_1(X0,k6_partfun1(X1)) = X0 ),
% 3.37/0.92      inference(cnf_transformation,[],[f81]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_375,plain,
% 3.37/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.37/0.92      | ~ v1_relat_1(X0)
% 3.37/0.92      | k5_relat_1(X0,k6_partfun1(X2)) = X0 ),
% 3.37/0.92      inference(resolution,[status(thm)],[c_356,c_6]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_698,plain,
% 3.37/0.92      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 3.37/0.92      | ~ v1_relat_1(X0_52)
% 3.37/0.92      | k5_relat_1(X0_52,k6_partfun1(X1_53)) = X0_52 ),
% 3.37/0.92      inference(subtyping,[status(esa)],[c_375]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_1177,plain,
% 3.37/0.92      ( k5_relat_1(X0_52,k6_partfun1(X0_53)) = X0_52
% 3.37/0.92      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_53,X0_53))) != iProver_top
% 3.37/0.92      | v1_relat_1(X0_52) != iProver_top ),
% 3.37/0.92      inference(predicate_to_equality,[status(thm)],[c_698]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_4837,plain,
% 3.37/0.92      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k2_funct_1(sK2)
% 3.37/0.92      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.37/0.92      inference(superposition,[status(thm)],[c_2715,c_1177]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_3760,plain,
% 3.37/0.92      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.37/0.92      | ~ v1_relat_1(k2_funct_1(sK2))
% 3.37/0.92      | k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k2_funct_1(sK2) ),
% 3.37/0.92      inference(instantiation,[status(thm)],[c_698]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_4919,plain,
% 3.37/0.92      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k2_funct_1(sK2) ),
% 3.37/0.92      inference(global_propositional_subsumption,
% 3.37/0.92                [status(thm)],
% 3.37/0.92                [c_4837,c_32,c_31,c_706,c_1363,c_1544,c_1575,c_3760]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_5462,plain,
% 3.37/0.92      ( k5_relat_1(k6_partfun1(sK1),sK3) = k2_funct_1(sK2) ),
% 3.37/0.92      inference(light_normalisation,[status(thm)],[c_5451,c_4598,c_4919]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_5473,plain,
% 3.37/0.92      ( k7_relat_1(sK3,sK1) = k2_funct_1(sK2) ),
% 3.37/0.92      inference(superposition,[status(thm)],[c_2118,c_5462]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_11,plain,
% 3.37/0.92      ( v4_relat_1(X0,X1)
% 3.37/0.92      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.37/0.92      inference(cnf_transformation,[],[f56]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_4,plain,
% 3.37/0.92      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 3.37/0.92      inference(cnf_transformation,[],[f50]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_338,plain,
% 3.37/0.92      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.37/0.92      | ~ v1_relat_1(X0)
% 3.37/0.92      | k7_relat_1(X0,X1) = X0 ),
% 3.37/0.92      inference(resolution,[status(thm)],[c_11,c_4]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_699,plain,
% 3.37/0.92      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 3.37/0.92      | ~ v1_relat_1(X0_52)
% 3.37/0.92      | k7_relat_1(X0_52,X0_53) = X0_52 ),
% 3.37/0.92      inference(subtyping,[status(esa)],[c_338]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_1176,plain,
% 3.37/0.92      ( k7_relat_1(X0_52,X0_53) = X0_52
% 3.37/0.92      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 3.37/0.92      | v1_relat_1(X0_52) != iProver_top ),
% 3.37/0.92      inference(predicate_to_equality,[status(thm)],[c_699]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_756,plain,
% 3.37/0.92      ( v1_relat_1(k2_zfmisc_1(X0_53,X1_53)) = iProver_top ),
% 3.37/0.92      inference(predicate_to_equality,[status(thm)],[c_717]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_782,plain,
% 3.37/0.92      ( k7_relat_1(X0_52,X0_53) = X0_52
% 3.37/0.92      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 3.37/0.92      | v1_relat_1(X0_52) != iProver_top ),
% 3.37/0.92      inference(predicate_to_equality,[status(thm)],[c_699]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_1372,plain,
% 3.37/0.92      ( m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 3.37/0.92      | v1_relat_1(X0_52) = iProver_top
% 3.37/0.92      | v1_relat_1(k2_zfmisc_1(X0_53,X1_53)) != iProver_top ),
% 3.37/0.92      inference(predicate_to_equality,[status(thm)],[c_1371]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_4431,plain,
% 3.37/0.92      ( m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 3.37/0.92      | k7_relat_1(X0_52,X0_53) = X0_52 ),
% 3.37/0.92      inference(global_propositional_subsumption,
% 3.37/0.92                [status(thm)],
% 3.37/0.92                [c_1176,c_756,c_782,c_1372]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_4432,plain,
% 3.37/0.92      ( k7_relat_1(X0_52,X0_53) = X0_52
% 3.37/0.92      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
% 3.37/0.92      inference(renaming,[status(thm)],[c_4431]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_4439,plain,
% 3.37/0.92      ( k7_relat_1(sK3,sK1) = sK3 ),
% 3.37/0.92      inference(superposition,[status(thm)],[c_1170,c_4432]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_5475,plain,
% 3.37/0.92      ( k2_funct_1(sK2) = sK3 ),
% 3.37/0.92      inference(light_normalisation,[status(thm)],[c_5473,c_4439]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_22,negated_conjecture,
% 3.37/0.92      ( k2_funct_1(sK2) != sK3 ),
% 3.37/0.92      inference(cnf_transformation,[],[f80]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(c_709,negated_conjecture,
% 3.37/0.92      ( k2_funct_1(sK2) != sK3 ),
% 3.37/0.92      inference(subtyping,[status(esa)],[c_22]) ).
% 3.37/0.92  
% 3.37/0.92  cnf(contradiction,plain,
% 3.37/0.92      ( $false ),
% 3.37/0.92      inference(minisat,[status(thm)],[c_5475,c_709]) ).
% 3.37/0.92  
% 3.37/0.92  
% 3.37/0.92  % SZS output end CNFRefutation for theBenchmark.p
% 3.37/0.92  
% 3.37/0.92  ------                               Statistics
% 3.37/0.92  
% 3.37/0.92  ------ General
% 3.37/0.92  
% 3.37/0.92  abstr_ref_over_cycles:                  0
% 3.37/0.92  abstr_ref_under_cycles:                 0
% 3.37/0.92  gc_basic_clause_elim:                   0
% 3.37/0.92  forced_gc_time:                         0
% 3.37/0.92  parsing_time:                           0.009
% 3.37/0.92  unif_index_cands_time:                  0.
% 3.37/0.92  unif_index_add_time:                    0.
% 3.37/0.92  orderings_time:                         0.
% 3.37/0.92  out_proof_time:                         0.012
% 3.37/0.92  total_time:                             0.233
% 3.37/0.92  num_of_symbols:                         58
% 3.37/0.92  num_of_terms:                           5694
% 3.37/0.92  
% 3.37/0.92  ------ Preprocessing
% 3.37/0.92  
% 3.37/0.92  num_of_splits:                          0
% 3.37/0.92  num_of_split_atoms:                     0
% 3.37/0.92  num_of_reused_defs:                     0
% 3.37/0.92  num_eq_ax_congr_red:                    13
% 3.37/0.92  num_of_sem_filtered_clauses:            1
% 3.37/0.92  num_of_subtypes:                        3
% 3.37/0.92  monotx_restored_types:                  0
% 3.37/0.92  sat_num_of_epr_types:                   0
% 3.37/0.92  sat_num_of_non_cyclic_types:            0
% 3.37/0.92  sat_guarded_non_collapsed_types:        1
% 3.37/0.92  num_pure_diseq_elim:                    0
% 3.37/0.92  simp_replaced_by:                       0
% 3.37/0.92  res_preprocessed:                       152
% 3.37/0.92  prep_upred:                             0
% 3.37/0.92  prep_unflattend:                        13
% 3.37/0.92  smt_new_axioms:                         0
% 3.37/0.92  pred_elim_cands:                        4
% 3.37/0.92  pred_elim:                              5
% 3.37/0.92  pred_elim_cl:                           7
% 3.37/0.92  pred_elim_cycles:                       7
% 3.37/0.92  merged_defs:                            0
% 3.37/0.92  merged_defs_ncl:                        0
% 3.37/0.92  bin_hyper_res:                          0
% 3.37/0.92  prep_cycles:                            4
% 3.37/0.92  pred_elim_time:                         0.003
% 3.37/0.92  splitting_time:                         0.
% 3.37/0.92  sem_filter_time:                        0.
% 3.37/0.92  monotx_time:                            0.
% 3.37/0.92  subtype_inf_time:                       0.
% 3.37/0.92  
% 3.37/0.92  ------ Problem properties
% 3.37/0.92  
% 3.37/0.92  clauses:                                27
% 3.37/0.92  conjectures:                            10
% 3.37/0.92  epr:                                    6
% 3.37/0.92  horn:                                   27
% 3.37/0.92  ground:                                 13
% 3.37/0.92  unary:                                  12
% 3.37/0.92  binary:                                 5
% 3.37/0.92  lits:                                   62
% 3.37/0.92  lits_eq:                                16
% 3.37/0.92  fd_pure:                                0
% 3.37/0.92  fd_pseudo:                              0
% 3.37/0.92  fd_cond:                                0
% 3.37/0.92  fd_pseudo_cond:                         0
% 3.37/0.92  ac_symbols:                             0
% 3.37/0.92  
% 3.37/0.92  ------ Propositional Solver
% 3.37/0.92  
% 3.37/0.92  prop_solver_calls:                      28
% 3.37/0.92  prop_fast_solver_calls:                 1028
% 3.37/0.92  smt_solver_calls:                       0
% 3.37/0.92  smt_fast_solver_calls:                  0
% 3.37/0.92  prop_num_of_clauses:                    2401
% 3.37/0.92  prop_preprocess_simplified:             6092
% 3.37/0.92  prop_fo_subsumed:                       44
% 3.37/0.92  prop_solver_time:                       0.
% 3.37/0.92  smt_solver_time:                        0.
% 3.37/0.92  smt_fast_solver_time:                   0.
% 3.37/0.92  prop_fast_solver_time:                  0.
% 3.37/0.92  prop_unsat_core_time:                   0.
% 3.37/0.92  
% 3.37/0.92  ------ QBF
% 3.37/0.92  
% 3.37/0.92  qbf_q_res:                              0
% 3.37/0.92  qbf_num_tautologies:                    0
% 3.37/0.92  qbf_prep_cycles:                        0
% 3.37/0.92  
% 3.37/0.92  ------ BMC1
% 3.37/0.92  
% 3.37/0.92  bmc1_current_bound:                     -1
% 3.37/0.92  bmc1_last_solved_bound:                 -1
% 3.37/0.92  bmc1_unsat_core_size:                   -1
% 3.37/0.92  bmc1_unsat_core_parents_size:           -1
% 3.37/0.92  bmc1_merge_next_fun:                    0
% 3.37/0.92  bmc1_unsat_core_clauses_time:           0.
% 3.37/0.92  
% 3.37/0.92  ------ Instantiation
% 3.37/0.92  
% 3.37/0.92  inst_num_of_clauses:                    750
% 3.37/0.92  inst_num_in_passive:                    281
% 3.37/0.92  inst_num_in_active:                     454
% 3.37/0.92  inst_num_in_unprocessed:                15
% 3.37/0.92  inst_num_of_loops:                      490
% 3.37/0.92  inst_num_of_learning_restarts:          0
% 3.37/0.92  inst_num_moves_active_passive:          33
% 3.37/0.92  inst_lit_activity:                      0
% 3.37/0.92  inst_lit_activity_moves:                1
% 3.37/0.92  inst_num_tautologies:                   0
% 3.37/0.92  inst_num_prop_implied:                  0
% 3.37/0.92  inst_num_existing_simplified:           0
% 3.37/0.92  inst_num_eq_res_simplified:             0
% 3.37/0.92  inst_num_child_elim:                    0
% 3.37/0.92  inst_num_of_dismatching_blockings:      75
% 3.37/0.92  inst_num_of_non_proper_insts:           345
% 3.37/0.92  inst_num_of_duplicates:                 0
% 3.37/0.92  inst_inst_num_from_inst_to_res:         0
% 3.37/0.92  inst_dismatching_checking_time:         0.
% 3.37/0.92  
% 3.37/0.92  ------ Resolution
% 3.37/0.92  
% 3.37/0.92  res_num_of_clauses:                     0
% 3.37/0.92  res_num_in_passive:                     0
% 3.37/0.92  res_num_in_active:                      0
% 3.37/0.92  res_num_of_loops:                       156
% 3.37/0.92  res_forward_subset_subsumed:            19
% 3.37/0.92  res_backward_subset_subsumed:           0
% 3.37/0.92  res_forward_subsumed:                   0
% 3.37/0.92  res_backward_subsumed:                  0
% 3.37/0.92  res_forward_subsumption_resolution:     0
% 3.37/0.92  res_backward_subsumption_resolution:    0
% 3.37/0.92  res_clause_to_clause_subsumption:       233
% 3.37/0.92  res_orphan_elimination:                 0
% 3.37/0.92  res_tautology_del:                      15
% 3.37/0.92  res_num_eq_res_simplified:              0
% 3.37/0.92  res_num_sel_changes:                    0
% 3.37/0.92  res_moves_from_active_to_pass:          0
% 3.37/0.92  
% 3.37/0.92  ------ Superposition
% 3.37/0.92  
% 3.37/0.92  sup_time_total:                         0.
% 3.37/0.92  sup_time_generating:                    0.
% 3.37/0.92  sup_time_sim_full:                      0.
% 3.37/0.92  sup_time_sim_immed:                     0.
% 3.37/0.92  
% 3.37/0.92  sup_num_of_clauses:                     152
% 3.37/0.92  sup_num_in_active:                      97
% 3.37/0.92  sup_num_in_passive:                     55
% 3.37/0.92  sup_num_of_loops:                       97
% 3.37/0.92  sup_fw_superposition:                   101
% 3.37/0.92  sup_bw_superposition:                   30
% 3.37/0.92  sup_immediate_simplified:               27
% 3.37/0.92  sup_given_eliminated:                   0
% 3.37/0.92  comparisons_done:                       0
% 3.37/0.92  comparisons_avoided:                    0
% 3.37/0.92  
% 3.37/0.92  ------ Simplifications
% 3.37/0.92  
% 3.37/0.92  
% 3.37/0.92  sim_fw_subset_subsumed:                 0
% 3.37/0.92  sim_bw_subset_subsumed:                 0
% 3.37/0.92  sim_fw_subsumed:                        2
% 3.37/0.92  sim_bw_subsumed:                        0
% 3.37/0.92  sim_fw_subsumption_res:                 1
% 3.37/0.92  sim_bw_subsumption_res:                 0
% 3.37/0.92  sim_tautology_del:                      0
% 3.37/0.92  sim_eq_tautology_del:                   0
% 3.37/0.92  sim_eq_res_simp:                        0
% 3.37/0.92  sim_fw_demodulated:                     8
% 3.37/0.92  sim_bw_demodulated:                     1
% 3.37/0.92  sim_light_normalised:                   18
% 3.37/0.92  sim_joinable_taut:                      0
% 3.37/0.92  sim_joinable_simp:                      0
% 3.37/0.92  sim_ac_normalised:                      0
% 3.37/0.92  sim_smt_subsumption:                    0
% 3.37/0.92  
%------------------------------------------------------------------------------
