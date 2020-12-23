%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:28 EST 2020

% Result     : Theorem 47.46s
% Output     : CNFRefutation 47.46s
% Verified   : 
% Statistics : Number of formulae       :  274 (5490 expanded)
%              Number of clauses        :  198 (1553 expanded)
%              Number of leaves         :   20 (1396 expanded)
%              Depth                    :   30
%              Number of atoms          : 1037 (48085 expanded)
%              Number of equality atoms :  633 (17584 expanded)
%              Maximal formula depth    :   15 (   5 average)
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
    inference(ennf_transformation,[],[f17])).

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
    inference(flattening,[],[f38])).

fof(f43,plain,(
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

fof(f42,plain,
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

fof(f44,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f39,f43,f42])).

fof(f72,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f44])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f76,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f44])).

fof(f75,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f44])).

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
    inference(ennf_transformation,[],[f10])).

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

fof(f41,plain,(
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

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f74,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f79,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f44])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => ( v2_funct_1(X0)
              & v2_funct_1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X0)
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f73,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f34])).

fof(f67,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f70,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f28])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f77,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f44])).

fof(f12,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f66,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f32])).

fof(f65,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f3,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f14,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f82,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f48,f68])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f51,plain,(
    ! [X0] :
      ( k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f85,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f51,f68])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0)
              & k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f53,f68])).

fof(f15,axiom,(
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

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f87,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f57])).

fof(f71,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f80,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f44])).

fof(f81,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f44])).

fof(f78,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_164589,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_164601,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_165180,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_164589,c_164601])).

cnf(c_29,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_165182,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_165180,c_29])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_164592,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_164595,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_166039,plain,
    ( k1_relset_1(sK1,sK0,sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_164592,c_164595])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_164602,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_165279,plain,
    ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_164592,c_164602])).

cnf(c_166051,plain,
    ( k1_relat_1(sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_166039,c_165279])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_40,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_26,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_670,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_699,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_670])).

cnf(c_671,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_8546,plain,
    ( sK0 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_671])).

cnf(c_8547,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8546])).

cnf(c_23239,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_23240,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_23292,plain,
    ( k1_relset_1(sK1,sK0,sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_23239,c_23240])).

cnf(c_23241,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_23283,plain,
    ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_23239,c_23241])).

cnf(c_23293,plain,
    ( k1_relat_1(sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_23292,c_23283])).

cnf(c_172859,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_166051,c_40,c_26,c_699,c_8547,c_23293])).

cnf(c_4,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | v2_funct_1(X1)
    | ~ v2_funct_1(k5_relat_1(X0,X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X1) != k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_164607,plain,
    ( k1_relat_1(X0) != k2_relat_1(X1)
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) = iProver_top
    | v2_funct_1(k5_relat_1(X1,X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_172871,plain,
    ( k2_relat_1(X0) != sK1
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_172859,c_164607])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_39,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_41,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_56736,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_56737,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_56736])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_56801,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_56802,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_56801])).

cnf(c_57478,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_57135,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(arAF1_k2_zfmisc_1_0_1(sK1)))
    | ~ iProver_ARSWP_238 ),
    inference(arg_filter_abstr,[status(unp)],[c_30])).

cnf(c_57456,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(arAF1_k2_zfmisc_1_0_1(sK1))) = iProver_top
    | iProver_ARSWP_238 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_57135])).

cnf(c_57130,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(arAF1_k2_zfmisc_1_0_1(X1)))
    | ~ iProver_ARSWP_233
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(arg_filter_abstr,[status(unp)],[c_18])).

cnf(c_57461,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(arAF1_k2_zfmisc_1_0_1(X0))) != iProver_top
    | iProver_ARSWP_233 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_57130])).

cnf(c_58948,plain,
    ( k1_relset_1(sK1,X0,sK3) = sK1
    | k1_xboole_0 = X0
    | v1_funct_2(sK3,sK1,X0) != iProver_top
    | iProver_ARSWP_238 != iProver_top
    | iProver_ARSWP_233 != iProver_top ),
    inference(superposition,[status(thm)],[c_57456,c_57461])).

cnf(c_60710,plain,
    ( k1_relset_1(sK1,sK0,sK3) = sK1
    | sK0 = k1_xboole_0
    | iProver_ARSWP_238 != iProver_top
    | iProver_ARSWP_233 != iProver_top ),
    inference(superposition,[status(thm)],[c_57478,c_58948])).

cnf(c_23272,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k1_relset_1(sK1,sK0,sK3) = sK1
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_60717,plain,
    ( k1_relset_1(sK1,sK0,sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_60710,c_31,c_30,c_26,c_23272])).

cnf(c_57123,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(arAF1_k2_zfmisc_1_0_1(X1)))
    | ~ iProver_ARSWP_226
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(arg_filter_abstr,[status(unp)],[c_9])).

cnf(c_57468,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(arAF1_k2_zfmisc_1_0_1(X0))) != iProver_top
    | iProver_ARSWP_226 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_57123])).

cnf(c_58618,plain,
    ( k1_relset_1(sK1,X0,sK3) = k1_relat_1(sK3)
    | iProver_ARSWP_238 != iProver_top
    | iProver_ARSWP_226 != iProver_top ),
    inference(superposition,[status(thm)],[c_57456,c_57468])).

cnf(c_60722,plain,
    ( k1_relat_1(sK3) = sK1
    | iProver_ARSWP_238 != iProver_top
    | iProver_ARSWP_226 != iProver_top ),
    inference(superposition,[status(thm)],[c_60717,c_58618])).

cnf(c_60864,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_60722,c_40,c_26,c_699,c_8547,c_23293])).

cnf(c_57484,plain,
    ( k1_relat_1(X0) != k2_relat_1(X1)
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) = iProver_top
    | v2_funct_1(k5_relat_1(X1,X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_60897,plain,
    ( k2_relat_1(X0) != sK1
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_60864,c_57484])).

cnf(c_213605,plain,
    ( v1_relat_1(X0) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
    | k2_relat_1(X0) != sK1
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_172871,c_39,c_41,c_56737,c_56802,c_60897])).

cnf(c_213606,plain,
    ( k2_relat_1(X0) != sK1
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_213605])).

cnf(c_213615,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_165182,c_213606])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_164288,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | ~ iProver_ARSWP_247
    | arAF1_k1_partfun1_0_1_2(X4,X5) = k5_relat_1(X3,X0) ),
    inference(arg_filter_abstr,[status(unp)],[c_22])).

cnf(c_164579,plain,
    ( arAF1_k1_partfun1_0_1_2(X0,X1) = k5_relat_1(X2,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | iProver_ARSWP_247 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_164288])).

cnf(c_165487,plain,
    ( k5_relat_1(sK2,X0) = arAF1_k1_partfun1_0_1_2(sK0,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | iProver_ARSWP_247 != iProver_top ),
    inference(superposition,[status(thm)],[c_164589,c_164579])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_36,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_165820,plain,
    ( v1_funct_1(X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | k5_relat_1(sK2,X0) = arAF1_k1_partfun1_0_1_2(sK0,sK1)
    | iProver_ARSWP_247 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_165487,c_36])).

cnf(c_165821,plain,
    ( k5_relat_1(sK2,X0) = arAF1_k1_partfun1_0_1_2(sK0,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | iProver_ARSWP_247 != iProver_top ),
    inference(renaming,[status(thm)],[c_165820])).

cnf(c_165831,plain,
    ( arAF1_k1_partfun1_0_1_2(sK0,sK1) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK3) != iProver_top
    | iProver_ARSWP_247 != iProver_top ),
    inference(superposition,[status(thm)],[c_164592,c_165821])).

cnf(c_165885,plain,
    ( arAF1_k1_partfun1_0_1_2(sK0,sK1) = k5_relat_1(sK2,sK3)
    | iProver_ARSWP_247 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_165831,c_39])).

cnf(c_12,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_28,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_393,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_28])).

cnf(c_394,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_393])).

cnf(c_21,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_402,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_394,c_21])).

cnf(c_164290,plain,
    ( ~ m1_subset_1(arAF1_k1_partfun1_0_1_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ iProver_ARSWP_249
    | k6_partfun1(sK0) = arAF1_k1_partfun1_0_1_2(sK0,sK1) ),
    inference(arg_filter_abstr,[status(unp)],[c_402])).

cnf(c_164577,plain,
    ( k6_partfun1(sK0) = arAF1_k1_partfun1_0_1_2(sK0,sK1)
    | m1_subset_1(arAF1_k1_partfun1_0_1_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | iProver_ARSWP_249 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_164290])).

cnf(c_165891,plain,
    ( arAF1_k1_partfun1_0_1_2(sK0,sK1) = k6_partfun1(sK0)
    | m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | iProver_ARSWP_249 != iProver_top
    | iProver_ARSWP_247 != iProver_top ),
    inference(superposition,[status(thm)],[c_165885,c_164577])).

cnf(c_38,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_131335,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_131338,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_131340,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_131849,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_131338,c_131340])).

cnf(c_56621,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_56623,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_56871,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_56621,c_56623])).

cnf(c_132113,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_131849,c_39,c_56871])).

cnf(c_132114,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_132113])).

cnf(c_132123,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_131335,c_132114])).

cnf(c_56739,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(X1,X2,sK1,sK0,X0,sK3) = k5_relat_1(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_56808,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_56739])).

cnf(c_132178,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_132123,c_35,c_33,c_32,c_30,c_56808])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_131343,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_132183,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_132178,c_131343])).

cnf(c_170523,plain,
    ( arAF1_k1_partfun1_0_1_2(sK0,sK1) = k6_partfun1(sK0)
    | iProver_ARSWP_249 != iProver_top
    | iProver_ARSWP_247 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_165891,c_36,c_38,c_39,c_41,c_132183])).

cnf(c_170541,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | iProver_ARSWP_249 != iProver_top
    | iProver_ARSWP_247 != iProver_top ),
    inference(superposition,[status(thm)],[c_170523,c_165885])).

cnf(c_131331,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_402])).

cnf(c_132181,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_132178,c_131331])).

cnf(c_170873,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_170541,c_36,c_38,c_39,c_41,c_132181,c_132183])).

cnf(c_213695,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_213615,c_170873])).

cnf(c_56618,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_56630,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_56831,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_56618,c_56630])).

cnf(c_56850,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_56851,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_56850])).

cnf(c_213718,plain,
    ( v2_funct_1(sK3) = iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_213695,c_36,c_56831,c_56851])).

cnf(c_213719,plain,
    ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_213718])).

cnf(c_2,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_164609,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_213724,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_213719,c_164609])).

cnf(c_164590,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_7,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_164604,plain,
    ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_165551,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_164590,c_164604])).

cnf(c_38347,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_38356,plain,
    ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_38531,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_38347,c_38356])).

cnf(c_165617,plain,
    ( v2_funct_1(sK3) != iProver_top
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_165551,c_41,c_38531,c_56737,c_56802])).

cnf(c_165618,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
    | v2_funct_1(sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_165617])).

cnf(c_172862,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | v2_funct_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_172859,c_165618])).

cnf(c_213726,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
    inference(superposition,[status(thm)],[c_213724,c_172862])).

cnf(c_165832,plain,
    ( arAF1_k1_partfun1_0_1_2(sK0,sK1) = k5_relat_1(sK2,sK2)
    | v1_funct_1(sK2) != iProver_top
    | iProver_ARSWP_247 != iProver_top ),
    inference(superposition,[status(thm)],[c_164589,c_165821])).

cnf(c_166216,plain,
    ( arAF1_k1_partfun1_0_1_2(sK0,sK1) = k5_relat_1(sK2,sK2)
    | iProver_ARSWP_247 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_165832,c_36])).

cnf(c_166222,plain,
    ( k5_relat_1(sK2,sK2) = k5_relat_1(sK2,sK3)
    | iProver_ARSWP_247 != iProver_top ),
    inference(superposition,[status(thm)],[c_165885,c_166216])).

cnf(c_8,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k1_relat_1(X1) != k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_164603,plain,
    ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k1_relat_1(X1) != k2_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v2_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_166662,plain,
    ( k5_relat_1(sK2,sK2) != k6_partfun1(k2_relat_1(sK3))
    | k2_funct_1(sK3) = sK2
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | iProver_ARSWP_247 != iProver_top ),
    inference(superposition,[status(thm)],[c_166222,c_164603])).

cnf(c_165179,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_164592,c_164601])).

cnf(c_23,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X3,X1,X0)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_406,plain,
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
    inference(resolution_lifted,[status(thm)],[c_23,c_28])).

cnf(c_407,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0
    | k6_partfun1(sK0) != k6_partfun1(sK0) ),
    inference(unflattening,[status(thm)],[c_406])).

cnf(c_492,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_407])).

cnf(c_164291,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | ~ iProver_ARSWP_250
    | k2_relset_1(X1,sK0,X0) = sK0
    | arAF1_k1_partfun1_0_1_2(sK0,X1) != arAF1_k1_partfun1_0_1_2(sK0,sK1) ),
    inference(arg_filter_abstr,[status(unp)],[c_492])).

cnf(c_164576,plain,
    ( k2_relset_1(X0,sK0,X1) = sK0
    | arAF1_k1_partfun1_0_1_2(sK0,X0) != arAF1_k1_partfun1_0_1_2(sK0,sK1)
    | v1_funct_2(X1,X0,sK0) != iProver_top
    | v1_funct_2(X2,sK0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | iProver_ARSWP_250 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_164291])).

cnf(c_164965,plain,
    ( k2_relset_1(sK1,sK0,X0) = sK0
    | v1_funct_2(X1,sK0,sK1) != iProver_top
    | v1_funct_2(X0,sK1,sK0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | iProver_ARSWP_250 != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_164576])).

cnf(c_165099,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | v1_funct_2(X0,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | iProver_ARSWP_250 != iProver_top ),
    inference(superposition,[status(thm)],[c_164592,c_164965])).

cnf(c_132332,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_132181,c_36,c_38,c_39,c_41,c_132183])).

cnf(c_132335,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    inference(demodulation,[status(thm)],[c_132332,c_132178])).

cnf(c_11,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_358,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | X2 != X6
    | X2 != X5
    | k1_partfun1(X2,X1,X1,X2,X3,X0) != X4
    | k2_relset_1(X1,X2,X0) = X2
    | k6_partfun1(X2) != X4 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_23])).

cnf(c_359,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ m1_subset_1(k1_partfun1(X2,X1,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X2,X0) = X2
    | k6_partfun1(X2) != k1_partfun1(X2,X1,X1,X2,X3,X0) ),
    inference(unflattening,[status(thm)],[c_358])).

cnf(c_381,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X2,X0) = X2
    | k6_partfun1(X2) != k1_partfun1(X2,X1,X1,X2,X3,X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_359,c_19])).

cnf(c_131332,plain,
    ( k2_relset_1(X0,X1,X2) = X1
    | k6_partfun1(X1) != k1_partfun1(X1,X0,X0,X1,X3,X2)
    | v1_funct_2(X2,X0,X1) != iProver_top
    | v1_funct_2(X3,X1,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_381])).

cnf(c_132481,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_132335,c_131332])).

cnf(c_131346,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_131606,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_131338,c_131346])).

cnf(c_132489,plain,
    ( k2_relat_1(sK3) = sK0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_132481,c_131606])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_37,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_132185,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | k5_relat_1(sK2,sK3) != k6_partfun1(sK0)
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_132178,c_131332])).

cnf(c_132194,plain,
    ( k5_relat_1(sK2,sK3) != k6_partfun1(sK0)
    | k2_relat_1(sK3) = sK0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_132185,c_131606])).

cnf(c_133538,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_132489,c_36,c_37,c_38,c_39,c_40,c_41,c_132181,c_132183,c_132194])).

cnf(c_133543,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(demodulation,[status(thm)],[c_133538,c_131606])).

cnf(c_165141,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_165099,c_133543])).

cnf(c_165185,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_165179,c_165141])).

cnf(c_166672,plain,
    ( k5_relat_1(sK2,sK2) != k6_partfun1(sK0)
    | k2_funct_1(sK3) = sK2
    | k1_relat_1(sK3) != sK1
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | iProver_ARSWP_247 != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_166662,c_165182,c_165185])).

cnf(c_131348,plain,
    ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k1_relat_1(X1) != k2_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v2_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_132336,plain,
    ( k2_funct_1(sK3) = sK2
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_132332,c_131348])).

cnf(c_131607,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_131335,c_131346])).

cnf(c_131609,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_131607,c_29])).

cnf(c_131344,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_131733,plain,
    ( k1_relset_1(sK1,sK0,sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_131338,c_131344])).

cnf(c_131347,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_131656,plain,
    ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_131338,c_131347])).

cnf(c_131744,plain,
    ( k1_relat_1(sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_131733,c_131656])).

cnf(c_131837,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_131744,c_40,c_26,c_699,c_8547,c_23293])).

cnf(c_132337,plain,
    ( k2_funct_1(sK3) = sK2
    | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
    | sK1 != sK1
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_132336,c_131609,c_131837])).

cnf(c_132338,plain,
    ( k2_funct_1(sK3) = sK2
    | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_132337])).

cnf(c_133458,plain,
    ( k2_funct_1(sK3) = sK2
    | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
    | v2_funct_1(sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_132338,c_36,c_39,c_41,c_56737,c_56802,c_56831,c_56851])).

cnf(c_133541,plain,
    ( k2_funct_1(sK3) = sK2
    | k6_partfun1(sK0) != k6_partfun1(sK0)
    | v2_funct_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_133538,c_133458])).

cnf(c_133550,plain,
    ( k2_funct_1(sK3) = sK2
    | v2_funct_1(sK3) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_133541])).

cnf(c_167499,plain,
    ( v2_funct_1(sK3) != iProver_top
    | k2_funct_1(sK3) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_166672,c_133550])).

cnf(c_167500,plain,
    ( k2_funct_1(sK3) = sK2
    | v2_funct_1(sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_167499])).

cnf(c_213728,plain,
    ( k2_funct_1(sK3) = sK2 ),
    inference(superposition,[status(thm)],[c_213724,c_167500])).

cnf(c_213733,plain,
    ( k5_relat_1(sK3,sK2) = k6_partfun1(sK1) ),
    inference(light_normalisation,[status(thm)],[c_213726,c_213728])).

cnf(c_214535,plain,
    ( k2_funct_1(sK2) = sK3
    | k1_relat_1(sK2) != k2_relat_1(sK3)
    | k6_partfun1(k2_relat_1(sK2)) != k6_partfun1(sK1)
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_213733,c_164603])).

cnf(c_166040,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_164589,c_164595])).

cnf(c_165280,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_164589,c_164602])).

cnf(c_166044,plain,
    ( k1_relat_1(sK2) = sK0
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_166040,c_165280])).

cnf(c_25,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_8544,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_671])).

cnf(c_8545,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8544])).

cnf(c_56624,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_56925,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_56618,c_56624])).

cnf(c_56626,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_56815,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_56618,c_56626])).

cnf(c_56929,plain,
    ( k1_relat_1(sK2) = sK0
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_56925,c_56815])).

cnf(c_172155,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_166044,c_37,c_25,c_699,c_8545,c_56929])).

cnf(c_214536,plain,
    ( k2_funct_1(sK2) = sK3
    | k6_partfun1(sK1) != k6_partfun1(sK1)
    | sK0 != sK0
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_214535,c_165182,c_165185,c_172155])).

cnf(c_214537,plain,
    ( k2_funct_1(sK2) = sK3
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_214536])).

cnf(c_24,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_27,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_43,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_214537,c_56851,c_56831,c_56802,c_56737,c_24,c_43,c_41,c_39,c_36])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:50:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 47.46/6.51  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 47.46/6.51  
% 47.46/6.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 47.46/6.51  
% 47.46/6.51  ------  iProver source info
% 47.46/6.51  
% 47.46/6.51  git: date: 2020-06-30 10:37:57 +0100
% 47.46/6.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 47.46/6.51  git: non_committed_changes: false
% 47.46/6.51  git: last_make_outside_of_git: false
% 47.46/6.51  
% 47.46/6.51  ------ 
% 47.46/6.51  ------ Parsing...
% 47.46/6.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 47.46/6.51  
% 47.46/6.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 47.46/6.51  
% 47.46/6.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 47.46/6.51  
% 47.46/6.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 47.46/6.51  ------ Proving...
% 47.46/6.51  ------ Problem Properties 
% 47.46/6.51  
% 47.46/6.51  
% 47.46/6.51  clauses                                 35
% 47.46/6.51  conjectures                             11
% 47.46/6.51  EPR                                     7
% 47.46/6.51  Horn                                    31
% 47.46/6.51  unary                                   15
% 47.46/6.51  binary                                  3
% 47.46/6.51  lits                                    106
% 47.46/6.51  lits eq                                 28
% 47.46/6.51  fd_pure                                 0
% 47.46/6.51  fd_pseudo                               0
% 47.46/6.51  fd_cond                                 3
% 47.46/6.51  fd_pseudo_cond                          1
% 47.46/6.51  AC symbols                              0
% 47.46/6.51  
% 47.46/6.51  ------ Input Options Time Limit: Unbounded
% 47.46/6.51  
% 47.46/6.51  
% 47.46/6.51  
% 47.46/6.51  
% 47.46/6.51  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 47.46/6.51  Current options:
% 47.46/6.51  ------ 
% 47.46/6.51  
% 47.46/6.51  
% 47.46/6.51  
% 47.46/6.51  
% 47.46/6.51  ------ Proving...
% 47.46/6.51  
% 47.46/6.51  
% 47.46/6.51  ------ Preprocessing... sf_s  rm: 7 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 47.46/6.51  
% 47.46/6.51  ------ Proving...
% 47.46/6.51  
% 47.46/6.51  
% 47.46/6.51  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 47.46/6.51  
% 47.46/6.51  ------ Proving...
% 47.46/6.51  
% 47.46/6.51  
% 47.46/6.51  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 47.46/6.51  
% 47.46/6.51  ------ Proving...
% 47.46/6.51  
% 47.46/6.51  
% 47.46/6.51  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 47.46/6.51  
% 47.46/6.51  ------ Proving...
% 47.46/6.51  
% 47.46/6.51  
% 47.46/6.51  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 47.46/6.51  
% 47.46/6.51  ------ Proving...
% 47.46/6.51  
% 47.46/6.51  
% 47.46/6.51  ------ Preprocessing... sf_s  rm: 8 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 47.46/6.51  
% 47.46/6.51  ------ Proving...
% 47.46/6.51  
% 47.46/6.51  
% 47.46/6.51  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 47.46/6.51  
% 47.46/6.51  ------ Proving...
% 47.46/6.51  
% 47.46/6.51  
% 47.46/6.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 47.46/6.51  
% 47.46/6.51  ------ Proving...
% 47.46/6.51  
% 47.46/6.51  
% 47.46/6.51  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 47.46/6.51  
% 47.46/6.51  ------ Proving...
% 47.46/6.51  
% 47.46/6.51  
% 47.46/6.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 47.46/6.51  
% 47.46/6.51  ------ Proving...
% 47.46/6.51  
% 47.46/6.51  
% 47.46/6.51  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 47.46/6.51  
% 47.46/6.51  ------ Proving...
% 47.46/6.51  
% 47.46/6.51  
% 47.46/6.51  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 47.46/6.51  
% 47.46/6.51  ------ Proving...
% 47.46/6.51  
% 47.46/6.51  
% 47.46/6.51  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 47.46/6.51  
% 47.46/6.51  ------ Proving...
% 47.46/6.51  
% 47.46/6.51  
% 47.46/6.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 47.46/6.51  
% 47.46/6.51  ------ Proving...
% 47.46/6.51  
% 47.46/6.51  
% 47.46/6.51  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 47.46/6.51  
% 47.46/6.51  ------ Proving...
% 47.46/6.51  
% 47.46/6.51  
% 47.46/6.51  % SZS status Theorem for theBenchmark.p
% 47.46/6.51  
% 47.46/6.51  % SZS output start CNFRefutation for theBenchmark.p
% 47.46/6.51  
% 47.46/6.51  fof(f16,conjecture,(
% 47.46/6.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 47.46/6.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.46/6.51  
% 47.46/6.51  fof(f17,negated_conjecture,(
% 47.46/6.51    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 47.46/6.51    inference(negated_conjecture,[],[f16])).
% 47.46/6.51  
% 47.46/6.51  fof(f38,plain,(
% 47.46/6.51    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 47.46/6.51    inference(ennf_transformation,[],[f17])).
% 47.46/6.51  
% 47.46/6.51  fof(f39,plain,(
% 47.46/6.51    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 47.46/6.51    inference(flattening,[],[f38])).
% 47.46/6.51  
% 47.46/6.51  fof(f43,plain,(
% 47.46/6.51    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 47.46/6.51    introduced(choice_axiom,[])).
% 47.46/6.51  
% 47.46/6.51  fof(f42,plain,(
% 47.46/6.51    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 47.46/6.51    introduced(choice_axiom,[])).
% 47.46/6.51  
% 47.46/6.51  fof(f44,plain,(
% 47.46/6.51    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 47.46/6.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f39,f43,f42])).
% 47.46/6.51  
% 47.46/6.51  fof(f72,plain,(
% 47.46/6.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 47.46/6.51    inference(cnf_transformation,[],[f44])).
% 47.46/6.51  
% 47.46/6.51  fof(f8,axiom,(
% 47.46/6.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 47.46/6.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.46/6.51  
% 47.46/6.51  fof(f27,plain,(
% 47.46/6.51    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 47.46/6.51    inference(ennf_transformation,[],[f8])).
% 47.46/6.51  
% 47.46/6.51  fof(f55,plain,(
% 47.46/6.51    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 47.46/6.51    inference(cnf_transformation,[],[f27])).
% 47.46/6.51  
% 47.46/6.51  fof(f76,plain,(
% 47.46/6.51    k2_relset_1(sK0,sK1,sK2) = sK1),
% 47.46/6.51    inference(cnf_transformation,[],[f44])).
% 47.46/6.51  
% 47.46/6.51  fof(f75,plain,(
% 47.46/6.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 47.46/6.51    inference(cnf_transformation,[],[f44])).
% 47.46/6.51  
% 47.46/6.51  fof(f10,axiom,(
% 47.46/6.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 47.46/6.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.46/6.51  
% 47.46/6.51  fof(f30,plain,(
% 47.46/6.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 47.46/6.51    inference(ennf_transformation,[],[f10])).
% 47.46/6.51  
% 47.46/6.51  fof(f31,plain,(
% 47.46/6.51    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 47.46/6.51    inference(flattening,[],[f30])).
% 47.46/6.51  
% 47.46/6.51  fof(f41,plain,(
% 47.46/6.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 47.46/6.51    inference(nnf_transformation,[],[f31])).
% 47.46/6.51  
% 47.46/6.51  fof(f58,plain,(
% 47.46/6.51    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 47.46/6.51    inference(cnf_transformation,[],[f41])).
% 47.46/6.51  
% 47.46/6.51  fof(f7,axiom,(
% 47.46/6.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 47.46/6.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.46/6.51  
% 47.46/6.51  fof(f26,plain,(
% 47.46/6.51    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 47.46/6.51    inference(ennf_transformation,[],[f7])).
% 47.46/6.51  
% 47.46/6.51  fof(f54,plain,(
% 47.46/6.51    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 47.46/6.51    inference(cnf_transformation,[],[f26])).
% 47.46/6.51  
% 47.46/6.51  fof(f74,plain,(
% 47.46/6.51    v1_funct_2(sK3,sK1,sK0)),
% 47.46/6.51    inference(cnf_transformation,[],[f44])).
% 47.46/6.51  
% 47.46/6.51  fof(f79,plain,(
% 47.46/6.51    k1_xboole_0 != sK0),
% 47.46/6.51    inference(cnf_transformation,[],[f44])).
% 47.46/6.51  
% 47.46/6.51  fof(f4,axiom,(
% 47.46/6.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 47.46/6.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.46/6.51  
% 47.46/6.51  fof(f20,plain,(
% 47.46/6.51    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 47.46/6.51    inference(ennf_transformation,[],[f4])).
% 47.46/6.51  
% 47.46/6.51  fof(f21,plain,(
% 47.46/6.51    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 47.46/6.51    inference(flattening,[],[f20])).
% 47.46/6.51  
% 47.46/6.51  fof(f50,plain,(
% 47.46/6.51    ( ! [X0,X1] : (v2_funct_1(X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 47.46/6.51    inference(cnf_transformation,[],[f21])).
% 47.46/6.51  
% 47.46/6.51  fof(f73,plain,(
% 47.46/6.51    v1_funct_1(sK3)),
% 47.46/6.51    inference(cnf_transformation,[],[f44])).
% 47.46/6.51  
% 47.46/6.51  fof(f1,axiom,(
% 47.46/6.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 47.46/6.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.46/6.51  
% 47.46/6.51  fof(f19,plain,(
% 47.46/6.51    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 47.46/6.51    inference(ennf_transformation,[],[f1])).
% 47.46/6.51  
% 47.46/6.51  fof(f45,plain,(
% 47.46/6.51    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 47.46/6.51    inference(cnf_transformation,[],[f19])).
% 47.46/6.51  
% 47.46/6.51  fof(f2,axiom,(
% 47.46/6.51    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 47.46/6.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.46/6.51  
% 47.46/6.51  fof(f46,plain,(
% 47.46/6.51    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 47.46/6.51    inference(cnf_transformation,[],[f2])).
% 47.46/6.51  
% 47.46/6.51  fof(f13,axiom,(
% 47.46/6.51    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 47.46/6.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.46/6.51  
% 47.46/6.51  fof(f34,plain,(
% 47.46/6.51    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 47.46/6.51    inference(ennf_transformation,[],[f13])).
% 47.46/6.51  
% 47.46/6.51  fof(f35,plain,(
% 47.46/6.51    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 47.46/6.51    inference(flattening,[],[f34])).
% 47.46/6.51  
% 47.46/6.51  fof(f67,plain,(
% 47.46/6.51    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 47.46/6.51    inference(cnf_transformation,[],[f35])).
% 47.46/6.51  
% 47.46/6.51  fof(f70,plain,(
% 47.46/6.51    v1_funct_1(sK2)),
% 47.46/6.51    inference(cnf_transformation,[],[f44])).
% 47.46/6.51  
% 47.46/6.51  fof(f9,axiom,(
% 47.46/6.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 47.46/6.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.46/6.51  
% 47.46/6.51  fof(f28,plain,(
% 47.46/6.51    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 47.46/6.51    inference(ennf_transformation,[],[f9])).
% 47.46/6.51  
% 47.46/6.51  fof(f29,plain,(
% 47.46/6.51    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 47.46/6.51    inference(flattening,[],[f28])).
% 47.46/6.51  
% 47.46/6.51  fof(f40,plain,(
% 47.46/6.51    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 47.46/6.51    inference(nnf_transformation,[],[f29])).
% 47.46/6.51  
% 47.46/6.51  fof(f56,plain,(
% 47.46/6.51    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 47.46/6.51    inference(cnf_transformation,[],[f40])).
% 47.46/6.51  
% 47.46/6.51  fof(f77,plain,(
% 47.46/6.51    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 47.46/6.51    inference(cnf_transformation,[],[f44])).
% 47.46/6.51  
% 47.46/6.51  fof(f12,axiom,(
% 47.46/6.51    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 47.46/6.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.46/6.51  
% 47.46/6.51  fof(f18,plain,(
% 47.46/6.51    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 47.46/6.51    inference(pure_predicate_removal,[],[f12])).
% 47.46/6.51  
% 47.46/6.51  fof(f66,plain,(
% 47.46/6.51    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 47.46/6.51    inference(cnf_transformation,[],[f18])).
% 47.46/6.51  
% 47.46/6.51  fof(f11,axiom,(
% 47.46/6.51    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 47.46/6.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.46/6.51  
% 47.46/6.51  fof(f32,plain,(
% 47.46/6.51    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 47.46/6.51    inference(ennf_transformation,[],[f11])).
% 47.46/6.51  
% 47.46/6.51  fof(f33,plain,(
% 47.46/6.51    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 47.46/6.51    inference(flattening,[],[f32])).
% 47.46/6.51  
% 47.46/6.51  fof(f65,plain,(
% 47.46/6.51    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 47.46/6.51    inference(cnf_transformation,[],[f33])).
% 47.46/6.51  
% 47.46/6.51  fof(f3,axiom,(
% 47.46/6.51    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 47.46/6.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.46/6.51  
% 47.46/6.51  fof(f48,plain,(
% 47.46/6.51    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 47.46/6.51    inference(cnf_transformation,[],[f3])).
% 47.46/6.51  
% 47.46/6.51  fof(f14,axiom,(
% 47.46/6.51    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 47.46/6.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.46/6.51  
% 47.46/6.51  fof(f68,plain,(
% 47.46/6.51    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 47.46/6.51    inference(cnf_transformation,[],[f14])).
% 47.46/6.51  
% 47.46/6.51  fof(f82,plain,(
% 47.46/6.51    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 47.46/6.51    inference(definition_unfolding,[],[f48,f68])).
% 47.46/6.51  
% 47.46/6.51  fof(f5,axiom,(
% 47.46/6.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)))))),
% 47.46/6.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.46/6.51  
% 47.46/6.51  fof(f22,plain,(
% 47.46/6.51    ! [X0] : (((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 47.46/6.51    inference(ennf_transformation,[],[f5])).
% 47.46/6.51  
% 47.46/6.51  fof(f23,plain,(
% 47.46/6.51    ! [X0] : ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 47.46/6.51    inference(flattening,[],[f22])).
% 47.46/6.51  
% 47.46/6.51  fof(f51,plain,(
% 47.46/6.51    ( ! [X0] : (k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 47.46/6.51    inference(cnf_transformation,[],[f23])).
% 47.46/6.51  
% 47.46/6.51  fof(f85,plain,(
% 47.46/6.51    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 47.46/6.51    inference(definition_unfolding,[],[f51,f68])).
% 47.46/6.51  
% 47.46/6.51  fof(f6,axiom,(
% 47.46/6.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 47.46/6.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.46/6.51  
% 47.46/6.51  fof(f24,plain,(
% 47.46/6.51    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 47.46/6.51    inference(ennf_transformation,[],[f6])).
% 47.46/6.51  
% 47.46/6.51  fof(f25,plain,(
% 47.46/6.51    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 47.46/6.51    inference(flattening,[],[f24])).
% 47.46/6.51  
% 47.46/6.51  fof(f53,plain,(
% 47.46/6.51    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 47.46/6.51    inference(cnf_transformation,[],[f25])).
% 47.46/6.51  
% 47.46/6.51  fof(f86,plain,(
% 47.46/6.51    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 47.46/6.51    inference(definition_unfolding,[],[f53,f68])).
% 47.46/6.51  
% 47.46/6.51  fof(f15,axiom,(
% 47.46/6.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 47.46/6.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.46/6.51  
% 47.46/6.51  fof(f36,plain,(
% 47.46/6.51    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 47.46/6.51    inference(ennf_transformation,[],[f15])).
% 47.46/6.51  
% 47.46/6.51  fof(f37,plain,(
% 47.46/6.51    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 47.46/6.51    inference(flattening,[],[f36])).
% 47.46/6.51  
% 47.46/6.51  fof(f69,plain,(
% 47.46/6.51    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 47.46/6.51    inference(cnf_transformation,[],[f37])).
% 47.46/6.51  
% 47.46/6.51  fof(f57,plain,(
% 47.46/6.51    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 47.46/6.51    inference(cnf_transformation,[],[f40])).
% 47.46/6.51  
% 47.46/6.51  fof(f87,plain,(
% 47.46/6.51    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 47.46/6.51    inference(equality_resolution,[],[f57])).
% 47.46/6.51  
% 47.46/6.51  fof(f71,plain,(
% 47.46/6.51    v1_funct_2(sK2,sK0,sK1)),
% 47.46/6.51    inference(cnf_transformation,[],[f44])).
% 47.46/6.51  
% 47.46/6.51  fof(f80,plain,(
% 47.46/6.51    k1_xboole_0 != sK1),
% 47.46/6.51    inference(cnf_transformation,[],[f44])).
% 47.46/6.51  
% 47.46/6.51  fof(f81,plain,(
% 47.46/6.51    k2_funct_1(sK2) != sK3),
% 47.46/6.51    inference(cnf_transformation,[],[f44])).
% 47.46/6.51  
% 47.46/6.51  fof(f78,plain,(
% 47.46/6.51    v2_funct_1(sK2)),
% 47.46/6.51    inference(cnf_transformation,[],[f44])).
% 47.46/6.51  
% 47.46/6.51  cnf(c_33,negated_conjecture,
% 47.46/6.51      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 47.46/6.51      inference(cnf_transformation,[],[f72]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_164589,plain,
% 47.46/6.51      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 47.46/6.51      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_10,plain,
% 47.46/6.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 47.46/6.51      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 47.46/6.51      inference(cnf_transformation,[],[f55]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_164601,plain,
% 47.46/6.51      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 47.46/6.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 47.46/6.51      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_165180,plain,
% 47.46/6.51      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 47.46/6.51      inference(superposition,[status(thm)],[c_164589,c_164601]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_29,negated_conjecture,
% 47.46/6.51      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 47.46/6.51      inference(cnf_transformation,[],[f76]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_165182,plain,
% 47.46/6.51      ( k2_relat_1(sK2) = sK1 ),
% 47.46/6.51      inference(light_normalisation,[status(thm)],[c_165180,c_29]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_30,negated_conjecture,
% 47.46/6.51      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 47.46/6.51      inference(cnf_transformation,[],[f75]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_164592,plain,
% 47.46/6.51      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 47.46/6.51      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_18,plain,
% 47.46/6.51      ( ~ v1_funct_2(X0,X1,X2)
% 47.46/6.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 47.46/6.51      | k1_relset_1(X1,X2,X0) = X1
% 47.46/6.51      | k1_xboole_0 = X2 ),
% 47.46/6.51      inference(cnf_transformation,[],[f58]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_164595,plain,
% 47.46/6.51      ( k1_relset_1(X0,X1,X2) = X0
% 47.46/6.51      | k1_xboole_0 = X1
% 47.46/6.51      | v1_funct_2(X2,X0,X1) != iProver_top
% 47.46/6.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 47.46/6.51      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_166039,plain,
% 47.46/6.51      ( k1_relset_1(sK1,sK0,sK3) = sK1
% 47.46/6.51      | sK0 = k1_xboole_0
% 47.46/6.51      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 47.46/6.51      inference(superposition,[status(thm)],[c_164592,c_164595]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_9,plain,
% 47.46/6.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 47.46/6.51      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 47.46/6.51      inference(cnf_transformation,[],[f54]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_164602,plain,
% 47.46/6.51      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 47.46/6.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 47.46/6.51      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_165279,plain,
% 47.46/6.51      ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
% 47.46/6.51      inference(superposition,[status(thm)],[c_164592,c_164602]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_166051,plain,
% 47.46/6.51      ( k1_relat_1(sK3) = sK1
% 47.46/6.51      | sK0 = k1_xboole_0
% 47.46/6.51      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 47.46/6.51      inference(demodulation,[status(thm)],[c_166039,c_165279]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_31,negated_conjecture,
% 47.46/6.51      ( v1_funct_2(sK3,sK1,sK0) ),
% 47.46/6.51      inference(cnf_transformation,[],[f74]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_40,plain,
% 47.46/6.51      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 47.46/6.51      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_26,negated_conjecture,
% 47.46/6.51      ( k1_xboole_0 != sK0 ),
% 47.46/6.51      inference(cnf_transformation,[],[f79]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_670,plain,( X0 = X0 ),theory(equality) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_699,plain,
% 47.46/6.51      ( k1_xboole_0 = k1_xboole_0 ),
% 47.46/6.51      inference(instantiation,[status(thm)],[c_670]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_671,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_8546,plain,
% 47.46/6.51      ( sK0 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK0 ),
% 47.46/6.51      inference(instantiation,[status(thm)],[c_671]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_8547,plain,
% 47.46/6.51      ( sK0 != k1_xboole_0
% 47.46/6.51      | k1_xboole_0 = sK0
% 47.46/6.51      | k1_xboole_0 != k1_xboole_0 ),
% 47.46/6.51      inference(instantiation,[status(thm)],[c_8546]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_23239,plain,
% 47.46/6.51      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 47.46/6.51      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_23240,plain,
% 47.46/6.51      ( k1_relset_1(X0,X1,X2) = X0
% 47.46/6.51      | k1_xboole_0 = X1
% 47.46/6.51      | v1_funct_2(X2,X0,X1) != iProver_top
% 47.46/6.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 47.46/6.51      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_23292,plain,
% 47.46/6.51      ( k1_relset_1(sK1,sK0,sK3) = sK1
% 47.46/6.51      | sK0 = k1_xboole_0
% 47.46/6.51      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 47.46/6.51      inference(superposition,[status(thm)],[c_23239,c_23240]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_23241,plain,
% 47.46/6.51      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 47.46/6.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 47.46/6.51      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_23283,plain,
% 47.46/6.51      ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
% 47.46/6.51      inference(superposition,[status(thm)],[c_23239,c_23241]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_23293,plain,
% 47.46/6.51      ( k1_relat_1(sK3) = sK1
% 47.46/6.51      | sK0 = k1_xboole_0
% 47.46/6.51      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 47.46/6.51      inference(demodulation,[status(thm)],[c_23292,c_23283]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_172859,plain,
% 47.46/6.51      ( k1_relat_1(sK3) = sK1 ),
% 47.46/6.51      inference(global_propositional_subsumption,
% 47.46/6.51                [status(thm)],
% 47.46/6.51                [c_166051,c_40,c_26,c_699,c_8547,c_23293]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_4,plain,
% 47.46/6.51      ( ~ v1_funct_1(X0)
% 47.46/6.51      | ~ v1_funct_1(X1)
% 47.46/6.51      | v2_funct_1(X1)
% 47.46/6.51      | ~ v2_funct_1(k5_relat_1(X0,X1))
% 47.46/6.51      | ~ v1_relat_1(X1)
% 47.46/6.51      | ~ v1_relat_1(X0)
% 47.46/6.51      | k1_relat_1(X1) != k2_relat_1(X0) ),
% 47.46/6.51      inference(cnf_transformation,[],[f50]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_164607,plain,
% 47.46/6.51      ( k1_relat_1(X0) != k2_relat_1(X1)
% 47.46/6.51      | v1_funct_1(X1) != iProver_top
% 47.46/6.51      | v1_funct_1(X0) != iProver_top
% 47.46/6.51      | v2_funct_1(X0) = iProver_top
% 47.46/6.51      | v2_funct_1(k5_relat_1(X1,X0)) != iProver_top
% 47.46/6.51      | v1_relat_1(X0) != iProver_top
% 47.46/6.51      | v1_relat_1(X1) != iProver_top ),
% 47.46/6.51      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_172871,plain,
% 47.46/6.51      ( k2_relat_1(X0) != sK1
% 47.46/6.51      | v1_funct_1(X0) != iProver_top
% 47.46/6.51      | v1_funct_1(sK3) != iProver_top
% 47.46/6.51      | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
% 47.46/6.51      | v2_funct_1(sK3) = iProver_top
% 47.46/6.51      | v1_relat_1(X0) != iProver_top
% 47.46/6.51      | v1_relat_1(sK3) != iProver_top ),
% 47.46/6.51      inference(superposition,[status(thm)],[c_172859,c_164607]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_32,negated_conjecture,
% 47.46/6.51      ( v1_funct_1(sK3) ),
% 47.46/6.51      inference(cnf_transformation,[],[f73]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_39,plain,
% 47.46/6.51      ( v1_funct_1(sK3) = iProver_top ),
% 47.46/6.51      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_41,plain,
% 47.46/6.51      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 47.46/6.51      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_0,plain,
% 47.46/6.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 47.46/6.51      | ~ v1_relat_1(X1)
% 47.46/6.51      | v1_relat_1(X0) ),
% 47.46/6.51      inference(cnf_transformation,[],[f45]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_56736,plain,
% 47.46/6.51      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 47.46/6.51      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
% 47.46/6.51      | v1_relat_1(sK3) ),
% 47.46/6.51      inference(instantiation,[status(thm)],[c_0]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_56737,plain,
% 47.46/6.51      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 47.46/6.51      | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 47.46/6.51      | v1_relat_1(sK3) = iProver_top ),
% 47.46/6.51      inference(predicate_to_equality,[status(thm)],[c_56736]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_1,plain,
% 47.46/6.51      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 47.46/6.51      inference(cnf_transformation,[],[f46]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_56801,plain,
% 47.46/6.51      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
% 47.46/6.51      inference(instantiation,[status(thm)],[c_1]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_56802,plain,
% 47.46/6.51      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
% 47.46/6.51      inference(predicate_to_equality,[status(thm)],[c_56801]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_57478,plain,
% 47.46/6.51      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 47.46/6.51      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_57135,negated_conjecture,
% 47.46/6.51      ( m1_subset_1(sK3,k1_zfmisc_1(arAF1_k2_zfmisc_1_0_1(sK1)))
% 47.46/6.51      | ~ iProver_ARSWP_238 ),
% 47.46/6.51      inference(arg_filter_abstr,[status(unp)],[c_30]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_57456,plain,
% 47.46/6.51      ( m1_subset_1(sK3,k1_zfmisc_1(arAF1_k2_zfmisc_1_0_1(sK1))) = iProver_top
% 47.46/6.51      | iProver_ARSWP_238 != iProver_top ),
% 47.46/6.51      inference(predicate_to_equality,[status(thm)],[c_57135]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_57130,plain,
% 47.46/6.51      ( ~ v1_funct_2(X0,X1,X2)
% 47.46/6.51      | ~ m1_subset_1(X0,k1_zfmisc_1(arAF1_k2_zfmisc_1_0_1(X1)))
% 47.46/6.51      | ~ iProver_ARSWP_233
% 47.46/6.51      | k1_relset_1(X1,X2,X0) = X1
% 47.46/6.51      | k1_xboole_0 = X2 ),
% 47.46/6.51      inference(arg_filter_abstr,[status(unp)],[c_18]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_57461,plain,
% 47.46/6.51      ( k1_relset_1(X0,X1,X2) = X0
% 47.46/6.51      | k1_xboole_0 = X1
% 47.46/6.51      | v1_funct_2(X2,X0,X1) != iProver_top
% 47.46/6.51      | m1_subset_1(X2,k1_zfmisc_1(arAF1_k2_zfmisc_1_0_1(X0))) != iProver_top
% 47.46/6.51      | iProver_ARSWP_233 != iProver_top ),
% 47.46/6.51      inference(predicate_to_equality,[status(thm)],[c_57130]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_58948,plain,
% 47.46/6.51      ( k1_relset_1(sK1,X0,sK3) = sK1
% 47.46/6.51      | k1_xboole_0 = X0
% 47.46/6.51      | v1_funct_2(sK3,sK1,X0) != iProver_top
% 47.46/6.51      | iProver_ARSWP_238 != iProver_top
% 47.46/6.51      | iProver_ARSWP_233 != iProver_top ),
% 47.46/6.51      inference(superposition,[status(thm)],[c_57456,c_57461]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_60710,plain,
% 47.46/6.51      ( k1_relset_1(sK1,sK0,sK3) = sK1
% 47.46/6.51      | sK0 = k1_xboole_0
% 47.46/6.51      | iProver_ARSWP_238 != iProver_top
% 47.46/6.51      | iProver_ARSWP_233 != iProver_top ),
% 47.46/6.51      inference(superposition,[status(thm)],[c_57478,c_58948]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_23272,plain,
% 47.46/6.51      ( ~ v1_funct_2(sK3,sK1,sK0)
% 47.46/6.51      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 47.46/6.51      | k1_relset_1(sK1,sK0,sK3) = sK1
% 47.46/6.51      | k1_xboole_0 = sK0 ),
% 47.46/6.51      inference(instantiation,[status(thm)],[c_18]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_60717,plain,
% 47.46/6.51      ( k1_relset_1(sK1,sK0,sK3) = sK1 ),
% 47.46/6.51      inference(global_propositional_subsumption,
% 47.46/6.51                [status(thm)],
% 47.46/6.51                [c_60710,c_31,c_30,c_26,c_23272]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_57123,plain,
% 47.46/6.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(arAF1_k2_zfmisc_1_0_1(X1)))
% 47.46/6.51      | ~ iProver_ARSWP_226
% 47.46/6.51      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 47.46/6.51      inference(arg_filter_abstr,[status(unp)],[c_9]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_57468,plain,
% 47.46/6.51      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 47.46/6.51      | m1_subset_1(X2,k1_zfmisc_1(arAF1_k2_zfmisc_1_0_1(X0))) != iProver_top
% 47.46/6.51      | iProver_ARSWP_226 != iProver_top ),
% 47.46/6.51      inference(predicate_to_equality,[status(thm)],[c_57123]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_58618,plain,
% 47.46/6.51      ( k1_relset_1(sK1,X0,sK3) = k1_relat_1(sK3)
% 47.46/6.51      | iProver_ARSWP_238 != iProver_top
% 47.46/6.51      | iProver_ARSWP_226 != iProver_top ),
% 47.46/6.51      inference(superposition,[status(thm)],[c_57456,c_57468]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_60722,plain,
% 47.46/6.51      ( k1_relat_1(sK3) = sK1
% 47.46/6.51      | iProver_ARSWP_238 != iProver_top
% 47.46/6.51      | iProver_ARSWP_226 != iProver_top ),
% 47.46/6.51      inference(superposition,[status(thm)],[c_60717,c_58618]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_60864,plain,
% 47.46/6.51      ( k1_relat_1(sK3) = sK1 ),
% 47.46/6.51      inference(global_propositional_subsumption,
% 47.46/6.51                [status(thm)],
% 47.46/6.51                [c_60722,c_40,c_26,c_699,c_8547,c_23293]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_57484,plain,
% 47.46/6.51      ( k1_relat_1(X0) != k2_relat_1(X1)
% 47.46/6.51      | v1_funct_1(X1) != iProver_top
% 47.46/6.51      | v1_funct_1(X0) != iProver_top
% 47.46/6.51      | v2_funct_1(X0) = iProver_top
% 47.46/6.51      | v2_funct_1(k5_relat_1(X1,X0)) != iProver_top
% 47.46/6.51      | v1_relat_1(X0) != iProver_top
% 47.46/6.51      | v1_relat_1(X1) != iProver_top ),
% 47.46/6.51      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_60897,plain,
% 47.46/6.51      ( k2_relat_1(X0) != sK1
% 47.46/6.51      | v1_funct_1(X0) != iProver_top
% 47.46/6.51      | v1_funct_1(sK3) != iProver_top
% 47.46/6.51      | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
% 47.46/6.51      | v2_funct_1(sK3) = iProver_top
% 47.46/6.51      | v1_relat_1(X0) != iProver_top
% 47.46/6.51      | v1_relat_1(sK3) != iProver_top ),
% 47.46/6.51      inference(superposition,[status(thm)],[c_60864,c_57484]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_213605,plain,
% 47.46/6.51      ( v1_relat_1(X0) != iProver_top
% 47.46/6.51      | v2_funct_1(sK3) = iProver_top
% 47.46/6.51      | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
% 47.46/6.51      | k2_relat_1(X0) != sK1
% 47.46/6.51      | v1_funct_1(X0) != iProver_top ),
% 47.46/6.51      inference(global_propositional_subsumption,
% 47.46/6.51                [status(thm)],
% 47.46/6.51                [c_172871,c_39,c_41,c_56737,c_56802,c_60897]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_213606,plain,
% 47.46/6.51      ( k2_relat_1(X0) != sK1
% 47.46/6.51      | v1_funct_1(X0) != iProver_top
% 47.46/6.51      | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
% 47.46/6.51      | v2_funct_1(sK3) = iProver_top
% 47.46/6.51      | v1_relat_1(X0) != iProver_top ),
% 47.46/6.51      inference(renaming,[status(thm)],[c_213605]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_213615,plain,
% 47.46/6.51      ( v1_funct_1(sK2) != iProver_top
% 47.46/6.51      | v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
% 47.46/6.51      | v2_funct_1(sK3) = iProver_top
% 47.46/6.51      | v1_relat_1(sK2) != iProver_top ),
% 47.46/6.51      inference(superposition,[status(thm)],[c_165182,c_213606]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_22,plain,
% 47.46/6.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 47.46/6.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 47.46/6.51      | ~ v1_funct_1(X0)
% 47.46/6.51      | ~ v1_funct_1(X3)
% 47.46/6.51      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 47.46/6.51      inference(cnf_transformation,[],[f67]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_164288,plain,
% 47.46/6.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 47.46/6.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 47.46/6.51      | ~ v1_funct_1(X0)
% 47.46/6.51      | ~ v1_funct_1(X3)
% 47.46/6.51      | ~ iProver_ARSWP_247
% 47.46/6.51      | arAF1_k1_partfun1_0_1_2(X4,X5) = k5_relat_1(X3,X0) ),
% 47.46/6.51      inference(arg_filter_abstr,[status(unp)],[c_22]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_164579,plain,
% 47.46/6.51      ( arAF1_k1_partfun1_0_1_2(X0,X1) = k5_relat_1(X2,X3)
% 47.46/6.51      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 47.46/6.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 47.46/6.51      | v1_funct_1(X2) != iProver_top
% 47.46/6.51      | v1_funct_1(X3) != iProver_top
% 47.46/6.51      | iProver_ARSWP_247 != iProver_top ),
% 47.46/6.51      inference(predicate_to_equality,[status(thm)],[c_164288]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_165487,plain,
% 47.46/6.51      ( k5_relat_1(sK2,X0) = arAF1_k1_partfun1_0_1_2(sK0,sK1)
% 47.46/6.51      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 47.46/6.51      | v1_funct_1(X0) != iProver_top
% 47.46/6.51      | v1_funct_1(sK2) != iProver_top
% 47.46/6.51      | iProver_ARSWP_247 != iProver_top ),
% 47.46/6.51      inference(superposition,[status(thm)],[c_164589,c_164579]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_35,negated_conjecture,
% 47.46/6.51      ( v1_funct_1(sK2) ),
% 47.46/6.51      inference(cnf_transformation,[],[f70]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_36,plain,
% 47.46/6.51      ( v1_funct_1(sK2) = iProver_top ),
% 47.46/6.51      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_165820,plain,
% 47.46/6.51      ( v1_funct_1(X0) != iProver_top
% 47.46/6.51      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 47.46/6.51      | k5_relat_1(sK2,X0) = arAF1_k1_partfun1_0_1_2(sK0,sK1)
% 47.46/6.51      | iProver_ARSWP_247 != iProver_top ),
% 47.46/6.51      inference(global_propositional_subsumption,
% 47.46/6.51                [status(thm)],
% 47.46/6.51                [c_165487,c_36]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_165821,plain,
% 47.46/6.51      ( k5_relat_1(sK2,X0) = arAF1_k1_partfun1_0_1_2(sK0,sK1)
% 47.46/6.51      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 47.46/6.51      | v1_funct_1(X0) != iProver_top
% 47.46/6.51      | iProver_ARSWP_247 != iProver_top ),
% 47.46/6.51      inference(renaming,[status(thm)],[c_165820]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_165831,plain,
% 47.46/6.51      ( arAF1_k1_partfun1_0_1_2(sK0,sK1) = k5_relat_1(sK2,sK3)
% 47.46/6.51      | v1_funct_1(sK3) != iProver_top
% 47.46/6.51      | iProver_ARSWP_247 != iProver_top ),
% 47.46/6.51      inference(superposition,[status(thm)],[c_164592,c_165821]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_165885,plain,
% 47.46/6.51      ( arAF1_k1_partfun1_0_1_2(sK0,sK1) = k5_relat_1(sK2,sK3)
% 47.46/6.51      | iProver_ARSWP_247 != iProver_top ),
% 47.46/6.51      inference(global_propositional_subsumption,
% 47.46/6.51                [status(thm)],
% 47.46/6.51                [c_165831,c_39]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_12,plain,
% 47.46/6.51      ( ~ r2_relset_1(X0,X1,X2,X3)
% 47.46/6.51      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 47.46/6.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 47.46/6.51      | X3 = X2 ),
% 47.46/6.51      inference(cnf_transformation,[],[f56]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_28,negated_conjecture,
% 47.46/6.51      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 47.46/6.51      inference(cnf_transformation,[],[f77]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_393,plain,
% 47.46/6.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 47.46/6.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 47.46/6.51      | X3 = X0
% 47.46/6.51      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 47.46/6.51      | k6_partfun1(sK0) != X3
% 47.46/6.51      | sK0 != X2
% 47.46/6.51      | sK0 != X1 ),
% 47.46/6.51      inference(resolution_lifted,[status(thm)],[c_12,c_28]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_394,plain,
% 47.46/6.51      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 47.46/6.51      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 47.46/6.51      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 47.46/6.51      inference(unflattening,[status(thm)],[c_393]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_21,plain,
% 47.46/6.51      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 47.46/6.51      inference(cnf_transformation,[],[f66]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_402,plain,
% 47.46/6.51      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 47.46/6.51      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 47.46/6.51      inference(forward_subsumption_resolution,
% 47.46/6.51                [status(thm)],
% 47.46/6.51                [c_394,c_21]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_164290,plain,
% 47.46/6.51      ( ~ m1_subset_1(arAF1_k1_partfun1_0_1_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 47.46/6.51      | ~ iProver_ARSWP_249
% 47.46/6.51      | k6_partfun1(sK0) = arAF1_k1_partfun1_0_1_2(sK0,sK1) ),
% 47.46/6.51      inference(arg_filter_abstr,[status(unp)],[c_402]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_164577,plain,
% 47.46/6.51      ( k6_partfun1(sK0) = arAF1_k1_partfun1_0_1_2(sK0,sK1)
% 47.46/6.51      | m1_subset_1(arAF1_k1_partfun1_0_1_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 47.46/6.51      | iProver_ARSWP_249 != iProver_top ),
% 47.46/6.51      inference(predicate_to_equality,[status(thm)],[c_164290]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_165891,plain,
% 47.46/6.51      ( arAF1_k1_partfun1_0_1_2(sK0,sK1) = k6_partfun1(sK0)
% 47.46/6.51      | m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 47.46/6.51      | iProver_ARSWP_249 != iProver_top
% 47.46/6.51      | iProver_ARSWP_247 != iProver_top ),
% 47.46/6.51      inference(superposition,[status(thm)],[c_165885,c_164577]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_38,plain,
% 47.46/6.51      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 47.46/6.51      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_131335,plain,
% 47.46/6.51      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 47.46/6.51      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_131338,plain,
% 47.46/6.51      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 47.46/6.51      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_131340,plain,
% 47.46/6.51      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 47.46/6.51      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 47.46/6.51      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 47.46/6.51      | v1_funct_1(X4) != iProver_top
% 47.46/6.51      | v1_funct_1(X5) != iProver_top ),
% 47.46/6.51      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_131849,plain,
% 47.46/6.51      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 47.46/6.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 47.46/6.51      | v1_funct_1(X2) != iProver_top
% 47.46/6.51      | v1_funct_1(sK3) != iProver_top ),
% 47.46/6.51      inference(superposition,[status(thm)],[c_131338,c_131340]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_56621,plain,
% 47.46/6.51      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 47.46/6.51      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_56623,plain,
% 47.46/6.51      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 47.46/6.51      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 47.46/6.51      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 47.46/6.51      | v1_funct_1(X4) != iProver_top
% 47.46/6.51      | v1_funct_1(X5) != iProver_top ),
% 47.46/6.51      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_56871,plain,
% 47.46/6.51      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 47.46/6.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 47.46/6.51      | v1_funct_1(X2) != iProver_top
% 47.46/6.51      | v1_funct_1(sK3) != iProver_top ),
% 47.46/6.51      inference(superposition,[status(thm)],[c_56621,c_56623]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_132113,plain,
% 47.46/6.51      ( v1_funct_1(X2) != iProver_top
% 47.46/6.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 47.46/6.51      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 47.46/6.51      inference(global_propositional_subsumption,
% 47.46/6.51                [status(thm)],
% 47.46/6.51                [c_131849,c_39,c_56871]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_132114,plain,
% 47.46/6.51      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 47.46/6.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 47.46/6.51      | v1_funct_1(X2) != iProver_top ),
% 47.46/6.51      inference(renaming,[status(thm)],[c_132113]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_132123,plain,
% 47.46/6.51      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 47.46/6.51      | v1_funct_1(sK2) != iProver_top ),
% 47.46/6.51      inference(superposition,[status(thm)],[c_131335,c_132114]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_56739,plain,
% 47.46/6.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 47.46/6.51      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 47.46/6.51      | ~ v1_funct_1(X0)
% 47.46/6.51      | ~ v1_funct_1(sK3)
% 47.46/6.51      | k1_partfun1(X1,X2,sK1,sK0,X0,sK3) = k5_relat_1(X0,sK3) ),
% 47.46/6.51      inference(instantiation,[status(thm)],[c_22]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_56808,plain,
% 47.46/6.51      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 47.46/6.51      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 47.46/6.51      | ~ v1_funct_1(sK3)
% 47.46/6.51      | ~ v1_funct_1(sK2)
% 47.46/6.51      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 47.46/6.51      inference(instantiation,[status(thm)],[c_56739]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_132178,plain,
% 47.46/6.51      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 47.46/6.51      inference(global_propositional_subsumption,
% 47.46/6.51                [status(thm)],
% 47.46/6.51                [c_132123,c_35,c_33,c_32,c_30,c_56808]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_19,plain,
% 47.46/6.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 47.46/6.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 47.46/6.51      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 47.46/6.51      | ~ v1_funct_1(X0)
% 47.46/6.51      | ~ v1_funct_1(X3) ),
% 47.46/6.51      inference(cnf_transformation,[],[f65]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_131343,plain,
% 47.46/6.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 47.46/6.51      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 47.46/6.51      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 47.46/6.51      | v1_funct_1(X3) != iProver_top
% 47.46/6.51      | v1_funct_1(X0) != iProver_top ),
% 47.46/6.51      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_132183,plain,
% 47.46/6.51      ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 47.46/6.51      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 47.46/6.51      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 47.46/6.51      | v1_funct_1(sK3) != iProver_top
% 47.46/6.51      | v1_funct_1(sK2) != iProver_top ),
% 47.46/6.51      inference(superposition,[status(thm)],[c_132178,c_131343]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_170523,plain,
% 47.46/6.51      ( arAF1_k1_partfun1_0_1_2(sK0,sK1) = k6_partfun1(sK0)
% 47.46/6.51      | iProver_ARSWP_249 != iProver_top
% 47.46/6.51      | iProver_ARSWP_247 != iProver_top ),
% 47.46/6.51      inference(global_propositional_subsumption,
% 47.46/6.51                [status(thm)],
% 47.46/6.51                [c_165891,c_36,c_38,c_39,c_41,c_132183]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_170541,plain,
% 47.46/6.51      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 47.46/6.51      | iProver_ARSWP_249 != iProver_top
% 47.46/6.51      | iProver_ARSWP_247 != iProver_top ),
% 47.46/6.51      inference(superposition,[status(thm)],[c_170523,c_165885]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_131331,plain,
% 47.46/6.51      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 47.46/6.51      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 47.46/6.51      inference(predicate_to_equality,[status(thm)],[c_402]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_132181,plain,
% 47.46/6.51      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 47.46/6.51      | m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 47.46/6.51      inference(demodulation,[status(thm)],[c_132178,c_131331]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_170873,plain,
% 47.46/6.51      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 47.46/6.51      inference(global_propositional_subsumption,
% 47.46/6.51                [status(thm)],
% 47.46/6.51                [c_170541,c_36,c_38,c_39,c_41,c_132181,c_132183]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_213695,plain,
% 47.46/6.51      ( v1_funct_1(sK2) != iProver_top
% 47.46/6.51      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 47.46/6.51      | v2_funct_1(sK3) = iProver_top
% 47.46/6.51      | v1_relat_1(sK2) != iProver_top ),
% 47.46/6.51      inference(light_normalisation,[status(thm)],[c_213615,c_170873]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_56618,plain,
% 47.46/6.51      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 47.46/6.51      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_56630,plain,
% 47.46/6.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 47.46/6.51      | v1_relat_1(X1) != iProver_top
% 47.46/6.51      | v1_relat_1(X0) = iProver_top ),
% 47.46/6.51      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_56831,plain,
% 47.46/6.51      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 47.46/6.51      | v1_relat_1(sK2) = iProver_top ),
% 47.46/6.51      inference(superposition,[status(thm)],[c_56618,c_56630]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_56850,plain,
% 47.46/6.51      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 47.46/6.51      inference(instantiation,[status(thm)],[c_1]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_56851,plain,
% 47.46/6.51      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 47.46/6.51      inference(predicate_to_equality,[status(thm)],[c_56850]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_213718,plain,
% 47.46/6.51      ( v2_funct_1(sK3) = iProver_top
% 47.46/6.51      | v2_funct_1(k6_partfun1(sK0)) != iProver_top ),
% 47.46/6.51      inference(global_propositional_subsumption,
% 47.46/6.51                [status(thm)],
% 47.46/6.51                [c_213695,c_36,c_56831,c_56851]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_213719,plain,
% 47.46/6.51      ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 47.46/6.51      | v2_funct_1(sK3) = iProver_top ),
% 47.46/6.51      inference(renaming,[status(thm)],[c_213718]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_2,plain,
% 47.46/6.51      ( v2_funct_1(k6_partfun1(X0)) ),
% 47.46/6.51      inference(cnf_transformation,[],[f82]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_164609,plain,
% 47.46/6.51      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 47.46/6.51      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_213724,plain,
% 47.46/6.51      ( v2_funct_1(sK3) = iProver_top ),
% 47.46/6.51      inference(forward_subsumption_resolution,
% 47.46/6.51                [status(thm)],
% 47.46/6.51                [c_213719,c_164609]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_164590,plain,
% 47.46/6.51      ( v1_funct_1(sK3) = iProver_top ),
% 47.46/6.51      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_7,plain,
% 47.46/6.51      ( ~ v1_funct_1(X0)
% 47.46/6.51      | ~ v2_funct_1(X0)
% 47.46/6.51      | ~ v1_relat_1(X0)
% 47.46/6.51      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
% 47.46/6.51      inference(cnf_transformation,[],[f85]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_164604,plain,
% 47.46/6.51      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
% 47.46/6.51      | v1_funct_1(X0) != iProver_top
% 47.46/6.51      | v2_funct_1(X0) != iProver_top
% 47.46/6.51      | v1_relat_1(X0) != iProver_top ),
% 47.46/6.51      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_165551,plain,
% 47.46/6.51      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
% 47.46/6.51      | v2_funct_1(sK3) != iProver_top
% 47.46/6.51      | v1_relat_1(sK3) != iProver_top ),
% 47.46/6.51      inference(superposition,[status(thm)],[c_164590,c_164604]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_38347,plain,
% 47.46/6.51      ( v1_funct_1(sK3) = iProver_top ),
% 47.46/6.51      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_38356,plain,
% 47.46/6.51      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
% 47.46/6.51      | v1_funct_1(X0) != iProver_top
% 47.46/6.51      | v2_funct_1(X0) != iProver_top
% 47.46/6.51      | v1_relat_1(X0) != iProver_top ),
% 47.46/6.51      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_38531,plain,
% 47.46/6.51      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
% 47.46/6.51      | v2_funct_1(sK3) != iProver_top
% 47.46/6.51      | v1_relat_1(sK3) != iProver_top ),
% 47.46/6.51      inference(superposition,[status(thm)],[c_38347,c_38356]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_165617,plain,
% 47.46/6.51      ( v2_funct_1(sK3) != iProver_top
% 47.46/6.51      | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3)) ),
% 47.46/6.51      inference(global_propositional_subsumption,
% 47.46/6.51                [status(thm)],
% 47.46/6.51                [c_165551,c_41,c_38531,c_56737,c_56802]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_165618,plain,
% 47.46/6.51      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
% 47.46/6.51      | v2_funct_1(sK3) != iProver_top ),
% 47.46/6.51      inference(renaming,[status(thm)],[c_165617]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_172862,plain,
% 47.46/6.51      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
% 47.46/6.51      | v2_funct_1(sK3) != iProver_top ),
% 47.46/6.51      inference(demodulation,[status(thm)],[c_172859,c_165618]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_213726,plain,
% 47.46/6.51      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
% 47.46/6.51      inference(superposition,[status(thm)],[c_213724,c_172862]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_165832,plain,
% 47.46/6.51      ( arAF1_k1_partfun1_0_1_2(sK0,sK1) = k5_relat_1(sK2,sK2)
% 47.46/6.51      | v1_funct_1(sK2) != iProver_top
% 47.46/6.51      | iProver_ARSWP_247 != iProver_top ),
% 47.46/6.51      inference(superposition,[status(thm)],[c_164589,c_165821]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_166216,plain,
% 47.46/6.51      ( arAF1_k1_partfun1_0_1_2(sK0,sK1) = k5_relat_1(sK2,sK2)
% 47.46/6.51      | iProver_ARSWP_247 != iProver_top ),
% 47.46/6.51      inference(global_propositional_subsumption,
% 47.46/6.51                [status(thm)],
% 47.46/6.51                [c_165832,c_36]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_166222,plain,
% 47.46/6.51      ( k5_relat_1(sK2,sK2) = k5_relat_1(sK2,sK3)
% 47.46/6.51      | iProver_ARSWP_247 != iProver_top ),
% 47.46/6.51      inference(superposition,[status(thm)],[c_165885,c_166216]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_8,plain,
% 47.46/6.51      ( ~ v1_funct_1(X0)
% 47.46/6.51      | ~ v1_funct_1(X1)
% 47.46/6.51      | ~ v2_funct_1(X1)
% 47.46/6.51      | ~ v1_relat_1(X1)
% 47.46/6.51      | ~ v1_relat_1(X0)
% 47.46/6.51      | k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 47.46/6.51      | k2_funct_1(X1) = X0
% 47.46/6.51      | k1_relat_1(X1) != k2_relat_1(X0) ),
% 47.46/6.51      inference(cnf_transformation,[],[f86]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_164603,plain,
% 47.46/6.51      ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 47.46/6.51      | k2_funct_1(X1) = X0
% 47.46/6.51      | k1_relat_1(X1) != k2_relat_1(X0)
% 47.46/6.51      | v1_funct_1(X0) != iProver_top
% 47.46/6.51      | v1_funct_1(X1) != iProver_top
% 47.46/6.51      | v2_funct_1(X1) != iProver_top
% 47.46/6.51      | v1_relat_1(X1) != iProver_top
% 47.46/6.51      | v1_relat_1(X0) != iProver_top ),
% 47.46/6.51      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_166662,plain,
% 47.46/6.51      ( k5_relat_1(sK2,sK2) != k6_partfun1(k2_relat_1(sK3))
% 47.46/6.51      | k2_funct_1(sK3) = sK2
% 47.46/6.51      | k1_relat_1(sK3) != k2_relat_1(sK2)
% 47.46/6.51      | v1_funct_1(sK3) != iProver_top
% 47.46/6.51      | v1_funct_1(sK2) != iProver_top
% 47.46/6.51      | v2_funct_1(sK3) != iProver_top
% 47.46/6.51      | v1_relat_1(sK3) != iProver_top
% 47.46/6.51      | v1_relat_1(sK2) != iProver_top
% 47.46/6.51      | iProver_ARSWP_247 != iProver_top ),
% 47.46/6.51      inference(superposition,[status(thm)],[c_166222,c_164603]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_165179,plain,
% 47.46/6.51      ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 47.46/6.51      inference(superposition,[status(thm)],[c_164592,c_164601]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_23,plain,
% 47.46/6.51      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 47.46/6.51      | ~ v1_funct_2(X3,X1,X0)
% 47.46/6.51      | ~ v1_funct_2(X2,X0,X1)
% 47.46/6.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 47.46/6.51      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 47.46/6.51      | ~ v1_funct_1(X2)
% 47.46/6.51      | ~ v1_funct_1(X3)
% 47.46/6.51      | k2_relset_1(X1,X0,X3) = X0 ),
% 47.46/6.51      inference(cnf_transformation,[],[f69]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_406,plain,
% 47.46/6.51      ( ~ v1_funct_2(X0,X1,X2)
% 47.46/6.51      | ~ v1_funct_2(X3,X2,X1)
% 47.46/6.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 47.46/6.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 47.46/6.51      | ~ v1_funct_1(X0)
% 47.46/6.51      | ~ v1_funct_1(X3)
% 47.46/6.51      | k1_partfun1(X2,X1,X1,X2,X3,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 47.46/6.51      | k2_relset_1(X1,X2,X0) = X2
% 47.46/6.51      | k6_partfun1(X2) != k6_partfun1(sK0)
% 47.46/6.51      | sK0 != X2 ),
% 47.46/6.51      inference(resolution_lifted,[status(thm)],[c_23,c_28]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_407,plain,
% 47.46/6.51      ( ~ v1_funct_2(X0,X1,sK0)
% 47.46/6.51      | ~ v1_funct_2(X2,sK0,X1)
% 47.46/6.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 47.46/6.51      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 47.46/6.51      | ~ v1_funct_1(X0)
% 47.46/6.51      | ~ v1_funct_1(X2)
% 47.46/6.51      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 47.46/6.51      | k2_relset_1(X1,sK0,X0) = sK0
% 47.46/6.51      | k6_partfun1(sK0) != k6_partfun1(sK0) ),
% 47.46/6.51      inference(unflattening,[status(thm)],[c_406]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_492,plain,
% 47.46/6.51      ( ~ v1_funct_2(X0,X1,sK0)
% 47.46/6.51      | ~ v1_funct_2(X2,sK0,X1)
% 47.46/6.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 47.46/6.51      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 47.46/6.51      | ~ v1_funct_1(X0)
% 47.46/6.51      | ~ v1_funct_1(X2)
% 47.46/6.51      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 47.46/6.51      | k2_relset_1(X1,sK0,X0) = sK0 ),
% 47.46/6.51      inference(equality_resolution_simp,[status(thm)],[c_407]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_164291,plain,
% 47.46/6.51      ( ~ v1_funct_2(X0,X1,sK0)
% 47.46/6.51      | ~ v1_funct_2(X2,sK0,X1)
% 47.46/6.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 47.46/6.51      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 47.46/6.51      | ~ v1_funct_1(X0)
% 47.46/6.51      | ~ v1_funct_1(X2)
% 47.46/6.51      | ~ iProver_ARSWP_250
% 47.46/6.51      | k2_relset_1(X1,sK0,X0) = sK0
% 47.46/6.51      | arAF1_k1_partfun1_0_1_2(sK0,X1) != arAF1_k1_partfun1_0_1_2(sK0,sK1) ),
% 47.46/6.51      inference(arg_filter_abstr,[status(unp)],[c_492]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_164576,plain,
% 47.46/6.51      ( k2_relset_1(X0,sK0,X1) = sK0
% 47.46/6.51      | arAF1_k1_partfun1_0_1_2(sK0,X0) != arAF1_k1_partfun1_0_1_2(sK0,sK1)
% 47.46/6.51      | v1_funct_2(X1,X0,sK0) != iProver_top
% 47.46/6.51      | v1_funct_2(X2,sK0,X0) != iProver_top
% 47.46/6.51      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 47.46/6.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 47.46/6.51      | v1_funct_1(X2) != iProver_top
% 47.46/6.51      | v1_funct_1(X1) != iProver_top
% 47.46/6.51      | iProver_ARSWP_250 != iProver_top ),
% 47.46/6.51      inference(predicate_to_equality,[status(thm)],[c_164291]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_164965,plain,
% 47.46/6.51      ( k2_relset_1(sK1,sK0,X0) = sK0
% 47.46/6.51      | v1_funct_2(X1,sK0,sK1) != iProver_top
% 47.46/6.51      | v1_funct_2(X0,sK1,sK0) != iProver_top
% 47.46/6.51      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 47.46/6.51      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 47.46/6.51      | v1_funct_1(X0) != iProver_top
% 47.46/6.51      | v1_funct_1(X1) != iProver_top
% 47.46/6.51      | iProver_ARSWP_250 != iProver_top ),
% 47.46/6.51      inference(equality_resolution,[status(thm)],[c_164576]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_165099,plain,
% 47.46/6.51      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 47.46/6.51      | v1_funct_2(X0,sK0,sK1) != iProver_top
% 47.46/6.51      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 47.46/6.51      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 47.46/6.51      | v1_funct_1(X0) != iProver_top
% 47.46/6.51      | v1_funct_1(sK3) != iProver_top
% 47.46/6.51      | iProver_ARSWP_250 != iProver_top ),
% 47.46/6.51      inference(superposition,[status(thm)],[c_164592,c_164965]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_132332,plain,
% 47.46/6.51      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 47.46/6.51      inference(global_propositional_subsumption,
% 47.46/6.51                [status(thm)],
% 47.46/6.51                [c_132181,c_36,c_38,c_39,c_41,c_132183]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_132335,plain,
% 47.46/6.51      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
% 47.46/6.51      inference(demodulation,[status(thm)],[c_132332,c_132178]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_11,plain,
% 47.46/6.51      ( r2_relset_1(X0,X1,X2,X2)
% 47.46/6.51      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 47.46/6.51      inference(cnf_transformation,[],[f87]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_358,plain,
% 47.46/6.51      ( ~ v1_funct_2(X0,X1,X2)
% 47.46/6.51      | ~ v1_funct_2(X3,X2,X1)
% 47.46/6.51      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
% 47.46/6.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 47.46/6.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 47.46/6.51      | ~ v1_funct_1(X3)
% 47.46/6.51      | ~ v1_funct_1(X0)
% 47.46/6.51      | X2 != X6
% 47.46/6.51      | X2 != X5
% 47.46/6.51      | k1_partfun1(X2,X1,X1,X2,X3,X0) != X4
% 47.46/6.51      | k2_relset_1(X1,X2,X0) = X2
% 47.46/6.51      | k6_partfun1(X2) != X4 ),
% 47.46/6.51      inference(resolution_lifted,[status(thm)],[c_11,c_23]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_359,plain,
% 47.46/6.51      ( ~ v1_funct_2(X0,X1,X2)
% 47.46/6.51      | ~ v1_funct_2(X3,X2,X1)
% 47.46/6.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 47.46/6.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 47.46/6.51      | ~ m1_subset_1(k1_partfun1(X2,X1,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X2)))
% 47.46/6.51      | ~ v1_funct_1(X0)
% 47.46/6.51      | ~ v1_funct_1(X3)
% 47.46/6.51      | k2_relset_1(X1,X2,X0) = X2
% 47.46/6.51      | k6_partfun1(X2) != k1_partfun1(X2,X1,X1,X2,X3,X0) ),
% 47.46/6.51      inference(unflattening,[status(thm)],[c_358]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_381,plain,
% 47.46/6.51      ( ~ v1_funct_2(X0,X1,X2)
% 47.46/6.51      | ~ v1_funct_2(X3,X2,X1)
% 47.46/6.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 47.46/6.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 47.46/6.51      | ~ v1_funct_1(X0)
% 47.46/6.51      | ~ v1_funct_1(X3)
% 47.46/6.51      | k2_relset_1(X1,X2,X0) = X2
% 47.46/6.51      | k6_partfun1(X2) != k1_partfun1(X2,X1,X1,X2,X3,X0) ),
% 47.46/6.51      inference(forward_subsumption_resolution,
% 47.46/6.51                [status(thm)],
% 47.46/6.51                [c_359,c_19]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_131332,plain,
% 47.46/6.51      ( k2_relset_1(X0,X1,X2) = X1
% 47.46/6.51      | k6_partfun1(X1) != k1_partfun1(X1,X0,X0,X1,X3,X2)
% 47.46/6.51      | v1_funct_2(X2,X0,X1) != iProver_top
% 47.46/6.51      | v1_funct_2(X3,X1,X0) != iProver_top
% 47.46/6.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 47.46/6.51      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
% 47.46/6.51      | v1_funct_1(X3) != iProver_top
% 47.46/6.51      | v1_funct_1(X2) != iProver_top ),
% 47.46/6.51      inference(predicate_to_equality,[status(thm)],[c_381]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_132481,plain,
% 47.46/6.51      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 47.46/6.51      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 47.46/6.51      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 47.46/6.51      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 47.46/6.51      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 47.46/6.51      | v1_funct_1(sK3) != iProver_top
% 47.46/6.51      | v1_funct_1(sK2) != iProver_top ),
% 47.46/6.51      inference(superposition,[status(thm)],[c_132335,c_131332]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_131346,plain,
% 47.46/6.51      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 47.46/6.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 47.46/6.51      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_131606,plain,
% 47.46/6.51      ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 47.46/6.51      inference(superposition,[status(thm)],[c_131338,c_131346]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_132489,plain,
% 47.46/6.51      ( k2_relat_1(sK3) = sK0
% 47.46/6.51      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 47.46/6.51      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 47.46/6.51      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 47.46/6.51      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 47.46/6.51      | v1_funct_1(sK3) != iProver_top
% 47.46/6.51      | v1_funct_1(sK2) != iProver_top ),
% 47.46/6.51      inference(demodulation,[status(thm)],[c_132481,c_131606]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_34,negated_conjecture,
% 47.46/6.51      ( v1_funct_2(sK2,sK0,sK1) ),
% 47.46/6.51      inference(cnf_transformation,[],[f71]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_37,plain,
% 47.46/6.51      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 47.46/6.51      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_132185,plain,
% 47.46/6.51      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 47.46/6.51      | k5_relat_1(sK2,sK3) != k6_partfun1(sK0)
% 47.46/6.51      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 47.46/6.51      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 47.46/6.51      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 47.46/6.51      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 47.46/6.51      | v1_funct_1(sK3) != iProver_top
% 47.46/6.51      | v1_funct_1(sK2) != iProver_top ),
% 47.46/6.51      inference(superposition,[status(thm)],[c_132178,c_131332]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_132194,plain,
% 47.46/6.51      ( k5_relat_1(sK2,sK3) != k6_partfun1(sK0)
% 47.46/6.51      | k2_relat_1(sK3) = sK0
% 47.46/6.51      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 47.46/6.51      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 47.46/6.51      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 47.46/6.51      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 47.46/6.51      | v1_funct_1(sK3) != iProver_top
% 47.46/6.51      | v1_funct_1(sK2) != iProver_top ),
% 47.46/6.51      inference(demodulation,[status(thm)],[c_132185,c_131606]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_133538,plain,
% 47.46/6.51      ( k2_relat_1(sK3) = sK0 ),
% 47.46/6.51      inference(global_propositional_subsumption,
% 47.46/6.51                [status(thm)],
% 47.46/6.51                [c_132489,c_36,c_37,c_38,c_39,c_40,c_41,c_132181,
% 47.46/6.51                 c_132183,c_132194]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_133543,plain,
% 47.46/6.51      ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 47.46/6.51      inference(demodulation,[status(thm)],[c_133538,c_131606]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_165141,plain,
% 47.46/6.51      ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 47.46/6.51      inference(global_propositional_subsumption,
% 47.46/6.51                [status(thm)],
% 47.46/6.51                [c_165099,c_133543]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_165185,plain,
% 47.46/6.51      ( k2_relat_1(sK3) = sK0 ),
% 47.46/6.51      inference(light_normalisation,[status(thm)],[c_165179,c_165141]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_166672,plain,
% 47.46/6.51      ( k5_relat_1(sK2,sK2) != k6_partfun1(sK0)
% 47.46/6.51      | k2_funct_1(sK3) = sK2
% 47.46/6.51      | k1_relat_1(sK3) != sK1
% 47.46/6.51      | v1_funct_1(sK3) != iProver_top
% 47.46/6.51      | v1_funct_1(sK2) != iProver_top
% 47.46/6.51      | v2_funct_1(sK3) != iProver_top
% 47.46/6.51      | v1_relat_1(sK3) != iProver_top
% 47.46/6.51      | v1_relat_1(sK2) != iProver_top
% 47.46/6.51      | iProver_ARSWP_247 != iProver_top ),
% 47.46/6.51      inference(light_normalisation,
% 47.46/6.51                [status(thm)],
% 47.46/6.51                [c_166662,c_165182,c_165185]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_131348,plain,
% 47.46/6.51      ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 47.46/6.51      | k2_funct_1(X1) = X0
% 47.46/6.51      | k1_relat_1(X1) != k2_relat_1(X0)
% 47.46/6.51      | v1_funct_1(X0) != iProver_top
% 47.46/6.51      | v1_funct_1(X1) != iProver_top
% 47.46/6.51      | v2_funct_1(X1) != iProver_top
% 47.46/6.51      | v1_relat_1(X1) != iProver_top
% 47.46/6.51      | v1_relat_1(X0) != iProver_top ),
% 47.46/6.51      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_132336,plain,
% 47.46/6.51      ( k2_funct_1(sK3) = sK2
% 47.46/6.51      | k1_relat_1(sK3) != k2_relat_1(sK2)
% 47.46/6.51      | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
% 47.46/6.51      | v1_funct_1(sK3) != iProver_top
% 47.46/6.51      | v1_funct_1(sK2) != iProver_top
% 47.46/6.51      | v2_funct_1(sK3) != iProver_top
% 47.46/6.51      | v1_relat_1(sK3) != iProver_top
% 47.46/6.51      | v1_relat_1(sK2) != iProver_top ),
% 47.46/6.51      inference(superposition,[status(thm)],[c_132332,c_131348]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_131607,plain,
% 47.46/6.51      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 47.46/6.51      inference(superposition,[status(thm)],[c_131335,c_131346]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_131609,plain,
% 47.46/6.51      ( k2_relat_1(sK2) = sK1 ),
% 47.46/6.51      inference(light_normalisation,[status(thm)],[c_131607,c_29]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_131344,plain,
% 47.46/6.51      ( k1_relset_1(X0,X1,X2) = X0
% 47.46/6.51      | k1_xboole_0 = X1
% 47.46/6.51      | v1_funct_2(X2,X0,X1) != iProver_top
% 47.46/6.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 47.46/6.51      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_131733,plain,
% 47.46/6.51      ( k1_relset_1(sK1,sK0,sK3) = sK1
% 47.46/6.51      | sK0 = k1_xboole_0
% 47.46/6.51      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 47.46/6.51      inference(superposition,[status(thm)],[c_131338,c_131344]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_131347,plain,
% 47.46/6.51      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 47.46/6.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 47.46/6.51      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_131656,plain,
% 47.46/6.51      ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
% 47.46/6.51      inference(superposition,[status(thm)],[c_131338,c_131347]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_131744,plain,
% 47.46/6.51      ( k1_relat_1(sK3) = sK1
% 47.46/6.51      | sK0 = k1_xboole_0
% 47.46/6.51      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 47.46/6.51      inference(demodulation,[status(thm)],[c_131733,c_131656]) ).
% 47.46/6.51  
% 47.46/6.51  cnf(c_131837,plain,
% 47.46/6.51      ( k1_relat_1(sK3) = sK1 ),
% 47.46/6.51      inference(global_propositional_subsumption,
% 47.46/6.52                [status(thm)],
% 47.46/6.52                [c_131744,c_40,c_26,c_699,c_8547,c_23293]) ).
% 47.46/6.52  
% 47.46/6.52  cnf(c_132337,plain,
% 47.46/6.52      ( k2_funct_1(sK3) = sK2
% 47.46/6.52      | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
% 47.46/6.52      | sK1 != sK1
% 47.46/6.52      | v1_funct_1(sK3) != iProver_top
% 47.46/6.52      | v1_funct_1(sK2) != iProver_top
% 47.46/6.52      | v2_funct_1(sK3) != iProver_top
% 47.46/6.52      | v1_relat_1(sK3) != iProver_top
% 47.46/6.52      | v1_relat_1(sK2) != iProver_top ),
% 47.46/6.52      inference(light_normalisation,
% 47.46/6.52                [status(thm)],
% 47.46/6.52                [c_132336,c_131609,c_131837]) ).
% 47.46/6.52  
% 47.46/6.52  cnf(c_132338,plain,
% 47.46/6.52      ( k2_funct_1(sK3) = sK2
% 47.46/6.52      | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
% 47.46/6.52      | v1_funct_1(sK3) != iProver_top
% 47.46/6.52      | v1_funct_1(sK2) != iProver_top
% 47.46/6.52      | v2_funct_1(sK3) != iProver_top
% 47.46/6.52      | v1_relat_1(sK3) != iProver_top
% 47.46/6.52      | v1_relat_1(sK2) != iProver_top ),
% 47.46/6.52      inference(equality_resolution_simp,[status(thm)],[c_132337]) ).
% 47.46/6.52  
% 47.46/6.52  cnf(c_133458,plain,
% 47.46/6.52      ( k2_funct_1(sK3) = sK2
% 47.46/6.52      | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
% 47.46/6.52      | v2_funct_1(sK3) != iProver_top ),
% 47.46/6.52      inference(global_propositional_subsumption,
% 47.46/6.52                [status(thm)],
% 47.46/6.52                [c_132338,c_36,c_39,c_41,c_56737,c_56802,c_56831,c_56851]) ).
% 47.46/6.52  
% 47.46/6.52  cnf(c_133541,plain,
% 47.46/6.52      ( k2_funct_1(sK3) = sK2
% 47.46/6.52      | k6_partfun1(sK0) != k6_partfun1(sK0)
% 47.46/6.52      | v2_funct_1(sK3) != iProver_top ),
% 47.46/6.52      inference(demodulation,[status(thm)],[c_133538,c_133458]) ).
% 47.46/6.52  
% 47.46/6.52  cnf(c_133550,plain,
% 47.46/6.52      ( k2_funct_1(sK3) = sK2 | v2_funct_1(sK3) != iProver_top ),
% 47.46/6.52      inference(equality_resolution_simp,[status(thm)],[c_133541]) ).
% 47.46/6.52  
% 47.46/6.52  cnf(c_167499,plain,
% 47.46/6.52      ( v2_funct_1(sK3) != iProver_top | k2_funct_1(sK3) = sK2 ),
% 47.46/6.52      inference(global_propositional_subsumption,
% 47.46/6.52                [status(thm)],
% 47.46/6.52                [c_166672,c_133550]) ).
% 47.46/6.52  
% 47.46/6.52  cnf(c_167500,plain,
% 47.46/6.52      ( k2_funct_1(sK3) = sK2 | v2_funct_1(sK3) != iProver_top ),
% 47.46/6.52      inference(renaming,[status(thm)],[c_167499]) ).
% 47.46/6.52  
% 47.46/6.52  cnf(c_213728,plain,
% 47.46/6.52      ( k2_funct_1(sK3) = sK2 ),
% 47.46/6.52      inference(superposition,[status(thm)],[c_213724,c_167500]) ).
% 47.46/6.52  
% 47.46/6.52  cnf(c_213733,plain,
% 47.46/6.52      ( k5_relat_1(sK3,sK2) = k6_partfun1(sK1) ),
% 47.46/6.52      inference(light_normalisation,[status(thm)],[c_213726,c_213728]) ).
% 47.46/6.52  
% 47.46/6.52  cnf(c_214535,plain,
% 47.46/6.52      ( k2_funct_1(sK2) = sK3
% 47.46/6.52      | k1_relat_1(sK2) != k2_relat_1(sK3)
% 47.46/6.52      | k6_partfun1(k2_relat_1(sK2)) != k6_partfun1(sK1)
% 47.46/6.52      | v1_funct_1(sK3) != iProver_top
% 47.46/6.52      | v1_funct_1(sK2) != iProver_top
% 47.46/6.52      | v2_funct_1(sK2) != iProver_top
% 47.46/6.52      | v1_relat_1(sK3) != iProver_top
% 47.46/6.52      | v1_relat_1(sK2) != iProver_top ),
% 47.46/6.52      inference(superposition,[status(thm)],[c_213733,c_164603]) ).
% 47.46/6.52  
% 47.46/6.52  cnf(c_166040,plain,
% 47.46/6.52      ( k1_relset_1(sK0,sK1,sK2) = sK0
% 47.46/6.52      | sK1 = k1_xboole_0
% 47.46/6.52      | v1_funct_2(sK2,sK0,sK1) != iProver_top ),
% 47.46/6.52      inference(superposition,[status(thm)],[c_164589,c_164595]) ).
% 47.46/6.52  
% 47.46/6.52  cnf(c_165280,plain,
% 47.46/6.52      ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
% 47.46/6.52      inference(superposition,[status(thm)],[c_164589,c_164602]) ).
% 47.46/6.52  
% 47.46/6.52  cnf(c_166044,plain,
% 47.46/6.52      ( k1_relat_1(sK2) = sK0
% 47.46/6.52      | sK1 = k1_xboole_0
% 47.46/6.52      | v1_funct_2(sK2,sK0,sK1) != iProver_top ),
% 47.46/6.52      inference(demodulation,[status(thm)],[c_166040,c_165280]) ).
% 47.46/6.52  
% 47.46/6.52  cnf(c_25,negated_conjecture,
% 47.46/6.52      ( k1_xboole_0 != sK1 ),
% 47.46/6.52      inference(cnf_transformation,[],[f80]) ).
% 47.46/6.52  
% 47.46/6.52  cnf(c_8544,plain,
% 47.46/6.52      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 47.46/6.52      inference(instantiation,[status(thm)],[c_671]) ).
% 47.46/6.52  
% 47.46/6.52  cnf(c_8545,plain,
% 47.46/6.52      ( sK1 != k1_xboole_0
% 47.46/6.52      | k1_xboole_0 = sK1
% 47.46/6.52      | k1_xboole_0 != k1_xboole_0 ),
% 47.46/6.52      inference(instantiation,[status(thm)],[c_8544]) ).
% 47.46/6.52  
% 47.46/6.52  cnf(c_56624,plain,
% 47.46/6.52      ( k1_relset_1(X0,X1,X2) = X0
% 47.46/6.52      | k1_xboole_0 = X1
% 47.46/6.52      | v1_funct_2(X2,X0,X1) != iProver_top
% 47.46/6.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 47.46/6.52      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 47.46/6.52  
% 47.46/6.52  cnf(c_56925,plain,
% 47.46/6.52      ( k1_relset_1(sK0,sK1,sK2) = sK0
% 47.46/6.52      | sK1 = k1_xboole_0
% 47.46/6.52      | v1_funct_2(sK2,sK0,sK1) != iProver_top ),
% 47.46/6.52      inference(superposition,[status(thm)],[c_56618,c_56624]) ).
% 47.46/6.52  
% 47.46/6.52  cnf(c_56626,plain,
% 47.46/6.52      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 47.46/6.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 47.46/6.52      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 47.46/6.52  
% 47.46/6.52  cnf(c_56815,plain,
% 47.46/6.52      ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
% 47.46/6.52      inference(superposition,[status(thm)],[c_56618,c_56626]) ).
% 47.46/6.52  
% 47.46/6.52  cnf(c_56929,plain,
% 47.46/6.52      ( k1_relat_1(sK2) = sK0
% 47.46/6.52      | sK1 = k1_xboole_0
% 47.46/6.52      | v1_funct_2(sK2,sK0,sK1) != iProver_top ),
% 47.46/6.52      inference(demodulation,[status(thm)],[c_56925,c_56815]) ).
% 47.46/6.52  
% 47.46/6.52  cnf(c_172155,plain,
% 47.46/6.52      ( k1_relat_1(sK2) = sK0 ),
% 47.46/6.52      inference(global_propositional_subsumption,
% 47.46/6.52                [status(thm)],
% 47.46/6.52                [c_166044,c_37,c_25,c_699,c_8545,c_56929]) ).
% 47.46/6.52  
% 47.46/6.52  cnf(c_214536,plain,
% 47.46/6.52      ( k2_funct_1(sK2) = sK3
% 47.46/6.52      | k6_partfun1(sK1) != k6_partfun1(sK1)
% 47.46/6.52      | sK0 != sK0
% 47.46/6.52      | v1_funct_1(sK3) != iProver_top
% 47.46/6.52      | v1_funct_1(sK2) != iProver_top
% 47.46/6.52      | v2_funct_1(sK2) != iProver_top
% 47.46/6.52      | v1_relat_1(sK3) != iProver_top
% 47.46/6.52      | v1_relat_1(sK2) != iProver_top ),
% 47.46/6.52      inference(light_normalisation,
% 47.46/6.52                [status(thm)],
% 47.46/6.52                [c_214535,c_165182,c_165185,c_172155]) ).
% 47.46/6.52  
% 47.46/6.52  cnf(c_214537,plain,
% 47.46/6.52      ( k2_funct_1(sK2) = sK3
% 47.46/6.52      | v1_funct_1(sK3) != iProver_top
% 47.46/6.52      | v1_funct_1(sK2) != iProver_top
% 47.46/6.52      | v2_funct_1(sK2) != iProver_top
% 47.46/6.52      | v1_relat_1(sK3) != iProver_top
% 47.46/6.52      | v1_relat_1(sK2) != iProver_top ),
% 47.46/6.52      inference(equality_resolution_simp,[status(thm)],[c_214536]) ).
% 47.46/6.52  
% 47.46/6.52  cnf(c_24,negated_conjecture,
% 47.46/6.52      ( k2_funct_1(sK2) != sK3 ),
% 47.46/6.52      inference(cnf_transformation,[],[f81]) ).
% 47.46/6.52  
% 47.46/6.52  cnf(c_27,negated_conjecture,
% 47.46/6.52      ( v2_funct_1(sK2) ),
% 47.46/6.52      inference(cnf_transformation,[],[f78]) ).
% 47.46/6.52  
% 47.46/6.52  cnf(c_43,plain,
% 47.46/6.52      ( v2_funct_1(sK2) = iProver_top ),
% 47.46/6.52      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 47.46/6.52  
% 47.46/6.52  cnf(contradiction,plain,
% 47.46/6.52      ( $false ),
% 47.46/6.52      inference(minisat,
% 47.46/6.52                [status(thm)],
% 47.46/6.52                [c_214537,c_56851,c_56831,c_56802,c_56737,c_24,c_43,c_41,
% 47.46/6.52                 c_39,c_36]) ).
% 47.46/6.52  
% 47.46/6.52  
% 47.46/6.52  % SZS output end CNFRefutation for theBenchmark.p
% 47.46/6.52  
% 47.46/6.52  ------                               Statistics
% 47.46/6.52  
% 47.46/6.52  ------ Selected
% 47.46/6.52  
% 47.46/6.52  total_time:                             5.726
% 47.46/6.52  
%------------------------------------------------------------------------------
