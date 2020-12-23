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
% DateTime   : Thu Dec  3 12:03:29 EST 2020

% Result     : Theorem 7.82s
% Output     : CNFRefutation 7.82s
% Verified   : 
% Statistics : Number of formulae       :  169 (1068 expanded)
%              Number of clauses        :   98 ( 324 expanded)
%              Number of leaves         :   20 ( 271 expanded)
%              Depth                    :   21
%              Number of atoms          :  657 (8739 expanded)
%              Number of equality atoms :  317 (3228 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f14,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f80,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f49,f66])).

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

fof(f70,plain,(
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

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f74,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f44])).

fof(f73,plain,(
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

fof(f56,plain,(
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

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f72,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f77,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f44])).

fof(f3,axiom,(
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
    inference(ennf_transformation,[],[f3])).

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

fof(f48,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X0)
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f71,plain,(
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

fof(f65,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f35])).

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

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f75,plain,(
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

fof(f64,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f68,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f44])).

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

fof(f63,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
              & k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f50,f66])).

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

fof(f67,plain,(
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

fof(f69,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f51,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f79,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_4,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1138,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1119,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1134,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1965,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1119,c_1134])).

cnf(c_27,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1966,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_1965,c_27])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1122,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1128,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2813,plain,
    ( k1_relset_1(sK1,sK0,sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1122,c_1128])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1135,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2100,plain,
    ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1122,c_1135])).

cnf(c_2816,plain,
    ( k1_relat_1(sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2813,c_2100])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_38,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_24,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_634,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_661,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_634])).

cnf(c_635,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1220,plain,
    ( sK0 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_635])).

cnf(c_1221,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1220])).

cnf(c_5865,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2816,c_38,c_24,c_661,c_1221])).

cnf(c_2,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | v2_funct_1(X1)
    | ~ v2_funct_1(k5_relat_1(X0,X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X1) != k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1140,plain,
    ( k1_relat_1(X0) != k2_relat_1(X1)
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) = iProver_top
    | v2_funct_1(k5_relat_1(X1,X0)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_5868,plain,
    ( k2_relat_1(X0) != sK1
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5865,c_1140])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_37,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1142,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2105,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1122,c_1142])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_2267,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2268,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2267])).

cnf(c_21777,plain,
    ( v1_relat_1(X0) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
    | k2_relat_1(X0) != sK1
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5868,c_37,c_2105,c_2268])).

cnf(c_21778,plain,
    ( k2_relat_1(X0) != sK1
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_21777])).

cnf(c_21783,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1966,c_21778])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1124,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2626,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1122,c_1124])).

cnf(c_2822,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2626,c_37])).

cnf(c_2823,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_2822])).

cnf(c_2830,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1119,c_2823])).

cnf(c_10,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_26,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_370,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_26])).

cnf(c_371,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_370])).

cnf(c_19,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_379,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_371,c_19])).

cnf(c_1115,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_379])).

cnf(c_33,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1222,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1862,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1115,c_33,c_31,c_30,c_28,c_379,c_1222])).

cnf(c_2831,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2830,c_1862])).

cnf(c_34,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_3188,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2831,c_34])).

cnf(c_21785,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_21783,c_3188])).

cnf(c_1141,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2106,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1119,c_1142])).

cnf(c_2376,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1141,c_2106])).

cnf(c_21812,plain,
    ( v2_funct_1(sK3) = iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_21785,c_34,c_2376])).

cnf(c_21813,plain,
    ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_21812])).

cnf(c_21816,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1138,c_21813])).

cnf(c_5,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k1_relat_1(X1) != k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1137,plain,
    ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k1_relat_1(X1) != k2_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v2_funct_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4105,plain,
    ( k2_funct_1(sK3) = sK2
    | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3188,c_1137])).

cnf(c_1964,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1122,c_1134])).

cnf(c_21,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X3,X1,X0)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_383,plain,
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
    inference(resolution_lifted,[status(thm)],[c_21,c_26])).

cnf(c_384,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0
    | k6_partfun1(sK0) != k6_partfun1(sK0) ),
    inference(unflattening,[status(thm)],[c_383])).

cnf(c_467,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_384])).

cnf(c_1114,plain,
    ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X0,sK0,X2) = sK0
    | v1_funct_2(X2,X0,sK0) != iProver_top
    | v1_funct_2(X1,sK0,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_467])).

cnf(c_1596,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1114])).

cnf(c_32,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_35,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_36,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_39,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_1869,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1596,c_34,c_35,c_36,c_37,c_38,c_39])).

cnf(c_1967,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_1964,c_1869])).

cnf(c_4106,plain,
    ( k2_funct_1(sK3) = sK2
    | k6_partfun1(sK0) != k6_partfun1(sK0)
    | k1_relat_1(sK3) != sK1
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4105,c_1966,c_1967])).

cnf(c_4107,plain,
    ( k2_funct_1(sK3) = sK2
    | k1_relat_1(sK3) != sK1
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4106])).

cnf(c_4909,plain,
    ( k2_funct_1(sK3) = sK2
    | v2_funct_1(sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4107,c_34,c_37,c_38,c_24,c_661,c_1221,c_2105,c_2268,c_2376,c_2816])).

cnf(c_22087,plain,
    ( k2_funct_1(sK3) = sK2 ),
    inference(superposition,[status(thm)],[c_21816,c_4909])).

cnf(c_1120,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_6,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1136,plain,
    ( k2_funct_1(k2_funct_1(X0)) = X0
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2148,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = sK3
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1120,c_1136])).

cnf(c_2438,plain,
    ( v2_funct_1(sK3) != iProver_top
    | k2_funct_1(k2_funct_1(sK3)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2148,c_2105,c_2268])).

cnf(c_2439,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = sK3
    | v2_funct_1(sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_2438])).

cnf(c_22088,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = sK3 ),
    inference(superposition,[status(thm)],[c_21816,c_2439])).

cnf(c_22089,plain,
    ( k2_funct_1(sK2) = sK3 ),
    inference(demodulation,[status(thm)],[c_22087,c_22088])).

cnf(c_22,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f79])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_22089,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:42:47 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 7.82/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.82/1.49  
% 7.82/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.82/1.49  
% 7.82/1.49  ------  iProver source info
% 7.82/1.49  
% 7.82/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.82/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.82/1.49  git: non_committed_changes: false
% 7.82/1.49  git: last_make_outside_of_git: false
% 7.82/1.49  
% 7.82/1.49  ------ 
% 7.82/1.49  
% 7.82/1.49  ------ Input Options
% 7.82/1.49  
% 7.82/1.49  --out_options                           all
% 7.82/1.49  --tptp_safe_out                         true
% 7.82/1.49  --problem_path                          ""
% 7.82/1.49  --include_path                          ""
% 7.82/1.49  --clausifier                            res/vclausify_rel
% 7.82/1.49  --clausifier_options                    ""
% 7.82/1.49  --stdin                                 false
% 7.82/1.49  --stats_out                             all
% 7.82/1.49  
% 7.82/1.49  ------ General Options
% 7.82/1.49  
% 7.82/1.49  --fof                                   false
% 7.82/1.49  --time_out_real                         305.
% 7.82/1.49  --time_out_virtual                      -1.
% 7.82/1.49  --symbol_type_check                     false
% 7.82/1.49  --clausify_out                          false
% 7.82/1.49  --sig_cnt_out                           false
% 7.82/1.49  --trig_cnt_out                          false
% 7.82/1.49  --trig_cnt_out_tolerance                1.
% 7.82/1.49  --trig_cnt_out_sk_spl                   false
% 7.82/1.49  --abstr_cl_out                          false
% 7.82/1.49  
% 7.82/1.49  ------ Global Options
% 7.82/1.49  
% 7.82/1.49  --schedule                              default
% 7.82/1.49  --add_important_lit                     false
% 7.82/1.49  --prop_solver_per_cl                    1000
% 7.82/1.49  --min_unsat_core                        false
% 7.82/1.49  --soft_assumptions                      false
% 7.82/1.49  --soft_lemma_size                       3
% 7.82/1.49  --prop_impl_unit_size                   0
% 7.82/1.49  --prop_impl_unit                        []
% 7.82/1.49  --share_sel_clauses                     true
% 7.82/1.49  --reset_solvers                         false
% 7.82/1.49  --bc_imp_inh                            [conj_cone]
% 7.82/1.49  --conj_cone_tolerance                   3.
% 7.82/1.49  --extra_neg_conj                        none
% 7.82/1.49  --large_theory_mode                     true
% 7.82/1.49  --prolific_symb_bound                   200
% 7.82/1.49  --lt_threshold                          2000
% 7.82/1.49  --clause_weak_htbl                      true
% 7.82/1.49  --gc_record_bc_elim                     false
% 7.82/1.49  
% 7.82/1.49  ------ Preprocessing Options
% 7.82/1.49  
% 7.82/1.49  --preprocessing_flag                    true
% 7.82/1.49  --time_out_prep_mult                    0.1
% 7.82/1.49  --splitting_mode                        input
% 7.82/1.49  --splitting_grd                         true
% 7.82/1.49  --splitting_cvd                         false
% 7.82/1.49  --splitting_cvd_svl                     false
% 7.82/1.49  --splitting_nvd                         32
% 7.82/1.49  --sub_typing                            true
% 7.82/1.49  --prep_gs_sim                           true
% 7.82/1.49  --prep_unflatten                        true
% 7.82/1.49  --prep_res_sim                          true
% 7.82/1.49  --prep_upred                            true
% 7.82/1.49  --prep_sem_filter                       exhaustive
% 7.82/1.49  --prep_sem_filter_out                   false
% 7.82/1.49  --pred_elim                             true
% 7.82/1.49  --res_sim_input                         true
% 7.82/1.49  --eq_ax_congr_red                       true
% 7.82/1.49  --pure_diseq_elim                       true
% 7.82/1.49  --brand_transform                       false
% 7.82/1.49  --non_eq_to_eq                          false
% 7.82/1.49  --prep_def_merge                        true
% 7.82/1.49  --prep_def_merge_prop_impl              false
% 7.82/1.49  --prep_def_merge_mbd                    true
% 7.82/1.49  --prep_def_merge_tr_red                 false
% 7.82/1.49  --prep_def_merge_tr_cl                  false
% 7.82/1.49  --smt_preprocessing                     true
% 7.82/1.49  --smt_ac_axioms                         fast
% 7.82/1.49  --preprocessed_out                      false
% 7.82/1.49  --preprocessed_stats                    false
% 7.82/1.49  
% 7.82/1.49  ------ Abstraction refinement Options
% 7.82/1.49  
% 7.82/1.49  --abstr_ref                             []
% 7.82/1.49  --abstr_ref_prep                        false
% 7.82/1.49  --abstr_ref_until_sat                   false
% 7.82/1.49  --abstr_ref_sig_restrict                funpre
% 7.82/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.82/1.49  --abstr_ref_under                       []
% 7.82/1.49  
% 7.82/1.49  ------ SAT Options
% 7.82/1.49  
% 7.82/1.49  --sat_mode                              false
% 7.82/1.49  --sat_fm_restart_options                ""
% 7.82/1.49  --sat_gr_def                            false
% 7.82/1.49  --sat_epr_types                         true
% 7.82/1.49  --sat_non_cyclic_types                  false
% 7.82/1.49  --sat_finite_models                     false
% 7.82/1.49  --sat_fm_lemmas                         false
% 7.82/1.49  --sat_fm_prep                           false
% 7.82/1.49  --sat_fm_uc_incr                        true
% 7.82/1.49  --sat_out_model                         small
% 7.82/1.49  --sat_out_clauses                       false
% 7.82/1.49  
% 7.82/1.49  ------ QBF Options
% 7.82/1.49  
% 7.82/1.49  --qbf_mode                              false
% 7.82/1.49  --qbf_elim_univ                         false
% 7.82/1.49  --qbf_dom_inst                          none
% 7.82/1.49  --qbf_dom_pre_inst                      false
% 7.82/1.49  --qbf_sk_in                             false
% 7.82/1.49  --qbf_pred_elim                         true
% 7.82/1.49  --qbf_split                             512
% 7.82/1.49  
% 7.82/1.49  ------ BMC1 Options
% 7.82/1.49  
% 7.82/1.49  --bmc1_incremental                      false
% 7.82/1.49  --bmc1_axioms                           reachable_all
% 7.82/1.49  --bmc1_min_bound                        0
% 7.82/1.49  --bmc1_max_bound                        -1
% 7.82/1.49  --bmc1_max_bound_default                -1
% 7.82/1.49  --bmc1_symbol_reachability              true
% 7.82/1.49  --bmc1_property_lemmas                  false
% 7.82/1.49  --bmc1_k_induction                      false
% 7.82/1.49  --bmc1_non_equiv_states                 false
% 7.82/1.49  --bmc1_deadlock                         false
% 7.82/1.49  --bmc1_ucm                              false
% 7.82/1.49  --bmc1_add_unsat_core                   none
% 7.82/1.49  --bmc1_unsat_core_children              false
% 7.82/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.82/1.49  --bmc1_out_stat                         full
% 7.82/1.49  --bmc1_ground_init                      false
% 7.82/1.49  --bmc1_pre_inst_next_state              false
% 7.82/1.49  --bmc1_pre_inst_state                   false
% 7.82/1.49  --bmc1_pre_inst_reach_state             false
% 7.82/1.49  --bmc1_out_unsat_core                   false
% 7.82/1.49  --bmc1_aig_witness_out                  false
% 7.82/1.49  --bmc1_verbose                          false
% 7.82/1.49  --bmc1_dump_clauses_tptp                false
% 7.82/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.82/1.49  --bmc1_dump_file                        -
% 7.82/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.82/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.82/1.49  --bmc1_ucm_extend_mode                  1
% 7.82/1.49  --bmc1_ucm_init_mode                    2
% 7.82/1.49  --bmc1_ucm_cone_mode                    none
% 7.82/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.82/1.49  --bmc1_ucm_relax_model                  4
% 7.82/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.82/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.82/1.49  --bmc1_ucm_layered_model                none
% 7.82/1.49  --bmc1_ucm_max_lemma_size               10
% 7.82/1.49  
% 7.82/1.49  ------ AIG Options
% 7.82/1.49  
% 7.82/1.49  --aig_mode                              false
% 7.82/1.49  
% 7.82/1.49  ------ Instantiation Options
% 7.82/1.49  
% 7.82/1.49  --instantiation_flag                    true
% 7.82/1.49  --inst_sos_flag                         true
% 7.82/1.49  --inst_sos_phase                        true
% 7.82/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.82/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.82/1.49  --inst_lit_sel_side                     num_symb
% 7.82/1.49  --inst_solver_per_active                1400
% 7.82/1.49  --inst_solver_calls_frac                1.
% 7.82/1.49  --inst_passive_queue_type               priority_queues
% 7.82/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.82/1.49  --inst_passive_queues_freq              [25;2]
% 7.82/1.49  --inst_dismatching                      true
% 7.82/1.49  --inst_eager_unprocessed_to_passive     true
% 7.82/1.49  --inst_prop_sim_given                   true
% 7.82/1.49  --inst_prop_sim_new                     false
% 7.82/1.49  --inst_subs_new                         false
% 7.82/1.49  --inst_eq_res_simp                      false
% 7.82/1.49  --inst_subs_given                       false
% 7.82/1.49  --inst_orphan_elimination               true
% 7.82/1.49  --inst_learning_loop_flag               true
% 7.82/1.49  --inst_learning_start                   3000
% 7.82/1.49  --inst_learning_factor                  2
% 7.82/1.49  --inst_start_prop_sim_after_learn       3
% 7.82/1.49  --inst_sel_renew                        solver
% 7.82/1.49  --inst_lit_activity_flag                true
% 7.82/1.49  --inst_restr_to_given                   false
% 7.82/1.49  --inst_activity_threshold               500
% 7.82/1.49  --inst_out_proof                        true
% 7.82/1.49  
% 7.82/1.49  ------ Resolution Options
% 7.82/1.49  
% 7.82/1.49  --resolution_flag                       true
% 7.82/1.49  --res_lit_sel                           adaptive
% 7.82/1.49  --res_lit_sel_side                      none
% 7.82/1.49  --res_ordering                          kbo
% 7.82/1.49  --res_to_prop_solver                    active
% 7.82/1.49  --res_prop_simpl_new                    false
% 7.82/1.49  --res_prop_simpl_given                  true
% 7.82/1.49  --res_passive_queue_type                priority_queues
% 7.82/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.82/1.49  --res_passive_queues_freq               [15;5]
% 7.82/1.49  --res_forward_subs                      full
% 7.82/1.49  --res_backward_subs                     full
% 7.82/1.49  --res_forward_subs_resolution           true
% 7.82/1.49  --res_backward_subs_resolution          true
% 7.82/1.49  --res_orphan_elimination                true
% 7.82/1.49  --res_time_limit                        2.
% 7.82/1.49  --res_out_proof                         true
% 7.82/1.49  
% 7.82/1.49  ------ Superposition Options
% 7.82/1.49  
% 7.82/1.49  --superposition_flag                    true
% 7.82/1.49  --sup_passive_queue_type                priority_queues
% 7.82/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.82/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.82/1.49  --demod_completeness_check              fast
% 7.82/1.49  --demod_use_ground                      true
% 7.82/1.49  --sup_to_prop_solver                    passive
% 7.82/1.49  --sup_prop_simpl_new                    true
% 7.82/1.49  --sup_prop_simpl_given                  true
% 7.82/1.49  --sup_fun_splitting                     true
% 7.82/1.49  --sup_smt_interval                      50000
% 7.82/1.49  
% 7.82/1.49  ------ Superposition Simplification Setup
% 7.82/1.49  
% 7.82/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.82/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.82/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.82/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.82/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.82/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.82/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.82/1.49  --sup_immed_triv                        [TrivRules]
% 7.82/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.82/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.82/1.49  --sup_immed_bw_main                     []
% 7.82/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.82/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.82/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.82/1.49  --sup_input_bw                          []
% 7.82/1.49  
% 7.82/1.49  ------ Combination Options
% 7.82/1.49  
% 7.82/1.49  --comb_res_mult                         3
% 7.82/1.49  --comb_sup_mult                         2
% 7.82/1.49  --comb_inst_mult                        10
% 7.82/1.49  
% 7.82/1.49  ------ Debug Options
% 7.82/1.49  
% 7.82/1.49  --dbg_backtrace                         false
% 7.82/1.49  --dbg_dump_prop_clauses                 false
% 7.82/1.49  --dbg_dump_prop_clauses_file            -
% 7.82/1.49  --dbg_out_stat                          false
% 7.82/1.49  ------ Parsing...
% 7.82/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.82/1.49  
% 7.82/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.82/1.49  
% 7.82/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.82/1.49  
% 7.82/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.82/1.49  ------ Proving...
% 7.82/1.49  ------ Problem Properties 
% 7.82/1.49  
% 7.82/1.49  
% 7.82/1.49  clauses                                 33
% 7.82/1.49  conjectures                             11
% 7.82/1.49  EPR                                     7
% 7.82/1.49  Horn                                    29
% 7.82/1.49  unary                                   14
% 7.82/1.49  binary                                  3
% 7.82/1.49  lits                                    101
% 7.82/1.49  lits eq                                 27
% 7.82/1.49  fd_pure                                 0
% 7.82/1.49  fd_pseudo                               0
% 7.82/1.49  fd_cond                                 3
% 7.82/1.49  fd_pseudo_cond                          1
% 7.82/1.49  AC symbols                              0
% 7.82/1.49  
% 7.82/1.49  ------ Schedule dynamic 5 is on 
% 7.82/1.49  
% 7.82/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.82/1.49  
% 7.82/1.49  
% 7.82/1.49  ------ 
% 7.82/1.49  Current options:
% 7.82/1.49  ------ 
% 7.82/1.49  
% 7.82/1.49  ------ Input Options
% 7.82/1.49  
% 7.82/1.49  --out_options                           all
% 7.82/1.49  --tptp_safe_out                         true
% 7.82/1.49  --problem_path                          ""
% 7.82/1.49  --include_path                          ""
% 7.82/1.49  --clausifier                            res/vclausify_rel
% 7.82/1.49  --clausifier_options                    ""
% 7.82/1.49  --stdin                                 false
% 7.82/1.49  --stats_out                             all
% 7.82/1.49  
% 7.82/1.49  ------ General Options
% 7.82/1.49  
% 7.82/1.49  --fof                                   false
% 7.82/1.49  --time_out_real                         305.
% 7.82/1.49  --time_out_virtual                      -1.
% 7.82/1.49  --symbol_type_check                     false
% 7.82/1.49  --clausify_out                          false
% 7.82/1.49  --sig_cnt_out                           false
% 7.82/1.49  --trig_cnt_out                          false
% 7.82/1.49  --trig_cnt_out_tolerance                1.
% 7.82/1.49  --trig_cnt_out_sk_spl                   false
% 7.82/1.49  --abstr_cl_out                          false
% 7.82/1.49  
% 7.82/1.49  ------ Global Options
% 7.82/1.49  
% 7.82/1.49  --schedule                              default
% 7.82/1.49  --add_important_lit                     false
% 7.82/1.49  --prop_solver_per_cl                    1000
% 7.82/1.49  --min_unsat_core                        false
% 7.82/1.49  --soft_assumptions                      false
% 7.82/1.49  --soft_lemma_size                       3
% 7.82/1.49  --prop_impl_unit_size                   0
% 7.82/1.49  --prop_impl_unit                        []
% 7.82/1.49  --share_sel_clauses                     true
% 7.82/1.49  --reset_solvers                         false
% 7.82/1.49  --bc_imp_inh                            [conj_cone]
% 7.82/1.49  --conj_cone_tolerance                   3.
% 7.82/1.49  --extra_neg_conj                        none
% 7.82/1.49  --large_theory_mode                     true
% 7.82/1.49  --prolific_symb_bound                   200
% 7.82/1.49  --lt_threshold                          2000
% 7.82/1.49  --clause_weak_htbl                      true
% 7.82/1.49  --gc_record_bc_elim                     false
% 7.82/1.49  
% 7.82/1.49  ------ Preprocessing Options
% 7.82/1.49  
% 7.82/1.49  --preprocessing_flag                    true
% 7.82/1.49  --time_out_prep_mult                    0.1
% 7.82/1.49  --splitting_mode                        input
% 7.82/1.49  --splitting_grd                         true
% 7.82/1.49  --splitting_cvd                         false
% 7.82/1.49  --splitting_cvd_svl                     false
% 7.82/1.49  --splitting_nvd                         32
% 7.82/1.49  --sub_typing                            true
% 7.82/1.49  --prep_gs_sim                           true
% 7.82/1.49  --prep_unflatten                        true
% 7.82/1.49  --prep_res_sim                          true
% 7.82/1.49  --prep_upred                            true
% 7.82/1.49  --prep_sem_filter                       exhaustive
% 7.82/1.49  --prep_sem_filter_out                   false
% 7.82/1.49  --pred_elim                             true
% 7.82/1.49  --res_sim_input                         true
% 7.82/1.49  --eq_ax_congr_red                       true
% 7.82/1.49  --pure_diseq_elim                       true
% 7.82/1.49  --brand_transform                       false
% 7.82/1.49  --non_eq_to_eq                          false
% 7.82/1.49  --prep_def_merge                        true
% 7.82/1.49  --prep_def_merge_prop_impl              false
% 7.82/1.49  --prep_def_merge_mbd                    true
% 7.82/1.49  --prep_def_merge_tr_red                 false
% 7.82/1.49  --prep_def_merge_tr_cl                  false
% 7.82/1.49  --smt_preprocessing                     true
% 7.82/1.49  --smt_ac_axioms                         fast
% 7.82/1.49  --preprocessed_out                      false
% 7.82/1.49  --preprocessed_stats                    false
% 7.82/1.49  
% 7.82/1.49  ------ Abstraction refinement Options
% 7.82/1.49  
% 7.82/1.49  --abstr_ref                             []
% 7.82/1.49  --abstr_ref_prep                        false
% 7.82/1.49  --abstr_ref_until_sat                   false
% 7.82/1.49  --abstr_ref_sig_restrict                funpre
% 7.82/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.82/1.49  --abstr_ref_under                       []
% 7.82/1.49  
% 7.82/1.49  ------ SAT Options
% 7.82/1.49  
% 7.82/1.49  --sat_mode                              false
% 7.82/1.49  --sat_fm_restart_options                ""
% 7.82/1.49  --sat_gr_def                            false
% 7.82/1.49  --sat_epr_types                         true
% 7.82/1.49  --sat_non_cyclic_types                  false
% 7.82/1.50  --sat_finite_models                     false
% 7.82/1.50  --sat_fm_lemmas                         false
% 7.82/1.50  --sat_fm_prep                           false
% 7.82/1.50  --sat_fm_uc_incr                        true
% 7.82/1.50  --sat_out_model                         small
% 7.82/1.50  --sat_out_clauses                       false
% 7.82/1.50  
% 7.82/1.50  ------ QBF Options
% 7.82/1.50  
% 7.82/1.50  --qbf_mode                              false
% 7.82/1.50  --qbf_elim_univ                         false
% 7.82/1.50  --qbf_dom_inst                          none
% 7.82/1.50  --qbf_dom_pre_inst                      false
% 7.82/1.50  --qbf_sk_in                             false
% 7.82/1.50  --qbf_pred_elim                         true
% 7.82/1.50  --qbf_split                             512
% 7.82/1.50  
% 7.82/1.50  ------ BMC1 Options
% 7.82/1.50  
% 7.82/1.50  --bmc1_incremental                      false
% 7.82/1.50  --bmc1_axioms                           reachable_all
% 7.82/1.50  --bmc1_min_bound                        0
% 7.82/1.50  --bmc1_max_bound                        -1
% 7.82/1.50  --bmc1_max_bound_default                -1
% 7.82/1.50  --bmc1_symbol_reachability              true
% 7.82/1.50  --bmc1_property_lemmas                  false
% 7.82/1.50  --bmc1_k_induction                      false
% 7.82/1.50  --bmc1_non_equiv_states                 false
% 7.82/1.50  --bmc1_deadlock                         false
% 7.82/1.50  --bmc1_ucm                              false
% 7.82/1.50  --bmc1_add_unsat_core                   none
% 7.82/1.50  --bmc1_unsat_core_children              false
% 7.82/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.82/1.50  --bmc1_out_stat                         full
% 7.82/1.50  --bmc1_ground_init                      false
% 7.82/1.50  --bmc1_pre_inst_next_state              false
% 7.82/1.50  --bmc1_pre_inst_state                   false
% 7.82/1.50  --bmc1_pre_inst_reach_state             false
% 7.82/1.50  --bmc1_out_unsat_core                   false
% 7.82/1.50  --bmc1_aig_witness_out                  false
% 7.82/1.50  --bmc1_verbose                          false
% 7.82/1.50  --bmc1_dump_clauses_tptp                false
% 7.82/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.82/1.50  --bmc1_dump_file                        -
% 7.82/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.82/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.82/1.50  --bmc1_ucm_extend_mode                  1
% 7.82/1.50  --bmc1_ucm_init_mode                    2
% 7.82/1.50  --bmc1_ucm_cone_mode                    none
% 7.82/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.82/1.50  --bmc1_ucm_relax_model                  4
% 7.82/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.82/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.82/1.50  --bmc1_ucm_layered_model                none
% 7.82/1.50  --bmc1_ucm_max_lemma_size               10
% 7.82/1.50  
% 7.82/1.50  ------ AIG Options
% 7.82/1.50  
% 7.82/1.50  --aig_mode                              false
% 7.82/1.50  
% 7.82/1.50  ------ Instantiation Options
% 7.82/1.50  
% 7.82/1.50  --instantiation_flag                    true
% 7.82/1.50  --inst_sos_flag                         true
% 7.82/1.50  --inst_sos_phase                        true
% 7.82/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.82/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.82/1.50  --inst_lit_sel_side                     none
% 7.82/1.50  --inst_solver_per_active                1400
% 7.82/1.50  --inst_solver_calls_frac                1.
% 7.82/1.50  --inst_passive_queue_type               priority_queues
% 7.82/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.82/1.50  --inst_passive_queues_freq              [25;2]
% 7.82/1.50  --inst_dismatching                      true
% 7.82/1.50  --inst_eager_unprocessed_to_passive     true
% 7.82/1.50  --inst_prop_sim_given                   true
% 7.82/1.50  --inst_prop_sim_new                     false
% 7.82/1.50  --inst_subs_new                         false
% 7.82/1.50  --inst_eq_res_simp                      false
% 7.82/1.50  --inst_subs_given                       false
% 7.82/1.50  --inst_orphan_elimination               true
% 7.82/1.50  --inst_learning_loop_flag               true
% 7.82/1.50  --inst_learning_start                   3000
% 7.82/1.50  --inst_learning_factor                  2
% 7.82/1.50  --inst_start_prop_sim_after_learn       3
% 7.82/1.50  --inst_sel_renew                        solver
% 7.82/1.50  --inst_lit_activity_flag                true
% 7.82/1.50  --inst_restr_to_given                   false
% 7.82/1.50  --inst_activity_threshold               500
% 7.82/1.50  --inst_out_proof                        true
% 7.82/1.50  
% 7.82/1.50  ------ Resolution Options
% 7.82/1.50  
% 7.82/1.50  --resolution_flag                       false
% 7.82/1.50  --res_lit_sel                           adaptive
% 7.82/1.50  --res_lit_sel_side                      none
% 7.82/1.50  --res_ordering                          kbo
% 7.82/1.50  --res_to_prop_solver                    active
% 7.82/1.50  --res_prop_simpl_new                    false
% 7.82/1.50  --res_prop_simpl_given                  true
% 7.82/1.50  --res_passive_queue_type                priority_queues
% 7.82/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.82/1.50  --res_passive_queues_freq               [15;5]
% 7.82/1.50  --res_forward_subs                      full
% 7.82/1.50  --res_backward_subs                     full
% 7.82/1.50  --res_forward_subs_resolution           true
% 7.82/1.50  --res_backward_subs_resolution          true
% 7.82/1.50  --res_orphan_elimination                true
% 7.82/1.50  --res_time_limit                        2.
% 7.82/1.50  --res_out_proof                         true
% 7.82/1.50  
% 7.82/1.50  ------ Superposition Options
% 7.82/1.50  
% 7.82/1.50  --superposition_flag                    true
% 7.82/1.50  --sup_passive_queue_type                priority_queues
% 7.82/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.82/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.82/1.50  --demod_completeness_check              fast
% 7.82/1.50  --demod_use_ground                      true
% 7.82/1.50  --sup_to_prop_solver                    passive
% 7.82/1.50  --sup_prop_simpl_new                    true
% 7.82/1.50  --sup_prop_simpl_given                  true
% 7.82/1.50  --sup_fun_splitting                     true
% 7.82/1.50  --sup_smt_interval                      50000
% 7.82/1.50  
% 7.82/1.50  ------ Superposition Simplification Setup
% 7.82/1.50  
% 7.82/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.82/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.82/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.82/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.82/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.82/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.82/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.82/1.50  --sup_immed_triv                        [TrivRules]
% 7.82/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.82/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.82/1.50  --sup_immed_bw_main                     []
% 7.82/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.82/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.82/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.82/1.50  --sup_input_bw                          []
% 7.82/1.50  
% 7.82/1.50  ------ Combination Options
% 7.82/1.50  
% 7.82/1.50  --comb_res_mult                         3
% 7.82/1.50  --comb_sup_mult                         2
% 7.82/1.50  --comb_inst_mult                        10
% 7.82/1.50  
% 7.82/1.50  ------ Debug Options
% 7.82/1.50  
% 7.82/1.50  --dbg_backtrace                         false
% 7.82/1.50  --dbg_dump_prop_clauses                 false
% 7.82/1.50  --dbg_dump_prop_clauses_file            -
% 7.82/1.50  --dbg_out_stat                          false
% 7.82/1.50  
% 7.82/1.50  
% 7.82/1.50  
% 7.82/1.50  
% 7.82/1.50  ------ Proving...
% 7.82/1.50  
% 7.82/1.50  
% 7.82/1.50  % SZS status Theorem for theBenchmark.p
% 7.82/1.50  
% 7.82/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.82/1.50  
% 7.82/1.50  fof(f4,axiom,(
% 7.82/1.50    ! [X0] : v2_funct_1(k6_relat_1(X0))),
% 7.82/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.50  
% 7.82/1.50  fof(f49,plain,(
% 7.82/1.50    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 7.82/1.50    inference(cnf_transformation,[],[f4])).
% 7.82/1.50  
% 7.82/1.50  fof(f14,axiom,(
% 7.82/1.50    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 7.82/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.50  
% 7.82/1.50  fof(f66,plain,(
% 7.82/1.50    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 7.82/1.50    inference(cnf_transformation,[],[f14])).
% 7.82/1.50  
% 7.82/1.50  fof(f80,plain,(
% 7.82/1.50    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 7.82/1.50    inference(definition_unfolding,[],[f49,f66])).
% 7.82/1.50  
% 7.82/1.50  fof(f16,conjecture,(
% 7.82/1.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 7.82/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.50  
% 7.82/1.50  fof(f17,negated_conjecture,(
% 7.82/1.50    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 7.82/1.50    inference(negated_conjecture,[],[f16])).
% 7.82/1.50  
% 7.82/1.50  fof(f38,plain,(
% 7.82/1.50    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 7.82/1.50    inference(ennf_transformation,[],[f17])).
% 7.82/1.50  
% 7.82/1.50  fof(f39,plain,(
% 7.82/1.50    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 7.82/1.50    inference(flattening,[],[f38])).
% 7.82/1.50  
% 7.82/1.50  fof(f43,plain,(
% 7.82/1.50    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 7.82/1.50    introduced(choice_axiom,[])).
% 7.82/1.50  
% 7.82/1.50  fof(f42,plain,(
% 7.82/1.50    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 7.82/1.50    introduced(choice_axiom,[])).
% 7.82/1.50  
% 7.82/1.50  fof(f44,plain,(
% 7.82/1.50    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 7.82/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f39,f43,f42])).
% 7.82/1.50  
% 7.82/1.50  fof(f70,plain,(
% 7.82/1.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 7.82/1.50    inference(cnf_transformation,[],[f44])).
% 7.82/1.50  
% 7.82/1.50  fof(f8,axiom,(
% 7.82/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 7.82/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.50  
% 7.82/1.50  fof(f27,plain,(
% 7.82/1.50    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.82/1.50    inference(ennf_transformation,[],[f8])).
% 7.82/1.50  
% 7.82/1.50  fof(f53,plain,(
% 7.82/1.50    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.82/1.50    inference(cnf_transformation,[],[f27])).
% 7.82/1.50  
% 7.82/1.50  fof(f74,plain,(
% 7.82/1.50    k2_relset_1(sK0,sK1,sK2) = sK1),
% 7.82/1.50    inference(cnf_transformation,[],[f44])).
% 7.82/1.50  
% 7.82/1.50  fof(f73,plain,(
% 7.82/1.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 7.82/1.50    inference(cnf_transformation,[],[f44])).
% 7.82/1.50  
% 7.82/1.50  fof(f10,axiom,(
% 7.82/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 7.82/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.50  
% 7.82/1.50  fof(f30,plain,(
% 7.82/1.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.82/1.50    inference(ennf_transformation,[],[f10])).
% 7.82/1.50  
% 7.82/1.50  fof(f31,plain,(
% 7.82/1.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.82/1.50    inference(flattening,[],[f30])).
% 7.82/1.50  
% 7.82/1.50  fof(f41,plain,(
% 7.82/1.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.82/1.50    inference(nnf_transformation,[],[f31])).
% 7.82/1.50  
% 7.82/1.50  fof(f56,plain,(
% 7.82/1.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.82/1.50    inference(cnf_transformation,[],[f41])).
% 7.82/1.50  
% 7.82/1.50  fof(f7,axiom,(
% 7.82/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 7.82/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.50  
% 7.82/1.50  fof(f26,plain,(
% 7.82/1.50    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.82/1.50    inference(ennf_transformation,[],[f7])).
% 7.82/1.50  
% 7.82/1.50  fof(f52,plain,(
% 7.82/1.50    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.82/1.50    inference(cnf_transformation,[],[f26])).
% 7.82/1.50  
% 7.82/1.50  fof(f72,plain,(
% 7.82/1.50    v1_funct_2(sK3,sK1,sK0)),
% 7.82/1.50    inference(cnf_transformation,[],[f44])).
% 7.82/1.50  
% 7.82/1.50  fof(f77,plain,(
% 7.82/1.50    k1_xboole_0 != sK0),
% 7.82/1.50    inference(cnf_transformation,[],[f44])).
% 7.82/1.50  
% 7.82/1.50  fof(f3,axiom,(
% 7.82/1.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 7.82/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.50  
% 7.82/1.50  fof(f20,plain,(
% 7.82/1.50    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.82/1.50    inference(ennf_transformation,[],[f3])).
% 7.82/1.50  
% 7.82/1.50  fof(f21,plain,(
% 7.82/1.50    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.82/1.50    inference(flattening,[],[f20])).
% 7.82/1.50  
% 7.82/1.50  fof(f48,plain,(
% 7.82/1.50    ( ! [X0,X1] : (v2_funct_1(X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.82/1.50    inference(cnf_transformation,[],[f21])).
% 7.82/1.50  
% 7.82/1.50  fof(f71,plain,(
% 7.82/1.50    v1_funct_1(sK3)),
% 7.82/1.50    inference(cnf_transformation,[],[f44])).
% 7.82/1.50  
% 7.82/1.50  fof(f1,axiom,(
% 7.82/1.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 7.82/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.50  
% 7.82/1.50  fof(f19,plain,(
% 7.82/1.50    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 7.82/1.50    inference(ennf_transformation,[],[f1])).
% 7.82/1.50  
% 7.82/1.50  fof(f45,plain,(
% 7.82/1.50    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 7.82/1.50    inference(cnf_transformation,[],[f19])).
% 7.82/1.50  
% 7.82/1.50  fof(f2,axiom,(
% 7.82/1.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 7.82/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.50  
% 7.82/1.50  fof(f46,plain,(
% 7.82/1.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 7.82/1.50    inference(cnf_transformation,[],[f2])).
% 7.82/1.50  
% 7.82/1.50  fof(f13,axiom,(
% 7.82/1.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 7.82/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.50  
% 7.82/1.50  fof(f34,plain,(
% 7.82/1.50    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 7.82/1.50    inference(ennf_transformation,[],[f13])).
% 7.82/1.50  
% 7.82/1.50  fof(f35,plain,(
% 7.82/1.50    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 7.82/1.50    inference(flattening,[],[f34])).
% 7.82/1.50  
% 7.82/1.50  fof(f65,plain,(
% 7.82/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 7.82/1.50    inference(cnf_transformation,[],[f35])).
% 7.82/1.50  
% 7.82/1.50  fof(f9,axiom,(
% 7.82/1.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 7.82/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.50  
% 7.82/1.50  fof(f28,plain,(
% 7.82/1.50    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 7.82/1.50    inference(ennf_transformation,[],[f9])).
% 7.82/1.50  
% 7.82/1.50  fof(f29,plain,(
% 7.82/1.50    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.82/1.50    inference(flattening,[],[f28])).
% 7.82/1.50  
% 7.82/1.50  fof(f40,plain,(
% 7.82/1.50    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.82/1.50    inference(nnf_transformation,[],[f29])).
% 7.82/1.50  
% 7.82/1.50  fof(f54,plain,(
% 7.82/1.50    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.82/1.50    inference(cnf_transformation,[],[f40])).
% 7.82/1.50  
% 7.82/1.50  fof(f75,plain,(
% 7.82/1.50    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 7.82/1.50    inference(cnf_transformation,[],[f44])).
% 7.82/1.50  
% 7.82/1.50  fof(f12,axiom,(
% 7.82/1.50    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 7.82/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.50  
% 7.82/1.50  fof(f18,plain,(
% 7.82/1.50    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 7.82/1.50    inference(pure_predicate_removal,[],[f12])).
% 7.82/1.50  
% 7.82/1.50  fof(f64,plain,(
% 7.82/1.50    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 7.82/1.50    inference(cnf_transformation,[],[f18])).
% 7.82/1.50  
% 7.82/1.50  fof(f68,plain,(
% 7.82/1.50    v1_funct_1(sK2)),
% 7.82/1.50    inference(cnf_transformation,[],[f44])).
% 7.82/1.50  
% 7.82/1.50  fof(f11,axiom,(
% 7.82/1.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 7.82/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.50  
% 7.82/1.50  fof(f32,plain,(
% 7.82/1.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 7.82/1.50    inference(ennf_transformation,[],[f11])).
% 7.82/1.50  
% 7.82/1.50  fof(f33,plain,(
% 7.82/1.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 7.82/1.50    inference(flattening,[],[f32])).
% 7.82/1.50  
% 7.82/1.50  fof(f63,plain,(
% 7.82/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 7.82/1.50    inference(cnf_transformation,[],[f33])).
% 7.82/1.50  
% 7.82/1.50  fof(f5,axiom,(
% 7.82/1.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 7.82/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.50  
% 7.82/1.50  fof(f22,plain,(
% 7.82/1.50    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.82/1.50    inference(ennf_transformation,[],[f5])).
% 7.82/1.50  
% 7.82/1.50  fof(f23,plain,(
% 7.82/1.50    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.82/1.50    inference(flattening,[],[f22])).
% 7.82/1.50  
% 7.82/1.50  fof(f50,plain,(
% 7.82/1.50    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.82/1.50    inference(cnf_transformation,[],[f23])).
% 7.82/1.50  
% 7.82/1.50  fof(f81,plain,(
% 7.82/1.50    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.82/1.50    inference(definition_unfolding,[],[f50,f66])).
% 7.82/1.50  
% 7.82/1.50  fof(f15,axiom,(
% 7.82/1.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 7.82/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.50  
% 7.82/1.50  fof(f36,plain,(
% 7.82/1.50    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 7.82/1.50    inference(ennf_transformation,[],[f15])).
% 7.82/1.50  
% 7.82/1.50  fof(f37,plain,(
% 7.82/1.50    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.82/1.50    inference(flattening,[],[f36])).
% 7.82/1.50  
% 7.82/1.50  fof(f67,plain,(
% 7.82/1.50    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.82/1.50    inference(cnf_transformation,[],[f37])).
% 7.82/1.50  
% 7.82/1.50  fof(f69,plain,(
% 7.82/1.50    v1_funct_2(sK2,sK0,sK1)),
% 7.82/1.50    inference(cnf_transformation,[],[f44])).
% 7.82/1.50  
% 7.82/1.50  fof(f6,axiom,(
% 7.82/1.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 7.82/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.50  
% 7.82/1.50  fof(f24,plain,(
% 7.82/1.50    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.82/1.50    inference(ennf_transformation,[],[f6])).
% 7.82/1.50  
% 7.82/1.50  fof(f25,plain,(
% 7.82/1.50    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.82/1.50    inference(flattening,[],[f24])).
% 7.82/1.50  
% 7.82/1.50  fof(f51,plain,(
% 7.82/1.50    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.82/1.50    inference(cnf_transformation,[],[f25])).
% 7.82/1.50  
% 7.82/1.50  fof(f79,plain,(
% 7.82/1.50    k2_funct_1(sK2) != sK3),
% 7.82/1.50    inference(cnf_transformation,[],[f44])).
% 7.82/1.50  
% 7.82/1.50  cnf(c_4,plain,
% 7.82/1.50      ( v2_funct_1(k6_partfun1(X0)) ),
% 7.82/1.50      inference(cnf_transformation,[],[f80]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_1138,plain,
% 7.82/1.50      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 7.82/1.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_31,negated_conjecture,
% 7.82/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 7.82/1.50      inference(cnf_transformation,[],[f70]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_1119,plain,
% 7.82/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.82/1.50      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_8,plain,
% 7.82/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.82/1.50      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 7.82/1.50      inference(cnf_transformation,[],[f53]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_1134,plain,
% 7.82/1.50      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 7.82/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.82/1.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_1965,plain,
% 7.82/1.50      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 7.82/1.50      inference(superposition,[status(thm)],[c_1119,c_1134]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_27,negated_conjecture,
% 7.82/1.50      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 7.82/1.50      inference(cnf_transformation,[],[f74]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_1966,plain,
% 7.82/1.50      ( k2_relat_1(sK2) = sK1 ),
% 7.82/1.50      inference(light_normalisation,[status(thm)],[c_1965,c_27]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_28,negated_conjecture,
% 7.82/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 7.82/1.50      inference(cnf_transformation,[],[f73]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_1122,plain,
% 7.82/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 7.82/1.50      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_16,plain,
% 7.82/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.82/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.82/1.50      | k1_relset_1(X1,X2,X0) = X1
% 7.82/1.50      | k1_xboole_0 = X2 ),
% 7.82/1.50      inference(cnf_transformation,[],[f56]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_1128,plain,
% 7.82/1.50      ( k1_relset_1(X0,X1,X2) = X0
% 7.82/1.50      | k1_xboole_0 = X1
% 7.82/1.50      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.82/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.82/1.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_2813,plain,
% 7.82/1.50      ( k1_relset_1(sK1,sK0,sK3) = sK1
% 7.82/1.50      | sK0 = k1_xboole_0
% 7.82/1.50      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 7.82/1.50      inference(superposition,[status(thm)],[c_1122,c_1128]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_7,plain,
% 7.82/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.82/1.50      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.82/1.50      inference(cnf_transformation,[],[f52]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_1135,plain,
% 7.82/1.50      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.82/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.82/1.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_2100,plain,
% 7.82/1.50      ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
% 7.82/1.50      inference(superposition,[status(thm)],[c_1122,c_1135]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_2816,plain,
% 7.82/1.50      ( k1_relat_1(sK3) = sK1
% 7.82/1.50      | sK0 = k1_xboole_0
% 7.82/1.50      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 7.82/1.50      inference(demodulation,[status(thm)],[c_2813,c_2100]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_29,negated_conjecture,
% 7.82/1.50      ( v1_funct_2(sK3,sK1,sK0) ),
% 7.82/1.50      inference(cnf_transformation,[],[f72]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_38,plain,
% 7.82/1.50      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 7.82/1.50      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_24,negated_conjecture,
% 7.82/1.50      ( k1_xboole_0 != sK0 ),
% 7.82/1.50      inference(cnf_transformation,[],[f77]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_634,plain,( X0 = X0 ),theory(equality) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_661,plain,
% 7.82/1.50      ( k1_xboole_0 = k1_xboole_0 ),
% 7.82/1.50      inference(instantiation,[status(thm)],[c_634]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_635,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_1220,plain,
% 7.82/1.50      ( sK0 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK0 ),
% 7.82/1.50      inference(instantiation,[status(thm)],[c_635]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_1221,plain,
% 7.82/1.50      ( sK0 != k1_xboole_0
% 7.82/1.50      | k1_xboole_0 = sK0
% 7.82/1.50      | k1_xboole_0 != k1_xboole_0 ),
% 7.82/1.50      inference(instantiation,[status(thm)],[c_1220]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_5865,plain,
% 7.82/1.50      ( k1_relat_1(sK3) = sK1 ),
% 7.82/1.50      inference(global_propositional_subsumption,
% 7.82/1.50                [status(thm)],
% 7.82/1.50                [c_2816,c_38,c_24,c_661,c_1221]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_2,plain,
% 7.82/1.50      ( ~ v1_funct_1(X0)
% 7.82/1.50      | ~ v1_funct_1(X1)
% 7.82/1.50      | v2_funct_1(X1)
% 7.82/1.50      | ~ v2_funct_1(k5_relat_1(X0,X1))
% 7.82/1.50      | ~ v1_relat_1(X1)
% 7.82/1.50      | ~ v1_relat_1(X0)
% 7.82/1.50      | k1_relat_1(X1) != k2_relat_1(X0) ),
% 7.82/1.50      inference(cnf_transformation,[],[f48]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_1140,plain,
% 7.82/1.50      ( k1_relat_1(X0) != k2_relat_1(X1)
% 7.82/1.50      | v1_funct_1(X1) != iProver_top
% 7.82/1.50      | v1_funct_1(X0) != iProver_top
% 7.82/1.50      | v2_funct_1(X0) = iProver_top
% 7.82/1.50      | v2_funct_1(k5_relat_1(X1,X0)) != iProver_top
% 7.82/1.50      | v1_relat_1(X1) != iProver_top
% 7.82/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.82/1.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_5868,plain,
% 7.82/1.50      ( k2_relat_1(X0) != sK1
% 7.82/1.50      | v1_funct_1(X0) != iProver_top
% 7.82/1.50      | v1_funct_1(sK3) != iProver_top
% 7.82/1.50      | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
% 7.82/1.50      | v2_funct_1(sK3) = iProver_top
% 7.82/1.50      | v1_relat_1(X0) != iProver_top
% 7.82/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.82/1.50      inference(superposition,[status(thm)],[c_5865,c_1140]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_30,negated_conjecture,
% 7.82/1.50      ( v1_funct_1(sK3) ),
% 7.82/1.50      inference(cnf_transformation,[],[f71]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_37,plain,
% 7.82/1.50      ( v1_funct_1(sK3) = iProver_top ),
% 7.82/1.50      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_0,plain,
% 7.82/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.82/1.50      | ~ v1_relat_1(X1)
% 7.82/1.50      | v1_relat_1(X0) ),
% 7.82/1.50      inference(cnf_transformation,[],[f45]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_1142,plain,
% 7.82/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.82/1.50      | v1_relat_1(X1) != iProver_top
% 7.82/1.50      | v1_relat_1(X0) = iProver_top ),
% 7.82/1.50      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_2105,plain,
% 7.82/1.50      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 7.82/1.50      | v1_relat_1(sK3) = iProver_top ),
% 7.82/1.50      inference(superposition,[status(thm)],[c_1122,c_1142]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_1,plain,
% 7.82/1.50      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 7.82/1.50      inference(cnf_transformation,[],[f46]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_2267,plain,
% 7.82/1.50      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
% 7.82/1.50      inference(instantiation,[status(thm)],[c_1]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_2268,plain,
% 7.82/1.50      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
% 7.82/1.50      inference(predicate_to_equality,[status(thm)],[c_2267]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_21777,plain,
% 7.82/1.50      ( v1_relat_1(X0) != iProver_top
% 7.82/1.50      | v2_funct_1(sK3) = iProver_top
% 7.82/1.50      | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
% 7.82/1.50      | k2_relat_1(X0) != sK1
% 7.82/1.50      | v1_funct_1(X0) != iProver_top ),
% 7.82/1.50      inference(global_propositional_subsumption,
% 7.82/1.50                [status(thm)],
% 7.82/1.50                [c_5868,c_37,c_2105,c_2268]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_21778,plain,
% 7.82/1.50      ( k2_relat_1(X0) != sK1
% 7.82/1.50      | v1_funct_1(X0) != iProver_top
% 7.82/1.50      | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
% 7.82/1.50      | v2_funct_1(sK3) = iProver_top
% 7.82/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.82/1.50      inference(renaming,[status(thm)],[c_21777]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_21783,plain,
% 7.82/1.50      ( v1_funct_1(sK2) != iProver_top
% 7.82/1.50      | v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
% 7.82/1.50      | v2_funct_1(sK3) = iProver_top
% 7.82/1.50      | v1_relat_1(sK2) != iProver_top ),
% 7.82/1.50      inference(superposition,[status(thm)],[c_1966,c_21778]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_20,plain,
% 7.82/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.82/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.82/1.50      | ~ v1_funct_1(X0)
% 7.82/1.50      | ~ v1_funct_1(X3)
% 7.82/1.50      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 7.82/1.50      inference(cnf_transformation,[],[f65]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_1124,plain,
% 7.82/1.50      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 7.82/1.50      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 7.82/1.50      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.82/1.50      | v1_funct_1(X4) != iProver_top
% 7.82/1.50      | v1_funct_1(X5) != iProver_top ),
% 7.82/1.50      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_2626,plain,
% 7.82/1.50      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 7.82/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.82/1.50      | v1_funct_1(X2) != iProver_top
% 7.82/1.50      | v1_funct_1(sK3) != iProver_top ),
% 7.82/1.50      inference(superposition,[status(thm)],[c_1122,c_1124]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_2822,plain,
% 7.82/1.50      ( v1_funct_1(X2) != iProver_top
% 7.82/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.82/1.50      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 7.82/1.50      inference(global_propositional_subsumption,
% 7.82/1.50                [status(thm)],
% 7.82/1.50                [c_2626,c_37]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_2823,plain,
% 7.82/1.50      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 7.82/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.82/1.50      | v1_funct_1(X2) != iProver_top ),
% 7.82/1.50      inference(renaming,[status(thm)],[c_2822]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_2830,plain,
% 7.82/1.50      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 7.82/1.50      | v1_funct_1(sK2) != iProver_top ),
% 7.82/1.50      inference(superposition,[status(thm)],[c_1119,c_2823]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_10,plain,
% 7.82/1.50      ( ~ r2_relset_1(X0,X1,X2,X3)
% 7.82/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.82/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.82/1.50      | X3 = X2 ),
% 7.82/1.50      inference(cnf_transformation,[],[f54]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_26,negated_conjecture,
% 7.82/1.50      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 7.82/1.50      inference(cnf_transformation,[],[f75]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_370,plain,
% 7.82/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.82/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.82/1.50      | X3 = X0
% 7.82/1.50      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 7.82/1.50      | k6_partfun1(sK0) != X3
% 7.82/1.50      | sK0 != X2
% 7.82/1.50      | sK0 != X1 ),
% 7.82/1.50      inference(resolution_lifted,[status(thm)],[c_10,c_26]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_371,plain,
% 7.82/1.50      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.82/1.50      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.82/1.50      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.82/1.50      inference(unflattening,[status(thm)],[c_370]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_19,plain,
% 7.82/1.50      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 7.82/1.50      inference(cnf_transformation,[],[f64]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_379,plain,
% 7.82/1.50      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.82/1.50      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.82/1.50      inference(forward_subsumption_resolution,
% 7.82/1.50                [status(thm)],
% 7.82/1.50                [c_371,c_19]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_1115,plain,
% 7.82/1.50      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.82/1.50      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 7.82/1.50      inference(predicate_to_equality,[status(thm)],[c_379]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_33,negated_conjecture,
% 7.82/1.50      ( v1_funct_1(sK2) ),
% 7.82/1.50      inference(cnf_transformation,[],[f68]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_17,plain,
% 7.82/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.82/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.82/1.50      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.82/1.50      | ~ v1_funct_1(X0)
% 7.82/1.50      | ~ v1_funct_1(X3) ),
% 7.82/1.50      inference(cnf_transformation,[],[f63]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_1222,plain,
% 7.82/1.50      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.82/1.50      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 7.82/1.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.82/1.50      | ~ v1_funct_1(sK3)
% 7.82/1.50      | ~ v1_funct_1(sK2) ),
% 7.82/1.50      inference(instantiation,[status(thm)],[c_17]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_1862,plain,
% 7.82/1.50      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.82/1.50      inference(global_propositional_subsumption,
% 7.82/1.50                [status(thm)],
% 7.82/1.50                [c_1115,c_33,c_31,c_30,c_28,c_379,c_1222]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_2831,plain,
% 7.82/1.50      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 7.82/1.50      | v1_funct_1(sK2) != iProver_top ),
% 7.82/1.50      inference(light_normalisation,[status(thm)],[c_2830,c_1862]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_34,plain,
% 7.82/1.50      ( v1_funct_1(sK2) = iProver_top ),
% 7.82/1.50      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_3188,plain,
% 7.82/1.50      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 7.82/1.50      inference(global_propositional_subsumption,
% 7.82/1.50                [status(thm)],
% 7.82/1.50                [c_2831,c_34]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_21785,plain,
% 7.82/1.50      ( v1_funct_1(sK2) != iProver_top
% 7.82/1.50      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 7.82/1.50      | v2_funct_1(sK3) = iProver_top
% 7.82/1.50      | v1_relat_1(sK2) != iProver_top ),
% 7.82/1.50      inference(light_normalisation,[status(thm)],[c_21783,c_3188]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_1141,plain,
% 7.82/1.50      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 7.82/1.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_2106,plain,
% 7.82/1.50      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 7.82/1.50      | v1_relat_1(sK2) = iProver_top ),
% 7.82/1.50      inference(superposition,[status(thm)],[c_1119,c_1142]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_2376,plain,
% 7.82/1.50      ( v1_relat_1(sK2) = iProver_top ),
% 7.82/1.50      inference(superposition,[status(thm)],[c_1141,c_2106]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_21812,plain,
% 7.82/1.50      ( v2_funct_1(sK3) = iProver_top
% 7.82/1.50      | v2_funct_1(k6_partfun1(sK0)) != iProver_top ),
% 7.82/1.50      inference(global_propositional_subsumption,
% 7.82/1.50                [status(thm)],
% 7.82/1.50                [c_21785,c_34,c_2376]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_21813,plain,
% 7.82/1.50      ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 7.82/1.50      | v2_funct_1(sK3) = iProver_top ),
% 7.82/1.50      inference(renaming,[status(thm)],[c_21812]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_21816,plain,
% 7.82/1.50      ( v2_funct_1(sK3) = iProver_top ),
% 7.82/1.50      inference(superposition,[status(thm)],[c_1138,c_21813]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_5,plain,
% 7.82/1.50      ( ~ v1_funct_1(X0)
% 7.82/1.50      | ~ v1_funct_1(X1)
% 7.82/1.50      | ~ v2_funct_1(X1)
% 7.82/1.50      | ~ v1_relat_1(X1)
% 7.82/1.50      | ~ v1_relat_1(X0)
% 7.82/1.50      | k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 7.82/1.50      | k2_funct_1(X1) = X0
% 7.82/1.50      | k1_relat_1(X1) != k2_relat_1(X0) ),
% 7.82/1.50      inference(cnf_transformation,[],[f81]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_1137,plain,
% 7.82/1.50      ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 7.82/1.50      | k2_funct_1(X1) = X0
% 7.82/1.50      | k1_relat_1(X1) != k2_relat_1(X0)
% 7.82/1.50      | v1_funct_1(X0) != iProver_top
% 7.82/1.50      | v1_funct_1(X1) != iProver_top
% 7.82/1.50      | v2_funct_1(X1) != iProver_top
% 7.82/1.50      | v1_relat_1(X0) != iProver_top
% 7.82/1.50      | v1_relat_1(X1) != iProver_top ),
% 7.82/1.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_4105,plain,
% 7.82/1.50      ( k2_funct_1(sK3) = sK2
% 7.82/1.50      | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
% 7.82/1.50      | k1_relat_1(sK3) != k2_relat_1(sK2)
% 7.82/1.50      | v1_funct_1(sK3) != iProver_top
% 7.82/1.50      | v1_funct_1(sK2) != iProver_top
% 7.82/1.50      | v2_funct_1(sK3) != iProver_top
% 7.82/1.50      | v1_relat_1(sK3) != iProver_top
% 7.82/1.50      | v1_relat_1(sK2) != iProver_top ),
% 7.82/1.50      inference(superposition,[status(thm)],[c_3188,c_1137]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_1964,plain,
% 7.82/1.50      ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 7.82/1.50      inference(superposition,[status(thm)],[c_1122,c_1134]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_21,plain,
% 7.82/1.50      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 7.82/1.50      | ~ v1_funct_2(X3,X1,X0)
% 7.82/1.50      | ~ v1_funct_2(X2,X0,X1)
% 7.82/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 7.82/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.82/1.50      | ~ v1_funct_1(X2)
% 7.82/1.50      | ~ v1_funct_1(X3)
% 7.82/1.50      | k2_relset_1(X1,X0,X3) = X0 ),
% 7.82/1.50      inference(cnf_transformation,[],[f67]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_383,plain,
% 7.82/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.82/1.50      | ~ v1_funct_2(X3,X2,X1)
% 7.82/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.82/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 7.82/1.50      | ~ v1_funct_1(X0)
% 7.82/1.50      | ~ v1_funct_1(X3)
% 7.82/1.50      | k1_partfun1(X2,X1,X1,X2,X3,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.82/1.50      | k2_relset_1(X1,X2,X0) = X2
% 7.82/1.50      | k6_partfun1(X2) != k6_partfun1(sK0)
% 7.82/1.50      | sK0 != X2 ),
% 7.82/1.50      inference(resolution_lifted,[status(thm)],[c_21,c_26]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_384,plain,
% 7.82/1.50      ( ~ v1_funct_2(X0,X1,sK0)
% 7.82/1.50      | ~ v1_funct_2(X2,sK0,X1)
% 7.82/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 7.82/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 7.82/1.50      | ~ v1_funct_1(X0)
% 7.82/1.50      | ~ v1_funct_1(X2)
% 7.82/1.50      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.82/1.50      | k2_relset_1(X1,sK0,X0) = sK0
% 7.82/1.50      | k6_partfun1(sK0) != k6_partfun1(sK0) ),
% 7.82/1.50      inference(unflattening,[status(thm)],[c_383]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_467,plain,
% 7.82/1.50      ( ~ v1_funct_2(X0,X1,sK0)
% 7.82/1.50      | ~ v1_funct_2(X2,sK0,X1)
% 7.82/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 7.82/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 7.82/1.50      | ~ v1_funct_1(X0)
% 7.82/1.50      | ~ v1_funct_1(X2)
% 7.82/1.50      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.82/1.50      | k2_relset_1(X1,sK0,X0) = sK0 ),
% 7.82/1.50      inference(equality_resolution_simp,[status(thm)],[c_384]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_1114,plain,
% 7.82/1.50      ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.82/1.50      | k2_relset_1(X0,sK0,X2) = sK0
% 7.82/1.50      | v1_funct_2(X2,X0,sK0) != iProver_top
% 7.82/1.50      | v1_funct_2(X1,sK0,X0) != iProver_top
% 7.82/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 7.82/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 7.82/1.50      | v1_funct_1(X1) != iProver_top
% 7.82/1.50      | v1_funct_1(X2) != iProver_top ),
% 7.82/1.50      inference(predicate_to_equality,[status(thm)],[c_467]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_1596,plain,
% 7.82/1.50      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 7.82/1.50      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 7.82/1.50      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 7.82/1.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 7.82/1.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.82/1.50      | v1_funct_1(sK3) != iProver_top
% 7.82/1.50      | v1_funct_1(sK2) != iProver_top ),
% 7.82/1.50      inference(equality_resolution,[status(thm)],[c_1114]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_32,negated_conjecture,
% 7.82/1.50      ( v1_funct_2(sK2,sK0,sK1) ),
% 7.82/1.50      inference(cnf_transformation,[],[f69]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_35,plain,
% 7.82/1.50      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 7.82/1.50      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_36,plain,
% 7.82/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.82/1.50      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_39,plain,
% 7.82/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 7.82/1.50      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_1869,plain,
% 7.82/1.50      ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 7.82/1.50      inference(global_propositional_subsumption,
% 7.82/1.50                [status(thm)],
% 7.82/1.50                [c_1596,c_34,c_35,c_36,c_37,c_38,c_39]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_1967,plain,
% 7.82/1.50      ( k2_relat_1(sK3) = sK0 ),
% 7.82/1.50      inference(light_normalisation,[status(thm)],[c_1964,c_1869]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_4106,plain,
% 7.82/1.50      ( k2_funct_1(sK3) = sK2
% 7.82/1.50      | k6_partfun1(sK0) != k6_partfun1(sK0)
% 7.82/1.50      | k1_relat_1(sK3) != sK1
% 7.82/1.50      | v1_funct_1(sK3) != iProver_top
% 7.82/1.50      | v1_funct_1(sK2) != iProver_top
% 7.82/1.50      | v2_funct_1(sK3) != iProver_top
% 7.82/1.50      | v1_relat_1(sK3) != iProver_top
% 7.82/1.50      | v1_relat_1(sK2) != iProver_top ),
% 7.82/1.50      inference(light_normalisation,[status(thm)],[c_4105,c_1966,c_1967]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_4107,plain,
% 7.82/1.50      ( k2_funct_1(sK3) = sK2
% 7.82/1.50      | k1_relat_1(sK3) != sK1
% 7.82/1.50      | v1_funct_1(sK3) != iProver_top
% 7.82/1.50      | v1_funct_1(sK2) != iProver_top
% 7.82/1.50      | v2_funct_1(sK3) != iProver_top
% 7.82/1.50      | v1_relat_1(sK3) != iProver_top
% 7.82/1.50      | v1_relat_1(sK2) != iProver_top ),
% 7.82/1.50      inference(equality_resolution_simp,[status(thm)],[c_4106]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_4909,plain,
% 7.82/1.50      ( k2_funct_1(sK3) = sK2 | v2_funct_1(sK3) != iProver_top ),
% 7.82/1.50      inference(global_propositional_subsumption,
% 7.82/1.50                [status(thm)],
% 7.82/1.50                [c_4107,c_34,c_37,c_38,c_24,c_661,c_1221,c_2105,c_2268,
% 7.82/1.50                 c_2376,c_2816]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_22087,plain,
% 7.82/1.50      ( k2_funct_1(sK3) = sK2 ),
% 7.82/1.50      inference(superposition,[status(thm)],[c_21816,c_4909]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_1120,plain,
% 7.82/1.50      ( v1_funct_1(sK3) = iProver_top ),
% 7.82/1.50      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_6,plain,
% 7.82/1.50      ( ~ v1_funct_1(X0)
% 7.82/1.50      | ~ v2_funct_1(X0)
% 7.82/1.50      | ~ v1_relat_1(X0)
% 7.82/1.50      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 7.82/1.50      inference(cnf_transformation,[],[f51]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_1136,plain,
% 7.82/1.50      ( k2_funct_1(k2_funct_1(X0)) = X0
% 7.82/1.50      | v1_funct_1(X0) != iProver_top
% 7.82/1.50      | v2_funct_1(X0) != iProver_top
% 7.82/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.82/1.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_2148,plain,
% 7.82/1.50      ( k2_funct_1(k2_funct_1(sK3)) = sK3
% 7.82/1.50      | v2_funct_1(sK3) != iProver_top
% 7.82/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.82/1.50      inference(superposition,[status(thm)],[c_1120,c_1136]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_2438,plain,
% 7.82/1.50      ( v2_funct_1(sK3) != iProver_top
% 7.82/1.50      | k2_funct_1(k2_funct_1(sK3)) = sK3 ),
% 7.82/1.50      inference(global_propositional_subsumption,
% 7.82/1.50                [status(thm)],
% 7.82/1.50                [c_2148,c_2105,c_2268]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_2439,plain,
% 7.82/1.50      ( k2_funct_1(k2_funct_1(sK3)) = sK3
% 7.82/1.50      | v2_funct_1(sK3) != iProver_top ),
% 7.82/1.50      inference(renaming,[status(thm)],[c_2438]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_22088,plain,
% 7.82/1.50      ( k2_funct_1(k2_funct_1(sK3)) = sK3 ),
% 7.82/1.50      inference(superposition,[status(thm)],[c_21816,c_2439]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_22089,plain,
% 7.82/1.50      ( k2_funct_1(sK2) = sK3 ),
% 7.82/1.50      inference(demodulation,[status(thm)],[c_22087,c_22088]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(c_22,negated_conjecture,
% 7.82/1.50      ( k2_funct_1(sK2) != sK3 ),
% 7.82/1.50      inference(cnf_transformation,[],[f79]) ).
% 7.82/1.50  
% 7.82/1.50  cnf(contradiction,plain,
% 7.82/1.50      ( $false ),
% 7.82/1.50      inference(minisat,[status(thm)],[c_22089,c_22]) ).
% 7.82/1.50  
% 7.82/1.50  
% 7.82/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.82/1.50  
% 7.82/1.50  ------                               Statistics
% 7.82/1.50  
% 7.82/1.50  ------ General
% 7.82/1.50  
% 7.82/1.50  abstr_ref_over_cycles:                  0
% 7.82/1.50  abstr_ref_under_cycles:                 0
% 7.82/1.50  gc_basic_clause_elim:                   0
% 7.82/1.50  forced_gc_time:                         0
% 7.82/1.50  parsing_time:                           0.009
% 7.82/1.50  unif_index_cands_time:                  0.
% 7.82/1.50  unif_index_add_time:                    0.
% 7.82/1.50  orderings_time:                         0.
% 7.82/1.50  out_proof_time:                         0.013
% 7.82/1.50  total_time:                             0.864
% 7.82/1.50  num_of_symbols:                         52
% 7.82/1.50  num_of_terms:                           31418
% 7.82/1.50  
% 7.82/1.50  ------ Preprocessing
% 7.82/1.50  
% 7.82/1.50  num_of_splits:                          0
% 7.82/1.50  num_of_split_atoms:                     0
% 7.82/1.50  num_of_reused_defs:                     0
% 7.82/1.50  num_eq_ax_congr_red:                    18
% 7.82/1.50  num_of_sem_filtered_clauses:            1
% 7.82/1.50  num_of_subtypes:                        0
% 7.82/1.50  monotx_restored_types:                  0
% 7.82/1.50  sat_num_of_epr_types:                   0
% 7.82/1.50  sat_num_of_non_cyclic_types:            0
% 7.82/1.50  sat_guarded_non_collapsed_types:        0
% 7.82/1.50  num_pure_diseq_elim:                    0
% 7.82/1.50  simp_replaced_by:                       0
% 7.82/1.50  res_preprocessed:                       162
% 7.82/1.50  prep_upred:                             0
% 7.82/1.50  prep_unflattend:                        12
% 7.82/1.50  smt_new_axioms:                         0
% 7.82/1.50  pred_elim_cands:                        5
% 7.82/1.50  pred_elim:                              1
% 7.82/1.50  pred_elim_cl:                           1
% 7.82/1.50  pred_elim_cycles:                       3
% 7.82/1.50  merged_defs:                            0
% 7.82/1.50  merged_defs_ncl:                        0
% 7.82/1.50  bin_hyper_res:                          0
% 7.82/1.50  prep_cycles:                            4
% 7.82/1.50  pred_elim_time:                         0.004
% 7.82/1.50  splitting_time:                         0.
% 7.82/1.50  sem_filter_time:                        0.
% 7.82/1.50  monotx_time:                            0.001
% 7.82/1.50  subtype_inf_time:                       0.
% 7.82/1.50  
% 7.82/1.50  ------ Problem properties
% 7.82/1.50  
% 7.82/1.50  clauses:                                33
% 7.82/1.50  conjectures:                            11
% 7.82/1.50  epr:                                    7
% 7.82/1.50  horn:                                   29
% 7.82/1.50  ground:                                 12
% 7.82/1.50  unary:                                  14
% 7.82/1.50  binary:                                 3
% 7.82/1.50  lits:                                   101
% 7.82/1.50  lits_eq:                                27
% 7.82/1.50  fd_pure:                                0
% 7.82/1.50  fd_pseudo:                              0
% 7.82/1.50  fd_cond:                                3
% 7.82/1.50  fd_pseudo_cond:                         1
% 7.82/1.50  ac_symbols:                             0
% 7.82/1.50  
% 7.82/1.50  ------ Propositional Solver
% 7.82/1.50  
% 7.82/1.50  prop_solver_calls:                      32
% 7.82/1.50  prop_fast_solver_calls:                 2460
% 7.82/1.50  smt_solver_calls:                       0
% 7.82/1.50  smt_fast_solver_calls:                  0
% 7.82/1.50  prop_num_of_clauses:                    11475
% 7.82/1.50  prop_preprocess_simplified:             21247
% 7.82/1.50  prop_fo_subsumed:                       517
% 7.82/1.50  prop_solver_time:                       0.
% 7.82/1.50  smt_solver_time:                        0.
% 7.82/1.50  smt_fast_solver_time:                   0.
% 7.82/1.50  prop_fast_solver_time:                  0.
% 7.82/1.50  prop_unsat_core_time:                   0.002
% 7.82/1.50  
% 7.82/1.50  ------ QBF
% 7.82/1.50  
% 7.82/1.50  qbf_q_res:                              0
% 7.82/1.50  qbf_num_tautologies:                    0
% 7.82/1.50  qbf_prep_cycles:                        0
% 7.82/1.50  
% 7.82/1.50  ------ BMC1
% 7.82/1.50  
% 7.82/1.50  bmc1_current_bound:                     -1
% 7.82/1.50  bmc1_last_solved_bound:                 -1
% 7.82/1.50  bmc1_unsat_core_size:                   -1
% 7.82/1.50  bmc1_unsat_core_parents_size:           -1
% 7.82/1.50  bmc1_merge_next_fun:                    0
% 7.82/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.82/1.50  
% 7.82/1.50  ------ Instantiation
% 7.82/1.50  
% 7.82/1.50  inst_num_of_clauses:                    2974
% 7.82/1.50  inst_num_in_passive:                    667
% 7.82/1.50  inst_num_in_active:                     1564
% 7.82/1.50  inst_num_in_unprocessed:                743
% 7.82/1.50  inst_num_of_loops:                      1670
% 7.82/1.50  inst_num_of_learning_restarts:          0
% 7.82/1.50  inst_num_moves_active_passive:          103
% 7.82/1.50  inst_lit_activity:                      0
% 7.82/1.50  inst_lit_activity_moves:                1
% 7.82/1.50  inst_num_tautologies:                   0
% 7.82/1.50  inst_num_prop_implied:                  0
% 7.82/1.50  inst_num_existing_simplified:           0
% 7.82/1.50  inst_num_eq_res_simplified:             0
% 7.82/1.50  inst_num_child_elim:                    0
% 7.82/1.50  inst_num_of_dismatching_blockings:      958
% 7.82/1.50  inst_num_of_non_proper_insts:           3082
% 7.82/1.50  inst_num_of_duplicates:                 0
% 7.82/1.50  inst_inst_num_from_inst_to_res:         0
% 7.82/1.50  inst_dismatching_checking_time:         0.
% 7.82/1.50  
% 7.82/1.50  ------ Resolution
% 7.82/1.50  
% 7.82/1.50  res_num_of_clauses:                     0
% 7.82/1.50  res_num_in_passive:                     0
% 7.82/1.50  res_num_in_active:                      0
% 7.82/1.50  res_num_of_loops:                       166
% 7.82/1.50  res_forward_subset_subsumed:            200
% 7.82/1.50  res_backward_subset_subsumed:           0
% 7.82/1.50  res_forward_subsumed:                   0
% 7.82/1.50  res_backward_subsumed:                  0
% 7.82/1.50  res_forward_subsumption_resolution:     2
% 7.82/1.50  res_backward_subsumption_resolution:    0
% 7.82/1.50  res_clause_to_clause_subsumption:       2079
% 7.82/1.50  res_orphan_elimination:                 0
% 7.82/1.50  res_tautology_del:                      151
% 7.82/1.50  res_num_eq_res_simplified:              1
% 7.82/1.50  res_num_sel_changes:                    0
% 7.82/1.50  res_moves_from_active_to_pass:          0
% 7.82/1.50  
% 7.82/1.50  ------ Superposition
% 7.82/1.50  
% 7.82/1.50  sup_time_total:                         0.
% 7.82/1.50  sup_time_generating:                    0.
% 7.82/1.50  sup_time_sim_full:                      0.
% 7.82/1.50  sup_time_sim_immed:                     0.
% 7.82/1.50  
% 7.82/1.50  sup_num_of_clauses:                     881
% 7.82/1.50  sup_num_in_active:                      317
% 7.82/1.50  sup_num_in_passive:                     564
% 7.82/1.50  sup_num_of_loops:                       333
% 7.82/1.50  sup_fw_superposition:                   492
% 7.82/1.50  sup_bw_superposition:                   502
% 7.82/1.50  sup_immediate_simplified:               427
% 7.82/1.50  sup_given_eliminated:                   0
% 7.82/1.50  comparisons_done:                       0
% 7.82/1.50  comparisons_avoided:                    1
% 7.82/1.50  
% 7.82/1.50  ------ Simplifications
% 7.82/1.50  
% 7.82/1.50  
% 7.82/1.50  sim_fw_subset_subsumed:                 27
% 7.82/1.50  sim_bw_subset_subsumed:                 64
% 7.82/1.50  sim_fw_subsumed:                        10
% 7.82/1.50  sim_bw_subsumed:                        4
% 7.82/1.50  sim_fw_subsumption_res:                 0
% 7.82/1.50  sim_bw_subsumption_res:                 0
% 7.82/1.50  sim_tautology_del:                      0
% 7.82/1.50  sim_eq_tautology_del:                   30
% 7.82/1.50  sim_eq_res_simp:                        1
% 7.82/1.50  sim_fw_demodulated:                     27
% 7.82/1.50  sim_bw_demodulated:                     4
% 7.82/1.50  sim_light_normalised:                   396
% 7.82/1.50  sim_joinable_taut:                      0
% 7.82/1.50  sim_joinable_simp:                      0
% 7.82/1.50  sim_ac_normalised:                      0
% 7.82/1.50  sim_smt_subsumption:                    0
% 7.82/1.50  
%------------------------------------------------------------------------------
