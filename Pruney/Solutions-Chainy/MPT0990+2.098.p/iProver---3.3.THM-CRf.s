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
% DateTime   : Thu Dec  3 12:03:17 EST 2020

% Result     : Theorem 8.18s
% Output     : CNFRefutation 8.18s
% Verified   : 
% Statistics : Number of formulae       :  199 (4000 expanded)
%              Number of clauses        :  128 (1060 expanded)
%              Number of leaves         :   22 (1079 expanded)
%              Depth                    :   24
%              Number of atoms          :  787 (35005 expanded)
%              Number of equality atoms :  392 (12764 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f23])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f15,conjecture,(
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

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f39,plain,(
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

fof(f38,plain,
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

fof(f40,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f36,f39,f38])).

fof(f71,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f40])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f8])).

fof(f11,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f83,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f52,f56])).

fof(f64,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f66,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f40])).

fof(f67,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f69,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f40])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f25])).

fof(f54,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f70,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f40])).

fof(f13,axiom,(
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

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f60,plain,(
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
    inference(cnf_transformation,[],[f32])).

fof(f65,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f68,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f73,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f40])).

fof(f2,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f78,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f44,f56])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f18,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f45,plain,(
    ! [X0] :
      ( k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f81,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f45,f56])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f4,axiom,(
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

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f47,f56])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f12,axiom,(
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

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f72,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f27])).

fof(f55,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f14,axiom,(
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

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f1,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f76,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f42,f56])).

fof(f74,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f40])).

fof(f75,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_10,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_26,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_354,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_26])).

cnf(c_355,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_354])).

cnf(c_11,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_363,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_355,c_11])).

cnf(c_1067,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_363])).

cnf(c_33,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1174,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1758,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1067,c_33,c_31,c_30,c_28,c_363,c_1174])).

cnf(c_27,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_17,plain,
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
    inference(cnf_transformation,[],[f60])).

cnf(c_1080,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4697,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_27,c_1080])).

cnf(c_34,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_35,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_36,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_4704,plain,
    ( v1_funct_1(X1) != iProver_top
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | k1_xboole_0 = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4697,c_34,c_35,c_36])).

cnf(c_4705,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4704])).

cnf(c_4708,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1758,c_4705])).

cnf(c_37,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_38,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_39,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_24,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_608,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_639,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_608])).

cnf(c_609,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1172,plain,
    ( sK0 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_609])).

cnf(c_1173,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1172])).

cnf(c_2,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_4729,plain,
    ( v2_funct_1(k6_partfun1(sK0)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_4730,plain,
    ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4729])).

cnf(c_4967,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4708,c_37,c_38,c_39,c_24,c_639,c_1173,c_4730])).

cnf(c_1072,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_5,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v2_funct_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1089,plain,
    ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2031,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
    | v1_relat_1(sK3) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1072,c_1089])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1214,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1573,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1214])).

cnf(c_1574,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1573])).

cnf(c_2233,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
    | v2_funct_1(sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2031,c_39,c_1574])).

cnf(c_4972,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3)) ),
    inference(superposition,[status(thm)],[c_4967,c_2233])).

cnf(c_6,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v2_funct_1(X0)
    | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
    | k2_funct_1(X0) = X1
    | k1_relat_1(X0) != k2_relat_1(X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1088,plain,
    ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k1_relat_1(X1) != k2_relat_1(X0)
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v2_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_5019,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = sK3
    | k1_relat_1(k2_funct_1(sK3)) != k2_relat_1(sK3)
    | k6_partfun1(k2_relat_1(k2_funct_1(sK3))) != k6_partfun1(k1_relat_1(sK3))
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v2_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4972,c_1088])).

cnf(c_1074,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1086,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1990,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1074,c_1086])).

cnf(c_15,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_367,plain,
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
    inference(resolution_lifted,[status(thm)],[c_15,c_26])).

cnf(c_368,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0
    | k6_partfun1(sK0) != k6_partfun1(sK0) ),
    inference(unflattening,[status(thm)],[c_367])).

cnf(c_449,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_368])).

cnf(c_1066,plain,
    ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X0,sK0,X2) = sK0
    | v1_funct_2(X2,X0,sK0) != iProver_top
    | v1_funct_2(X1,sK0,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_449])).

cnf(c_1596,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1066])).

cnf(c_1765,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1596,c_34,c_35,c_36,c_37,c_38,c_39])).

cnf(c_1993,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_1990,c_1765])).

cnf(c_5020,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = sK3
    | k1_relat_1(k2_funct_1(sK3)) != sK0
    | k6_partfun1(k2_relat_1(k2_funct_1(sK3))) != k6_partfun1(k1_relat_1(sK3))
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v2_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5019,c_1993])).

cnf(c_25,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1684,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_5021,plain,
    ( ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v2_funct_1(k2_funct_1(sK3))
    | k2_funct_1(k2_funct_1(sK3)) = sK3
    | k1_relat_1(k2_funct_1(sK3)) != sK0
    | k6_partfun1(k2_relat_1(k2_funct_1(sK3))) != k6_partfun1(k1_relat_1(sK3)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5020])).

cnf(c_1071,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1082,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2748,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1074,c_1082])).

cnf(c_2812,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2748,c_37])).

cnf(c_2813,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_2812])).

cnf(c_2821,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1071,c_2813])).

cnf(c_2822,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2821,c_1758])).

cnf(c_3651,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2822,c_34])).

cnf(c_3774,plain,
    ( k2_funct_1(sK3) = sK2
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3651,c_1088])).

cnf(c_1991,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1071,c_1086])).

cnf(c_1992,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_1991,c_27])).

cnf(c_3775,plain,
    ( k2_funct_1(sK3) = sK2
    | k1_relat_1(sK3) != sK1
    | k6_partfun1(sK0) != k6_partfun1(sK0)
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3774,c_1992,c_1993])).

cnf(c_3776,plain,
    ( k2_funct_1(sK3) = sK2
    | k1_relat_1(sK3) != sK1
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3775])).

cnf(c_3778,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ v2_funct_1(sK3)
    | k2_funct_1(sK3) = sK2
    | k1_relat_1(sK3) != sK1 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3776])).

cnf(c_4709,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(k6_partfun1(sK0))
    | v2_funct_1(sK3)
    | sK0 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4708])).

cnf(c_5165,plain,
    ( k1_relat_1(sK3) != sK1
    | k2_funct_1(sK3) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3776,c_33,c_31,c_30,c_29,c_28,c_24,c_639,c_1173,c_1573,c_1684,c_3778,c_4709,c_4729])).

cnf(c_5166,plain,
    ( k2_funct_1(sK3) = sK2
    | k1_relat_1(sK3) != sK1 ),
    inference(renaming,[status(thm)],[c_5165])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1076,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2685,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1765,c_1076])).

cnf(c_2688,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | sK0 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2685])).

cnf(c_5220,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2685,c_30,c_29,c_28,c_24,c_639,c_1173,c_2688,c_4709,c_4729])).

cnf(c_5222,plain,
    ( k6_partfun1(k1_relat_1(sK3)) = k6_partfun1(sK1) ),
    inference(demodulation,[status(thm)],[c_5220,c_4972])).

cnf(c_0,plain,
    ( k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_5706,plain,
    ( k2_relat_1(k6_partfun1(sK1)) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_5222,c_0])).

cnf(c_5707,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(demodulation,[status(thm)],[c_5706,c_0])).

cnf(c_617,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1351,plain,
    ( v1_funct_1(X0)
    | ~ v1_funct_1(sK2)
    | X0 != sK2 ),
    inference(instantiation,[status(thm)],[c_617])).

cnf(c_1430,plain,
    ( v1_funct_1(k2_funct_1(X0))
    | ~ v1_funct_1(sK2)
    | k2_funct_1(X0) != sK2 ),
    inference(instantiation,[status(thm)],[c_1351])).

cnf(c_7982,plain,
    ( v1_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK2)
    | k2_funct_1(sK3) != sK2 ),
    inference(instantiation,[status(thm)],[c_1430])).

cnf(c_614,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1737,plain,
    ( v1_relat_1(X0)
    | ~ v1_relat_1(sK2)
    | X0 != sK2 ),
    inference(instantiation,[status(thm)],[c_614])).

cnf(c_2266,plain,
    ( v1_relat_1(k2_funct_1(X0))
    | ~ v1_relat_1(sK2)
    | k2_funct_1(X0) != sK2 ),
    inference(instantiation,[status(thm)],[c_1737])).

cnf(c_7980,plain,
    ( v1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK2)
    | k2_funct_1(sK3) != sK2 ),
    inference(instantiation,[status(thm)],[c_2266])).

cnf(c_613,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2118,plain,
    ( v2_funct_1(X0)
    | ~ v2_funct_1(sK2)
    | X0 != sK2 ),
    inference(instantiation,[status(thm)],[c_613])).

cnf(c_2539,plain,
    ( v2_funct_1(k2_funct_1(X0))
    | ~ v2_funct_1(sK2)
    | k2_funct_1(X0) != sK2 ),
    inference(instantiation,[status(thm)],[c_2118])).

cnf(c_7979,plain,
    ( v2_funct_1(k2_funct_1(sK3))
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK3) != sK2 ),
    inference(instantiation,[status(thm)],[c_2539])).

cnf(c_22533,plain,
    ( k6_partfun1(k2_relat_1(k2_funct_1(sK3))) != k6_partfun1(k1_relat_1(sK3))
    | k1_relat_1(k2_funct_1(sK3)) != sK0
    | k2_funct_1(k2_funct_1(sK3)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5020,c_33,c_31,c_30,c_29,c_28,c_25,c_24,c_639,c_1173,c_1573,c_1684,c_3778,c_4709,c_4729,c_5021,c_5707,c_7982,c_7980,c_7979])).

cnf(c_22534,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = sK3
    | k1_relat_1(k2_funct_1(sK3)) != sK0
    | k6_partfun1(k2_relat_1(k2_funct_1(sK3))) != k6_partfun1(k1_relat_1(sK3)) ),
    inference(renaming,[status(thm)],[c_22533])).

cnf(c_2684,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_27,c_1076])).

cnf(c_1069,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_2032,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
    | v1_relat_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1069,c_1089])).

cnf(c_41,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1685,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1684])).

cnf(c_2238,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2032,c_36,c_41,c_1685])).

cnf(c_2687,plain,
    ( k6_partfun1(k1_relat_1(sK2)) = k6_partfun1(sK0)
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2684,c_2238])).

cnf(c_23,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1152,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_609])).

cnf(c_1153,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1152])).

cnf(c_3571,plain,
    ( k6_partfun1(k1_relat_1(sK2)) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2687,c_34,c_35,c_36,c_41,c_23,c_639,c_1153])).

cnf(c_3579,plain,
    ( k2_relat_1(k6_partfun1(sK0)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_3571,c_0])).

cnf(c_3580,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(demodulation,[status(thm)],[c_3579,c_0])).

cnf(c_5844,plain,
    ( k2_funct_1(sK3) = sK2
    | sK1 != sK1 ),
    inference(demodulation,[status(thm)],[c_5707,c_5166])).

cnf(c_5861,plain,
    ( k2_funct_1(sK3) = sK2 ),
    inference(equality_resolution_simp,[status(thm)],[c_5844])).

cnf(c_22535,plain,
    ( k2_funct_1(sK2) = sK3
    | k6_partfun1(sK1) != k6_partfun1(sK1)
    | sK0 != sK0 ),
    inference(light_normalisation,[status(thm)],[c_22534,c_1992,c_3580,c_5707,c_5861])).

cnf(c_22536,plain,
    ( k2_funct_1(sK2) = sK3 ),
    inference(equality_resolution_simp,[status(thm)],[c_22535])).

cnf(c_22,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f75])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_22536,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.11  % Command    : iproveropt_run.sh %d %s
% 0.11/0.32  % Computer   : n005.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 19:19:47 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  % Running in FOF mode
% 8.18/1.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.18/1.50  
% 8.18/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 8.18/1.50  
% 8.18/1.50  ------  iProver source info
% 8.18/1.50  
% 8.18/1.50  git: date: 2020-06-30 10:37:57 +0100
% 8.18/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 8.18/1.50  git: non_committed_changes: false
% 8.18/1.50  git: last_make_outside_of_git: false
% 8.18/1.50  
% 8.18/1.50  ------ 
% 8.18/1.50  
% 8.18/1.50  ------ Input Options
% 8.18/1.50  
% 8.18/1.50  --out_options                           all
% 8.18/1.50  --tptp_safe_out                         true
% 8.18/1.50  --problem_path                          ""
% 8.18/1.50  --include_path                          ""
% 8.18/1.50  --clausifier                            res/vclausify_rel
% 8.18/1.50  --clausifier_options                    ""
% 8.18/1.50  --stdin                                 false
% 8.18/1.50  --stats_out                             all
% 8.18/1.50  
% 8.18/1.50  ------ General Options
% 8.18/1.50  
% 8.18/1.50  --fof                                   false
% 8.18/1.50  --time_out_real                         305.
% 8.18/1.50  --time_out_virtual                      -1.
% 8.18/1.50  --symbol_type_check                     false
% 8.18/1.50  --clausify_out                          false
% 8.18/1.50  --sig_cnt_out                           false
% 8.18/1.50  --trig_cnt_out                          false
% 8.18/1.50  --trig_cnt_out_tolerance                1.
% 8.18/1.50  --trig_cnt_out_sk_spl                   false
% 8.18/1.50  --abstr_cl_out                          false
% 8.18/1.50  
% 8.18/1.50  ------ Global Options
% 8.18/1.50  
% 8.18/1.50  --schedule                              default
% 8.18/1.50  --add_important_lit                     false
% 8.18/1.50  --prop_solver_per_cl                    1000
% 8.18/1.50  --min_unsat_core                        false
% 8.18/1.50  --soft_assumptions                      false
% 8.18/1.50  --soft_lemma_size                       3
% 8.18/1.50  --prop_impl_unit_size                   0
% 8.18/1.50  --prop_impl_unit                        []
% 8.18/1.50  --share_sel_clauses                     true
% 8.18/1.50  --reset_solvers                         false
% 8.18/1.50  --bc_imp_inh                            [conj_cone]
% 8.18/1.50  --conj_cone_tolerance                   3.
% 8.18/1.50  --extra_neg_conj                        none
% 8.18/1.50  --large_theory_mode                     true
% 8.18/1.50  --prolific_symb_bound                   200
% 8.18/1.50  --lt_threshold                          2000
% 8.18/1.50  --clause_weak_htbl                      true
% 8.18/1.50  --gc_record_bc_elim                     false
% 8.18/1.50  
% 8.18/1.50  ------ Preprocessing Options
% 8.18/1.50  
% 8.18/1.50  --preprocessing_flag                    true
% 8.18/1.50  --time_out_prep_mult                    0.1
% 8.18/1.50  --splitting_mode                        input
% 8.18/1.50  --splitting_grd                         true
% 8.18/1.50  --splitting_cvd                         false
% 8.18/1.50  --splitting_cvd_svl                     false
% 8.18/1.50  --splitting_nvd                         32
% 8.18/1.50  --sub_typing                            true
% 8.18/1.50  --prep_gs_sim                           true
% 8.18/1.50  --prep_unflatten                        true
% 8.18/1.50  --prep_res_sim                          true
% 8.18/1.50  --prep_upred                            true
% 8.18/1.50  --prep_sem_filter                       exhaustive
% 8.18/1.50  --prep_sem_filter_out                   false
% 8.18/1.50  --pred_elim                             true
% 8.18/1.50  --res_sim_input                         true
% 8.18/1.50  --eq_ax_congr_red                       true
% 8.18/1.50  --pure_diseq_elim                       true
% 8.18/1.50  --brand_transform                       false
% 8.18/1.50  --non_eq_to_eq                          false
% 8.18/1.50  --prep_def_merge                        true
% 8.18/1.50  --prep_def_merge_prop_impl              false
% 8.18/1.50  --prep_def_merge_mbd                    true
% 8.18/1.50  --prep_def_merge_tr_red                 false
% 8.18/1.50  --prep_def_merge_tr_cl                  false
% 8.18/1.50  --smt_preprocessing                     true
% 8.18/1.50  --smt_ac_axioms                         fast
% 8.18/1.50  --preprocessed_out                      false
% 8.18/1.50  --preprocessed_stats                    false
% 8.18/1.50  
% 8.18/1.50  ------ Abstraction refinement Options
% 8.18/1.50  
% 8.18/1.50  --abstr_ref                             []
% 8.18/1.50  --abstr_ref_prep                        false
% 8.18/1.50  --abstr_ref_until_sat                   false
% 8.18/1.50  --abstr_ref_sig_restrict                funpre
% 8.18/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 8.18/1.50  --abstr_ref_under                       []
% 8.18/1.50  
% 8.18/1.50  ------ SAT Options
% 8.18/1.50  
% 8.18/1.50  --sat_mode                              false
% 8.18/1.50  --sat_fm_restart_options                ""
% 8.18/1.50  --sat_gr_def                            false
% 8.18/1.50  --sat_epr_types                         true
% 8.18/1.50  --sat_non_cyclic_types                  false
% 8.18/1.50  --sat_finite_models                     false
% 8.18/1.50  --sat_fm_lemmas                         false
% 8.18/1.50  --sat_fm_prep                           false
% 8.18/1.50  --sat_fm_uc_incr                        true
% 8.18/1.50  --sat_out_model                         small
% 8.18/1.50  --sat_out_clauses                       false
% 8.18/1.50  
% 8.18/1.50  ------ QBF Options
% 8.18/1.50  
% 8.18/1.50  --qbf_mode                              false
% 8.18/1.50  --qbf_elim_univ                         false
% 8.18/1.50  --qbf_dom_inst                          none
% 8.18/1.50  --qbf_dom_pre_inst                      false
% 8.18/1.50  --qbf_sk_in                             false
% 8.18/1.50  --qbf_pred_elim                         true
% 8.18/1.50  --qbf_split                             512
% 8.18/1.50  
% 8.18/1.50  ------ BMC1 Options
% 8.18/1.50  
% 8.18/1.50  --bmc1_incremental                      false
% 8.18/1.50  --bmc1_axioms                           reachable_all
% 8.18/1.50  --bmc1_min_bound                        0
% 8.18/1.50  --bmc1_max_bound                        -1
% 8.18/1.50  --bmc1_max_bound_default                -1
% 8.18/1.50  --bmc1_symbol_reachability              true
% 8.18/1.50  --bmc1_property_lemmas                  false
% 8.18/1.50  --bmc1_k_induction                      false
% 8.18/1.50  --bmc1_non_equiv_states                 false
% 8.18/1.50  --bmc1_deadlock                         false
% 8.18/1.50  --bmc1_ucm                              false
% 8.18/1.50  --bmc1_add_unsat_core                   none
% 8.18/1.50  --bmc1_unsat_core_children              false
% 8.18/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 8.18/1.50  --bmc1_out_stat                         full
% 8.18/1.50  --bmc1_ground_init                      false
% 8.18/1.50  --bmc1_pre_inst_next_state              false
% 8.18/1.50  --bmc1_pre_inst_state                   false
% 8.18/1.50  --bmc1_pre_inst_reach_state             false
% 8.18/1.50  --bmc1_out_unsat_core                   false
% 8.18/1.50  --bmc1_aig_witness_out                  false
% 8.18/1.50  --bmc1_verbose                          false
% 8.18/1.50  --bmc1_dump_clauses_tptp                false
% 8.18/1.50  --bmc1_dump_unsat_core_tptp             false
% 8.18/1.50  --bmc1_dump_file                        -
% 8.18/1.50  --bmc1_ucm_expand_uc_limit              128
% 8.18/1.50  --bmc1_ucm_n_expand_iterations          6
% 8.18/1.50  --bmc1_ucm_extend_mode                  1
% 8.18/1.50  --bmc1_ucm_init_mode                    2
% 8.18/1.50  --bmc1_ucm_cone_mode                    none
% 8.18/1.50  --bmc1_ucm_reduced_relation_type        0
% 8.18/1.50  --bmc1_ucm_relax_model                  4
% 8.18/1.50  --bmc1_ucm_full_tr_after_sat            true
% 8.18/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 8.18/1.50  --bmc1_ucm_layered_model                none
% 8.18/1.50  --bmc1_ucm_max_lemma_size               10
% 8.18/1.50  
% 8.18/1.50  ------ AIG Options
% 8.18/1.50  
% 8.18/1.50  --aig_mode                              false
% 8.18/1.50  
% 8.18/1.50  ------ Instantiation Options
% 8.18/1.50  
% 8.18/1.50  --instantiation_flag                    true
% 8.18/1.50  --inst_sos_flag                         true
% 8.18/1.50  --inst_sos_phase                        true
% 8.18/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 8.18/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 8.18/1.50  --inst_lit_sel_side                     num_symb
% 8.18/1.50  --inst_solver_per_active                1400
% 8.18/1.50  --inst_solver_calls_frac                1.
% 8.18/1.50  --inst_passive_queue_type               priority_queues
% 8.18/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 8.18/1.50  --inst_passive_queues_freq              [25;2]
% 8.18/1.50  --inst_dismatching                      true
% 8.18/1.50  --inst_eager_unprocessed_to_passive     true
% 8.18/1.50  --inst_prop_sim_given                   true
% 8.18/1.50  --inst_prop_sim_new                     false
% 8.18/1.50  --inst_subs_new                         false
% 8.18/1.50  --inst_eq_res_simp                      false
% 8.18/1.50  --inst_subs_given                       false
% 8.18/1.50  --inst_orphan_elimination               true
% 8.18/1.50  --inst_learning_loop_flag               true
% 8.18/1.50  --inst_learning_start                   3000
% 8.18/1.50  --inst_learning_factor                  2
% 8.18/1.50  --inst_start_prop_sim_after_learn       3
% 8.18/1.50  --inst_sel_renew                        solver
% 8.18/1.50  --inst_lit_activity_flag                true
% 8.18/1.50  --inst_restr_to_given                   false
% 8.18/1.50  --inst_activity_threshold               500
% 8.18/1.50  --inst_out_proof                        true
% 8.18/1.50  
% 8.18/1.50  ------ Resolution Options
% 8.18/1.50  
% 8.18/1.50  --resolution_flag                       true
% 8.18/1.50  --res_lit_sel                           adaptive
% 8.18/1.50  --res_lit_sel_side                      none
% 8.18/1.50  --res_ordering                          kbo
% 8.18/1.50  --res_to_prop_solver                    active
% 8.18/1.50  --res_prop_simpl_new                    false
% 8.18/1.50  --res_prop_simpl_given                  true
% 8.18/1.50  --res_passive_queue_type                priority_queues
% 8.18/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 8.18/1.50  --res_passive_queues_freq               [15;5]
% 8.18/1.50  --res_forward_subs                      full
% 8.18/1.50  --res_backward_subs                     full
% 8.18/1.50  --res_forward_subs_resolution           true
% 8.18/1.50  --res_backward_subs_resolution          true
% 8.18/1.50  --res_orphan_elimination                true
% 8.18/1.50  --res_time_limit                        2.
% 8.18/1.50  --res_out_proof                         true
% 8.18/1.50  
% 8.18/1.50  ------ Superposition Options
% 8.18/1.50  
% 8.18/1.50  --superposition_flag                    true
% 8.18/1.50  --sup_passive_queue_type                priority_queues
% 8.18/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 8.18/1.50  --sup_passive_queues_freq               [8;1;4]
% 8.18/1.50  --demod_completeness_check              fast
% 8.18/1.50  --demod_use_ground                      true
% 8.18/1.50  --sup_to_prop_solver                    passive
% 8.18/1.50  --sup_prop_simpl_new                    true
% 8.18/1.50  --sup_prop_simpl_given                  true
% 8.18/1.50  --sup_fun_splitting                     true
% 8.18/1.50  --sup_smt_interval                      50000
% 8.18/1.50  
% 8.18/1.50  ------ Superposition Simplification Setup
% 8.18/1.50  
% 8.18/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 8.18/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 8.18/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 8.18/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 8.18/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 8.18/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 8.18/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 8.18/1.50  --sup_immed_triv                        [TrivRules]
% 8.18/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 8.18/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.18/1.50  --sup_immed_bw_main                     []
% 8.18/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 8.18/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 8.18/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.18/1.50  --sup_input_bw                          []
% 8.18/1.50  
% 8.18/1.50  ------ Combination Options
% 8.18/1.50  
% 8.18/1.50  --comb_res_mult                         3
% 8.18/1.50  --comb_sup_mult                         2
% 8.18/1.50  --comb_inst_mult                        10
% 8.18/1.50  
% 8.18/1.50  ------ Debug Options
% 8.18/1.50  
% 8.18/1.50  --dbg_backtrace                         false
% 8.18/1.50  --dbg_dump_prop_clauses                 false
% 8.18/1.50  --dbg_dump_prop_clauses_file            -
% 8.18/1.50  --dbg_out_stat                          false
% 8.18/1.50  ------ Parsing...
% 8.18/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 8.18/1.50  
% 8.18/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 8.18/1.50  
% 8.18/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 8.18/1.50  
% 8.18/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.18/1.50  ------ Proving...
% 8.18/1.50  ------ Problem Properties 
% 8.18/1.50  
% 8.18/1.50  
% 8.18/1.50  clauses                                 33
% 8.18/1.50  conjectures                             11
% 8.18/1.50  EPR                                     7
% 8.18/1.50  Horn                                    29
% 8.18/1.50  unary                                   16
% 8.18/1.50  binary                                  3
% 8.18/1.50  lits                                    121
% 8.18/1.50  lits eq                                 30
% 8.18/1.50  fd_pure                                 0
% 8.18/1.50  fd_pseudo                               0
% 8.18/1.50  fd_cond                                 4
% 8.18/1.50  fd_pseudo_cond                          1
% 8.18/1.50  AC symbols                              0
% 8.18/1.50  
% 8.18/1.50  ------ Schedule dynamic 5 is on 
% 8.18/1.50  
% 8.18/1.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 8.18/1.50  
% 8.18/1.50  
% 8.18/1.50  ------ 
% 8.18/1.50  Current options:
% 8.18/1.50  ------ 
% 8.18/1.50  
% 8.18/1.50  ------ Input Options
% 8.18/1.50  
% 8.18/1.50  --out_options                           all
% 8.18/1.50  --tptp_safe_out                         true
% 8.18/1.50  --problem_path                          ""
% 8.18/1.50  --include_path                          ""
% 8.18/1.50  --clausifier                            res/vclausify_rel
% 8.18/1.50  --clausifier_options                    ""
% 8.18/1.50  --stdin                                 false
% 8.18/1.50  --stats_out                             all
% 8.18/1.50  
% 8.18/1.50  ------ General Options
% 8.18/1.50  
% 8.18/1.50  --fof                                   false
% 8.18/1.50  --time_out_real                         305.
% 8.18/1.50  --time_out_virtual                      -1.
% 8.18/1.50  --symbol_type_check                     false
% 8.18/1.50  --clausify_out                          false
% 8.18/1.50  --sig_cnt_out                           false
% 8.18/1.50  --trig_cnt_out                          false
% 8.18/1.50  --trig_cnt_out_tolerance                1.
% 8.18/1.50  --trig_cnt_out_sk_spl                   false
% 8.18/1.50  --abstr_cl_out                          false
% 8.18/1.50  
% 8.18/1.50  ------ Global Options
% 8.18/1.50  
% 8.18/1.50  --schedule                              default
% 8.18/1.50  --add_important_lit                     false
% 8.18/1.50  --prop_solver_per_cl                    1000
% 8.18/1.50  --min_unsat_core                        false
% 8.18/1.50  --soft_assumptions                      false
% 8.18/1.50  --soft_lemma_size                       3
% 8.18/1.50  --prop_impl_unit_size                   0
% 8.18/1.50  --prop_impl_unit                        []
% 8.18/1.50  --share_sel_clauses                     true
% 8.18/1.50  --reset_solvers                         false
% 8.18/1.50  --bc_imp_inh                            [conj_cone]
% 8.18/1.50  --conj_cone_tolerance                   3.
% 8.18/1.50  --extra_neg_conj                        none
% 8.18/1.50  --large_theory_mode                     true
% 8.18/1.50  --prolific_symb_bound                   200
% 8.18/1.50  --lt_threshold                          2000
% 8.18/1.50  --clause_weak_htbl                      true
% 8.18/1.50  --gc_record_bc_elim                     false
% 8.18/1.50  
% 8.18/1.50  ------ Preprocessing Options
% 8.18/1.50  
% 8.18/1.50  --preprocessing_flag                    true
% 8.18/1.50  --time_out_prep_mult                    0.1
% 8.18/1.50  --splitting_mode                        input
% 8.18/1.50  --splitting_grd                         true
% 8.18/1.50  --splitting_cvd                         false
% 8.18/1.50  --splitting_cvd_svl                     false
% 8.18/1.50  --splitting_nvd                         32
% 8.18/1.50  --sub_typing                            true
% 8.18/1.50  --prep_gs_sim                           true
% 8.18/1.50  --prep_unflatten                        true
% 8.18/1.50  --prep_res_sim                          true
% 8.18/1.50  --prep_upred                            true
% 8.18/1.50  --prep_sem_filter                       exhaustive
% 8.18/1.50  --prep_sem_filter_out                   false
% 8.18/1.50  --pred_elim                             true
% 8.18/1.50  --res_sim_input                         true
% 8.18/1.50  --eq_ax_congr_red                       true
% 8.18/1.50  --pure_diseq_elim                       true
% 8.18/1.50  --brand_transform                       false
% 8.18/1.50  --non_eq_to_eq                          false
% 8.18/1.50  --prep_def_merge                        true
% 8.18/1.50  --prep_def_merge_prop_impl              false
% 8.18/1.50  --prep_def_merge_mbd                    true
% 8.18/1.50  --prep_def_merge_tr_red                 false
% 8.18/1.50  --prep_def_merge_tr_cl                  false
% 8.18/1.50  --smt_preprocessing                     true
% 8.18/1.50  --smt_ac_axioms                         fast
% 8.18/1.50  --preprocessed_out                      false
% 8.18/1.50  --preprocessed_stats                    false
% 8.18/1.50  
% 8.18/1.50  ------ Abstraction refinement Options
% 8.18/1.50  
% 8.18/1.50  --abstr_ref                             []
% 8.18/1.50  --abstr_ref_prep                        false
% 8.18/1.50  --abstr_ref_until_sat                   false
% 8.18/1.50  --abstr_ref_sig_restrict                funpre
% 8.18/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 8.18/1.50  --abstr_ref_under                       []
% 8.18/1.50  
% 8.18/1.50  ------ SAT Options
% 8.18/1.50  
% 8.18/1.50  --sat_mode                              false
% 8.18/1.50  --sat_fm_restart_options                ""
% 8.18/1.50  --sat_gr_def                            false
% 8.18/1.50  --sat_epr_types                         true
% 8.18/1.50  --sat_non_cyclic_types                  false
% 8.18/1.50  --sat_finite_models                     false
% 8.18/1.50  --sat_fm_lemmas                         false
% 8.18/1.50  --sat_fm_prep                           false
% 8.18/1.50  --sat_fm_uc_incr                        true
% 8.18/1.50  --sat_out_model                         small
% 8.18/1.50  --sat_out_clauses                       false
% 8.18/1.50  
% 8.18/1.50  ------ QBF Options
% 8.18/1.50  
% 8.18/1.50  --qbf_mode                              false
% 8.18/1.50  --qbf_elim_univ                         false
% 8.18/1.50  --qbf_dom_inst                          none
% 8.18/1.50  --qbf_dom_pre_inst                      false
% 8.18/1.50  --qbf_sk_in                             false
% 8.18/1.50  --qbf_pred_elim                         true
% 8.18/1.50  --qbf_split                             512
% 8.18/1.50  
% 8.18/1.50  ------ BMC1 Options
% 8.18/1.50  
% 8.18/1.50  --bmc1_incremental                      false
% 8.18/1.50  --bmc1_axioms                           reachable_all
% 8.18/1.50  --bmc1_min_bound                        0
% 8.18/1.50  --bmc1_max_bound                        -1
% 8.18/1.50  --bmc1_max_bound_default                -1
% 8.18/1.50  --bmc1_symbol_reachability              true
% 8.18/1.50  --bmc1_property_lemmas                  false
% 8.18/1.50  --bmc1_k_induction                      false
% 8.18/1.50  --bmc1_non_equiv_states                 false
% 8.18/1.50  --bmc1_deadlock                         false
% 8.18/1.50  --bmc1_ucm                              false
% 8.18/1.50  --bmc1_add_unsat_core                   none
% 8.18/1.50  --bmc1_unsat_core_children              false
% 8.18/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 8.18/1.50  --bmc1_out_stat                         full
% 8.18/1.50  --bmc1_ground_init                      false
% 8.18/1.50  --bmc1_pre_inst_next_state              false
% 8.18/1.50  --bmc1_pre_inst_state                   false
% 8.18/1.50  --bmc1_pre_inst_reach_state             false
% 8.18/1.50  --bmc1_out_unsat_core                   false
% 8.18/1.50  --bmc1_aig_witness_out                  false
% 8.18/1.50  --bmc1_verbose                          false
% 8.18/1.50  --bmc1_dump_clauses_tptp                false
% 8.18/1.50  --bmc1_dump_unsat_core_tptp             false
% 8.18/1.50  --bmc1_dump_file                        -
% 8.18/1.50  --bmc1_ucm_expand_uc_limit              128
% 8.18/1.50  --bmc1_ucm_n_expand_iterations          6
% 8.18/1.50  --bmc1_ucm_extend_mode                  1
% 8.18/1.50  --bmc1_ucm_init_mode                    2
% 8.18/1.50  --bmc1_ucm_cone_mode                    none
% 8.18/1.50  --bmc1_ucm_reduced_relation_type        0
% 8.18/1.50  --bmc1_ucm_relax_model                  4
% 8.18/1.50  --bmc1_ucm_full_tr_after_sat            true
% 8.18/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 8.18/1.50  --bmc1_ucm_layered_model                none
% 8.18/1.50  --bmc1_ucm_max_lemma_size               10
% 8.18/1.50  
% 8.18/1.50  ------ AIG Options
% 8.18/1.50  
% 8.18/1.50  --aig_mode                              false
% 8.18/1.50  
% 8.18/1.50  ------ Instantiation Options
% 8.18/1.50  
% 8.18/1.50  --instantiation_flag                    true
% 8.18/1.50  --inst_sos_flag                         true
% 8.18/1.50  --inst_sos_phase                        true
% 8.18/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 8.18/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 8.18/1.50  --inst_lit_sel_side                     none
% 8.18/1.50  --inst_solver_per_active                1400
% 8.18/1.50  --inst_solver_calls_frac                1.
% 8.18/1.50  --inst_passive_queue_type               priority_queues
% 8.18/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 8.18/1.50  --inst_passive_queues_freq              [25;2]
% 8.18/1.50  --inst_dismatching                      true
% 8.18/1.50  --inst_eager_unprocessed_to_passive     true
% 8.18/1.50  --inst_prop_sim_given                   true
% 8.18/1.50  --inst_prop_sim_new                     false
% 8.18/1.50  --inst_subs_new                         false
% 8.18/1.50  --inst_eq_res_simp                      false
% 8.18/1.50  --inst_subs_given                       false
% 8.18/1.50  --inst_orphan_elimination               true
% 8.18/1.50  --inst_learning_loop_flag               true
% 8.18/1.50  --inst_learning_start                   3000
% 8.18/1.50  --inst_learning_factor                  2
% 8.18/1.50  --inst_start_prop_sim_after_learn       3
% 8.18/1.50  --inst_sel_renew                        solver
% 8.18/1.50  --inst_lit_activity_flag                true
% 8.18/1.50  --inst_restr_to_given                   false
% 8.18/1.50  --inst_activity_threshold               500
% 8.18/1.50  --inst_out_proof                        true
% 8.18/1.50  
% 8.18/1.50  ------ Resolution Options
% 8.18/1.50  
% 8.18/1.50  --resolution_flag                       false
% 8.18/1.50  --res_lit_sel                           adaptive
% 8.18/1.50  --res_lit_sel_side                      none
% 8.18/1.50  --res_ordering                          kbo
% 8.18/1.50  --res_to_prop_solver                    active
% 8.18/1.50  --res_prop_simpl_new                    false
% 8.18/1.50  --res_prop_simpl_given                  true
% 8.18/1.50  --res_passive_queue_type                priority_queues
% 8.18/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 8.18/1.50  --res_passive_queues_freq               [15;5]
% 8.18/1.50  --res_forward_subs                      full
% 8.18/1.50  --res_backward_subs                     full
% 8.18/1.50  --res_forward_subs_resolution           true
% 8.18/1.50  --res_backward_subs_resolution          true
% 8.18/1.50  --res_orphan_elimination                true
% 8.18/1.50  --res_time_limit                        2.
% 8.18/1.50  --res_out_proof                         true
% 8.18/1.50  
% 8.18/1.50  ------ Superposition Options
% 8.18/1.50  
% 8.18/1.50  --superposition_flag                    true
% 8.18/1.50  --sup_passive_queue_type                priority_queues
% 8.18/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 8.18/1.50  --sup_passive_queues_freq               [8;1;4]
% 8.18/1.50  --demod_completeness_check              fast
% 8.18/1.50  --demod_use_ground                      true
% 8.18/1.50  --sup_to_prop_solver                    passive
% 8.18/1.50  --sup_prop_simpl_new                    true
% 8.18/1.50  --sup_prop_simpl_given                  true
% 8.18/1.50  --sup_fun_splitting                     true
% 8.18/1.50  --sup_smt_interval                      50000
% 8.18/1.50  
% 8.18/1.50  ------ Superposition Simplification Setup
% 8.18/1.50  
% 8.18/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 8.18/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 8.18/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 8.18/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 8.18/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 8.18/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 8.18/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 8.18/1.50  --sup_immed_triv                        [TrivRules]
% 8.18/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 8.18/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.18/1.50  --sup_immed_bw_main                     []
% 8.18/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 8.18/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 8.18/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.18/1.50  --sup_input_bw                          []
% 8.18/1.50  
% 8.18/1.50  ------ Combination Options
% 8.18/1.50  
% 8.18/1.50  --comb_res_mult                         3
% 8.18/1.50  --comb_sup_mult                         2
% 8.18/1.50  --comb_inst_mult                        10
% 8.18/1.50  
% 8.18/1.50  ------ Debug Options
% 8.18/1.50  
% 8.18/1.50  --dbg_backtrace                         false
% 8.18/1.50  --dbg_dump_prop_clauses                 false
% 8.18/1.50  --dbg_dump_prop_clauses_file            -
% 8.18/1.50  --dbg_out_stat                          false
% 8.18/1.50  
% 8.18/1.50  
% 8.18/1.50  
% 8.18/1.50  
% 8.18/1.50  ------ Proving...
% 8.18/1.50  
% 8.18/1.50  
% 8.18/1.50  % SZS status Theorem for theBenchmark.p
% 8.18/1.50  
% 8.18/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 8.18/1.50  
% 8.18/1.50  fof(f7,axiom,(
% 8.18/1.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 8.18/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.18/1.50  
% 8.18/1.50  fof(f23,plain,(
% 8.18/1.50    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 8.18/1.50    inference(ennf_transformation,[],[f7])).
% 8.18/1.50  
% 8.18/1.50  fof(f24,plain,(
% 8.18/1.50    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.18/1.50    inference(flattening,[],[f23])).
% 8.18/1.50  
% 8.18/1.50  fof(f37,plain,(
% 8.18/1.50    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.18/1.50    inference(nnf_transformation,[],[f24])).
% 8.18/1.50  
% 8.18/1.50  fof(f50,plain,(
% 8.18/1.50    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 8.18/1.50    inference(cnf_transformation,[],[f37])).
% 8.18/1.50  
% 8.18/1.50  fof(f15,conjecture,(
% 8.18/1.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 8.18/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.18/1.50  
% 8.18/1.50  fof(f16,negated_conjecture,(
% 8.18/1.50    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 8.18/1.50    inference(negated_conjecture,[],[f15])).
% 8.18/1.50  
% 8.18/1.50  fof(f35,plain,(
% 8.18/1.50    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 8.18/1.50    inference(ennf_transformation,[],[f16])).
% 8.18/1.50  
% 8.18/1.50  fof(f36,plain,(
% 8.18/1.50    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 8.18/1.50    inference(flattening,[],[f35])).
% 8.18/1.50  
% 8.18/1.50  fof(f39,plain,(
% 8.18/1.50    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 8.18/1.50    introduced(choice_axiom,[])).
% 8.18/1.50  
% 8.18/1.50  fof(f38,plain,(
% 8.18/1.50    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 8.18/1.50    introduced(choice_axiom,[])).
% 8.18/1.50  
% 8.18/1.50  fof(f40,plain,(
% 8.18/1.50    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 8.18/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f36,f39,f38])).
% 8.18/1.50  
% 8.18/1.50  fof(f71,plain,(
% 8.18/1.50    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 8.18/1.50    inference(cnf_transformation,[],[f40])).
% 8.18/1.50  
% 8.18/1.50  fof(f8,axiom,(
% 8.18/1.50    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 8.18/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.18/1.50  
% 8.18/1.50  fof(f52,plain,(
% 8.18/1.50    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 8.18/1.50    inference(cnf_transformation,[],[f8])).
% 8.18/1.50  
% 8.18/1.50  fof(f11,axiom,(
% 8.18/1.50    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 8.18/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.18/1.50  
% 8.18/1.50  fof(f56,plain,(
% 8.18/1.50    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 8.18/1.50    inference(cnf_transformation,[],[f11])).
% 8.18/1.50  
% 8.18/1.50  fof(f83,plain,(
% 8.18/1.50    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 8.18/1.50    inference(definition_unfolding,[],[f52,f56])).
% 8.18/1.50  
% 8.18/1.50  fof(f64,plain,(
% 8.18/1.50    v1_funct_1(sK2)),
% 8.18/1.50    inference(cnf_transformation,[],[f40])).
% 8.18/1.50  
% 8.18/1.50  fof(f66,plain,(
% 8.18/1.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 8.18/1.50    inference(cnf_transformation,[],[f40])).
% 8.18/1.50  
% 8.18/1.50  fof(f67,plain,(
% 8.18/1.50    v1_funct_1(sK3)),
% 8.18/1.50    inference(cnf_transformation,[],[f40])).
% 8.18/1.50  
% 8.18/1.50  fof(f69,plain,(
% 8.18/1.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 8.18/1.50    inference(cnf_transformation,[],[f40])).
% 8.18/1.50  
% 8.18/1.50  fof(f9,axiom,(
% 8.18/1.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 8.18/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.18/1.50  
% 8.18/1.50  fof(f25,plain,(
% 8.18/1.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 8.18/1.50    inference(ennf_transformation,[],[f9])).
% 8.18/1.50  
% 8.18/1.50  fof(f26,plain,(
% 8.18/1.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 8.18/1.50    inference(flattening,[],[f25])).
% 8.18/1.50  
% 8.18/1.50  fof(f54,plain,(
% 8.18/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 8.18/1.50    inference(cnf_transformation,[],[f26])).
% 8.18/1.50  
% 8.18/1.50  fof(f70,plain,(
% 8.18/1.50    k2_relset_1(sK0,sK1,sK2) = sK1),
% 8.18/1.50    inference(cnf_transformation,[],[f40])).
% 8.18/1.50  
% 8.18/1.50  fof(f13,axiom,(
% 8.18/1.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 8.18/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.18/1.50  
% 8.18/1.50  fof(f31,plain,(
% 8.18/1.50    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 8.18/1.50    inference(ennf_transformation,[],[f13])).
% 8.18/1.50  
% 8.18/1.50  fof(f32,plain,(
% 8.18/1.50    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 8.18/1.50    inference(flattening,[],[f31])).
% 8.18/1.50  
% 8.18/1.50  fof(f60,plain,(
% 8.18/1.50    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X4) | k1_xboole_0 = X2 | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 8.18/1.50    inference(cnf_transformation,[],[f32])).
% 8.18/1.50  
% 8.18/1.50  fof(f65,plain,(
% 8.18/1.50    v1_funct_2(sK2,sK0,sK1)),
% 8.18/1.50    inference(cnf_transformation,[],[f40])).
% 8.18/1.50  
% 8.18/1.50  fof(f68,plain,(
% 8.18/1.50    v1_funct_2(sK3,sK1,sK0)),
% 8.18/1.50    inference(cnf_transformation,[],[f40])).
% 8.18/1.50  
% 8.18/1.50  fof(f73,plain,(
% 8.18/1.50    k1_xboole_0 != sK0),
% 8.18/1.50    inference(cnf_transformation,[],[f40])).
% 8.18/1.50  
% 8.18/1.50  fof(f2,axiom,(
% 8.18/1.50    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 8.18/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.18/1.50  
% 8.18/1.50  fof(f44,plain,(
% 8.18/1.50    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 8.18/1.50    inference(cnf_transformation,[],[f2])).
% 8.18/1.50  
% 8.18/1.50  fof(f78,plain,(
% 8.18/1.50    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 8.18/1.50    inference(definition_unfolding,[],[f44,f56])).
% 8.18/1.50  
% 8.18/1.50  fof(f3,axiom,(
% 8.18/1.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)))))),
% 8.18/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.18/1.50  
% 8.18/1.50  fof(f17,plain,(
% 8.18/1.50    ! [X0] : (((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 8.18/1.50    inference(ennf_transformation,[],[f3])).
% 8.18/1.50  
% 8.18/1.50  fof(f18,plain,(
% 8.18/1.50    ! [X0] : ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 8.18/1.50    inference(flattening,[],[f17])).
% 8.18/1.50  
% 8.18/1.50  fof(f45,plain,(
% 8.18/1.50    ( ! [X0] : (k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 8.18/1.50    inference(cnf_transformation,[],[f18])).
% 8.18/1.50  
% 8.18/1.50  fof(f81,plain,(
% 8.18/1.50    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 8.18/1.50    inference(definition_unfolding,[],[f45,f56])).
% 8.18/1.50  
% 8.18/1.50  fof(f5,axiom,(
% 8.18/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 8.18/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.18/1.50  
% 8.18/1.50  fof(f21,plain,(
% 8.18/1.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.18/1.50    inference(ennf_transformation,[],[f5])).
% 8.18/1.50  
% 8.18/1.50  fof(f48,plain,(
% 8.18/1.50    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 8.18/1.50    inference(cnf_transformation,[],[f21])).
% 8.18/1.50  
% 8.18/1.50  fof(f4,axiom,(
% 8.18/1.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 8.18/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.18/1.50  
% 8.18/1.50  fof(f19,plain,(
% 8.18/1.50    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 8.18/1.50    inference(ennf_transformation,[],[f4])).
% 8.18/1.50  
% 8.18/1.50  fof(f20,plain,(
% 8.18/1.50    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 8.18/1.50    inference(flattening,[],[f19])).
% 8.18/1.50  
% 8.18/1.50  fof(f47,plain,(
% 8.18/1.50    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 8.18/1.50    inference(cnf_transformation,[],[f20])).
% 8.18/1.50  
% 8.18/1.50  fof(f82,plain,(
% 8.18/1.50    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 8.18/1.50    inference(definition_unfolding,[],[f47,f56])).
% 8.18/1.50  
% 8.18/1.50  fof(f6,axiom,(
% 8.18/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 8.18/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.18/1.50  
% 8.18/1.50  fof(f22,plain,(
% 8.18/1.50    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.18/1.50    inference(ennf_transformation,[],[f6])).
% 8.18/1.50  
% 8.18/1.50  fof(f49,plain,(
% 8.18/1.50    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 8.18/1.50    inference(cnf_transformation,[],[f22])).
% 8.18/1.50  
% 8.18/1.50  fof(f12,axiom,(
% 8.18/1.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 8.18/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.18/1.50  
% 8.18/1.50  fof(f29,plain,(
% 8.18/1.50    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 8.18/1.50    inference(ennf_transformation,[],[f12])).
% 8.18/1.50  
% 8.18/1.50  fof(f30,plain,(
% 8.18/1.50    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 8.18/1.50    inference(flattening,[],[f29])).
% 8.18/1.50  
% 8.18/1.50  fof(f57,plain,(
% 8.18/1.50    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 8.18/1.50    inference(cnf_transformation,[],[f30])).
% 8.18/1.50  
% 8.18/1.50  fof(f72,plain,(
% 8.18/1.50    v2_funct_1(sK2)),
% 8.18/1.50    inference(cnf_transformation,[],[f40])).
% 8.18/1.50  
% 8.18/1.50  fof(f10,axiom,(
% 8.18/1.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 8.18/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.18/1.50  
% 8.18/1.50  fof(f27,plain,(
% 8.18/1.50    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 8.18/1.50    inference(ennf_transformation,[],[f10])).
% 8.18/1.50  
% 8.18/1.50  fof(f28,plain,(
% 8.18/1.50    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 8.18/1.50    inference(flattening,[],[f27])).
% 8.18/1.50  
% 8.18/1.50  fof(f55,plain,(
% 8.18/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 8.18/1.50    inference(cnf_transformation,[],[f28])).
% 8.18/1.50  
% 8.18/1.50  fof(f14,axiom,(
% 8.18/1.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 8.18/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.18/1.50  
% 8.18/1.50  fof(f33,plain,(
% 8.18/1.50    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 8.18/1.50    inference(ennf_transformation,[],[f14])).
% 8.18/1.50  
% 8.18/1.50  fof(f34,plain,(
% 8.18/1.50    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 8.18/1.50    inference(flattening,[],[f33])).
% 8.18/1.50  
% 8.18/1.50  fof(f62,plain,(
% 8.18/1.50    ( ! [X2,X0,X1] : (k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 8.18/1.50    inference(cnf_transformation,[],[f34])).
% 8.18/1.50  
% 8.18/1.50  fof(f1,axiom,(
% 8.18/1.50    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 8.18/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.18/1.50  
% 8.18/1.50  fof(f42,plain,(
% 8.18/1.50    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 8.18/1.50    inference(cnf_transformation,[],[f1])).
% 8.18/1.50  
% 8.18/1.50  fof(f76,plain,(
% 8.18/1.50    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 8.18/1.50    inference(definition_unfolding,[],[f42,f56])).
% 8.18/1.50  
% 8.18/1.50  fof(f74,plain,(
% 8.18/1.50    k1_xboole_0 != sK1),
% 8.18/1.50    inference(cnf_transformation,[],[f40])).
% 8.18/1.50  
% 8.18/1.50  fof(f75,plain,(
% 8.18/1.50    k2_funct_1(sK2) != sK3),
% 8.18/1.50    inference(cnf_transformation,[],[f40])).
% 8.18/1.50  
% 8.18/1.50  cnf(c_10,plain,
% 8.18/1.50      ( ~ r2_relset_1(X0,X1,X2,X3)
% 8.18/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 8.18/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 8.18/1.50      | X3 = X2 ),
% 8.18/1.50      inference(cnf_transformation,[],[f50]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_26,negated_conjecture,
% 8.18/1.50      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 8.18/1.50      inference(cnf_transformation,[],[f71]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_354,plain,
% 8.18/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.18/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.18/1.50      | X3 = X0
% 8.18/1.50      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 8.18/1.50      | k6_partfun1(sK0) != X3
% 8.18/1.50      | sK0 != X2
% 8.18/1.50      | sK0 != X1 ),
% 8.18/1.50      inference(resolution_lifted,[status(thm)],[c_10,c_26]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_355,plain,
% 8.18/1.50      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 8.18/1.50      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 8.18/1.50      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 8.18/1.50      inference(unflattening,[status(thm)],[c_354]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_11,plain,
% 8.18/1.50      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 8.18/1.50      inference(cnf_transformation,[],[f83]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_363,plain,
% 8.18/1.50      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 8.18/1.50      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 8.18/1.50      inference(forward_subsumption_resolution,
% 8.18/1.50                [status(thm)],
% 8.18/1.50                [c_355,c_11]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_1067,plain,
% 8.18/1.50      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 8.18/1.50      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 8.18/1.50      inference(predicate_to_equality,[status(thm)],[c_363]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_33,negated_conjecture,
% 8.18/1.50      ( v1_funct_1(sK2) ),
% 8.18/1.50      inference(cnf_transformation,[],[f64]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_31,negated_conjecture,
% 8.18/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 8.18/1.50      inference(cnf_transformation,[],[f66]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_30,negated_conjecture,
% 8.18/1.50      ( v1_funct_1(sK3) ),
% 8.18/1.50      inference(cnf_transformation,[],[f67]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_28,negated_conjecture,
% 8.18/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 8.18/1.50      inference(cnf_transformation,[],[f69]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_12,plain,
% 8.18/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.18/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 8.18/1.50      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 8.18/1.50      | ~ v1_funct_1(X0)
% 8.18/1.50      | ~ v1_funct_1(X3) ),
% 8.18/1.50      inference(cnf_transformation,[],[f54]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_1174,plain,
% 8.18/1.50      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 8.18/1.50      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 8.18/1.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 8.18/1.50      | ~ v1_funct_1(sK3)
% 8.18/1.50      | ~ v1_funct_1(sK2) ),
% 8.18/1.50      inference(instantiation,[status(thm)],[c_12]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_1758,plain,
% 8.18/1.50      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 8.18/1.50      inference(global_propositional_subsumption,
% 8.18/1.50                [status(thm)],
% 8.18/1.50                [c_1067,c_33,c_31,c_30,c_28,c_363,c_1174]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_27,negated_conjecture,
% 8.18/1.50      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 8.18/1.50      inference(cnf_transformation,[],[f70]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_17,plain,
% 8.18/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 8.18/1.50      | ~ v1_funct_2(X3,X4,X1)
% 8.18/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 8.18/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.18/1.50      | ~ v1_funct_1(X0)
% 8.18/1.50      | ~ v1_funct_1(X3)
% 8.18/1.50      | v2_funct_1(X0)
% 8.18/1.50      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 8.18/1.50      | k2_relset_1(X4,X1,X3) != X1
% 8.18/1.50      | k1_xboole_0 = X2 ),
% 8.18/1.50      inference(cnf_transformation,[],[f60]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_1080,plain,
% 8.18/1.50      ( k2_relset_1(X0,X1,X2) != X1
% 8.18/1.50      | k1_xboole_0 = X3
% 8.18/1.50      | v1_funct_2(X4,X1,X3) != iProver_top
% 8.18/1.50      | v1_funct_2(X2,X0,X1) != iProver_top
% 8.18/1.50      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
% 8.18/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 8.18/1.50      | v1_funct_1(X4) != iProver_top
% 8.18/1.50      | v1_funct_1(X2) != iProver_top
% 8.18/1.50      | v2_funct_1(X4) = iProver_top
% 8.18/1.50      | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top ),
% 8.18/1.50      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_4697,plain,
% 8.18/1.50      ( k1_xboole_0 = X0
% 8.18/1.50      | v1_funct_2(X1,sK1,X0) != iProver_top
% 8.18/1.50      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 8.18/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 8.18/1.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 8.18/1.50      | v1_funct_1(X1) != iProver_top
% 8.18/1.50      | v1_funct_1(sK2) != iProver_top
% 8.18/1.50      | v2_funct_1(X1) = iProver_top
% 8.18/1.50      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
% 8.18/1.50      inference(superposition,[status(thm)],[c_27,c_1080]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_34,plain,
% 8.18/1.50      ( v1_funct_1(sK2) = iProver_top ),
% 8.18/1.50      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_32,negated_conjecture,
% 8.18/1.50      ( v1_funct_2(sK2,sK0,sK1) ),
% 8.18/1.50      inference(cnf_transformation,[],[f65]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_35,plain,
% 8.18/1.50      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 8.18/1.50      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_36,plain,
% 8.18/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 8.18/1.50      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_4704,plain,
% 8.18/1.50      ( v1_funct_1(X1) != iProver_top
% 8.18/1.50      | v1_funct_2(X1,sK1,X0) != iProver_top
% 8.18/1.50      | k1_xboole_0 = X0
% 8.18/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 8.18/1.50      | v2_funct_1(X1) = iProver_top
% 8.18/1.50      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
% 8.18/1.50      inference(global_propositional_subsumption,
% 8.18/1.50                [status(thm)],
% 8.18/1.50                [c_4697,c_34,c_35,c_36]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_4705,plain,
% 8.18/1.50      ( k1_xboole_0 = X0
% 8.18/1.50      | v1_funct_2(X1,sK1,X0) != iProver_top
% 8.18/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 8.18/1.50      | v1_funct_1(X1) != iProver_top
% 8.18/1.50      | v2_funct_1(X1) = iProver_top
% 8.18/1.50      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
% 8.18/1.50      inference(renaming,[status(thm)],[c_4704]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_4708,plain,
% 8.18/1.50      ( sK0 = k1_xboole_0
% 8.18/1.50      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 8.18/1.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 8.18/1.50      | v1_funct_1(sK3) != iProver_top
% 8.18/1.50      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 8.18/1.50      | v2_funct_1(sK3) = iProver_top ),
% 8.18/1.50      inference(superposition,[status(thm)],[c_1758,c_4705]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_37,plain,
% 8.18/1.50      ( v1_funct_1(sK3) = iProver_top ),
% 8.18/1.50      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_29,negated_conjecture,
% 8.18/1.50      ( v1_funct_2(sK3,sK1,sK0) ),
% 8.18/1.50      inference(cnf_transformation,[],[f68]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_38,plain,
% 8.18/1.50      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 8.18/1.50      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_39,plain,
% 8.18/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 8.18/1.50      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_24,negated_conjecture,
% 8.18/1.50      ( k1_xboole_0 != sK0 ),
% 8.18/1.50      inference(cnf_transformation,[],[f73]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_608,plain,( X0 = X0 ),theory(equality) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_639,plain,
% 8.18/1.50      ( k1_xboole_0 = k1_xboole_0 ),
% 8.18/1.50      inference(instantiation,[status(thm)],[c_608]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_609,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_1172,plain,
% 8.18/1.50      ( sK0 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK0 ),
% 8.18/1.50      inference(instantiation,[status(thm)],[c_609]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_1173,plain,
% 8.18/1.50      ( sK0 != k1_xboole_0
% 8.18/1.50      | k1_xboole_0 = sK0
% 8.18/1.50      | k1_xboole_0 != k1_xboole_0 ),
% 8.18/1.50      inference(instantiation,[status(thm)],[c_1172]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_2,plain,
% 8.18/1.50      ( v2_funct_1(k6_partfun1(X0)) ),
% 8.18/1.50      inference(cnf_transformation,[],[f78]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_4729,plain,
% 8.18/1.50      ( v2_funct_1(k6_partfun1(sK0)) ),
% 8.18/1.50      inference(instantiation,[status(thm)],[c_2]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_4730,plain,
% 8.18/1.50      ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
% 8.18/1.50      inference(predicate_to_equality,[status(thm)],[c_4729]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_4967,plain,
% 8.18/1.50      ( v2_funct_1(sK3) = iProver_top ),
% 8.18/1.50      inference(global_propositional_subsumption,
% 8.18/1.50                [status(thm)],
% 8.18/1.50                [c_4708,c_37,c_38,c_39,c_24,c_639,c_1173,c_4730]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_1072,plain,
% 8.18/1.50      ( v1_funct_1(sK3) = iProver_top ),
% 8.18/1.50      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_5,plain,
% 8.18/1.50      ( ~ v1_funct_1(X0)
% 8.18/1.50      | ~ v1_relat_1(X0)
% 8.18/1.50      | ~ v2_funct_1(X0)
% 8.18/1.50      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
% 8.18/1.50      inference(cnf_transformation,[],[f81]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_1089,plain,
% 8.18/1.50      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
% 8.18/1.50      | v1_funct_1(X0) != iProver_top
% 8.18/1.50      | v1_relat_1(X0) != iProver_top
% 8.18/1.50      | v2_funct_1(X0) != iProver_top ),
% 8.18/1.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_2031,plain,
% 8.18/1.50      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
% 8.18/1.50      | v1_relat_1(sK3) != iProver_top
% 8.18/1.50      | v2_funct_1(sK3) != iProver_top ),
% 8.18/1.50      inference(superposition,[status(thm)],[c_1072,c_1089]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_7,plain,
% 8.18/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.18/1.50      | v1_relat_1(X0) ),
% 8.18/1.50      inference(cnf_transformation,[],[f48]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_1214,plain,
% 8.18/1.50      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 8.18/1.50      | v1_relat_1(sK3) ),
% 8.18/1.50      inference(instantiation,[status(thm)],[c_7]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_1573,plain,
% 8.18/1.50      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 8.18/1.50      | v1_relat_1(sK3) ),
% 8.18/1.50      inference(instantiation,[status(thm)],[c_1214]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_1574,plain,
% 8.18/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 8.18/1.50      | v1_relat_1(sK3) = iProver_top ),
% 8.18/1.50      inference(predicate_to_equality,[status(thm)],[c_1573]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_2233,plain,
% 8.18/1.50      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
% 8.18/1.50      | v2_funct_1(sK3) != iProver_top ),
% 8.18/1.50      inference(global_propositional_subsumption,
% 8.18/1.50                [status(thm)],
% 8.18/1.50                [c_2031,c_39,c_1574]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_4972,plain,
% 8.18/1.50      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3)) ),
% 8.18/1.50      inference(superposition,[status(thm)],[c_4967,c_2233]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_6,plain,
% 8.18/1.50      ( ~ v1_funct_1(X0)
% 8.18/1.50      | ~ v1_funct_1(X1)
% 8.18/1.50      | ~ v1_relat_1(X0)
% 8.18/1.50      | ~ v1_relat_1(X1)
% 8.18/1.50      | ~ v2_funct_1(X0)
% 8.18/1.50      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
% 8.18/1.50      | k2_funct_1(X0) = X1
% 8.18/1.50      | k1_relat_1(X0) != k2_relat_1(X1) ),
% 8.18/1.50      inference(cnf_transformation,[],[f82]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_1088,plain,
% 8.18/1.50      ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 8.18/1.50      | k2_funct_1(X1) = X0
% 8.18/1.50      | k1_relat_1(X1) != k2_relat_1(X0)
% 8.18/1.50      | v1_funct_1(X1) != iProver_top
% 8.18/1.50      | v1_funct_1(X0) != iProver_top
% 8.18/1.50      | v1_relat_1(X1) != iProver_top
% 8.18/1.50      | v1_relat_1(X0) != iProver_top
% 8.18/1.50      | v2_funct_1(X1) != iProver_top ),
% 8.18/1.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_5019,plain,
% 8.18/1.50      ( k2_funct_1(k2_funct_1(sK3)) = sK3
% 8.18/1.50      | k1_relat_1(k2_funct_1(sK3)) != k2_relat_1(sK3)
% 8.18/1.50      | k6_partfun1(k2_relat_1(k2_funct_1(sK3))) != k6_partfun1(k1_relat_1(sK3))
% 8.18/1.50      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 8.18/1.50      | v1_funct_1(sK3) != iProver_top
% 8.18/1.50      | v1_relat_1(k2_funct_1(sK3)) != iProver_top
% 8.18/1.50      | v1_relat_1(sK3) != iProver_top
% 8.18/1.50      | v2_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 8.18/1.50      inference(superposition,[status(thm)],[c_4972,c_1088]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_1074,plain,
% 8.18/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 8.18/1.50      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_8,plain,
% 8.18/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.18/1.50      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 8.18/1.50      inference(cnf_transformation,[],[f49]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_1086,plain,
% 8.18/1.50      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 8.18/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 8.18/1.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_1990,plain,
% 8.18/1.50      ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 8.18/1.50      inference(superposition,[status(thm)],[c_1074,c_1086]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_15,plain,
% 8.18/1.50      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 8.18/1.50      | ~ v1_funct_2(X2,X0,X1)
% 8.18/1.50      | ~ v1_funct_2(X3,X1,X0)
% 8.18/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 8.18/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 8.18/1.50      | ~ v1_funct_1(X2)
% 8.18/1.50      | ~ v1_funct_1(X3)
% 8.18/1.50      | k2_relset_1(X1,X0,X3) = X0 ),
% 8.18/1.50      inference(cnf_transformation,[],[f57]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_367,plain,
% 8.18/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 8.18/1.50      | ~ v1_funct_2(X3,X2,X1)
% 8.18/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 8.18/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.18/1.50      | ~ v1_funct_1(X0)
% 8.18/1.50      | ~ v1_funct_1(X3)
% 8.18/1.50      | k1_partfun1(X2,X1,X1,X2,X3,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 8.18/1.50      | k2_relset_1(X1,X2,X0) = X2
% 8.18/1.50      | k6_partfun1(X2) != k6_partfun1(sK0)
% 8.18/1.50      | sK0 != X2 ),
% 8.18/1.50      inference(resolution_lifted,[status(thm)],[c_15,c_26]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_368,plain,
% 8.18/1.50      ( ~ v1_funct_2(X0,X1,sK0)
% 8.18/1.50      | ~ v1_funct_2(X2,sK0,X1)
% 8.18/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 8.18/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 8.18/1.50      | ~ v1_funct_1(X0)
% 8.18/1.50      | ~ v1_funct_1(X2)
% 8.18/1.50      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 8.18/1.50      | k2_relset_1(X1,sK0,X0) = sK0
% 8.18/1.50      | k6_partfun1(sK0) != k6_partfun1(sK0) ),
% 8.18/1.50      inference(unflattening,[status(thm)],[c_367]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_449,plain,
% 8.18/1.50      ( ~ v1_funct_2(X0,X1,sK0)
% 8.18/1.50      | ~ v1_funct_2(X2,sK0,X1)
% 8.18/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 8.18/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 8.18/1.50      | ~ v1_funct_1(X0)
% 8.18/1.50      | ~ v1_funct_1(X2)
% 8.18/1.50      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 8.18/1.50      | k2_relset_1(X1,sK0,X0) = sK0 ),
% 8.18/1.50      inference(equality_resolution_simp,[status(thm)],[c_368]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_1066,plain,
% 8.18/1.50      ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 8.18/1.50      | k2_relset_1(X0,sK0,X2) = sK0
% 8.18/1.50      | v1_funct_2(X2,X0,sK0) != iProver_top
% 8.18/1.50      | v1_funct_2(X1,sK0,X0) != iProver_top
% 8.18/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 8.18/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 8.18/1.50      | v1_funct_1(X2) != iProver_top
% 8.18/1.50      | v1_funct_1(X1) != iProver_top ),
% 8.18/1.50      inference(predicate_to_equality,[status(thm)],[c_449]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_1596,plain,
% 8.18/1.50      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 8.18/1.50      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 8.18/1.50      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 8.18/1.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 8.18/1.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 8.18/1.50      | v1_funct_1(sK3) != iProver_top
% 8.18/1.50      | v1_funct_1(sK2) != iProver_top ),
% 8.18/1.50      inference(equality_resolution,[status(thm)],[c_1066]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_1765,plain,
% 8.18/1.50      ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 8.18/1.50      inference(global_propositional_subsumption,
% 8.18/1.50                [status(thm)],
% 8.18/1.50                [c_1596,c_34,c_35,c_36,c_37,c_38,c_39]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_1993,plain,
% 8.18/1.50      ( k2_relat_1(sK3) = sK0 ),
% 8.18/1.50      inference(light_normalisation,[status(thm)],[c_1990,c_1765]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_5020,plain,
% 8.18/1.50      ( k2_funct_1(k2_funct_1(sK3)) = sK3
% 8.18/1.50      | k1_relat_1(k2_funct_1(sK3)) != sK0
% 8.18/1.50      | k6_partfun1(k2_relat_1(k2_funct_1(sK3))) != k6_partfun1(k1_relat_1(sK3))
% 8.18/1.50      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 8.18/1.50      | v1_funct_1(sK3) != iProver_top
% 8.18/1.50      | v1_relat_1(k2_funct_1(sK3)) != iProver_top
% 8.18/1.50      | v1_relat_1(sK3) != iProver_top
% 8.18/1.50      | v2_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 8.18/1.50      inference(light_normalisation,[status(thm)],[c_5019,c_1993]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_25,negated_conjecture,
% 8.18/1.50      ( v2_funct_1(sK2) ),
% 8.18/1.50      inference(cnf_transformation,[],[f72]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_1684,plain,
% 8.18/1.50      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 8.18/1.50      | v1_relat_1(sK2) ),
% 8.18/1.50      inference(instantiation,[status(thm)],[c_7]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_5021,plain,
% 8.18/1.50      ( ~ v1_funct_1(k2_funct_1(sK3))
% 8.18/1.50      | ~ v1_funct_1(sK3)
% 8.18/1.50      | ~ v1_relat_1(k2_funct_1(sK3))
% 8.18/1.50      | ~ v1_relat_1(sK3)
% 8.18/1.50      | ~ v2_funct_1(k2_funct_1(sK3))
% 8.18/1.50      | k2_funct_1(k2_funct_1(sK3)) = sK3
% 8.18/1.50      | k1_relat_1(k2_funct_1(sK3)) != sK0
% 8.18/1.50      | k6_partfun1(k2_relat_1(k2_funct_1(sK3))) != k6_partfun1(k1_relat_1(sK3)) ),
% 8.18/1.50      inference(predicate_to_equality_rev,[status(thm)],[c_5020]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_1071,plain,
% 8.18/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 8.18/1.50      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_14,plain,
% 8.18/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.18/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 8.18/1.50      | ~ v1_funct_1(X0)
% 8.18/1.50      | ~ v1_funct_1(X3)
% 8.18/1.50      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 8.18/1.50      inference(cnf_transformation,[],[f55]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_1082,plain,
% 8.18/1.50      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 8.18/1.50      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 8.18/1.50      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 8.18/1.50      | v1_funct_1(X5) != iProver_top
% 8.18/1.50      | v1_funct_1(X4) != iProver_top ),
% 8.18/1.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_2748,plain,
% 8.18/1.50      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 8.18/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 8.18/1.50      | v1_funct_1(X2) != iProver_top
% 8.18/1.50      | v1_funct_1(sK3) != iProver_top ),
% 8.18/1.50      inference(superposition,[status(thm)],[c_1074,c_1082]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_2812,plain,
% 8.18/1.50      ( v1_funct_1(X2) != iProver_top
% 8.18/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 8.18/1.50      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 8.18/1.50      inference(global_propositional_subsumption,
% 8.18/1.50                [status(thm)],
% 8.18/1.50                [c_2748,c_37]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_2813,plain,
% 8.18/1.50      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 8.18/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 8.18/1.50      | v1_funct_1(X2) != iProver_top ),
% 8.18/1.50      inference(renaming,[status(thm)],[c_2812]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_2821,plain,
% 8.18/1.50      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 8.18/1.50      | v1_funct_1(sK2) != iProver_top ),
% 8.18/1.50      inference(superposition,[status(thm)],[c_1071,c_2813]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_2822,plain,
% 8.18/1.50      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 8.18/1.50      | v1_funct_1(sK2) != iProver_top ),
% 8.18/1.50      inference(light_normalisation,[status(thm)],[c_2821,c_1758]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_3651,plain,
% 8.18/1.50      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 8.18/1.50      inference(global_propositional_subsumption,
% 8.18/1.50                [status(thm)],
% 8.18/1.50                [c_2822,c_34]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_3774,plain,
% 8.18/1.50      ( k2_funct_1(sK3) = sK2
% 8.18/1.50      | k1_relat_1(sK3) != k2_relat_1(sK2)
% 8.18/1.50      | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
% 8.18/1.50      | v1_funct_1(sK3) != iProver_top
% 8.18/1.50      | v1_funct_1(sK2) != iProver_top
% 8.18/1.50      | v1_relat_1(sK3) != iProver_top
% 8.18/1.50      | v1_relat_1(sK2) != iProver_top
% 8.18/1.50      | v2_funct_1(sK3) != iProver_top ),
% 8.18/1.50      inference(superposition,[status(thm)],[c_3651,c_1088]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_1991,plain,
% 8.18/1.50      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 8.18/1.50      inference(superposition,[status(thm)],[c_1071,c_1086]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_1992,plain,
% 8.18/1.50      ( k2_relat_1(sK2) = sK1 ),
% 8.18/1.50      inference(light_normalisation,[status(thm)],[c_1991,c_27]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_3775,plain,
% 8.18/1.50      ( k2_funct_1(sK3) = sK2
% 8.18/1.50      | k1_relat_1(sK3) != sK1
% 8.18/1.50      | k6_partfun1(sK0) != k6_partfun1(sK0)
% 8.18/1.50      | v1_funct_1(sK3) != iProver_top
% 8.18/1.50      | v1_funct_1(sK2) != iProver_top
% 8.18/1.50      | v1_relat_1(sK3) != iProver_top
% 8.18/1.50      | v1_relat_1(sK2) != iProver_top
% 8.18/1.50      | v2_funct_1(sK3) != iProver_top ),
% 8.18/1.50      inference(light_normalisation,[status(thm)],[c_3774,c_1992,c_1993]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_3776,plain,
% 8.18/1.50      ( k2_funct_1(sK3) = sK2
% 8.18/1.50      | k1_relat_1(sK3) != sK1
% 8.18/1.50      | v1_funct_1(sK3) != iProver_top
% 8.18/1.50      | v1_funct_1(sK2) != iProver_top
% 8.18/1.50      | v1_relat_1(sK3) != iProver_top
% 8.18/1.50      | v1_relat_1(sK2) != iProver_top
% 8.18/1.50      | v2_funct_1(sK3) != iProver_top ),
% 8.18/1.50      inference(equality_resolution_simp,[status(thm)],[c_3775]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_3778,plain,
% 8.18/1.50      ( ~ v1_funct_1(sK3)
% 8.18/1.50      | ~ v1_funct_1(sK2)
% 8.18/1.50      | ~ v1_relat_1(sK3)
% 8.18/1.50      | ~ v1_relat_1(sK2)
% 8.18/1.50      | ~ v2_funct_1(sK3)
% 8.18/1.50      | k2_funct_1(sK3) = sK2
% 8.18/1.50      | k1_relat_1(sK3) != sK1 ),
% 8.18/1.50      inference(predicate_to_equality_rev,[status(thm)],[c_3776]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_4709,plain,
% 8.18/1.50      ( ~ v1_funct_2(sK3,sK1,sK0)
% 8.18/1.50      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 8.18/1.50      | ~ v1_funct_1(sK3)
% 8.18/1.50      | ~ v2_funct_1(k6_partfun1(sK0))
% 8.18/1.50      | v2_funct_1(sK3)
% 8.18/1.50      | sK0 = k1_xboole_0 ),
% 8.18/1.50      inference(predicate_to_equality_rev,[status(thm)],[c_4708]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_5165,plain,
% 8.18/1.50      ( k1_relat_1(sK3) != sK1 | k2_funct_1(sK3) = sK2 ),
% 8.18/1.50      inference(global_propositional_subsumption,
% 8.18/1.50                [status(thm)],
% 8.18/1.50                [c_3776,c_33,c_31,c_30,c_29,c_28,c_24,c_639,c_1173,
% 8.18/1.50                 c_1573,c_1684,c_3778,c_4709,c_4729]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_5166,plain,
% 8.18/1.50      ( k2_funct_1(sK3) = sK2 | k1_relat_1(sK3) != sK1 ),
% 8.18/1.50      inference(renaming,[status(thm)],[c_5165]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_21,plain,
% 8.18/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 8.18/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.18/1.50      | ~ v1_funct_1(X0)
% 8.18/1.50      | ~ v2_funct_1(X0)
% 8.18/1.50      | k2_relset_1(X1,X2,X0) != X2
% 8.18/1.50      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 8.18/1.50      | k1_xboole_0 = X2 ),
% 8.18/1.50      inference(cnf_transformation,[],[f62]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_1076,plain,
% 8.18/1.50      ( k2_relset_1(X0,X1,X2) != X1
% 8.18/1.50      | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
% 8.18/1.50      | k1_xboole_0 = X1
% 8.18/1.50      | v1_funct_2(X2,X0,X1) != iProver_top
% 8.18/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 8.18/1.50      | v1_funct_1(X2) != iProver_top
% 8.18/1.50      | v2_funct_1(X2) != iProver_top ),
% 8.18/1.50      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_2685,plain,
% 8.18/1.50      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
% 8.18/1.50      | sK0 = k1_xboole_0
% 8.18/1.50      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 8.18/1.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 8.18/1.50      | v1_funct_1(sK3) != iProver_top
% 8.18/1.50      | v2_funct_1(sK3) != iProver_top ),
% 8.18/1.50      inference(superposition,[status(thm)],[c_1765,c_1076]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_2688,plain,
% 8.18/1.50      ( ~ v1_funct_2(sK3,sK1,sK0)
% 8.18/1.50      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 8.18/1.50      | ~ v1_funct_1(sK3)
% 8.18/1.50      | ~ v2_funct_1(sK3)
% 8.18/1.50      | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
% 8.18/1.50      | sK0 = k1_xboole_0 ),
% 8.18/1.50      inference(predicate_to_equality_rev,[status(thm)],[c_2685]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_5220,plain,
% 8.18/1.50      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
% 8.18/1.50      inference(global_propositional_subsumption,
% 8.18/1.50                [status(thm)],
% 8.18/1.50                [c_2685,c_30,c_29,c_28,c_24,c_639,c_1173,c_2688,c_4709,
% 8.18/1.50                 c_4729]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_5222,plain,
% 8.18/1.50      ( k6_partfun1(k1_relat_1(sK3)) = k6_partfun1(sK1) ),
% 8.18/1.50      inference(demodulation,[status(thm)],[c_5220,c_4972]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_0,plain,
% 8.18/1.50      ( k2_relat_1(k6_partfun1(X0)) = X0 ),
% 8.18/1.50      inference(cnf_transformation,[],[f76]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_5706,plain,
% 8.18/1.50      ( k2_relat_1(k6_partfun1(sK1)) = k1_relat_1(sK3) ),
% 8.18/1.50      inference(superposition,[status(thm)],[c_5222,c_0]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_5707,plain,
% 8.18/1.50      ( k1_relat_1(sK3) = sK1 ),
% 8.18/1.50      inference(demodulation,[status(thm)],[c_5706,c_0]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_617,plain,
% 8.18/1.50      ( ~ v1_funct_1(X0) | v1_funct_1(X1) | X1 != X0 ),
% 8.18/1.50      theory(equality) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_1351,plain,
% 8.18/1.50      ( v1_funct_1(X0) | ~ v1_funct_1(sK2) | X0 != sK2 ),
% 8.18/1.50      inference(instantiation,[status(thm)],[c_617]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_1430,plain,
% 8.18/1.50      ( v1_funct_1(k2_funct_1(X0))
% 8.18/1.50      | ~ v1_funct_1(sK2)
% 8.18/1.50      | k2_funct_1(X0) != sK2 ),
% 8.18/1.50      inference(instantiation,[status(thm)],[c_1351]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_7982,plain,
% 8.18/1.50      ( v1_funct_1(k2_funct_1(sK3))
% 8.18/1.50      | ~ v1_funct_1(sK2)
% 8.18/1.50      | k2_funct_1(sK3) != sK2 ),
% 8.18/1.50      inference(instantiation,[status(thm)],[c_1430]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_614,plain,
% 8.18/1.50      ( ~ v1_relat_1(X0) | v1_relat_1(X1) | X1 != X0 ),
% 8.18/1.50      theory(equality) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_1737,plain,
% 8.18/1.50      ( v1_relat_1(X0) | ~ v1_relat_1(sK2) | X0 != sK2 ),
% 8.18/1.50      inference(instantiation,[status(thm)],[c_614]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_2266,plain,
% 8.18/1.50      ( v1_relat_1(k2_funct_1(X0))
% 8.18/1.50      | ~ v1_relat_1(sK2)
% 8.18/1.50      | k2_funct_1(X0) != sK2 ),
% 8.18/1.50      inference(instantiation,[status(thm)],[c_1737]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_7980,plain,
% 8.18/1.50      ( v1_relat_1(k2_funct_1(sK3))
% 8.18/1.50      | ~ v1_relat_1(sK2)
% 8.18/1.50      | k2_funct_1(sK3) != sK2 ),
% 8.18/1.50      inference(instantiation,[status(thm)],[c_2266]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_613,plain,
% 8.18/1.50      ( ~ v2_funct_1(X0) | v2_funct_1(X1) | X1 != X0 ),
% 8.18/1.50      theory(equality) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_2118,plain,
% 8.18/1.50      ( v2_funct_1(X0) | ~ v2_funct_1(sK2) | X0 != sK2 ),
% 8.18/1.50      inference(instantiation,[status(thm)],[c_613]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_2539,plain,
% 8.18/1.50      ( v2_funct_1(k2_funct_1(X0))
% 8.18/1.50      | ~ v2_funct_1(sK2)
% 8.18/1.50      | k2_funct_1(X0) != sK2 ),
% 8.18/1.50      inference(instantiation,[status(thm)],[c_2118]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_7979,plain,
% 8.18/1.50      ( v2_funct_1(k2_funct_1(sK3))
% 8.18/1.50      | ~ v2_funct_1(sK2)
% 8.18/1.50      | k2_funct_1(sK3) != sK2 ),
% 8.18/1.50      inference(instantiation,[status(thm)],[c_2539]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_22533,plain,
% 8.18/1.50      ( k6_partfun1(k2_relat_1(k2_funct_1(sK3))) != k6_partfun1(k1_relat_1(sK3))
% 8.18/1.50      | k1_relat_1(k2_funct_1(sK3)) != sK0
% 8.18/1.50      | k2_funct_1(k2_funct_1(sK3)) = sK3 ),
% 8.18/1.50      inference(global_propositional_subsumption,
% 8.18/1.50                [status(thm)],
% 8.18/1.50                [c_5020,c_33,c_31,c_30,c_29,c_28,c_25,c_24,c_639,c_1173,
% 8.18/1.50                 c_1573,c_1684,c_3778,c_4709,c_4729,c_5021,c_5707,c_7982,
% 8.18/1.50                 c_7980,c_7979]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_22534,plain,
% 8.18/1.50      ( k2_funct_1(k2_funct_1(sK3)) = sK3
% 8.18/1.50      | k1_relat_1(k2_funct_1(sK3)) != sK0
% 8.18/1.50      | k6_partfun1(k2_relat_1(k2_funct_1(sK3))) != k6_partfun1(k1_relat_1(sK3)) ),
% 8.18/1.50      inference(renaming,[status(thm)],[c_22533]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_2684,plain,
% 8.18/1.50      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
% 8.18/1.50      | sK1 = k1_xboole_0
% 8.18/1.50      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 8.18/1.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 8.18/1.50      | v1_funct_1(sK2) != iProver_top
% 8.18/1.50      | v2_funct_1(sK2) != iProver_top ),
% 8.18/1.50      inference(superposition,[status(thm)],[c_27,c_1076]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_1069,plain,
% 8.18/1.50      ( v1_funct_1(sK2) = iProver_top ),
% 8.18/1.50      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_2032,plain,
% 8.18/1.50      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
% 8.18/1.50      | v1_relat_1(sK2) != iProver_top
% 8.18/1.50      | v2_funct_1(sK2) != iProver_top ),
% 8.18/1.50      inference(superposition,[status(thm)],[c_1069,c_1089]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_41,plain,
% 8.18/1.50      ( v2_funct_1(sK2) = iProver_top ),
% 8.18/1.50      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_1685,plain,
% 8.18/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 8.18/1.50      | v1_relat_1(sK2) = iProver_top ),
% 8.18/1.50      inference(predicate_to_equality,[status(thm)],[c_1684]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_2238,plain,
% 8.18/1.50      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
% 8.18/1.50      inference(global_propositional_subsumption,
% 8.18/1.50                [status(thm)],
% 8.18/1.50                [c_2032,c_36,c_41,c_1685]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_2687,plain,
% 8.18/1.50      ( k6_partfun1(k1_relat_1(sK2)) = k6_partfun1(sK0)
% 8.18/1.50      | sK1 = k1_xboole_0
% 8.18/1.50      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 8.18/1.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 8.18/1.50      | v1_funct_1(sK2) != iProver_top
% 8.18/1.50      | v2_funct_1(sK2) != iProver_top ),
% 8.18/1.50      inference(demodulation,[status(thm)],[c_2684,c_2238]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_23,negated_conjecture,
% 8.18/1.50      ( k1_xboole_0 != sK1 ),
% 8.18/1.50      inference(cnf_transformation,[],[f74]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_1152,plain,
% 8.18/1.50      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 8.18/1.50      inference(instantiation,[status(thm)],[c_609]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_1153,plain,
% 8.18/1.50      ( sK1 != k1_xboole_0
% 8.18/1.50      | k1_xboole_0 = sK1
% 8.18/1.50      | k1_xboole_0 != k1_xboole_0 ),
% 8.18/1.50      inference(instantiation,[status(thm)],[c_1152]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_3571,plain,
% 8.18/1.50      ( k6_partfun1(k1_relat_1(sK2)) = k6_partfun1(sK0) ),
% 8.18/1.50      inference(global_propositional_subsumption,
% 8.18/1.50                [status(thm)],
% 8.18/1.50                [c_2687,c_34,c_35,c_36,c_41,c_23,c_639,c_1153]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_3579,plain,
% 8.18/1.50      ( k2_relat_1(k6_partfun1(sK0)) = k1_relat_1(sK2) ),
% 8.18/1.50      inference(superposition,[status(thm)],[c_3571,c_0]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_3580,plain,
% 8.18/1.50      ( k1_relat_1(sK2) = sK0 ),
% 8.18/1.50      inference(demodulation,[status(thm)],[c_3579,c_0]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_5844,plain,
% 8.18/1.50      ( k2_funct_1(sK3) = sK2 | sK1 != sK1 ),
% 8.18/1.50      inference(demodulation,[status(thm)],[c_5707,c_5166]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_5861,plain,
% 8.18/1.50      ( k2_funct_1(sK3) = sK2 ),
% 8.18/1.50      inference(equality_resolution_simp,[status(thm)],[c_5844]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_22535,plain,
% 8.18/1.50      ( k2_funct_1(sK2) = sK3
% 8.18/1.50      | k6_partfun1(sK1) != k6_partfun1(sK1)
% 8.18/1.50      | sK0 != sK0 ),
% 8.18/1.50      inference(light_normalisation,
% 8.18/1.50                [status(thm)],
% 8.18/1.50                [c_22534,c_1992,c_3580,c_5707,c_5861]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_22536,plain,
% 8.18/1.50      ( k2_funct_1(sK2) = sK3 ),
% 8.18/1.50      inference(equality_resolution_simp,[status(thm)],[c_22535]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(c_22,negated_conjecture,
% 8.18/1.50      ( k2_funct_1(sK2) != sK3 ),
% 8.18/1.50      inference(cnf_transformation,[],[f75]) ).
% 8.18/1.50  
% 8.18/1.50  cnf(contradiction,plain,
% 8.18/1.50      ( $false ),
% 8.18/1.50      inference(minisat,[status(thm)],[c_22536,c_22]) ).
% 8.18/1.50  
% 8.18/1.50  
% 8.18/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 8.18/1.50  
% 8.18/1.50  ------                               Statistics
% 8.18/1.50  
% 8.18/1.50  ------ General
% 8.18/1.50  
% 8.18/1.50  abstr_ref_over_cycles:                  0
% 8.18/1.50  abstr_ref_under_cycles:                 0
% 8.18/1.50  gc_basic_clause_elim:                   0
% 8.18/1.50  forced_gc_time:                         0
% 8.18/1.50  parsing_time:                           0.007
% 8.18/1.50  unif_index_cands_time:                  0.
% 8.18/1.50  unif_index_add_time:                    0.
% 8.18/1.50  orderings_time:                         0.
% 8.18/1.50  out_proof_time:                         0.016
% 8.18/1.50  total_time:                             0.948
% 8.18/1.50  num_of_symbols:                         51
% 8.18/1.50  num_of_terms:                           36841
% 8.18/1.50  
% 8.18/1.50  ------ Preprocessing
% 8.18/1.50  
% 8.18/1.50  num_of_splits:                          0
% 8.18/1.50  num_of_split_atoms:                     0
% 8.18/1.50  num_of_reused_defs:                     0
% 8.18/1.50  num_eq_ax_congr_red:                    0
% 8.18/1.50  num_of_sem_filtered_clauses:            1
% 8.18/1.50  num_of_subtypes:                        0
% 8.18/1.50  monotx_restored_types:                  0
% 8.18/1.50  sat_num_of_epr_types:                   0
% 8.18/1.50  sat_num_of_non_cyclic_types:            0
% 8.18/1.50  sat_guarded_non_collapsed_types:        0
% 8.18/1.50  num_pure_diseq_elim:                    0
% 8.18/1.50  simp_replaced_by:                       0
% 8.18/1.50  res_preprocessed:                       166
% 8.18/1.50  prep_upred:                             0
% 8.18/1.50  prep_unflattend:                        12
% 8.18/1.50  smt_new_axioms:                         0
% 8.18/1.50  pred_elim_cands:                        5
% 8.18/1.50  pred_elim:                              1
% 8.18/1.50  pred_elim_cl:                           1
% 8.18/1.50  pred_elim_cycles:                       3
% 8.18/1.50  merged_defs:                            0
% 8.18/1.50  merged_defs_ncl:                        0
% 8.18/1.50  bin_hyper_res:                          0
% 8.18/1.50  prep_cycles:                            4
% 8.18/1.50  pred_elim_time:                         0.003
% 8.18/1.50  splitting_time:                         0.
% 8.18/1.50  sem_filter_time:                        0.
% 8.18/1.50  monotx_time:                            0.
% 8.18/1.50  subtype_inf_time:                       0.
% 8.18/1.50  
% 8.18/1.50  ------ Problem properties
% 8.18/1.50  
% 8.18/1.50  clauses:                                33
% 8.18/1.50  conjectures:                            11
% 8.18/1.50  epr:                                    7
% 8.18/1.50  horn:                                   29
% 8.18/1.50  ground:                                 12
% 8.18/1.50  unary:                                  16
% 8.18/1.50  binary:                                 3
% 8.18/1.50  lits:                                   121
% 8.18/1.50  lits_eq:                                30
% 8.18/1.50  fd_pure:                                0
% 8.18/1.50  fd_pseudo:                              0
% 8.18/1.50  fd_cond:                                4
% 8.18/1.50  fd_pseudo_cond:                         1
% 8.18/1.50  ac_symbols:                             0
% 8.18/1.50  
% 8.18/1.50  ------ Propositional Solver
% 8.18/1.50  
% 8.18/1.50  prop_solver_calls:                      34
% 8.18/1.50  prop_fast_solver_calls:                 2850
% 8.18/1.50  smt_solver_calls:                       0
% 8.18/1.50  smt_fast_solver_calls:                  0
% 8.18/1.50  prop_num_of_clauses:                    12810
% 8.18/1.50  prop_preprocess_simplified:             19511
% 8.18/1.50  prop_fo_subsumed:                       547
% 8.18/1.50  prop_solver_time:                       0.
% 8.18/1.50  smt_solver_time:                        0.
% 8.18/1.50  smt_fast_solver_time:                   0.
% 8.18/1.50  prop_fast_solver_time:                  0.
% 8.18/1.50  prop_unsat_core_time:                   0.002
% 8.18/1.50  
% 8.18/1.50  ------ QBF
% 8.18/1.50  
% 8.18/1.50  qbf_q_res:                              0
% 8.18/1.50  qbf_num_tautologies:                    0
% 8.18/1.50  qbf_prep_cycles:                        0
% 8.18/1.50  
% 8.18/1.50  ------ BMC1
% 8.18/1.50  
% 8.18/1.50  bmc1_current_bound:                     -1
% 8.18/1.50  bmc1_last_solved_bound:                 -1
% 8.18/1.50  bmc1_unsat_core_size:                   -1
% 8.18/1.50  bmc1_unsat_core_parents_size:           -1
% 8.18/1.50  bmc1_merge_next_fun:                    0
% 8.18/1.50  bmc1_unsat_core_clauses_time:           0.
% 8.18/1.50  
% 8.18/1.50  ------ Instantiation
% 8.18/1.50  
% 8.18/1.50  inst_num_of_clauses:                    3484
% 8.18/1.50  inst_num_in_passive:                    732
% 8.18/1.50  inst_num_in_active:                     1517
% 8.18/1.50  inst_num_in_unprocessed:                1235
% 8.18/1.50  inst_num_of_loops:                      1670
% 8.18/1.50  inst_num_of_learning_restarts:          0
% 8.18/1.50  inst_num_moves_active_passive:          149
% 8.18/1.50  inst_lit_activity:                      0
% 8.18/1.50  inst_lit_activity_moves:                2
% 8.18/1.50  inst_num_tautologies:                   0
% 8.18/1.50  inst_num_prop_implied:                  0
% 8.18/1.50  inst_num_existing_simplified:           0
% 8.18/1.50  inst_num_eq_res_simplified:             0
% 8.18/1.50  inst_num_child_elim:                    0
% 8.18/1.50  inst_num_of_dismatching_blockings:      616
% 8.18/1.50  inst_num_of_non_proper_insts:           2797
% 8.18/1.50  inst_num_of_duplicates:                 0
% 8.18/1.50  inst_inst_num_from_inst_to_res:         0
% 8.18/1.50  inst_dismatching_checking_time:         0.
% 8.18/1.50  
% 8.18/1.50  ------ Resolution
% 8.18/1.50  
% 8.18/1.50  res_num_of_clauses:                     0
% 8.18/1.50  res_num_in_passive:                     0
% 8.18/1.50  res_num_in_active:                      0
% 8.18/1.50  res_num_of_loops:                       170
% 8.18/1.50  res_forward_subset_subsumed:            232
% 8.18/1.50  res_backward_subset_subsumed:           0
% 8.18/1.50  res_forward_subsumed:                   0
% 8.18/1.50  res_backward_subsumed:                  0
% 8.18/1.50  res_forward_subsumption_resolution:     2
% 8.18/1.50  res_backward_subsumption_resolution:    0
% 8.18/1.50  res_clause_to_clause_subsumption:       2232
% 8.18/1.50  res_orphan_elimination:                 0
% 8.18/1.50  res_tautology_del:                      174
% 8.18/1.50  res_num_eq_res_simplified:              1
% 8.18/1.50  res_num_sel_changes:                    0
% 8.18/1.50  res_moves_from_active_to_pass:          0
% 8.18/1.50  
% 8.18/1.50  ------ Superposition
% 8.18/1.50  
% 8.18/1.50  sup_time_total:                         0.
% 8.18/1.50  sup_time_generating:                    0.
% 8.18/1.50  sup_time_sim_full:                      0.
% 8.18/1.50  sup_time_sim_immed:                     0.
% 8.18/1.50  
% 8.18/1.50  sup_num_of_clauses:                     1049
% 8.18/1.50  sup_num_in_active:                      317
% 8.18/1.50  sup_num_in_passive:                     732
% 8.18/1.50  sup_num_of_loops:                       332
% 8.18/1.50  sup_fw_superposition:                   384
% 8.18/1.50  sup_bw_superposition:                   783
% 8.18/1.50  sup_immediate_simplified:               348
% 8.18/1.50  sup_given_eliminated:                   2
% 8.18/1.50  comparisons_done:                       0
% 8.18/1.50  comparisons_avoided:                    4
% 8.18/1.50  
% 8.18/1.50  ------ Simplifications
% 8.18/1.50  
% 8.18/1.50  
% 8.18/1.50  sim_fw_subset_subsumed:                 21
% 8.18/1.50  sim_bw_subset_subsumed:                 29
% 8.18/1.50  sim_fw_subsumed:                        35
% 8.18/1.50  sim_bw_subsumed:                        9
% 8.18/1.50  sim_fw_subsumption_res:                 0
% 8.18/1.50  sim_bw_subsumption_res:                 0
% 8.18/1.50  sim_tautology_del:                      0
% 8.18/1.50  sim_eq_tautology_del:                   27
% 8.18/1.50  sim_eq_res_simp:                        3
% 8.18/1.50  sim_fw_demodulated:                     36
% 8.18/1.50  sim_bw_demodulated:                     8
% 8.18/1.50  sim_light_normalised:                   320
% 8.18/1.50  sim_joinable_taut:                      0
% 8.18/1.50  sim_joinable_simp:                      0
% 8.18/1.50  sim_ac_normalised:                      0
% 8.18/1.50  sim_smt_subsumption:                    0
% 8.18/1.50  
%------------------------------------------------------------------------------
