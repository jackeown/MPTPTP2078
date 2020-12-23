%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:01 EST 2020

% Result     : Theorem 3.12s
% Output     : CNFRefutation 3.12s
% Verified   : 
% Statistics : Number of formulae       :  190 ( 578 expanded)
%              Number of clauses        :  111 ( 193 expanded)
%              Number of leaves         :   20 ( 125 expanded)
%              Depth                    :   18
%              Number of atoms          :  570 (3486 expanded)
%              Number of equality atoms :  239 (1364 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,conjecture,(
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

fof(f19,negated_conjecture,(
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
    inference(negated_conjecture,[],[f18])).

fof(f20,plain,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_1(X3) )
           => ( ( v2_funct_1(X2)
                & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
                & k2_relset_1(X0,X1,X2) = X1 )
             => ( k2_funct_1(X2) = X3
                | k1_xboole_0 = X1
                | k1_xboole_0 = X0 ) ) ) ) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f41,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f42,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f41])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_1(X3) )
     => ( k2_funct_1(X2) != sK3
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & v2_funct_1(X2)
        & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0))
        & k2_relset_1(X0,X1,X2) = X1
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( k2_funct_1(X2) != X3
            & k1_xboole_0 != X1
            & k1_xboole_0 != X0
            & v2_funct_1(X2)
            & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & k2_relset_1(X0,X1,X2) = X1
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k2_funct_1(sK2) != X3
          & k1_xboole_0 != sK1
          & k1_xboole_0 != sK0
          & v2_funct_1(sK2)
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & k2_relset_1(sK0,sK1,sK2) = sK1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( k2_funct_1(sK2) != sK3
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & v2_funct_1(sK2)
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & k2_relset_1(sK0,sK1,sK2) = sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f42,f45,f44])).

fof(f73,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f46])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f71,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f46])).

fof(f70,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f50,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f76,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f29,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f57,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f17,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f17])).

fof(f85,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f57,f69])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f74,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f46])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f39])).

fof(f68,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f72,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f35])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f75,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f46])).

fof(f14,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f88,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f65,f69])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f37])).

fof(f67,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_partfun1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f49,f69])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f83,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f55,f69])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( v2_funct_1(X1)
              & v2_funct_1(X0) )
           => k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) = k2_funct_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) = k2_funct_1(k5_relat_1(X0,X1))
          | ~ v2_funct_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) = k2_funct_1(k5_relat_1(X0,X1))
          | ~ v2_funct_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) = k2_funct_1(k5_relat_1(X0,X1))
      | ~ v2_funct_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f9,axiom,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f87,plain,(
    ! [X0] : k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
    inference(definition_unfolding,[],[f59,f69,f69])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f81,plain,(
    ! [X0] : v1_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f53,f69])).

fof(f54,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f84,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f54,f69])).

fof(f79,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_506,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_991,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_506])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_517,plain,
    ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | v1_relat_1(X0_49) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_984,plain,
    ( m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_relat_1(X0_49) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_517])).

cnf(c_1524,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_991,c_984])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_504,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_993,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_504])).

cnf(c_1525,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_993,c_984])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_503,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(subtyping,[status(esa)],[c_31])).

cnf(c_994,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_503])).

cnf(c_4,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_525,plain,
    ( ~ v1_funct_1(X0_49)
    | ~ v1_relat_1(X0_49)
    | v1_relat_1(k2_funct_1(X0_49)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_977,plain,
    ( v1_funct_1(X0_49) != iProver_top
    | v1_relat_1(X0_49) != iProver_top
    | v1_relat_1(k2_funct_1(X0_49)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_525])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k5_relat_1(k5_relat_1(X2,X0),X1) = k5_relat_1(X2,k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_528,plain,
    ( ~ v1_relat_1(X0_49)
    | ~ v1_relat_1(X1_49)
    | ~ v1_relat_1(X2_49)
    | k5_relat_1(k5_relat_1(X2_49,X0_49),X1_49) = k5_relat_1(X2_49,k5_relat_1(X0_49,X1_49)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_974,plain,
    ( k5_relat_1(k5_relat_1(X0_49,X1_49),X2_49) = k5_relat_1(X0_49,k5_relat_1(X1_49,X2_49))
    | v1_relat_1(X1_49) != iProver_top
    | v1_relat_1(X2_49) != iProver_top
    | v1_relat_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_528])).

cnf(c_3119,plain,
    ( k5_relat_1(k2_funct_1(X0_49),k5_relat_1(X1_49,X2_49)) = k5_relat_1(k5_relat_1(k2_funct_1(X0_49),X1_49),X2_49)
    | v1_funct_1(X0_49) != iProver_top
    | v1_relat_1(X0_49) != iProver_top
    | v1_relat_1(X1_49) != iProver_top
    | v1_relat_1(X2_49) != iProver_top ),
    inference(superposition,[status(thm)],[c_977,c_974])).

cnf(c_6561,plain,
    ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0_49),X1_49) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0_49,X1_49))
    | v1_relat_1(X0_49) != iProver_top
    | v1_relat_1(X1_49) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_994,c_3119])).

cnf(c_33,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_1192,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_517])).

cnf(c_1193,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1192])).

cnf(c_6924,plain,
    ( v1_relat_1(X1_49) != iProver_top
    | v1_relat_1(X0_49) != iProver_top
    | k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0_49),X1_49) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0_49,X1_49)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6561,c_33,c_1193])).

cnf(c_6925,plain,
    ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0_49),X1_49) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0_49,X1_49))
    | v1_relat_1(X0_49) != iProver_top
    | v1_relat_1(X1_49) != iProver_top ),
    inference(renaming,[status(thm)],[c_6924])).

cnf(c_6933,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0_49)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),X0_49)
    | v1_relat_1(X0_49) != iProver_top ),
    inference(superposition,[status(thm)],[c_1525,c_6925])).

cnf(c_25,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_508,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_990,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_508])).

cnf(c_9,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_521,plain,
    ( ~ v2_funct_1(X0_49)
    | ~ v1_funct_1(X0_49)
    | ~ v1_relat_1(X0_49)
    | k5_relat_1(k2_funct_1(X0_49),X0_49) = k6_partfun1(k2_relat_1(X0_49)) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_981,plain,
    ( k5_relat_1(k2_funct_1(X0_49),X0_49) = k6_partfun1(k2_relat_1(X0_49))
    | v2_funct_1(X0_49) != iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | v1_relat_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_521])).

cnf(c_2243,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_990,c_981])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_516,plain,
    ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | k2_relset_1(X0_51,X1_51,X0_49) = k2_relat_1(X0_49) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_985,plain,
    ( k2_relset_1(X0_51,X1_51,X0_49) = k2_relat_1(X0_49)
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_516])).

cnf(c_1943,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_993,c_985])).

cnf(c_27,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_507,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_1948,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_1943,c_507])).

cnf(c_2256,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2243,c_1948])).

cnf(c_32,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_2401,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2256,c_32,c_33,c_1193])).

cnf(c_6956,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0_49)) = k5_relat_1(k6_partfun1(sK1),X0_49)
    | v1_relat_1(X0_49) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6933,c_2401])).

cnf(c_7003,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
    inference(superposition,[status(thm)],[c_1524,c_6956])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_512,plain,
    ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ m1_subset_1(X1_49,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51)))
    | ~ v1_funct_1(X0_49)
    | ~ v1_funct_1(X1_49)
    | k1_partfun1(X2_51,X3_51,X0_51,X1_51,X1_49,X0_49) = k5_relat_1(X1_49,X0_49) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_989,plain,
    ( k1_partfun1(X0_51,X1_51,X2_51,X3_51,X0_49,X1_49) = k5_relat_1(X0_49,X1_49)
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | m1_subset_1(X1_49,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51))) != iProver_top
    | v1_funct_1(X1_49) != iProver_top
    | v1_funct_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_512])).

cnf(c_3383,plain,
    ( k1_partfun1(X0_51,X1_51,sK1,sK0,X0_49,sK3) = k5_relat_1(X0_49,sK3)
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_991,c_989])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_34,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3771,plain,
    ( v1_funct_1(X0_49) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | k1_partfun1(X0_51,X1_51,sK1,sK0,X0_49,sK3) = k5_relat_1(X0_49,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3383,c_34])).

cnf(c_3772,plain,
    ( k1_partfun1(X0_51,X1_51,sK1,sK0,X0_49,sK3) = k5_relat_1(X0_49,sK3)
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X0_49) != iProver_top ),
    inference(renaming,[status(thm)],[c_3771])).

cnf(c_3781,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_993,c_3772])).

cnf(c_17,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_26,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_327,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_26])).

cnf(c_328,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_327])).

cnf(c_18,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_48,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_330,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_328,c_48])).

cnf(c_501,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_330])).

cnf(c_996,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_501])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_514,plain,
    ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ m1_subset_1(X1_49,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51)))
    | m1_subset_1(k1_partfun1(X2_51,X3_51,X0_51,X1_51,X1_49,X0_49),k1_zfmisc_1(k2_zfmisc_1(X2_51,X1_51)))
    | ~ v1_funct_1(X0_49)
    | ~ v1_funct_1(X1_49) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1305,plain,
    ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | m1_subset_1(k1_partfun1(X0_51,X1_51,sK1,sK0,X0_49,sK3),k1_zfmisc_1(k2_zfmisc_1(X0_51,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(X0_49)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_514])).

cnf(c_1447,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1305])).

cnf(c_1476,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_996,c_31,c_30,c_29,c_28,c_501,c_1447])).

cnf(c_3790,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3781,c_1476])).

cnf(c_4785,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3790,c_32])).

cnf(c_7017,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
    inference(light_normalisation,[status(thm)],[c_7003,c_4785])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_partfun1(X1),X0) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_527,plain,
    ( ~ v1_relat_1(X0_49)
    | k5_relat_1(k6_partfun1(X0_51),X0_49) = k7_relat_1(X0_49,X0_51) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_975,plain,
    ( k5_relat_1(k6_partfun1(X0_51),X0_49) = k7_relat_1(X0_49,X0_51)
    | v1_relat_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_527])).

cnf(c_1584,plain,
    ( k5_relat_1(k6_partfun1(X0_51),sK3) = k7_relat_1(sK3,X0_51) ),
    inference(superposition,[status(thm)],[c_1524,c_975])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v4_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_0,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_305,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_14,c_0])).

cnf(c_309,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_305,c_14,c_13,c_0])).

cnf(c_502,plain,
    ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | k7_relat_1(X0_49,X0_51) = X0_49 ),
    inference(subtyping,[status(esa)],[c_309])).

cnf(c_995,plain,
    ( k7_relat_1(X0_49,X0_51) = X0_49
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_502])).

cnf(c_2614,plain,
    ( k7_relat_1(sK3,sK1) = sK3 ),
    inference(superposition,[status(thm)],[c_991,c_995])).

cnf(c_2615,plain,
    ( k7_relat_1(sK2,sK0) = sK2 ),
    inference(superposition,[status(thm)],[c_993,c_995])).

cnf(c_7,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_522,plain,
    ( v2_funct_1(k6_partfun1(X0_51)) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_980,plain,
    ( v2_funct_1(k6_partfun1(X0_51)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_522])).

cnf(c_11,plain,
    ( ~ v2_funct_1(X0)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) = k2_funct_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_519,plain,
    ( ~ v2_funct_1(X0_49)
    | ~ v2_funct_1(X1_49)
    | ~ v1_funct_1(X0_49)
    | ~ v1_funct_1(X1_49)
    | ~ v1_relat_1(X1_49)
    | ~ v1_relat_1(X0_49)
    | k5_relat_1(k2_funct_1(X1_49),k2_funct_1(X0_49)) = k2_funct_1(k5_relat_1(X0_49,X1_49)) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_983,plain,
    ( k5_relat_1(k2_funct_1(X0_49),k2_funct_1(X1_49)) = k2_funct_1(k5_relat_1(X1_49,X0_49))
    | v2_funct_1(X0_49) != iProver_top
    | v2_funct_1(X1_49) != iProver_top
    | v1_funct_1(X1_49) != iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | v1_relat_1(X1_49) != iProver_top
    | v1_relat_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_519])).

cnf(c_3532,plain,
    ( k5_relat_1(k2_funct_1(X0_49),k2_funct_1(k6_partfun1(X0_51))) = k2_funct_1(k5_relat_1(k6_partfun1(X0_51),X0_49))
    | v2_funct_1(X0_49) != iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | v1_funct_1(k6_partfun1(X0_51)) != iProver_top
    | v1_relat_1(X0_49) != iProver_top
    | v1_relat_1(k6_partfun1(X0_51)) != iProver_top ),
    inference(superposition,[status(thm)],[c_980,c_983])).

cnf(c_12,plain,
    ( k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_518,plain,
    ( k2_funct_1(k6_partfun1(X0_51)) = k6_partfun1(X0_51) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_3539,plain,
    ( k2_funct_1(k5_relat_1(k6_partfun1(X0_51),X0_49)) = k5_relat_1(k2_funct_1(X0_49),k6_partfun1(X0_51))
    | v2_funct_1(X0_49) != iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | v1_funct_1(k6_partfun1(X0_51)) != iProver_top
    | v1_relat_1(X0_49) != iProver_top
    | v1_relat_1(k6_partfun1(X0_51)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3532,c_518])).

cnf(c_5,plain,
    ( v1_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_524,plain,
    ( v1_funct_1(k6_partfun1(X0_51)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_575,plain,
    ( v1_funct_1(k6_partfun1(X0_51)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_524])).

cnf(c_8,plain,
    ( v1_relat_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_523,plain,
    ( v1_relat_1(k6_partfun1(X0_51)) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_576,plain,
    ( v1_relat_1(k6_partfun1(X0_51)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_523])).

cnf(c_4641,plain,
    ( v1_relat_1(X0_49) != iProver_top
    | k2_funct_1(k5_relat_1(k6_partfun1(X0_51),X0_49)) = k5_relat_1(k2_funct_1(X0_49),k6_partfun1(X0_51))
    | v2_funct_1(X0_49) != iProver_top
    | v1_funct_1(X0_49) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3539,c_575,c_576])).

cnf(c_4642,plain,
    ( k2_funct_1(k5_relat_1(k6_partfun1(X0_51),X0_49)) = k5_relat_1(k2_funct_1(X0_49),k6_partfun1(X0_51))
    | v2_funct_1(X0_49) != iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | v1_relat_1(X0_49) != iProver_top ),
    inference(renaming,[status(thm)],[c_4641])).

cnf(c_4651,plain,
    ( k2_funct_1(k5_relat_1(k6_partfun1(X0_51),sK2)) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0_51))
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_990,c_4642])).

cnf(c_1588,plain,
    ( k5_relat_1(k6_partfun1(X0_51),sK2) = k7_relat_1(sK2,X0_51) ),
    inference(superposition,[status(thm)],[c_1525,c_975])).

cnf(c_4664,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0_51)) = k2_funct_1(k7_relat_1(sK2,X0_51))
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4651,c_1588])).

cnf(c_4805,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0_51)) = k2_funct_1(k7_relat_1(sK2,X0_51)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4664,c_32,c_33,c_1193])).

cnf(c_7018,plain,
    ( k2_funct_1(sK2) = sK3 ),
    inference(demodulation,[status(thm)],[c_7017,c_1584,c_2614,c_2615,c_4805])).

cnf(c_22,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_511,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7018,c_511])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:01:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.12/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.12/1.00  
% 3.12/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.12/1.00  
% 3.12/1.00  ------  iProver source info
% 3.12/1.00  
% 3.12/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.12/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.12/1.00  git: non_committed_changes: false
% 3.12/1.00  git: last_make_outside_of_git: false
% 3.12/1.00  
% 3.12/1.00  ------ 
% 3.12/1.00  
% 3.12/1.00  ------ Input Options
% 3.12/1.00  
% 3.12/1.00  --out_options                           all
% 3.12/1.00  --tptp_safe_out                         true
% 3.12/1.00  --problem_path                          ""
% 3.12/1.00  --include_path                          ""
% 3.12/1.00  --clausifier                            res/vclausify_rel
% 3.12/1.00  --clausifier_options                    --mode clausify
% 3.12/1.00  --stdin                                 false
% 3.12/1.00  --stats_out                             all
% 3.12/1.00  
% 3.12/1.00  ------ General Options
% 3.12/1.00  
% 3.12/1.00  --fof                                   false
% 3.12/1.00  --time_out_real                         305.
% 3.12/1.00  --time_out_virtual                      -1.
% 3.12/1.00  --symbol_type_check                     false
% 3.12/1.00  --clausify_out                          false
% 3.12/1.00  --sig_cnt_out                           false
% 3.12/1.00  --trig_cnt_out                          false
% 3.12/1.00  --trig_cnt_out_tolerance                1.
% 3.12/1.00  --trig_cnt_out_sk_spl                   false
% 3.12/1.00  --abstr_cl_out                          false
% 3.12/1.00  
% 3.12/1.00  ------ Global Options
% 3.12/1.00  
% 3.12/1.00  --schedule                              default
% 3.12/1.00  --add_important_lit                     false
% 3.12/1.00  --prop_solver_per_cl                    1000
% 3.12/1.00  --min_unsat_core                        false
% 3.12/1.00  --soft_assumptions                      false
% 3.12/1.00  --soft_lemma_size                       3
% 3.12/1.00  --prop_impl_unit_size                   0
% 3.12/1.00  --prop_impl_unit                        []
% 3.12/1.00  --share_sel_clauses                     true
% 3.12/1.00  --reset_solvers                         false
% 3.12/1.00  --bc_imp_inh                            [conj_cone]
% 3.12/1.00  --conj_cone_tolerance                   3.
% 3.12/1.00  --extra_neg_conj                        none
% 3.12/1.00  --large_theory_mode                     true
% 3.12/1.00  --prolific_symb_bound                   200
% 3.12/1.00  --lt_threshold                          2000
% 3.12/1.00  --clause_weak_htbl                      true
% 3.12/1.00  --gc_record_bc_elim                     false
% 3.12/1.00  
% 3.12/1.00  ------ Preprocessing Options
% 3.12/1.00  
% 3.12/1.00  --preprocessing_flag                    true
% 3.12/1.00  --time_out_prep_mult                    0.1
% 3.12/1.00  --splitting_mode                        input
% 3.12/1.00  --splitting_grd                         true
% 3.12/1.00  --splitting_cvd                         false
% 3.12/1.00  --splitting_cvd_svl                     false
% 3.12/1.00  --splitting_nvd                         32
% 3.12/1.00  --sub_typing                            true
% 3.12/1.00  --prep_gs_sim                           true
% 3.12/1.00  --prep_unflatten                        true
% 3.12/1.00  --prep_res_sim                          true
% 3.12/1.00  --prep_upred                            true
% 3.12/1.00  --prep_sem_filter                       exhaustive
% 3.12/1.00  --prep_sem_filter_out                   false
% 3.12/1.00  --pred_elim                             true
% 3.12/1.00  --res_sim_input                         true
% 3.12/1.00  --eq_ax_congr_red                       true
% 3.12/1.00  --pure_diseq_elim                       true
% 3.12/1.00  --brand_transform                       false
% 3.12/1.00  --non_eq_to_eq                          false
% 3.12/1.00  --prep_def_merge                        true
% 3.12/1.00  --prep_def_merge_prop_impl              false
% 3.12/1.00  --prep_def_merge_mbd                    true
% 3.12/1.00  --prep_def_merge_tr_red                 false
% 3.12/1.00  --prep_def_merge_tr_cl                  false
% 3.12/1.00  --smt_preprocessing                     true
% 3.12/1.00  --smt_ac_axioms                         fast
% 3.12/1.00  --preprocessed_out                      false
% 3.12/1.00  --preprocessed_stats                    false
% 3.12/1.00  
% 3.12/1.00  ------ Abstraction refinement Options
% 3.12/1.00  
% 3.12/1.00  --abstr_ref                             []
% 3.12/1.00  --abstr_ref_prep                        false
% 3.12/1.00  --abstr_ref_until_sat                   false
% 3.12/1.00  --abstr_ref_sig_restrict                funpre
% 3.12/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.12/1.00  --abstr_ref_under                       []
% 3.12/1.00  
% 3.12/1.00  ------ SAT Options
% 3.12/1.00  
% 3.12/1.00  --sat_mode                              false
% 3.12/1.00  --sat_fm_restart_options                ""
% 3.12/1.00  --sat_gr_def                            false
% 3.12/1.00  --sat_epr_types                         true
% 3.12/1.00  --sat_non_cyclic_types                  false
% 3.12/1.00  --sat_finite_models                     false
% 3.12/1.00  --sat_fm_lemmas                         false
% 3.12/1.00  --sat_fm_prep                           false
% 3.12/1.00  --sat_fm_uc_incr                        true
% 3.12/1.00  --sat_out_model                         small
% 3.12/1.00  --sat_out_clauses                       false
% 3.12/1.00  
% 3.12/1.00  ------ QBF Options
% 3.12/1.00  
% 3.12/1.00  --qbf_mode                              false
% 3.12/1.00  --qbf_elim_univ                         false
% 3.12/1.00  --qbf_dom_inst                          none
% 3.12/1.00  --qbf_dom_pre_inst                      false
% 3.12/1.00  --qbf_sk_in                             false
% 3.12/1.00  --qbf_pred_elim                         true
% 3.12/1.00  --qbf_split                             512
% 3.12/1.00  
% 3.12/1.00  ------ BMC1 Options
% 3.12/1.00  
% 3.12/1.00  --bmc1_incremental                      false
% 3.12/1.00  --bmc1_axioms                           reachable_all
% 3.12/1.00  --bmc1_min_bound                        0
% 3.12/1.00  --bmc1_max_bound                        -1
% 3.12/1.00  --bmc1_max_bound_default                -1
% 3.12/1.00  --bmc1_symbol_reachability              true
% 3.12/1.00  --bmc1_property_lemmas                  false
% 3.12/1.00  --bmc1_k_induction                      false
% 3.12/1.00  --bmc1_non_equiv_states                 false
% 3.12/1.00  --bmc1_deadlock                         false
% 3.12/1.00  --bmc1_ucm                              false
% 3.12/1.00  --bmc1_add_unsat_core                   none
% 3.12/1.00  --bmc1_unsat_core_children              false
% 3.12/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.12/1.00  --bmc1_out_stat                         full
% 3.12/1.00  --bmc1_ground_init                      false
% 3.12/1.00  --bmc1_pre_inst_next_state              false
% 3.12/1.00  --bmc1_pre_inst_state                   false
% 3.12/1.00  --bmc1_pre_inst_reach_state             false
% 3.12/1.00  --bmc1_out_unsat_core                   false
% 3.12/1.00  --bmc1_aig_witness_out                  false
% 3.12/1.00  --bmc1_verbose                          false
% 3.12/1.00  --bmc1_dump_clauses_tptp                false
% 3.12/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.12/1.00  --bmc1_dump_file                        -
% 3.12/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.12/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.12/1.00  --bmc1_ucm_extend_mode                  1
% 3.12/1.00  --bmc1_ucm_init_mode                    2
% 3.12/1.00  --bmc1_ucm_cone_mode                    none
% 3.12/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.12/1.00  --bmc1_ucm_relax_model                  4
% 3.12/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.12/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.12/1.00  --bmc1_ucm_layered_model                none
% 3.12/1.00  --bmc1_ucm_max_lemma_size               10
% 3.12/1.00  
% 3.12/1.00  ------ AIG Options
% 3.12/1.00  
% 3.12/1.00  --aig_mode                              false
% 3.12/1.00  
% 3.12/1.00  ------ Instantiation Options
% 3.12/1.00  
% 3.12/1.00  --instantiation_flag                    true
% 3.12/1.00  --inst_sos_flag                         false
% 3.12/1.00  --inst_sos_phase                        true
% 3.12/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.12/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.12/1.00  --inst_lit_sel_side                     num_symb
% 3.12/1.00  --inst_solver_per_active                1400
% 3.12/1.00  --inst_solver_calls_frac                1.
% 3.12/1.00  --inst_passive_queue_type               priority_queues
% 3.12/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.12/1.00  --inst_passive_queues_freq              [25;2]
% 3.12/1.00  --inst_dismatching                      true
% 3.12/1.00  --inst_eager_unprocessed_to_passive     true
% 3.12/1.00  --inst_prop_sim_given                   true
% 3.12/1.00  --inst_prop_sim_new                     false
% 3.12/1.00  --inst_subs_new                         false
% 3.12/1.00  --inst_eq_res_simp                      false
% 3.12/1.00  --inst_subs_given                       false
% 3.12/1.00  --inst_orphan_elimination               true
% 3.12/1.00  --inst_learning_loop_flag               true
% 3.12/1.00  --inst_learning_start                   3000
% 3.12/1.00  --inst_learning_factor                  2
% 3.12/1.00  --inst_start_prop_sim_after_learn       3
% 3.12/1.00  --inst_sel_renew                        solver
% 3.12/1.00  --inst_lit_activity_flag                true
% 3.12/1.00  --inst_restr_to_given                   false
% 3.12/1.00  --inst_activity_threshold               500
% 3.12/1.00  --inst_out_proof                        true
% 3.12/1.00  
% 3.12/1.00  ------ Resolution Options
% 3.12/1.00  
% 3.12/1.00  --resolution_flag                       true
% 3.12/1.00  --res_lit_sel                           adaptive
% 3.12/1.00  --res_lit_sel_side                      none
% 3.12/1.00  --res_ordering                          kbo
% 3.12/1.00  --res_to_prop_solver                    active
% 3.12/1.00  --res_prop_simpl_new                    false
% 3.12/1.00  --res_prop_simpl_given                  true
% 3.12/1.00  --res_passive_queue_type                priority_queues
% 3.12/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.12/1.00  --res_passive_queues_freq               [15;5]
% 3.12/1.00  --res_forward_subs                      full
% 3.12/1.00  --res_backward_subs                     full
% 3.12/1.00  --res_forward_subs_resolution           true
% 3.12/1.00  --res_backward_subs_resolution          true
% 3.12/1.00  --res_orphan_elimination                true
% 3.12/1.00  --res_time_limit                        2.
% 3.12/1.00  --res_out_proof                         true
% 3.12/1.00  
% 3.12/1.00  ------ Superposition Options
% 3.12/1.00  
% 3.12/1.00  --superposition_flag                    true
% 3.12/1.00  --sup_passive_queue_type                priority_queues
% 3.12/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.12/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.12/1.00  --demod_completeness_check              fast
% 3.12/1.00  --demod_use_ground                      true
% 3.12/1.00  --sup_to_prop_solver                    passive
% 3.12/1.00  --sup_prop_simpl_new                    true
% 3.12/1.00  --sup_prop_simpl_given                  true
% 3.12/1.00  --sup_fun_splitting                     false
% 3.12/1.00  --sup_smt_interval                      50000
% 3.12/1.00  
% 3.12/1.00  ------ Superposition Simplification Setup
% 3.12/1.00  
% 3.12/1.00  --sup_indices_passive                   []
% 3.12/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.12/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.12/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.12/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.12/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.12/1.00  --sup_full_bw                           [BwDemod]
% 3.12/1.00  --sup_immed_triv                        [TrivRules]
% 3.12/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.12/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.12/1.00  --sup_immed_bw_main                     []
% 3.12/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.12/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.12/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.12/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.12/1.00  
% 3.12/1.00  ------ Combination Options
% 3.12/1.00  
% 3.12/1.00  --comb_res_mult                         3
% 3.12/1.00  --comb_sup_mult                         2
% 3.12/1.00  --comb_inst_mult                        10
% 3.12/1.00  
% 3.12/1.00  ------ Debug Options
% 3.12/1.00  
% 3.12/1.00  --dbg_backtrace                         false
% 3.12/1.00  --dbg_dump_prop_clauses                 false
% 3.12/1.00  --dbg_dump_prop_clauses_file            -
% 3.12/1.00  --dbg_out_stat                          false
% 3.12/1.00  ------ Parsing...
% 3.12/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.12/1.00  
% 3.12/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.12/1.00  
% 3.12/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.12/1.00  
% 3.12/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.12/1.00  ------ Proving...
% 3.12/1.00  ------ Problem Properties 
% 3.12/1.00  
% 3.12/1.00  
% 3.12/1.00  clauses                                 28
% 3.12/1.00  conjectures                             9
% 3.12/1.00  EPR                                     5
% 3.12/1.00  Horn                                    28
% 3.12/1.00  unary                                   14
% 3.12/1.00  binary                                  5
% 3.12/1.00  lits                                    64
% 3.12/1.00  lits eq                                 14
% 3.12/1.00  fd_pure                                 0
% 3.12/1.00  fd_pseudo                               0
% 3.12/1.00  fd_cond                                 0
% 3.12/1.00  fd_pseudo_cond                          0
% 3.12/1.00  AC symbols                              0
% 3.12/1.00  
% 3.12/1.00  ------ Schedule dynamic 5 is on 
% 3.12/1.00  
% 3.12/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.12/1.00  
% 3.12/1.00  
% 3.12/1.00  ------ 
% 3.12/1.00  Current options:
% 3.12/1.00  ------ 
% 3.12/1.00  
% 3.12/1.00  ------ Input Options
% 3.12/1.00  
% 3.12/1.00  --out_options                           all
% 3.12/1.00  --tptp_safe_out                         true
% 3.12/1.00  --problem_path                          ""
% 3.12/1.00  --include_path                          ""
% 3.12/1.00  --clausifier                            res/vclausify_rel
% 3.12/1.00  --clausifier_options                    --mode clausify
% 3.12/1.00  --stdin                                 false
% 3.12/1.00  --stats_out                             all
% 3.12/1.00  
% 3.12/1.00  ------ General Options
% 3.12/1.00  
% 3.12/1.00  --fof                                   false
% 3.12/1.00  --time_out_real                         305.
% 3.12/1.00  --time_out_virtual                      -1.
% 3.12/1.00  --symbol_type_check                     false
% 3.12/1.00  --clausify_out                          false
% 3.12/1.00  --sig_cnt_out                           false
% 3.12/1.00  --trig_cnt_out                          false
% 3.12/1.00  --trig_cnt_out_tolerance                1.
% 3.12/1.00  --trig_cnt_out_sk_spl                   false
% 3.12/1.00  --abstr_cl_out                          false
% 3.12/1.00  
% 3.12/1.00  ------ Global Options
% 3.12/1.00  
% 3.12/1.00  --schedule                              default
% 3.12/1.00  --add_important_lit                     false
% 3.12/1.00  --prop_solver_per_cl                    1000
% 3.12/1.00  --min_unsat_core                        false
% 3.12/1.00  --soft_assumptions                      false
% 3.12/1.00  --soft_lemma_size                       3
% 3.12/1.00  --prop_impl_unit_size                   0
% 3.12/1.00  --prop_impl_unit                        []
% 3.12/1.00  --share_sel_clauses                     true
% 3.12/1.00  --reset_solvers                         false
% 3.12/1.00  --bc_imp_inh                            [conj_cone]
% 3.12/1.00  --conj_cone_tolerance                   3.
% 3.12/1.00  --extra_neg_conj                        none
% 3.12/1.00  --large_theory_mode                     true
% 3.12/1.00  --prolific_symb_bound                   200
% 3.12/1.00  --lt_threshold                          2000
% 3.12/1.00  --clause_weak_htbl                      true
% 3.12/1.00  --gc_record_bc_elim                     false
% 3.12/1.00  
% 3.12/1.00  ------ Preprocessing Options
% 3.12/1.00  
% 3.12/1.00  --preprocessing_flag                    true
% 3.12/1.00  --time_out_prep_mult                    0.1
% 3.12/1.00  --splitting_mode                        input
% 3.12/1.00  --splitting_grd                         true
% 3.12/1.00  --splitting_cvd                         false
% 3.12/1.00  --splitting_cvd_svl                     false
% 3.12/1.00  --splitting_nvd                         32
% 3.12/1.00  --sub_typing                            true
% 3.12/1.00  --prep_gs_sim                           true
% 3.12/1.00  --prep_unflatten                        true
% 3.12/1.00  --prep_res_sim                          true
% 3.12/1.00  --prep_upred                            true
% 3.12/1.00  --prep_sem_filter                       exhaustive
% 3.12/1.00  --prep_sem_filter_out                   false
% 3.12/1.00  --pred_elim                             true
% 3.12/1.00  --res_sim_input                         true
% 3.12/1.00  --eq_ax_congr_red                       true
% 3.12/1.00  --pure_diseq_elim                       true
% 3.12/1.00  --brand_transform                       false
% 3.12/1.00  --non_eq_to_eq                          false
% 3.12/1.00  --prep_def_merge                        true
% 3.12/1.00  --prep_def_merge_prop_impl              false
% 3.12/1.00  --prep_def_merge_mbd                    true
% 3.12/1.00  --prep_def_merge_tr_red                 false
% 3.12/1.00  --prep_def_merge_tr_cl                  false
% 3.12/1.00  --smt_preprocessing                     true
% 3.12/1.00  --smt_ac_axioms                         fast
% 3.12/1.00  --preprocessed_out                      false
% 3.12/1.00  --preprocessed_stats                    false
% 3.12/1.00  
% 3.12/1.00  ------ Abstraction refinement Options
% 3.12/1.00  
% 3.12/1.00  --abstr_ref                             []
% 3.12/1.00  --abstr_ref_prep                        false
% 3.12/1.00  --abstr_ref_until_sat                   false
% 3.12/1.00  --abstr_ref_sig_restrict                funpre
% 3.12/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.12/1.00  --abstr_ref_under                       []
% 3.12/1.00  
% 3.12/1.00  ------ SAT Options
% 3.12/1.00  
% 3.12/1.00  --sat_mode                              false
% 3.12/1.00  --sat_fm_restart_options                ""
% 3.12/1.00  --sat_gr_def                            false
% 3.12/1.00  --sat_epr_types                         true
% 3.12/1.00  --sat_non_cyclic_types                  false
% 3.12/1.00  --sat_finite_models                     false
% 3.12/1.00  --sat_fm_lemmas                         false
% 3.12/1.00  --sat_fm_prep                           false
% 3.12/1.00  --sat_fm_uc_incr                        true
% 3.12/1.00  --sat_out_model                         small
% 3.12/1.00  --sat_out_clauses                       false
% 3.12/1.00  
% 3.12/1.00  ------ QBF Options
% 3.12/1.00  
% 3.12/1.00  --qbf_mode                              false
% 3.12/1.00  --qbf_elim_univ                         false
% 3.12/1.00  --qbf_dom_inst                          none
% 3.12/1.00  --qbf_dom_pre_inst                      false
% 3.12/1.00  --qbf_sk_in                             false
% 3.12/1.00  --qbf_pred_elim                         true
% 3.12/1.00  --qbf_split                             512
% 3.12/1.00  
% 3.12/1.00  ------ BMC1 Options
% 3.12/1.00  
% 3.12/1.00  --bmc1_incremental                      false
% 3.12/1.00  --bmc1_axioms                           reachable_all
% 3.12/1.00  --bmc1_min_bound                        0
% 3.12/1.00  --bmc1_max_bound                        -1
% 3.12/1.00  --bmc1_max_bound_default                -1
% 3.12/1.00  --bmc1_symbol_reachability              true
% 3.12/1.00  --bmc1_property_lemmas                  false
% 3.12/1.00  --bmc1_k_induction                      false
% 3.12/1.00  --bmc1_non_equiv_states                 false
% 3.12/1.00  --bmc1_deadlock                         false
% 3.12/1.00  --bmc1_ucm                              false
% 3.12/1.00  --bmc1_add_unsat_core                   none
% 3.12/1.00  --bmc1_unsat_core_children              false
% 3.12/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.12/1.00  --bmc1_out_stat                         full
% 3.12/1.00  --bmc1_ground_init                      false
% 3.12/1.00  --bmc1_pre_inst_next_state              false
% 3.12/1.00  --bmc1_pre_inst_state                   false
% 3.12/1.00  --bmc1_pre_inst_reach_state             false
% 3.12/1.00  --bmc1_out_unsat_core                   false
% 3.12/1.00  --bmc1_aig_witness_out                  false
% 3.12/1.00  --bmc1_verbose                          false
% 3.12/1.00  --bmc1_dump_clauses_tptp                false
% 3.12/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.12/1.00  --bmc1_dump_file                        -
% 3.12/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.12/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.12/1.00  --bmc1_ucm_extend_mode                  1
% 3.12/1.00  --bmc1_ucm_init_mode                    2
% 3.12/1.00  --bmc1_ucm_cone_mode                    none
% 3.12/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.12/1.00  --bmc1_ucm_relax_model                  4
% 3.12/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.12/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.12/1.00  --bmc1_ucm_layered_model                none
% 3.12/1.00  --bmc1_ucm_max_lemma_size               10
% 3.12/1.00  
% 3.12/1.00  ------ AIG Options
% 3.12/1.00  
% 3.12/1.00  --aig_mode                              false
% 3.12/1.00  
% 3.12/1.00  ------ Instantiation Options
% 3.12/1.00  
% 3.12/1.00  --instantiation_flag                    true
% 3.12/1.00  --inst_sos_flag                         false
% 3.12/1.00  --inst_sos_phase                        true
% 3.12/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.12/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.12/1.00  --inst_lit_sel_side                     none
% 3.12/1.00  --inst_solver_per_active                1400
% 3.12/1.00  --inst_solver_calls_frac                1.
% 3.12/1.00  --inst_passive_queue_type               priority_queues
% 3.12/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.12/1.00  --inst_passive_queues_freq              [25;2]
% 3.12/1.00  --inst_dismatching                      true
% 3.12/1.00  --inst_eager_unprocessed_to_passive     true
% 3.12/1.00  --inst_prop_sim_given                   true
% 3.12/1.00  --inst_prop_sim_new                     false
% 3.12/1.00  --inst_subs_new                         false
% 3.12/1.00  --inst_eq_res_simp                      false
% 3.12/1.00  --inst_subs_given                       false
% 3.12/1.00  --inst_orphan_elimination               true
% 3.12/1.00  --inst_learning_loop_flag               true
% 3.12/1.00  --inst_learning_start                   3000
% 3.12/1.00  --inst_learning_factor                  2
% 3.12/1.00  --inst_start_prop_sim_after_learn       3
% 3.12/1.00  --inst_sel_renew                        solver
% 3.12/1.00  --inst_lit_activity_flag                true
% 3.12/1.00  --inst_restr_to_given                   false
% 3.12/1.00  --inst_activity_threshold               500
% 3.12/1.00  --inst_out_proof                        true
% 3.12/1.00  
% 3.12/1.00  ------ Resolution Options
% 3.12/1.00  
% 3.12/1.00  --resolution_flag                       false
% 3.12/1.00  --res_lit_sel                           adaptive
% 3.12/1.00  --res_lit_sel_side                      none
% 3.12/1.00  --res_ordering                          kbo
% 3.12/1.00  --res_to_prop_solver                    active
% 3.12/1.00  --res_prop_simpl_new                    false
% 3.12/1.00  --res_prop_simpl_given                  true
% 3.12/1.00  --res_passive_queue_type                priority_queues
% 3.12/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.12/1.00  --res_passive_queues_freq               [15;5]
% 3.12/1.00  --res_forward_subs                      full
% 3.12/1.00  --res_backward_subs                     full
% 3.12/1.00  --res_forward_subs_resolution           true
% 3.12/1.00  --res_backward_subs_resolution          true
% 3.12/1.00  --res_orphan_elimination                true
% 3.12/1.00  --res_time_limit                        2.
% 3.12/1.00  --res_out_proof                         true
% 3.12/1.00  
% 3.12/1.00  ------ Superposition Options
% 3.12/1.00  
% 3.12/1.00  --superposition_flag                    true
% 3.12/1.00  --sup_passive_queue_type                priority_queues
% 3.12/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.12/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.12/1.00  --demod_completeness_check              fast
% 3.12/1.00  --demod_use_ground                      true
% 3.12/1.00  --sup_to_prop_solver                    passive
% 3.12/1.00  --sup_prop_simpl_new                    true
% 3.12/1.00  --sup_prop_simpl_given                  true
% 3.12/1.00  --sup_fun_splitting                     false
% 3.12/1.00  --sup_smt_interval                      50000
% 3.12/1.00  
% 3.12/1.00  ------ Superposition Simplification Setup
% 3.12/1.00  
% 3.12/1.00  --sup_indices_passive                   []
% 3.12/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.12/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.12/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.12/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.12/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.12/1.00  --sup_full_bw                           [BwDemod]
% 3.12/1.00  --sup_immed_triv                        [TrivRules]
% 3.12/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.12/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.12/1.00  --sup_immed_bw_main                     []
% 3.12/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.12/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.12/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.12/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.12/1.00  
% 3.12/1.00  ------ Combination Options
% 3.12/1.00  
% 3.12/1.00  --comb_res_mult                         3
% 3.12/1.00  --comb_sup_mult                         2
% 3.12/1.00  --comb_inst_mult                        10
% 3.12/1.00  
% 3.12/1.00  ------ Debug Options
% 3.12/1.00  
% 3.12/1.00  --dbg_backtrace                         false
% 3.12/1.00  --dbg_dump_prop_clauses                 false
% 3.12/1.00  --dbg_dump_prop_clauses_file            -
% 3.12/1.00  --dbg_out_stat                          false
% 3.12/1.00  
% 3.12/1.00  
% 3.12/1.00  
% 3.12/1.00  
% 3.12/1.00  ------ Proving...
% 3.12/1.00  
% 3.12/1.00  
% 3.12/1.00  % SZS status Theorem for theBenchmark.p
% 3.12/1.00  
% 3.12/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.12/1.00  
% 3.12/1.00  fof(f18,conjecture,(
% 3.12/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 3.12/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.12/1.00  
% 3.12/1.00  fof(f19,negated_conjecture,(
% 3.12/1.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 3.12/1.00    inference(negated_conjecture,[],[f18])).
% 3.12/1.00  
% 3.12/1.00  fof(f20,plain,(
% 3.12/1.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 3.12/1.00    inference(pure_predicate_removal,[],[f19])).
% 3.12/1.00  
% 3.12/1.00  fof(f41,plain,(
% 3.12/1.00    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 3.12/1.00    inference(ennf_transformation,[],[f20])).
% 3.12/1.00  
% 3.12/1.00  fof(f42,plain,(
% 3.12/1.00    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 3.12/1.00    inference(flattening,[],[f41])).
% 3.12/1.00  
% 3.12/1.00  fof(f45,plain,(
% 3.12/1.00    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(sK3))) )),
% 3.12/1.00    introduced(choice_axiom,[])).
% 3.12/1.00  
% 3.12/1.00  fof(f44,plain,(
% 3.12/1.00    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2))),
% 3.12/1.00    introduced(choice_axiom,[])).
% 3.12/1.00  
% 3.12/1.00  fof(f46,plain,(
% 3.12/1.00    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2)),
% 3.12/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f42,f45,f44])).
% 3.12/1.00  
% 3.12/1.00  fof(f73,plain,(
% 3.12/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 3.12/1.00    inference(cnf_transformation,[],[f46])).
% 3.12/1.00  
% 3.12/1.00  fof(f10,axiom,(
% 3.12/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.12/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.12/1.00  
% 3.12/1.00  fof(f32,plain,(
% 3.12/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.12/1.00    inference(ennf_transformation,[],[f10])).
% 3.12/1.00  
% 3.12/1.00  fof(f60,plain,(
% 3.12/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.12/1.00    inference(cnf_transformation,[],[f32])).
% 3.12/1.00  
% 3.12/1.00  fof(f71,plain,(
% 3.12/1.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.12/1.00    inference(cnf_transformation,[],[f46])).
% 3.12/1.00  
% 3.12/1.00  fof(f70,plain,(
% 3.12/1.00    v1_funct_1(sK2)),
% 3.12/1.00    inference(cnf_transformation,[],[f46])).
% 3.12/1.00  
% 3.12/1.00  fof(f4,axiom,(
% 3.12/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.12/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.12/1.00  
% 3.12/1.00  fof(f26,plain,(
% 3.12/1.00    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.12/1.00    inference(ennf_transformation,[],[f4])).
% 3.12/1.00  
% 3.12/1.00  fof(f27,plain,(
% 3.12/1.00    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.12/1.00    inference(flattening,[],[f26])).
% 3.12/1.00  
% 3.12/1.00  fof(f50,plain,(
% 3.12/1.00    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.12/1.00    inference(cnf_transformation,[],[f27])).
% 3.12/1.00  
% 3.12/1.00  fof(f2,axiom,(
% 3.12/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2))))),
% 3.12/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.12/1.00  
% 3.12/1.00  fof(f24,plain,(
% 3.12/1.00    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.12/1.00    inference(ennf_transformation,[],[f2])).
% 3.12/1.00  
% 3.12/1.00  fof(f48,plain,(
% 3.12/1.00    ( ! [X2,X0,X1] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.12/1.00    inference(cnf_transformation,[],[f24])).
% 3.12/1.00  
% 3.12/1.00  fof(f76,plain,(
% 3.12/1.00    v2_funct_1(sK2)),
% 3.12/1.00    inference(cnf_transformation,[],[f46])).
% 3.12/1.00  
% 3.12/1.00  fof(f7,axiom,(
% 3.12/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 3.12/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.12/1.00  
% 3.12/1.00  fof(f28,plain,(
% 3.12/1.00    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.12/1.00    inference(ennf_transformation,[],[f7])).
% 3.12/1.00  
% 3.12/1.00  fof(f29,plain,(
% 3.12/1.00    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.12/1.00    inference(flattening,[],[f28])).
% 3.12/1.00  
% 3.12/1.00  fof(f57,plain,(
% 3.12/1.00    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.12/1.00    inference(cnf_transformation,[],[f29])).
% 3.12/1.00  
% 3.12/1.00  fof(f17,axiom,(
% 3.12/1.00    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.12/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.12/1.00  
% 3.12/1.00  fof(f69,plain,(
% 3.12/1.00    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.12/1.00    inference(cnf_transformation,[],[f17])).
% 3.12/1.00  
% 3.12/1.00  fof(f85,plain,(
% 3.12/1.00    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.12/1.00    inference(definition_unfolding,[],[f57,f69])).
% 3.12/1.00  
% 3.12/1.00  fof(f12,axiom,(
% 3.12/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.12/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.12/1.00  
% 3.12/1.00  fof(f34,plain,(
% 3.12/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.12/1.00    inference(ennf_transformation,[],[f12])).
% 3.12/1.00  
% 3.12/1.00  fof(f62,plain,(
% 3.12/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.12/1.00    inference(cnf_transformation,[],[f34])).
% 3.12/1.00  
% 3.12/1.00  fof(f74,plain,(
% 3.12/1.00    k2_relset_1(sK0,sK1,sK2) = sK1),
% 3.12/1.00    inference(cnf_transformation,[],[f46])).
% 3.12/1.00  
% 3.12/1.00  fof(f16,axiom,(
% 3.12/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.12/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.12/1.00  
% 3.12/1.00  fof(f39,plain,(
% 3.12/1.00    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.12/1.00    inference(ennf_transformation,[],[f16])).
% 3.12/1.00  
% 3.12/1.00  fof(f40,plain,(
% 3.12/1.00    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.12/1.00    inference(flattening,[],[f39])).
% 3.12/1.00  
% 3.12/1.00  fof(f68,plain,(
% 3.12/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.12/1.00    inference(cnf_transformation,[],[f40])).
% 3.12/1.00  
% 3.12/1.00  fof(f72,plain,(
% 3.12/1.00    v1_funct_1(sK3)),
% 3.12/1.00    inference(cnf_transformation,[],[f46])).
% 3.12/1.00  
% 3.12/1.00  fof(f13,axiom,(
% 3.12/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.12/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.12/1.00  
% 3.12/1.00  fof(f35,plain,(
% 3.12/1.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.12/1.00    inference(ennf_transformation,[],[f13])).
% 3.12/1.00  
% 3.12/1.00  fof(f36,plain,(
% 3.12/1.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.12/1.00    inference(flattening,[],[f35])).
% 3.12/1.00  
% 3.12/1.00  fof(f43,plain,(
% 3.12/1.00    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.12/1.00    inference(nnf_transformation,[],[f36])).
% 3.12/1.00  
% 3.12/1.00  fof(f63,plain,(
% 3.12/1.00    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.12/1.00    inference(cnf_transformation,[],[f43])).
% 3.12/1.00  
% 3.12/1.00  fof(f75,plain,(
% 3.12/1.00    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 3.12/1.00    inference(cnf_transformation,[],[f46])).
% 3.12/1.00  
% 3.12/1.00  fof(f14,axiom,(
% 3.12/1.00    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.12/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.12/1.00  
% 3.12/1.00  fof(f65,plain,(
% 3.12/1.00    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.12/1.00    inference(cnf_transformation,[],[f14])).
% 3.12/1.00  
% 3.12/1.00  fof(f88,plain,(
% 3.12/1.00    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.12/1.00    inference(definition_unfolding,[],[f65,f69])).
% 3.12/1.00  
% 3.12/1.00  fof(f15,axiom,(
% 3.12/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 3.12/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.12/1.00  
% 3.12/1.00  fof(f37,plain,(
% 3.12/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.12/1.00    inference(ennf_transformation,[],[f15])).
% 3.12/1.00  
% 3.12/1.00  fof(f38,plain,(
% 3.12/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.12/1.00    inference(flattening,[],[f37])).
% 3.12/1.00  
% 3.12/1.00  fof(f67,plain,(
% 3.12/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.12/1.00    inference(cnf_transformation,[],[f38])).
% 3.12/1.00  
% 3.12/1.00  fof(f3,axiom,(
% 3.12/1.00    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 3.12/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.12/1.00  
% 3.12/1.00  fof(f25,plain,(
% 3.12/1.00    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 3.12/1.00    inference(ennf_transformation,[],[f3])).
% 3.12/1.00  
% 3.12/1.00  fof(f49,plain,(
% 3.12/1.00    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 3.12/1.00    inference(cnf_transformation,[],[f25])).
% 3.12/1.00  
% 3.12/1.00  fof(f80,plain,(
% 3.12/1.00    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_partfun1(X0),X1) | ~v1_relat_1(X1)) )),
% 3.12/1.00    inference(definition_unfolding,[],[f49,f69])).
% 3.12/1.00  
% 3.12/1.00  fof(f11,axiom,(
% 3.12/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.12/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.12/1.00  
% 3.12/1.00  fof(f21,plain,(
% 3.12/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.12/1.00    inference(pure_predicate_removal,[],[f11])).
% 3.12/1.00  
% 3.12/1.00  fof(f33,plain,(
% 3.12/1.00    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.12/1.00    inference(ennf_transformation,[],[f21])).
% 3.12/1.00  
% 3.12/1.00  fof(f61,plain,(
% 3.12/1.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.12/1.00    inference(cnf_transformation,[],[f33])).
% 3.12/1.00  
% 3.12/1.00  fof(f1,axiom,(
% 3.12/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 3.12/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.12/1.00  
% 3.12/1.00  fof(f22,plain,(
% 3.12/1.00    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.12/1.00    inference(ennf_transformation,[],[f1])).
% 3.12/1.00  
% 3.12/1.00  fof(f23,plain,(
% 3.12/1.00    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.12/1.00    inference(flattening,[],[f22])).
% 3.12/1.00  
% 3.12/1.00  fof(f47,plain,(
% 3.12/1.00    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.12/1.00    inference(cnf_transformation,[],[f23])).
% 3.12/1.00  
% 3.12/1.00  fof(f6,axiom,(
% 3.12/1.00    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 3.12/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.12/1.00  
% 3.12/1.00  fof(f55,plain,(
% 3.12/1.00    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 3.12/1.00    inference(cnf_transformation,[],[f6])).
% 3.12/1.00  
% 3.12/1.00  fof(f83,plain,(
% 3.12/1.00    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 3.12/1.00    inference(definition_unfolding,[],[f55,f69])).
% 3.12/1.00  
% 3.12/1.00  fof(f8,axiom,(
% 3.12/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & v2_funct_1(X0)) => k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) = k2_funct_1(k5_relat_1(X0,X1)))))),
% 3.12/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.12/1.00  
% 3.12/1.00  fof(f30,plain,(
% 3.12/1.00    ! [X0] : (! [X1] : ((k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) = k2_funct_1(k5_relat_1(X0,X1)) | (~v2_funct_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.12/1.00    inference(ennf_transformation,[],[f8])).
% 3.12/1.00  
% 3.12/1.00  fof(f31,plain,(
% 3.12/1.00    ! [X0] : (! [X1] : (k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) = k2_funct_1(k5_relat_1(X0,X1)) | ~v2_funct_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.12/1.00    inference(flattening,[],[f30])).
% 3.12/1.00  
% 3.12/1.00  fof(f58,plain,(
% 3.12/1.00    ( ! [X0,X1] : (k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) = k2_funct_1(k5_relat_1(X0,X1)) | ~v2_funct_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.12/1.00    inference(cnf_transformation,[],[f31])).
% 3.12/1.00  
% 3.12/1.00  fof(f9,axiom,(
% 3.12/1.00    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))),
% 3.12/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.12/1.00  
% 3.12/1.00  fof(f59,plain,(
% 3.12/1.00    ( ! [X0] : (k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))) )),
% 3.12/1.00    inference(cnf_transformation,[],[f9])).
% 3.12/1.00  
% 3.12/1.00  fof(f87,plain,(
% 3.12/1.00    ( ! [X0] : (k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0)) )),
% 3.12/1.00    inference(definition_unfolding,[],[f59,f69,f69])).
% 3.12/1.00  
% 3.12/1.00  fof(f5,axiom,(
% 3.12/1.00    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 3.12/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.12/1.00  
% 3.12/1.00  fof(f53,plain,(
% 3.12/1.00    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 3.12/1.00    inference(cnf_transformation,[],[f5])).
% 3.12/1.00  
% 3.12/1.00  fof(f81,plain,(
% 3.12/1.00    ( ! [X0] : (v1_funct_1(k6_partfun1(X0))) )),
% 3.12/1.00    inference(definition_unfolding,[],[f53,f69])).
% 3.12/1.00  
% 3.12/1.00  fof(f54,plain,(
% 3.12/1.00    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 3.12/1.00    inference(cnf_transformation,[],[f6])).
% 3.12/1.00  
% 3.12/1.00  fof(f84,plain,(
% 3.12/1.00    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 3.12/1.00    inference(definition_unfolding,[],[f54,f69])).
% 3.12/1.00  
% 3.12/1.00  fof(f79,plain,(
% 3.12/1.00    k2_funct_1(sK2) != sK3),
% 3.12/1.00    inference(cnf_transformation,[],[f46])).
% 3.12/1.00  
% 3.12/1.00  cnf(c_28,negated_conjecture,
% 3.12/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 3.12/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_506,negated_conjecture,
% 3.12/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 3.12/1.00      inference(subtyping,[status(esa)],[c_28]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_991,plain,
% 3.12/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.12/1.00      inference(predicate_to_equality,[status(thm)],[c_506]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_13,plain,
% 3.12/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.12/1.00      | v1_relat_1(X0) ),
% 3.12/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_517,plain,
% 3.12/1.00      ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 3.12/1.00      | v1_relat_1(X0_49) ),
% 3.12/1.00      inference(subtyping,[status(esa)],[c_13]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_984,plain,
% 3.12/1.00      ( m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 3.12/1.00      | v1_relat_1(X0_49) = iProver_top ),
% 3.12/1.00      inference(predicate_to_equality,[status(thm)],[c_517]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_1524,plain,
% 3.12/1.00      ( v1_relat_1(sK3) = iProver_top ),
% 3.12/1.00      inference(superposition,[status(thm)],[c_991,c_984]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_30,negated_conjecture,
% 3.12/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.12/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_504,negated_conjecture,
% 3.12/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.12/1.00      inference(subtyping,[status(esa)],[c_30]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_993,plain,
% 3.12/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.12/1.00      inference(predicate_to_equality,[status(thm)],[c_504]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_1525,plain,
% 3.12/1.00      ( v1_relat_1(sK2) = iProver_top ),
% 3.12/1.00      inference(superposition,[status(thm)],[c_993,c_984]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_31,negated_conjecture,
% 3.12/1.00      ( v1_funct_1(sK2) ),
% 3.12/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_503,negated_conjecture,
% 3.12/1.00      ( v1_funct_1(sK2) ),
% 3.12/1.00      inference(subtyping,[status(esa)],[c_31]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_994,plain,
% 3.12/1.00      ( v1_funct_1(sK2) = iProver_top ),
% 3.12/1.00      inference(predicate_to_equality,[status(thm)],[c_503]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_4,plain,
% 3.12/1.00      ( ~ v1_funct_1(X0)
% 3.12/1.00      | ~ v1_relat_1(X0)
% 3.12/1.00      | v1_relat_1(k2_funct_1(X0)) ),
% 3.12/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_525,plain,
% 3.12/1.00      ( ~ v1_funct_1(X0_49)
% 3.12/1.00      | ~ v1_relat_1(X0_49)
% 3.12/1.00      | v1_relat_1(k2_funct_1(X0_49)) ),
% 3.12/1.00      inference(subtyping,[status(esa)],[c_4]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_977,plain,
% 3.12/1.00      ( v1_funct_1(X0_49) != iProver_top
% 3.12/1.00      | v1_relat_1(X0_49) != iProver_top
% 3.12/1.00      | v1_relat_1(k2_funct_1(X0_49)) = iProver_top ),
% 3.12/1.00      inference(predicate_to_equality,[status(thm)],[c_525]) ).
% 3.12/1.00  
% 3.12/1.00  cnf(c_1,plain,
% 3.12/1.00      ( ~ v1_relat_1(X0)
% 3.12/1.00      | ~ v1_relat_1(X1)
% 3.12/1.01      | ~ v1_relat_1(X2)
% 3.12/1.01      | k5_relat_1(k5_relat_1(X2,X0),X1) = k5_relat_1(X2,k5_relat_1(X0,X1)) ),
% 3.12/1.01      inference(cnf_transformation,[],[f48]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_528,plain,
% 3.12/1.01      ( ~ v1_relat_1(X0_49)
% 3.12/1.01      | ~ v1_relat_1(X1_49)
% 3.12/1.01      | ~ v1_relat_1(X2_49)
% 3.12/1.01      | k5_relat_1(k5_relat_1(X2_49,X0_49),X1_49) = k5_relat_1(X2_49,k5_relat_1(X0_49,X1_49)) ),
% 3.12/1.01      inference(subtyping,[status(esa)],[c_1]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_974,plain,
% 3.12/1.01      ( k5_relat_1(k5_relat_1(X0_49,X1_49),X2_49) = k5_relat_1(X0_49,k5_relat_1(X1_49,X2_49))
% 3.12/1.01      | v1_relat_1(X1_49) != iProver_top
% 3.12/1.01      | v1_relat_1(X2_49) != iProver_top
% 3.12/1.01      | v1_relat_1(X0_49) != iProver_top ),
% 3.12/1.01      inference(predicate_to_equality,[status(thm)],[c_528]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_3119,plain,
% 3.12/1.01      ( k5_relat_1(k2_funct_1(X0_49),k5_relat_1(X1_49,X2_49)) = k5_relat_1(k5_relat_1(k2_funct_1(X0_49),X1_49),X2_49)
% 3.12/1.01      | v1_funct_1(X0_49) != iProver_top
% 3.12/1.01      | v1_relat_1(X0_49) != iProver_top
% 3.12/1.01      | v1_relat_1(X1_49) != iProver_top
% 3.12/1.01      | v1_relat_1(X2_49) != iProver_top ),
% 3.12/1.01      inference(superposition,[status(thm)],[c_977,c_974]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_6561,plain,
% 3.12/1.01      ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0_49),X1_49) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0_49,X1_49))
% 3.12/1.01      | v1_relat_1(X0_49) != iProver_top
% 3.12/1.01      | v1_relat_1(X1_49) != iProver_top
% 3.12/1.01      | v1_relat_1(sK2) != iProver_top ),
% 3.12/1.01      inference(superposition,[status(thm)],[c_994,c_3119]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_33,plain,
% 3.12/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.12/1.01      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_1192,plain,
% 3.12/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.12/1.01      | v1_relat_1(sK2) ),
% 3.12/1.01      inference(instantiation,[status(thm)],[c_517]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_1193,plain,
% 3.12/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.12/1.01      | v1_relat_1(sK2) = iProver_top ),
% 3.12/1.01      inference(predicate_to_equality,[status(thm)],[c_1192]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_6924,plain,
% 3.12/1.01      ( v1_relat_1(X1_49) != iProver_top
% 3.12/1.01      | v1_relat_1(X0_49) != iProver_top
% 3.12/1.01      | k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0_49),X1_49) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0_49,X1_49)) ),
% 3.12/1.01      inference(global_propositional_subsumption,
% 3.12/1.01                [status(thm)],
% 3.12/1.01                [c_6561,c_33,c_1193]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_6925,plain,
% 3.12/1.01      ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0_49),X1_49) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0_49,X1_49))
% 3.12/1.01      | v1_relat_1(X0_49) != iProver_top
% 3.12/1.01      | v1_relat_1(X1_49) != iProver_top ),
% 3.12/1.01      inference(renaming,[status(thm)],[c_6924]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_6933,plain,
% 3.12/1.01      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0_49)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),X0_49)
% 3.12/1.01      | v1_relat_1(X0_49) != iProver_top ),
% 3.12/1.01      inference(superposition,[status(thm)],[c_1525,c_6925]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_25,negated_conjecture,
% 3.12/1.01      ( v2_funct_1(sK2) ),
% 3.12/1.01      inference(cnf_transformation,[],[f76]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_508,negated_conjecture,
% 3.12/1.01      ( v2_funct_1(sK2) ),
% 3.12/1.01      inference(subtyping,[status(esa)],[c_25]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_990,plain,
% 3.12/1.01      ( v2_funct_1(sK2) = iProver_top ),
% 3.12/1.01      inference(predicate_to_equality,[status(thm)],[c_508]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_9,plain,
% 3.12/1.01      ( ~ v2_funct_1(X0)
% 3.12/1.01      | ~ v1_funct_1(X0)
% 3.12/1.01      | ~ v1_relat_1(X0)
% 3.12/1.01      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
% 3.12/1.01      inference(cnf_transformation,[],[f85]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_521,plain,
% 3.12/1.01      ( ~ v2_funct_1(X0_49)
% 3.12/1.01      | ~ v1_funct_1(X0_49)
% 3.12/1.01      | ~ v1_relat_1(X0_49)
% 3.12/1.01      | k5_relat_1(k2_funct_1(X0_49),X0_49) = k6_partfun1(k2_relat_1(X0_49)) ),
% 3.12/1.01      inference(subtyping,[status(esa)],[c_9]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_981,plain,
% 3.12/1.01      ( k5_relat_1(k2_funct_1(X0_49),X0_49) = k6_partfun1(k2_relat_1(X0_49))
% 3.12/1.01      | v2_funct_1(X0_49) != iProver_top
% 3.12/1.01      | v1_funct_1(X0_49) != iProver_top
% 3.12/1.01      | v1_relat_1(X0_49) != iProver_top ),
% 3.12/1.01      inference(predicate_to_equality,[status(thm)],[c_521]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_2243,plain,
% 3.12/1.01      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
% 3.12/1.01      | v1_funct_1(sK2) != iProver_top
% 3.12/1.01      | v1_relat_1(sK2) != iProver_top ),
% 3.12/1.01      inference(superposition,[status(thm)],[c_990,c_981]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_15,plain,
% 3.12/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.12/1.01      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.12/1.01      inference(cnf_transformation,[],[f62]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_516,plain,
% 3.12/1.01      ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 3.12/1.01      | k2_relset_1(X0_51,X1_51,X0_49) = k2_relat_1(X0_49) ),
% 3.12/1.01      inference(subtyping,[status(esa)],[c_15]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_985,plain,
% 3.12/1.01      ( k2_relset_1(X0_51,X1_51,X0_49) = k2_relat_1(X0_49)
% 3.12/1.01      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top ),
% 3.12/1.01      inference(predicate_to_equality,[status(thm)],[c_516]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_1943,plain,
% 3.12/1.01      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 3.12/1.01      inference(superposition,[status(thm)],[c_993,c_985]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_27,negated_conjecture,
% 3.12/1.01      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 3.12/1.01      inference(cnf_transformation,[],[f74]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_507,negated_conjecture,
% 3.12/1.01      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 3.12/1.01      inference(subtyping,[status(esa)],[c_27]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_1948,plain,
% 3.12/1.01      ( k2_relat_1(sK2) = sK1 ),
% 3.12/1.01      inference(light_normalisation,[status(thm)],[c_1943,c_507]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_2256,plain,
% 3.12/1.01      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 3.12/1.01      | v1_funct_1(sK2) != iProver_top
% 3.12/1.01      | v1_relat_1(sK2) != iProver_top ),
% 3.12/1.01      inference(light_normalisation,[status(thm)],[c_2243,c_1948]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_32,plain,
% 3.12/1.01      ( v1_funct_1(sK2) = iProver_top ),
% 3.12/1.01      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_2401,plain,
% 3.12/1.01      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
% 3.12/1.01      inference(global_propositional_subsumption,
% 3.12/1.01                [status(thm)],
% 3.12/1.01                [c_2256,c_32,c_33,c_1193]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_6956,plain,
% 3.12/1.01      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0_49)) = k5_relat_1(k6_partfun1(sK1),X0_49)
% 3.12/1.01      | v1_relat_1(X0_49) != iProver_top ),
% 3.12/1.01      inference(light_normalisation,[status(thm)],[c_6933,c_2401]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_7003,plain,
% 3.12/1.01      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
% 3.12/1.01      inference(superposition,[status(thm)],[c_1524,c_6956]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_21,plain,
% 3.12/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.12/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.12/1.01      | ~ v1_funct_1(X0)
% 3.12/1.01      | ~ v1_funct_1(X3)
% 3.12/1.01      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.12/1.01      inference(cnf_transformation,[],[f68]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_512,plain,
% 3.12/1.01      ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 3.12/1.01      | ~ m1_subset_1(X1_49,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51)))
% 3.12/1.01      | ~ v1_funct_1(X0_49)
% 3.12/1.01      | ~ v1_funct_1(X1_49)
% 3.12/1.01      | k1_partfun1(X2_51,X3_51,X0_51,X1_51,X1_49,X0_49) = k5_relat_1(X1_49,X0_49) ),
% 3.12/1.01      inference(subtyping,[status(esa)],[c_21]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_989,plain,
% 3.12/1.01      ( k1_partfun1(X0_51,X1_51,X2_51,X3_51,X0_49,X1_49) = k5_relat_1(X0_49,X1_49)
% 3.12/1.01      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 3.12/1.01      | m1_subset_1(X1_49,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51))) != iProver_top
% 3.12/1.01      | v1_funct_1(X1_49) != iProver_top
% 3.12/1.01      | v1_funct_1(X0_49) != iProver_top ),
% 3.12/1.01      inference(predicate_to_equality,[status(thm)],[c_512]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_3383,plain,
% 3.12/1.01      ( k1_partfun1(X0_51,X1_51,sK1,sK0,X0_49,sK3) = k5_relat_1(X0_49,sK3)
% 3.12/1.01      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 3.12/1.01      | v1_funct_1(X0_49) != iProver_top
% 3.12/1.01      | v1_funct_1(sK3) != iProver_top ),
% 3.12/1.01      inference(superposition,[status(thm)],[c_991,c_989]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_29,negated_conjecture,
% 3.12/1.01      ( v1_funct_1(sK3) ),
% 3.12/1.01      inference(cnf_transformation,[],[f72]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_34,plain,
% 3.12/1.01      ( v1_funct_1(sK3) = iProver_top ),
% 3.12/1.01      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_3771,plain,
% 3.12/1.01      ( v1_funct_1(X0_49) != iProver_top
% 3.12/1.01      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 3.12/1.01      | k1_partfun1(X0_51,X1_51,sK1,sK0,X0_49,sK3) = k5_relat_1(X0_49,sK3) ),
% 3.12/1.01      inference(global_propositional_subsumption,
% 3.12/1.01                [status(thm)],
% 3.12/1.01                [c_3383,c_34]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_3772,plain,
% 3.12/1.01      ( k1_partfun1(X0_51,X1_51,sK1,sK0,X0_49,sK3) = k5_relat_1(X0_49,sK3)
% 3.12/1.01      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 3.12/1.01      | v1_funct_1(X0_49) != iProver_top ),
% 3.12/1.01      inference(renaming,[status(thm)],[c_3771]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_3781,plain,
% 3.12/1.01      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 3.12/1.01      | v1_funct_1(sK2) != iProver_top ),
% 3.12/1.01      inference(superposition,[status(thm)],[c_993,c_3772]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_17,plain,
% 3.12/1.01      ( ~ r2_relset_1(X0,X1,X2,X3)
% 3.12/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.12/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.12/1.01      | X3 = X2 ),
% 3.12/1.01      inference(cnf_transformation,[],[f63]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_26,negated_conjecture,
% 3.12/1.01      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 3.12/1.01      inference(cnf_transformation,[],[f75]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_327,plain,
% 3.12/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.12/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.12/1.01      | X3 = X0
% 3.12/1.01      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 3.12/1.01      | k6_partfun1(sK0) != X3
% 3.12/1.01      | sK0 != X2
% 3.12/1.01      | sK0 != X1 ),
% 3.12/1.01      inference(resolution_lifted,[status(thm)],[c_17,c_26]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_328,plain,
% 3.12/1.01      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.12/1.01      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.12/1.01      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.12/1.01      inference(unflattening,[status(thm)],[c_327]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_18,plain,
% 3.12/1.01      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.12/1.01      inference(cnf_transformation,[],[f88]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_48,plain,
% 3.12/1.01      ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.12/1.01      inference(instantiation,[status(thm)],[c_18]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_330,plain,
% 3.12/1.01      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.12/1.01      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.12/1.01      inference(global_propositional_subsumption,
% 3.12/1.01                [status(thm)],
% 3.12/1.01                [c_328,c_48]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_501,plain,
% 3.12/1.01      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.12/1.01      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.12/1.01      inference(subtyping,[status(esa)],[c_330]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_996,plain,
% 3.12/1.01      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.12/1.01      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.12/1.01      inference(predicate_to_equality,[status(thm)],[c_501]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_19,plain,
% 3.12/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.12/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.12/1.01      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.12/1.01      | ~ v1_funct_1(X0)
% 3.12/1.01      | ~ v1_funct_1(X3) ),
% 3.12/1.01      inference(cnf_transformation,[],[f67]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_514,plain,
% 3.12/1.01      ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 3.12/1.01      | ~ m1_subset_1(X1_49,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51)))
% 3.12/1.01      | m1_subset_1(k1_partfun1(X2_51,X3_51,X0_51,X1_51,X1_49,X0_49),k1_zfmisc_1(k2_zfmisc_1(X2_51,X1_51)))
% 3.12/1.01      | ~ v1_funct_1(X0_49)
% 3.12/1.01      | ~ v1_funct_1(X1_49) ),
% 3.12/1.01      inference(subtyping,[status(esa)],[c_19]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_1305,plain,
% 3.12/1.01      ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 3.12/1.01      | m1_subset_1(k1_partfun1(X0_51,X1_51,sK1,sK0,X0_49,sK3),k1_zfmisc_1(k2_zfmisc_1(X0_51,sK0)))
% 3.12/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.12/1.01      | ~ v1_funct_1(X0_49)
% 3.12/1.01      | ~ v1_funct_1(sK3) ),
% 3.12/1.01      inference(instantiation,[status(thm)],[c_514]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_1447,plain,
% 3.12/1.01      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.12/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.12/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.12/1.01      | ~ v1_funct_1(sK3)
% 3.12/1.01      | ~ v1_funct_1(sK2) ),
% 3.12/1.01      inference(instantiation,[status(thm)],[c_1305]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_1476,plain,
% 3.12/1.01      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.12/1.01      inference(global_propositional_subsumption,
% 3.12/1.01                [status(thm)],
% 3.12/1.01                [c_996,c_31,c_30,c_29,c_28,c_501,c_1447]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_3790,plain,
% 3.12/1.01      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 3.12/1.01      | v1_funct_1(sK2) != iProver_top ),
% 3.12/1.01      inference(light_normalisation,[status(thm)],[c_3781,c_1476]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_4785,plain,
% 3.12/1.01      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 3.12/1.01      inference(global_propositional_subsumption,
% 3.12/1.01                [status(thm)],
% 3.12/1.01                [c_3790,c_32]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_7017,plain,
% 3.12/1.01      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
% 3.12/1.01      inference(light_normalisation,[status(thm)],[c_7003,c_4785]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_2,plain,
% 3.12/1.01      ( ~ v1_relat_1(X0)
% 3.12/1.01      | k5_relat_1(k6_partfun1(X1),X0) = k7_relat_1(X0,X1) ),
% 3.12/1.01      inference(cnf_transformation,[],[f80]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_527,plain,
% 3.12/1.01      ( ~ v1_relat_1(X0_49)
% 3.12/1.01      | k5_relat_1(k6_partfun1(X0_51),X0_49) = k7_relat_1(X0_49,X0_51) ),
% 3.12/1.01      inference(subtyping,[status(esa)],[c_2]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_975,plain,
% 3.12/1.01      ( k5_relat_1(k6_partfun1(X0_51),X0_49) = k7_relat_1(X0_49,X0_51)
% 3.12/1.01      | v1_relat_1(X0_49) != iProver_top ),
% 3.12/1.01      inference(predicate_to_equality,[status(thm)],[c_527]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_1584,plain,
% 3.12/1.01      ( k5_relat_1(k6_partfun1(X0_51),sK3) = k7_relat_1(sK3,X0_51) ),
% 3.12/1.01      inference(superposition,[status(thm)],[c_1524,c_975]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_14,plain,
% 3.12/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.12/1.01      | v4_relat_1(X0,X1) ),
% 3.12/1.01      inference(cnf_transformation,[],[f61]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_0,plain,
% 3.12/1.01      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 3.12/1.01      inference(cnf_transformation,[],[f47]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_305,plain,
% 3.12/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.12/1.01      | ~ v1_relat_1(X0)
% 3.12/1.01      | k7_relat_1(X0,X1) = X0 ),
% 3.12/1.01      inference(resolution,[status(thm)],[c_14,c_0]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_309,plain,
% 3.12/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.12/1.01      | k7_relat_1(X0,X1) = X0 ),
% 3.12/1.01      inference(global_propositional_subsumption,
% 3.12/1.01                [status(thm)],
% 3.12/1.01                [c_305,c_14,c_13,c_0]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_502,plain,
% 3.12/1.01      ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 3.12/1.01      | k7_relat_1(X0_49,X0_51) = X0_49 ),
% 3.12/1.01      inference(subtyping,[status(esa)],[c_309]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_995,plain,
% 3.12/1.01      ( k7_relat_1(X0_49,X0_51) = X0_49
% 3.12/1.01      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top ),
% 3.12/1.01      inference(predicate_to_equality,[status(thm)],[c_502]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_2614,plain,
% 3.12/1.01      ( k7_relat_1(sK3,sK1) = sK3 ),
% 3.12/1.01      inference(superposition,[status(thm)],[c_991,c_995]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_2615,plain,
% 3.12/1.01      ( k7_relat_1(sK2,sK0) = sK2 ),
% 3.12/1.01      inference(superposition,[status(thm)],[c_993,c_995]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_7,plain,
% 3.12/1.01      ( v2_funct_1(k6_partfun1(X0)) ),
% 3.12/1.01      inference(cnf_transformation,[],[f83]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_522,plain,
% 3.12/1.01      ( v2_funct_1(k6_partfun1(X0_51)) ),
% 3.12/1.01      inference(subtyping,[status(esa)],[c_7]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_980,plain,
% 3.12/1.01      ( v2_funct_1(k6_partfun1(X0_51)) = iProver_top ),
% 3.12/1.01      inference(predicate_to_equality,[status(thm)],[c_522]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_11,plain,
% 3.12/1.01      ( ~ v2_funct_1(X0)
% 3.12/1.01      | ~ v2_funct_1(X1)
% 3.12/1.01      | ~ v1_funct_1(X0)
% 3.12/1.01      | ~ v1_funct_1(X1)
% 3.12/1.01      | ~ v1_relat_1(X1)
% 3.12/1.01      | ~ v1_relat_1(X0)
% 3.12/1.01      | k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) = k2_funct_1(k5_relat_1(X0,X1)) ),
% 3.12/1.01      inference(cnf_transformation,[],[f58]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_519,plain,
% 3.12/1.01      ( ~ v2_funct_1(X0_49)
% 3.12/1.01      | ~ v2_funct_1(X1_49)
% 3.12/1.01      | ~ v1_funct_1(X0_49)
% 3.12/1.01      | ~ v1_funct_1(X1_49)
% 3.12/1.01      | ~ v1_relat_1(X1_49)
% 3.12/1.01      | ~ v1_relat_1(X0_49)
% 3.12/1.01      | k5_relat_1(k2_funct_1(X1_49),k2_funct_1(X0_49)) = k2_funct_1(k5_relat_1(X0_49,X1_49)) ),
% 3.12/1.01      inference(subtyping,[status(esa)],[c_11]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_983,plain,
% 3.12/1.01      ( k5_relat_1(k2_funct_1(X0_49),k2_funct_1(X1_49)) = k2_funct_1(k5_relat_1(X1_49,X0_49))
% 3.12/1.01      | v2_funct_1(X0_49) != iProver_top
% 3.12/1.01      | v2_funct_1(X1_49) != iProver_top
% 3.12/1.01      | v1_funct_1(X1_49) != iProver_top
% 3.12/1.01      | v1_funct_1(X0_49) != iProver_top
% 3.12/1.01      | v1_relat_1(X1_49) != iProver_top
% 3.12/1.01      | v1_relat_1(X0_49) != iProver_top ),
% 3.12/1.01      inference(predicate_to_equality,[status(thm)],[c_519]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_3532,plain,
% 3.12/1.01      ( k5_relat_1(k2_funct_1(X0_49),k2_funct_1(k6_partfun1(X0_51))) = k2_funct_1(k5_relat_1(k6_partfun1(X0_51),X0_49))
% 3.12/1.01      | v2_funct_1(X0_49) != iProver_top
% 3.12/1.01      | v1_funct_1(X0_49) != iProver_top
% 3.12/1.01      | v1_funct_1(k6_partfun1(X0_51)) != iProver_top
% 3.12/1.01      | v1_relat_1(X0_49) != iProver_top
% 3.12/1.01      | v1_relat_1(k6_partfun1(X0_51)) != iProver_top ),
% 3.12/1.01      inference(superposition,[status(thm)],[c_980,c_983]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_12,plain,
% 3.12/1.01      ( k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
% 3.12/1.01      inference(cnf_transformation,[],[f87]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_518,plain,
% 3.12/1.01      ( k2_funct_1(k6_partfun1(X0_51)) = k6_partfun1(X0_51) ),
% 3.12/1.01      inference(subtyping,[status(esa)],[c_12]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_3539,plain,
% 3.12/1.01      ( k2_funct_1(k5_relat_1(k6_partfun1(X0_51),X0_49)) = k5_relat_1(k2_funct_1(X0_49),k6_partfun1(X0_51))
% 3.12/1.01      | v2_funct_1(X0_49) != iProver_top
% 3.12/1.01      | v1_funct_1(X0_49) != iProver_top
% 3.12/1.01      | v1_funct_1(k6_partfun1(X0_51)) != iProver_top
% 3.12/1.01      | v1_relat_1(X0_49) != iProver_top
% 3.12/1.01      | v1_relat_1(k6_partfun1(X0_51)) != iProver_top ),
% 3.12/1.01      inference(light_normalisation,[status(thm)],[c_3532,c_518]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_5,plain,
% 3.12/1.01      ( v1_funct_1(k6_partfun1(X0)) ),
% 3.12/1.01      inference(cnf_transformation,[],[f81]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_524,plain,
% 3.12/1.01      ( v1_funct_1(k6_partfun1(X0_51)) ),
% 3.12/1.01      inference(subtyping,[status(esa)],[c_5]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_575,plain,
% 3.12/1.01      ( v1_funct_1(k6_partfun1(X0_51)) = iProver_top ),
% 3.12/1.01      inference(predicate_to_equality,[status(thm)],[c_524]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_8,plain,
% 3.12/1.01      ( v1_relat_1(k6_partfun1(X0)) ),
% 3.12/1.01      inference(cnf_transformation,[],[f84]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_523,plain,
% 3.12/1.01      ( v1_relat_1(k6_partfun1(X0_51)) ),
% 3.12/1.01      inference(subtyping,[status(esa)],[c_8]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_576,plain,
% 3.12/1.01      ( v1_relat_1(k6_partfun1(X0_51)) = iProver_top ),
% 3.12/1.01      inference(predicate_to_equality,[status(thm)],[c_523]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_4641,plain,
% 3.12/1.01      ( v1_relat_1(X0_49) != iProver_top
% 3.12/1.01      | k2_funct_1(k5_relat_1(k6_partfun1(X0_51),X0_49)) = k5_relat_1(k2_funct_1(X0_49),k6_partfun1(X0_51))
% 3.12/1.01      | v2_funct_1(X0_49) != iProver_top
% 3.12/1.01      | v1_funct_1(X0_49) != iProver_top ),
% 3.12/1.01      inference(global_propositional_subsumption,
% 3.12/1.01                [status(thm)],
% 3.12/1.01                [c_3539,c_575,c_576]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_4642,plain,
% 3.12/1.01      ( k2_funct_1(k5_relat_1(k6_partfun1(X0_51),X0_49)) = k5_relat_1(k2_funct_1(X0_49),k6_partfun1(X0_51))
% 3.12/1.01      | v2_funct_1(X0_49) != iProver_top
% 3.12/1.01      | v1_funct_1(X0_49) != iProver_top
% 3.12/1.01      | v1_relat_1(X0_49) != iProver_top ),
% 3.12/1.01      inference(renaming,[status(thm)],[c_4641]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_4651,plain,
% 3.12/1.01      ( k2_funct_1(k5_relat_1(k6_partfun1(X0_51),sK2)) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0_51))
% 3.12/1.01      | v1_funct_1(sK2) != iProver_top
% 3.12/1.01      | v1_relat_1(sK2) != iProver_top ),
% 3.12/1.01      inference(superposition,[status(thm)],[c_990,c_4642]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_1588,plain,
% 3.12/1.01      ( k5_relat_1(k6_partfun1(X0_51),sK2) = k7_relat_1(sK2,X0_51) ),
% 3.12/1.01      inference(superposition,[status(thm)],[c_1525,c_975]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_4664,plain,
% 3.12/1.01      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0_51)) = k2_funct_1(k7_relat_1(sK2,X0_51))
% 3.12/1.01      | v1_funct_1(sK2) != iProver_top
% 3.12/1.01      | v1_relat_1(sK2) != iProver_top ),
% 3.12/1.01      inference(light_normalisation,[status(thm)],[c_4651,c_1588]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_4805,plain,
% 3.12/1.01      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0_51)) = k2_funct_1(k7_relat_1(sK2,X0_51)) ),
% 3.12/1.01      inference(global_propositional_subsumption,
% 3.12/1.01                [status(thm)],
% 3.12/1.01                [c_4664,c_32,c_33,c_1193]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_7018,plain,
% 3.12/1.01      ( k2_funct_1(sK2) = sK3 ),
% 3.12/1.01      inference(demodulation,
% 3.12/1.01                [status(thm)],
% 3.12/1.01                [c_7017,c_1584,c_2614,c_2615,c_4805]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_22,negated_conjecture,
% 3.12/1.01      ( k2_funct_1(sK2) != sK3 ),
% 3.12/1.01      inference(cnf_transformation,[],[f79]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(c_511,negated_conjecture,
% 3.12/1.01      ( k2_funct_1(sK2) != sK3 ),
% 3.12/1.01      inference(subtyping,[status(esa)],[c_22]) ).
% 3.12/1.01  
% 3.12/1.01  cnf(contradiction,plain,
% 3.12/1.01      ( $false ),
% 3.12/1.01      inference(minisat,[status(thm)],[c_7018,c_511]) ).
% 3.12/1.01  
% 3.12/1.01  
% 3.12/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.12/1.01  
% 3.12/1.01  ------                               Statistics
% 3.12/1.01  
% 3.12/1.01  ------ General
% 3.12/1.01  
% 3.12/1.01  abstr_ref_over_cycles:                  0
% 3.12/1.01  abstr_ref_under_cycles:                 0
% 3.12/1.01  gc_basic_clause_elim:                   0
% 3.12/1.01  forced_gc_time:                         0
% 3.12/1.01  parsing_time:                           0.011
% 3.12/1.01  unif_index_cands_time:                  0.
% 3.12/1.01  unif_index_add_time:                    0.
% 3.12/1.01  orderings_time:                         0.
% 3.12/1.01  out_proof_time:                         0.013
% 3.12/1.01  total_time:                             0.265
% 3.12/1.01  num_of_symbols:                         56
% 3.12/1.01  num_of_terms:                           7841
% 3.12/1.01  
% 3.12/1.01  ------ Preprocessing
% 3.12/1.01  
% 3.12/1.01  num_of_splits:                          0
% 3.12/1.01  num_of_split_atoms:                     0
% 3.12/1.01  num_of_reused_defs:                     0
% 3.12/1.01  num_eq_ax_congr_red:                    14
% 3.12/1.01  num_of_sem_filtered_clauses:            1
% 3.12/1.01  num_of_subtypes:                        4
% 3.12/1.01  monotx_restored_types:                  0
% 3.12/1.01  sat_num_of_epr_types:                   0
% 3.12/1.01  sat_num_of_non_cyclic_types:            0
% 3.12/1.01  sat_guarded_non_collapsed_types:        1
% 3.12/1.01  num_pure_diseq_elim:                    0
% 3.12/1.01  simp_replaced_by:                       0
% 3.12/1.01  res_preprocessed:                       150
% 3.12/1.01  prep_upred:                             0
% 3.12/1.01  prep_unflattend:                        8
% 3.12/1.01  smt_new_axioms:                         0
% 3.12/1.01  pred_elim_cands:                        4
% 3.12/1.01  pred_elim:                              2
% 3.12/1.01  pred_elim_cl:                           3
% 3.12/1.01  pred_elim_cycles:                       4
% 3.12/1.01  merged_defs:                            0
% 3.12/1.01  merged_defs_ncl:                        0
% 3.12/1.01  bin_hyper_res:                          0
% 3.12/1.01  prep_cycles:                            4
% 3.12/1.01  pred_elim_time:                         0.001
% 3.12/1.01  splitting_time:                         0.
% 3.12/1.01  sem_filter_time:                        0.
% 3.12/1.01  monotx_time:                            0.
% 3.12/1.01  subtype_inf_time:                       0.
% 3.12/1.01  
% 3.12/1.01  ------ Problem properties
% 3.12/1.01  
% 3.12/1.01  clauses:                                28
% 3.12/1.01  conjectures:                            9
% 3.12/1.01  epr:                                    5
% 3.12/1.01  horn:                                   28
% 3.12/1.01  ground:                                 10
% 3.12/1.01  unary:                                  14
% 3.12/1.01  binary:                                 5
% 3.12/1.01  lits:                                   64
% 3.12/1.01  lits_eq:                                14
% 3.12/1.01  fd_pure:                                0
% 3.12/1.01  fd_pseudo:                              0
% 3.12/1.01  fd_cond:                                0
% 3.12/1.01  fd_pseudo_cond:                         0
% 3.12/1.01  ac_symbols:                             0
% 3.12/1.01  
% 3.12/1.01  ------ Propositional Solver
% 3.12/1.01  
% 3.12/1.01  prop_solver_calls:                      29
% 3.12/1.01  prop_fast_solver_calls:                 1027
% 3.12/1.01  smt_solver_calls:                       0
% 3.12/1.01  smt_fast_solver_calls:                  0
% 3.12/1.01  prop_num_of_clauses:                    3100
% 3.12/1.01  prop_preprocess_simplified:             6908
% 3.12/1.01  prop_fo_subsumed:                       60
% 3.12/1.01  prop_solver_time:                       0.
% 3.12/1.01  smt_solver_time:                        0.
% 3.12/1.01  smt_fast_solver_time:                   0.
% 3.12/1.01  prop_fast_solver_time:                  0.
% 3.12/1.01  prop_unsat_core_time:                   0.
% 3.12/1.01  
% 3.12/1.01  ------ QBF
% 3.12/1.01  
% 3.12/1.01  qbf_q_res:                              0
% 3.12/1.01  qbf_num_tautologies:                    0
% 3.12/1.01  qbf_prep_cycles:                        0
% 3.12/1.01  
% 3.12/1.01  ------ BMC1
% 3.12/1.01  
% 3.12/1.01  bmc1_current_bound:                     -1
% 3.12/1.01  bmc1_last_solved_bound:                 -1
% 3.12/1.01  bmc1_unsat_core_size:                   -1
% 3.12/1.01  bmc1_unsat_core_parents_size:           -1
% 3.12/1.01  bmc1_merge_next_fun:                    0
% 3.12/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.12/1.01  
% 3.12/1.01  ------ Instantiation
% 3.12/1.01  
% 3.12/1.01  inst_num_of_clauses:                    822
% 3.12/1.01  inst_num_in_passive:                    284
% 3.12/1.01  inst_num_in_active:                     508
% 3.12/1.01  inst_num_in_unprocessed:                30
% 3.12/1.01  inst_num_of_loops:                      540
% 3.12/1.01  inst_num_of_learning_restarts:          0
% 3.12/1.01  inst_num_moves_active_passive:          29
% 3.12/1.01  inst_lit_activity:                      0
% 3.12/1.01  inst_lit_activity_moves:                1
% 3.12/1.01  inst_num_tautologies:                   0
% 3.12/1.01  inst_num_prop_implied:                  0
% 3.12/1.01  inst_num_existing_simplified:           0
% 3.12/1.01  inst_num_eq_res_simplified:             0
% 3.12/1.01  inst_num_child_elim:                    0
% 3.12/1.01  inst_num_of_dismatching_blockings:      197
% 3.12/1.01  inst_num_of_non_proper_insts:           389
% 3.12/1.01  inst_num_of_duplicates:                 0
% 3.12/1.01  inst_inst_num_from_inst_to_res:         0
% 3.12/1.01  inst_dismatching_checking_time:         0.
% 3.12/1.01  
% 3.12/1.01  ------ Resolution
% 3.12/1.01  
% 3.12/1.01  res_num_of_clauses:                     0
% 3.12/1.01  res_num_in_passive:                     0
% 3.12/1.01  res_num_in_active:                      0
% 3.12/1.01  res_num_of_loops:                       154
% 3.12/1.01  res_forward_subset_subsumed:            29
% 3.12/1.01  res_backward_subset_subsumed:           0
% 3.12/1.01  res_forward_subsumed:                   0
% 3.12/1.01  res_backward_subsumed:                  0
% 3.12/1.01  res_forward_subsumption_resolution:     0
% 3.12/1.01  res_backward_subsumption_resolution:    0
% 3.12/1.01  res_clause_to_clause_subsumption:       463
% 3.12/1.01  res_orphan_elimination:                 0
% 3.12/1.01  res_tautology_del:                      18
% 3.12/1.01  res_num_eq_res_simplified:              0
% 3.12/1.01  res_num_sel_changes:                    0
% 3.12/1.01  res_moves_from_active_to_pass:          0
% 3.12/1.01  
% 3.12/1.01  ------ Superposition
% 3.12/1.01  
% 3.12/1.01  sup_time_total:                         0.
% 3.12/1.01  sup_time_generating:                    0.
% 3.12/1.01  sup_time_sim_full:                      0.
% 3.12/1.01  sup_time_sim_immed:                     0.
% 3.12/1.01  
% 3.12/1.01  sup_num_of_clauses:                     250
% 3.12/1.01  sup_num_in_active:                      106
% 3.12/1.01  sup_num_in_passive:                     144
% 3.12/1.01  sup_num_of_loops:                       106
% 3.12/1.01  sup_fw_superposition:                   160
% 3.12/1.01  sup_bw_superposition:                   128
% 3.12/1.01  sup_immediate_simplified:               108
% 3.12/1.01  sup_given_eliminated:                   1
% 3.12/1.01  comparisons_done:                       0
% 3.12/1.01  comparisons_avoided:                    0
% 3.12/1.01  
% 3.12/1.01  ------ Simplifications
% 3.12/1.01  
% 3.12/1.01  
% 3.12/1.01  sim_fw_subset_subsumed:                 3
% 3.12/1.01  sim_bw_subset_subsumed:                 5
% 3.12/1.01  sim_fw_subsumed:                        14
% 3.12/1.01  sim_bw_subsumed:                        0
% 3.12/1.01  sim_fw_subsumption_res:                 1
% 3.12/1.01  sim_bw_subsumption_res:                 0
% 3.12/1.01  sim_tautology_del:                      3
% 3.12/1.01  sim_eq_tautology_del:                   8
% 3.12/1.01  sim_eq_res_simp:                        0
% 3.12/1.01  sim_fw_demodulated:                     12
% 3.12/1.01  sim_bw_demodulated:                     5
% 3.12/1.01  sim_light_normalised:                   90
% 3.12/1.01  sim_joinable_taut:                      0
% 3.12/1.01  sim_joinable_simp:                      0
% 3.12/1.01  sim_ac_normalised:                      0
% 3.12/1.01  sim_smt_subsumption:                    0
% 3.12/1.01  
%------------------------------------------------------------------------------
