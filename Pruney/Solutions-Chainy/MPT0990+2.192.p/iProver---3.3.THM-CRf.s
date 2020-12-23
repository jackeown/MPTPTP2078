%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:37 EST 2020

% Result     : Theorem 7.65s
% Output     : CNFRefutation 7.65s
% Verified   : 
% Statistics : Number of formulae       :  203 (3316 expanded)
%              Number of clauses        :  130 ( 920 expanded)
%              Number of leaves         :   23 ( 887 expanded)
%              Depth                    :   23
%              Number of atoms          :  780 (28741 expanded)
%              Number of equality atoms :  403 (10512 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f12,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f81,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f48,f59])).

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

fof(f41,plain,(
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

fof(f40,plain,
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

fof(f42,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f38,f41,f40])).

fof(f74,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f42])).

fof(f10,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f57,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f67,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f69,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f42])).

fof(f70,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f72,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f42])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f28,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f27])).

fof(f56,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f73,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f42])).

fof(f14,axiom,(
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

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f63,plain,(
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
    inference(cnf_transformation,[],[f34])).

fof(f68,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f71,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f76,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f42])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f49,plain,(
    ! [X0] :
      ( k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f84,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f49,f59])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

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

fof(f43,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f6,axiom,(
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
    inference(ennf_transformation,[],[f6])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f51,f59])).

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

fof(f13,axiom,(
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

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f75,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f29])).

fof(f58,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f15,axiom,(
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

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f3,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f79,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f46,f59])).

fof(f77,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f42])).

fof(f78,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_4,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1115,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_11,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_27,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_362,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_27])).

cnf(c_363,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_362])).

cnf(c_14,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_371,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_363,c_14])).

cnf(c_1091,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_371])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1200,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1787,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1091,c_34,c_32,c_31,c_29,c_371,c_1200])).

cnf(c_28,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_18,plain,
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
    inference(cnf_transformation,[],[f63])).

cnf(c_1104,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k1_xboole_0 = X3
    | v1_funct_2(X2,X0,X1) != iProver_top
    | v1_funct_2(X4,X1,X3) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v2_funct_1(X4) = iProver_top
    | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4653,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_28,c_1104])).

cnf(c_35,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_36,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_37,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_4846,plain,
    ( v1_funct_1(X1) != iProver_top
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | k1_xboole_0 = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4653,c_35,c_36,c_37])).

cnf(c_4847,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4846])).

cnf(c_4850,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1787,c_4847])).

cnf(c_38,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_39,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_40,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_25,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_621,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_652,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_621])).

cnf(c_622,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1198,plain,
    ( sK0 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_622])).

cnf(c_1199,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1198])).

cnf(c_4970,plain,
    ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4850,c_38,c_39,c_40,c_25,c_652,c_1199])).

cnf(c_4974,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1115,c_4970])).

cnf(c_1096,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_7,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1112,plain,
    ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2505,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1096,c_1112])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1116,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1098,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1117,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2285,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1098,c_1117])).

cnf(c_2401,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1116,c_2285])).

cnf(c_2570,plain,
    ( v2_funct_1(sK3) != iProver_top
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2505,c_2401])).

cnf(c_2571,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
    | v2_funct_1(sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_2570])).

cnf(c_4984,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3)) ),
    inference(superposition,[status(thm)],[c_4974,c_2571])).

cnf(c_8,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
    | k2_funct_1(X0) = X1
    | k1_relat_1(X0) != k2_relat_1(X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1111,plain,
    ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k1_relat_1(X1) != k2_relat_1(X0)
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4985,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = sK3
    | k1_relat_1(k2_funct_1(sK3)) != k2_relat_1(sK3)
    | k6_partfun1(k2_relat_1(k2_funct_1(sK3))) != k6_partfun1(k1_relat_1(sK3))
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4984,c_1111])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1110,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1988,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1098,c_1110])).

cnf(c_16,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_375,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k1_partfun1(X1,X2,X2,X1,X0,X3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X2,X1,X3) = X1
    | k6_partfun1(X1) != k6_partfun1(sK0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_27])).

cnf(c_376,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X0)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0
    | k6_partfun1(sK0) != k6_partfun1(sK0) ),
    inference(unflattening,[status(thm)],[c_375])).

cnf(c_458,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_376])).

cnf(c_1090,plain,
    ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X0,sK0,X2) = sK0
    | v1_funct_2(X2,X0,sK0) != iProver_top
    | v1_funct_2(X1,sK0,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_458])).

cnf(c_1637,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1090])).

cnf(c_1794,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1637,c_35,c_36,c_37,c_38,c_39,c_40])).

cnf(c_1991,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_1988,c_1794])).

cnf(c_4986,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = sK3
    | k1_relat_1(k2_funct_1(sK3)) != sK0
    | k6_partfun1(k2_relat_1(k2_funct_1(sK3))) != k6_partfun1(k1_relat_1(sK3))
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4985,c_1991])).

cnf(c_26,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_42,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_1095,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_2286,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1095,c_1117])).

cnf(c_2404,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1116,c_2286])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1106,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2673,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1098,c_1106])).

cnf(c_3260,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2673,c_38])).

cnf(c_3261,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_3260])).

cnf(c_3269,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1095,c_3261])).

cnf(c_3270,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3269,c_1787])).

cnf(c_4279,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3270,c_35])).

cnf(c_4281,plain,
    ( k2_funct_1(sK3) = sK2
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4279,c_1111])).

cnf(c_1989,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1095,c_1110])).

cnf(c_1990,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_1989,c_28])).

cnf(c_4282,plain,
    ( k2_funct_1(sK3) = sK2
    | k1_relat_1(sK3) != sK1
    | k6_partfun1(sK0) != k6_partfun1(sK0)
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4281,c_1990,c_1991])).

cnf(c_4283,plain,
    ( k2_funct_1(sK3) = sK2
    | k1_relat_1(sK3) != sK1
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4282])).

cnf(c_5426,plain,
    ( k1_relat_1(sK3) != sK1
    | k2_funct_1(sK3) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4283,c_35,c_38,c_2401,c_2404,c_4974])).

cnf(c_5427,plain,
    ( k2_funct_1(sK3) = sK2
    | k1_relat_1(sK3) != sK1 ),
    inference(renaming,[status(thm)],[c_5426])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1100,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2595,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1794,c_1100])).

cnf(c_5312,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2595,c_38,c_39,c_40,c_25,c_652,c_1199,c_4974])).

cnf(c_5314,plain,
    ( k6_partfun1(k1_relat_1(sK3)) = k6_partfun1(sK1) ),
    inference(demodulation,[status(thm)],[c_5312,c_4984])).

cnf(c_2,plain,
    ( k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_5772,plain,
    ( k2_relat_1(k6_partfun1(sK1)) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_5314,c_2])).

cnf(c_5773,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(demodulation,[status(thm)],[c_5772,c_2])).

cnf(c_633,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1377,plain,
    ( v1_funct_1(X0)
    | ~ v1_funct_1(sK2)
    | X0 != sK2 ),
    inference(instantiation,[status(thm)],[c_633])).

cnf(c_1462,plain,
    ( v1_funct_1(k2_funct_1(X0))
    | ~ v1_funct_1(sK2)
    | k2_funct_1(X0) != sK2 ),
    inference(instantiation,[status(thm)],[c_1377])).

cnf(c_7784,plain,
    ( v1_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK2)
    | k2_funct_1(sK3) != sK2 ),
    inference(instantiation,[status(thm)],[c_1462])).

cnf(c_7785,plain,
    ( k2_funct_1(sK3) != sK2
    | v1_funct_1(k2_funct_1(sK3)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7784])).

cnf(c_630,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2525,plain,
    ( v2_funct_1(X0)
    | ~ v2_funct_1(sK2)
    | X0 != sK2 ),
    inference(instantiation,[status(thm)],[c_630])).

cnf(c_4251,plain,
    ( v2_funct_1(k2_funct_1(X0))
    | ~ v2_funct_1(sK2)
    | k2_funct_1(X0) != sK2 ),
    inference(instantiation,[status(thm)],[c_2525])).

cnf(c_8469,plain,
    ( v2_funct_1(k2_funct_1(sK3))
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK3) != sK2 ),
    inference(instantiation,[status(thm)],[c_4251])).

cnf(c_8470,plain,
    ( k2_funct_1(sK3) != sK2
    | v2_funct_1(k2_funct_1(sK3)) = iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8469])).

cnf(c_623,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2558,plain,
    ( v1_relat_1(X0)
    | ~ v1_relat_1(sK2)
    | X0 != sK2 ),
    inference(instantiation,[status(thm)],[c_623])).

cnf(c_4948,plain,
    ( v1_relat_1(k2_funct_1(X0))
    | ~ v1_relat_1(sK2)
    | k2_funct_1(X0) != sK2 ),
    inference(instantiation,[status(thm)],[c_2558])).

cnf(c_8854,plain,
    ( v1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK2)
    | k2_funct_1(sK3) != sK2 ),
    inference(instantiation,[status(thm)],[c_4948])).

cnf(c_8855,plain,
    ( k2_funct_1(sK3) != sK2
    | v1_relat_1(k2_funct_1(sK3)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8854])).

cnf(c_15802,plain,
    ( k6_partfun1(k2_relat_1(k2_funct_1(sK3))) != k6_partfun1(k1_relat_1(sK3))
    | k1_relat_1(k2_funct_1(sK3)) != sK0
    | k2_funct_1(k2_funct_1(sK3)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4986,c_35,c_38,c_42,c_2401,c_2404,c_4283,c_4974,c_5773,c_7785,c_8470,c_8855])).

cnf(c_15803,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = sK3
    | k1_relat_1(k2_funct_1(sK3)) != sK0
    | k6_partfun1(k2_relat_1(k2_funct_1(sK3))) != k6_partfun1(k1_relat_1(sK3)) ),
    inference(renaming,[status(thm)],[c_15802])).

cnf(c_2594,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_28,c_1100])).

cnf(c_1093,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_2506,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1093,c_1112])).

cnf(c_2575,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2506,c_42,c_2404])).

cnf(c_2597,plain,
    ( k6_partfun1(k1_relat_1(sK2)) = k6_partfun1(sK0)
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2594,c_2575])).

cnf(c_24,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1178,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_622])).

cnf(c_1179,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1178])).

cnf(c_3507,plain,
    ( k6_partfun1(k1_relat_1(sK2)) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2597,c_35,c_36,c_37,c_42,c_24,c_652,c_1179])).

cnf(c_3515,plain,
    ( k2_relat_1(k6_partfun1(sK0)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_3507,c_2])).

cnf(c_3516,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(demodulation,[status(thm)],[c_3515,c_2])).

cnf(c_5803,plain,
    ( k2_funct_1(sK3) = sK2
    | sK1 != sK1 ),
    inference(demodulation,[status(thm)],[c_5773,c_5427])).

cnf(c_5814,plain,
    ( k2_funct_1(sK3) = sK2 ),
    inference(equality_resolution_simp,[status(thm)],[c_5803])).

cnf(c_15804,plain,
    ( k2_funct_1(sK2) = sK3
    | k6_partfun1(sK1) != k6_partfun1(sK1)
    | sK0 != sK0 ),
    inference(light_normalisation,[status(thm)],[c_15803,c_1990,c_3516,c_5773,c_5814])).

cnf(c_15805,plain,
    ( k2_funct_1(sK2) = sK3 ),
    inference(equality_resolution_simp,[status(thm)],[c_15804])).

cnf(c_23,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f78])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_15805,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:00:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.65/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.65/1.49  
% 7.65/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.65/1.49  
% 7.65/1.49  ------  iProver source info
% 7.65/1.49  
% 7.65/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.65/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.65/1.49  git: non_committed_changes: false
% 7.65/1.49  git: last_make_outside_of_git: false
% 7.65/1.49  
% 7.65/1.49  ------ 
% 7.65/1.49  
% 7.65/1.49  ------ Input Options
% 7.65/1.49  
% 7.65/1.49  --out_options                           all
% 7.65/1.49  --tptp_safe_out                         true
% 7.65/1.49  --problem_path                          ""
% 7.65/1.49  --include_path                          ""
% 7.65/1.49  --clausifier                            res/vclausify_rel
% 7.65/1.49  --clausifier_options                    ""
% 7.65/1.49  --stdin                                 false
% 7.65/1.49  --stats_out                             all
% 7.65/1.49  
% 7.65/1.49  ------ General Options
% 7.65/1.49  
% 7.65/1.49  --fof                                   false
% 7.65/1.49  --time_out_real                         305.
% 7.65/1.49  --time_out_virtual                      -1.
% 7.65/1.49  --symbol_type_check                     false
% 7.65/1.49  --clausify_out                          false
% 7.65/1.49  --sig_cnt_out                           false
% 7.65/1.49  --trig_cnt_out                          false
% 7.65/1.49  --trig_cnt_out_tolerance                1.
% 7.65/1.49  --trig_cnt_out_sk_spl                   false
% 7.65/1.49  --abstr_cl_out                          false
% 7.65/1.49  
% 7.65/1.49  ------ Global Options
% 7.65/1.49  
% 7.65/1.49  --schedule                              default
% 7.65/1.49  --add_important_lit                     false
% 7.65/1.49  --prop_solver_per_cl                    1000
% 7.65/1.49  --min_unsat_core                        false
% 7.65/1.49  --soft_assumptions                      false
% 7.65/1.49  --soft_lemma_size                       3
% 7.65/1.49  --prop_impl_unit_size                   0
% 7.65/1.49  --prop_impl_unit                        []
% 7.65/1.49  --share_sel_clauses                     true
% 7.65/1.49  --reset_solvers                         false
% 7.65/1.49  --bc_imp_inh                            [conj_cone]
% 7.65/1.49  --conj_cone_tolerance                   3.
% 7.65/1.49  --extra_neg_conj                        none
% 7.65/1.49  --large_theory_mode                     true
% 7.65/1.49  --prolific_symb_bound                   200
% 7.65/1.49  --lt_threshold                          2000
% 7.65/1.49  --clause_weak_htbl                      true
% 7.65/1.49  --gc_record_bc_elim                     false
% 7.65/1.49  
% 7.65/1.49  ------ Preprocessing Options
% 7.65/1.49  
% 7.65/1.49  --preprocessing_flag                    true
% 7.65/1.49  --time_out_prep_mult                    0.1
% 7.65/1.49  --splitting_mode                        input
% 7.65/1.49  --splitting_grd                         true
% 7.65/1.49  --splitting_cvd                         false
% 7.65/1.49  --splitting_cvd_svl                     false
% 7.65/1.49  --splitting_nvd                         32
% 7.65/1.49  --sub_typing                            true
% 7.65/1.49  --prep_gs_sim                           true
% 7.65/1.49  --prep_unflatten                        true
% 7.65/1.49  --prep_res_sim                          true
% 7.65/1.49  --prep_upred                            true
% 7.65/1.49  --prep_sem_filter                       exhaustive
% 7.65/1.49  --prep_sem_filter_out                   false
% 7.65/1.49  --pred_elim                             true
% 7.65/1.49  --res_sim_input                         true
% 7.65/1.49  --eq_ax_congr_red                       true
% 7.65/1.49  --pure_diseq_elim                       true
% 7.65/1.49  --brand_transform                       false
% 7.65/1.49  --non_eq_to_eq                          false
% 7.65/1.49  --prep_def_merge                        true
% 7.65/1.49  --prep_def_merge_prop_impl              false
% 7.65/1.50  --prep_def_merge_mbd                    true
% 7.65/1.50  --prep_def_merge_tr_red                 false
% 7.65/1.50  --prep_def_merge_tr_cl                  false
% 7.65/1.50  --smt_preprocessing                     true
% 7.65/1.50  --smt_ac_axioms                         fast
% 7.65/1.50  --preprocessed_out                      false
% 7.65/1.50  --preprocessed_stats                    false
% 7.65/1.50  
% 7.65/1.50  ------ Abstraction refinement Options
% 7.65/1.50  
% 7.65/1.50  --abstr_ref                             []
% 7.65/1.50  --abstr_ref_prep                        false
% 7.65/1.50  --abstr_ref_until_sat                   false
% 7.65/1.50  --abstr_ref_sig_restrict                funpre
% 7.65/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.65/1.50  --abstr_ref_under                       []
% 7.65/1.50  
% 7.65/1.50  ------ SAT Options
% 7.65/1.50  
% 7.65/1.50  --sat_mode                              false
% 7.65/1.50  --sat_fm_restart_options                ""
% 7.65/1.50  --sat_gr_def                            false
% 7.65/1.50  --sat_epr_types                         true
% 7.65/1.50  --sat_non_cyclic_types                  false
% 7.65/1.50  --sat_finite_models                     false
% 7.65/1.50  --sat_fm_lemmas                         false
% 7.65/1.50  --sat_fm_prep                           false
% 7.65/1.50  --sat_fm_uc_incr                        true
% 7.65/1.50  --sat_out_model                         small
% 7.65/1.50  --sat_out_clauses                       false
% 7.65/1.50  
% 7.65/1.50  ------ QBF Options
% 7.65/1.50  
% 7.65/1.50  --qbf_mode                              false
% 7.65/1.50  --qbf_elim_univ                         false
% 7.65/1.50  --qbf_dom_inst                          none
% 7.65/1.50  --qbf_dom_pre_inst                      false
% 7.65/1.50  --qbf_sk_in                             false
% 7.65/1.50  --qbf_pred_elim                         true
% 7.65/1.50  --qbf_split                             512
% 7.65/1.50  
% 7.65/1.50  ------ BMC1 Options
% 7.65/1.50  
% 7.65/1.50  --bmc1_incremental                      false
% 7.65/1.50  --bmc1_axioms                           reachable_all
% 7.65/1.50  --bmc1_min_bound                        0
% 7.65/1.50  --bmc1_max_bound                        -1
% 7.65/1.50  --bmc1_max_bound_default                -1
% 7.65/1.50  --bmc1_symbol_reachability              true
% 7.65/1.50  --bmc1_property_lemmas                  false
% 7.65/1.50  --bmc1_k_induction                      false
% 7.65/1.50  --bmc1_non_equiv_states                 false
% 7.65/1.50  --bmc1_deadlock                         false
% 7.65/1.50  --bmc1_ucm                              false
% 7.65/1.50  --bmc1_add_unsat_core                   none
% 7.65/1.50  --bmc1_unsat_core_children              false
% 7.65/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.65/1.50  --bmc1_out_stat                         full
% 7.65/1.50  --bmc1_ground_init                      false
% 7.65/1.50  --bmc1_pre_inst_next_state              false
% 7.65/1.50  --bmc1_pre_inst_state                   false
% 7.65/1.50  --bmc1_pre_inst_reach_state             false
% 7.65/1.50  --bmc1_out_unsat_core                   false
% 7.65/1.50  --bmc1_aig_witness_out                  false
% 7.65/1.50  --bmc1_verbose                          false
% 7.65/1.50  --bmc1_dump_clauses_tptp                false
% 7.65/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.65/1.50  --bmc1_dump_file                        -
% 7.65/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.65/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.65/1.50  --bmc1_ucm_extend_mode                  1
% 7.65/1.50  --bmc1_ucm_init_mode                    2
% 7.65/1.50  --bmc1_ucm_cone_mode                    none
% 7.65/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.65/1.50  --bmc1_ucm_relax_model                  4
% 7.65/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.65/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.65/1.50  --bmc1_ucm_layered_model                none
% 7.65/1.50  --bmc1_ucm_max_lemma_size               10
% 7.65/1.50  
% 7.65/1.50  ------ AIG Options
% 7.65/1.50  
% 7.65/1.50  --aig_mode                              false
% 7.65/1.50  
% 7.65/1.50  ------ Instantiation Options
% 7.65/1.50  
% 7.65/1.50  --instantiation_flag                    true
% 7.65/1.50  --inst_sos_flag                         true
% 7.65/1.50  --inst_sos_phase                        true
% 7.65/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.65/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.65/1.50  --inst_lit_sel_side                     num_symb
% 7.65/1.50  --inst_solver_per_active                1400
% 7.65/1.50  --inst_solver_calls_frac                1.
% 7.65/1.50  --inst_passive_queue_type               priority_queues
% 7.65/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.65/1.50  --inst_passive_queues_freq              [25;2]
% 7.65/1.50  --inst_dismatching                      true
% 7.65/1.50  --inst_eager_unprocessed_to_passive     true
% 7.65/1.50  --inst_prop_sim_given                   true
% 7.65/1.50  --inst_prop_sim_new                     false
% 7.65/1.50  --inst_subs_new                         false
% 7.65/1.50  --inst_eq_res_simp                      false
% 7.65/1.50  --inst_subs_given                       false
% 7.65/1.50  --inst_orphan_elimination               true
% 7.65/1.50  --inst_learning_loop_flag               true
% 7.65/1.50  --inst_learning_start                   3000
% 7.65/1.50  --inst_learning_factor                  2
% 7.65/1.50  --inst_start_prop_sim_after_learn       3
% 7.65/1.50  --inst_sel_renew                        solver
% 7.65/1.50  --inst_lit_activity_flag                true
% 7.65/1.50  --inst_restr_to_given                   false
% 7.65/1.50  --inst_activity_threshold               500
% 7.65/1.50  --inst_out_proof                        true
% 7.65/1.50  
% 7.65/1.50  ------ Resolution Options
% 7.65/1.50  
% 7.65/1.50  --resolution_flag                       true
% 7.65/1.50  --res_lit_sel                           adaptive
% 7.65/1.50  --res_lit_sel_side                      none
% 7.65/1.50  --res_ordering                          kbo
% 7.65/1.50  --res_to_prop_solver                    active
% 7.65/1.50  --res_prop_simpl_new                    false
% 7.65/1.50  --res_prop_simpl_given                  true
% 7.65/1.50  --res_passive_queue_type                priority_queues
% 7.65/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.65/1.50  --res_passive_queues_freq               [15;5]
% 7.65/1.50  --res_forward_subs                      full
% 7.65/1.50  --res_backward_subs                     full
% 7.65/1.50  --res_forward_subs_resolution           true
% 7.65/1.50  --res_backward_subs_resolution          true
% 7.65/1.50  --res_orphan_elimination                true
% 7.65/1.50  --res_time_limit                        2.
% 7.65/1.50  --res_out_proof                         true
% 7.65/1.50  
% 7.65/1.50  ------ Superposition Options
% 7.65/1.50  
% 7.65/1.50  --superposition_flag                    true
% 7.65/1.50  --sup_passive_queue_type                priority_queues
% 7.65/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.65/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.65/1.50  --demod_completeness_check              fast
% 7.65/1.50  --demod_use_ground                      true
% 7.65/1.50  --sup_to_prop_solver                    passive
% 7.65/1.50  --sup_prop_simpl_new                    true
% 7.65/1.50  --sup_prop_simpl_given                  true
% 7.65/1.50  --sup_fun_splitting                     true
% 7.65/1.50  --sup_smt_interval                      50000
% 7.65/1.50  
% 7.65/1.50  ------ Superposition Simplification Setup
% 7.65/1.50  
% 7.65/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.65/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.65/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.65/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.65/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.65/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.65/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.65/1.50  --sup_immed_triv                        [TrivRules]
% 7.65/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.65/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.65/1.50  --sup_immed_bw_main                     []
% 7.65/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.65/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.65/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.65/1.50  --sup_input_bw                          []
% 7.65/1.50  
% 7.65/1.50  ------ Combination Options
% 7.65/1.50  
% 7.65/1.50  --comb_res_mult                         3
% 7.65/1.50  --comb_sup_mult                         2
% 7.65/1.50  --comb_inst_mult                        10
% 7.65/1.50  
% 7.65/1.50  ------ Debug Options
% 7.65/1.50  
% 7.65/1.50  --dbg_backtrace                         false
% 7.65/1.50  --dbg_dump_prop_clauses                 false
% 7.65/1.50  --dbg_dump_prop_clauses_file            -
% 7.65/1.50  --dbg_out_stat                          false
% 7.65/1.50  ------ Parsing...
% 7.65/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.65/1.50  
% 7.65/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.65/1.50  
% 7.65/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.65/1.50  
% 7.65/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.65/1.50  ------ Proving...
% 7.65/1.50  ------ Problem Properties 
% 7.65/1.50  
% 7.65/1.50  
% 7.65/1.50  clauses                                 34
% 7.65/1.50  conjectures                             11
% 7.65/1.50  EPR                                     7
% 7.65/1.50  Horn                                    30
% 7.65/1.50  unary                                   17
% 7.65/1.50  binary                                  2
% 7.65/1.50  lits                                    123
% 7.65/1.50  lits eq                                 30
% 7.65/1.50  fd_pure                                 0
% 7.65/1.50  fd_pseudo                               0
% 7.65/1.50  fd_cond                                 4
% 7.65/1.50  fd_pseudo_cond                          1
% 7.65/1.50  AC symbols                              0
% 7.65/1.50  
% 7.65/1.50  ------ Schedule dynamic 5 is on 
% 7.65/1.50  
% 7.65/1.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.65/1.50  
% 7.65/1.50  
% 7.65/1.50  ------ 
% 7.65/1.50  Current options:
% 7.65/1.50  ------ 
% 7.65/1.50  
% 7.65/1.50  ------ Input Options
% 7.65/1.50  
% 7.65/1.50  --out_options                           all
% 7.65/1.50  --tptp_safe_out                         true
% 7.65/1.50  --problem_path                          ""
% 7.65/1.50  --include_path                          ""
% 7.65/1.50  --clausifier                            res/vclausify_rel
% 7.65/1.50  --clausifier_options                    ""
% 7.65/1.50  --stdin                                 false
% 7.65/1.50  --stats_out                             all
% 7.65/1.50  
% 7.65/1.50  ------ General Options
% 7.65/1.50  
% 7.65/1.50  --fof                                   false
% 7.65/1.50  --time_out_real                         305.
% 7.65/1.50  --time_out_virtual                      -1.
% 7.65/1.50  --symbol_type_check                     false
% 7.65/1.50  --clausify_out                          false
% 7.65/1.50  --sig_cnt_out                           false
% 7.65/1.50  --trig_cnt_out                          false
% 7.65/1.50  --trig_cnt_out_tolerance                1.
% 7.65/1.50  --trig_cnt_out_sk_spl                   false
% 7.65/1.50  --abstr_cl_out                          false
% 7.65/1.50  
% 7.65/1.50  ------ Global Options
% 7.65/1.50  
% 7.65/1.50  --schedule                              default
% 7.65/1.50  --add_important_lit                     false
% 7.65/1.50  --prop_solver_per_cl                    1000
% 7.65/1.50  --min_unsat_core                        false
% 7.65/1.50  --soft_assumptions                      false
% 7.65/1.50  --soft_lemma_size                       3
% 7.65/1.50  --prop_impl_unit_size                   0
% 7.65/1.50  --prop_impl_unit                        []
% 7.65/1.50  --share_sel_clauses                     true
% 7.65/1.50  --reset_solvers                         false
% 7.65/1.50  --bc_imp_inh                            [conj_cone]
% 7.65/1.50  --conj_cone_tolerance                   3.
% 7.65/1.50  --extra_neg_conj                        none
% 7.65/1.50  --large_theory_mode                     true
% 7.65/1.50  --prolific_symb_bound                   200
% 7.65/1.50  --lt_threshold                          2000
% 7.65/1.50  --clause_weak_htbl                      true
% 7.65/1.50  --gc_record_bc_elim                     false
% 7.65/1.50  
% 7.65/1.50  ------ Preprocessing Options
% 7.65/1.50  
% 7.65/1.50  --preprocessing_flag                    true
% 7.65/1.50  --time_out_prep_mult                    0.1
% 7.65/1.50  --splitting_mode                        input
% 7.65/1.50  --splitting_grd                         true
% 7.65/1.50  --splitting_cvd                         false
% 7.65/1.50  --splitting_cvd_svl                     false
% 7.65/1.50  --splitting_nvd                         32
% 7.65/1.50  --sub_typing                            true
% 7.65/1.50  --prep_gs_sim                           true
% 7.65/1.50  --prep_unflatten                        true
% 7.65/1.50  --prep_res_sim                          true
% 7.65/1.50  --prep_upred                            true
% 7.65/1.50  --prep_sem_filter                       exhaustive
% 7.65/1.50  --prep_sem_filter_out                   false
% 7.65/1.50  --pred_elim                             true
% 7.65/1.50  --res_sim_input                         true
% 7.65/1.50  --eq_ax_congr_red                       true
% 7.65/1.50  --pure_diseq_elim                       true
% 7.65/1.50  --brand_transform                       false
% 7.65/1.50  --non_eq_to_eq                          false
% 7.65/1.50  --prep_def_merge                        true
% 7.65/1.50  --prep_def_merge_prop_impl              false
% 7.65/1.50  --prep_def_merge_mbd                    true
% 7.65/1.50  --prep_def_merge_tr_red                 false
% 7.65/1.50  --prep_def_merge_tr_cl                  false
% 7.65/1.50  --smt_preprocessing                     true
% 7.65/1.50  --smt_ac_axioms                         fast
% 7.65/1.50  --preprocessed_out                      false
% 7.65/1.50  --preprocessed_stats                    false
% 7.65/1.50  
% 7.65/1.50  ------ Abstraction refinement Options
% 7.65/1.50  
% 7.65/1.50  --abstr_ref                             []
% 7.65/1.50  --abstr_ref_prep                        false
% 7.65/1.50  --abstr_ref_until_sat                   false
% 7.65/1.50  --abstr_ref_sig_restrict                funpre
% 7.65/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.65/1.50  --abstr_ref_under                       []
% 7.65/1.50  
% 7.65/1.50  ------ SAT Options
% 7.65/1.50  
% 7.65/1.50  --sat_mode                              false
% 7.65/1.50  --sat_fm_restart_options                ""
% 7.65/1.50  --sat_gr_def                            false
% 7.65/1.50  --sat_epr_types                         true
% 7.65/1.50  --sat_non_cyclic_types                  false
% 7.65/1.50  --sat_finite_models                     false
% 7.65/1.50  --sat_fm_lemmas                         false
% 7.65/1.50  --sat_fm_prep                           false
% 7.65/1.50  --sat_fm_uc_incr                        true
% 7.65/1.50  --sat_out_model                         small
% 7.65/1.50  --sat_out_clauses                       false
% 7.65/1.50  
% 7.65/1.50  ------ QBF Options
% 7.65/1.50  
% 7.65/1.50  --qbf_mode                              false
% 7.65/1.50  --qbf_elim_univ                         false
% 7.65/1.50  --qbf_dom_inst                          none
% 7.65/1.50  --qbf_dom_pre_inst                      false
% 7.65/1.50  --qbf_sk_in                             false
% 7.65/1.50  --qbf_pred_elim                         true
% 7.65/1.50  --qbf_split                             512
% 7.65/1.50  
% 7.65/1.50  ------ BMC1 Options
% 7.65/1.50  
% 7.65/1.50  --bmc1_incremental                      false
% 7.65/1.50  --bmc1_axioms                           reachable_all
% 7.65/1.50  --bmc1_min_bound                        0
% 7.65/1.50  --bmc1_max_bound                        -1
% 7.65/1.50  --bmc1_max_bound_default                -1
% 7.65/1.50  --bmc1_symbol_reachability              true
% 7.65/1.50  --bmc1_property_lemmas                  false
% 7.65/1.50  --bmc1_k_induction                      false
% 7.65/1.50  --bmc1_non_equiv_states                 false
% 7.65/1.50  --bmc1_deadlock                         false
% 7.65/1.50  --bmc1_ucm                              false
% 7.65/1.50  --bmc1_add_unsat_core                   none
% 7.65/1.50  --bmc1_unsat_core_children              false
% 7.65/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.65/1.50  --bmc1_out_stat                         full
% 7.65/1.50  --bmc1_ground_init                      false
% 7.65/1.50  --bmc1_pre_inst_next_state              false
% 7.65/1.50  --bmc1_pre_inst_state                   false
% 7.65/1.50  --bmc1_pre_inst_reach_state             false
% 7.65/1.50  --bmc1_out_unsat_core                   false
% 7.65/1.50  --bmc1_aig_witness_out                  false
% 7.65/1.50  --bmc1_verbose                          false
% 7.65/1.50  --bmc1_dump_clauses_tptp                false
% 7.65/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.65/1.50  --bmc1_dump_file                        -
% 7.65/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.65/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.65/1.50  --bmc1_ucm_extend_mode                  1
% 7.65/1.50  --bmc1_ucm_init_mode                    2
% 7.65/1.50  --bmc1_ucm_cone_mode                    none
% 7.65/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.65/1.50  --bmc1_ucm_relax_model                  4
% 7.65/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.65/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.65/1.50  --bmc1_ucm_layered_model                none
% 7.65/1.50  --bmc1_ucm_max_lemma_size               10
% 7.65/1.50  
% 7.65/1.50  ------ AIG Options
% 7.65/1.50  
% 7.65/1.50  --aig_mode                              false
% 7.65/1.50  
% 7.65/1.50  ------ Instantiation Options
% 7.65/1.50  
% 7.65/1.50  --instantiation_flag                    true
% 7.65/1.50  --inst_sos_flag                         true
% 7.65/1.50  --inst_sos_phase                        true
% 7.65/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.65/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.65/1.50  --inst_lit_sel_side                     none
% 7.65/1.50  --inst_solver_per_active                1400
% 7.65/1.50  --inst_solver_calls_frac                1.
% 7.65/1.50  --inst_passive_queue_type               priority_queues
% 7.65/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.65/1.50  --inst_passive_queues_freq              [25;2]
% 7.65/1.50  --inst_dismatching                      true
% 7.65/1.50  --inst_eager_unprocessed_to_passive     true
% 7.65/1.50  --inst_prop_sim_given                   true
% 7.65/1.50  --inst_prop_sim_new                     false
% 7.65/1.50  --inst_subs_new                         false
% 7.65/1.50  --inst_eq_res_simp                      false
% 7.65/1.50  --inst_subs_given                       false
% 7.65/1.50  --inst_orphan_elimination               true
% 7.65/1.50  --inst_learning_loop_flag               true
% 7.65/1.50  --inst_learning_start                   3000
% 7.65/1.50  --inst_learning_factor                  2
% 7.65/1.50  --inst_start_prop_sim_after_learn       3
% 7.65/1.50  --inst_sel_renew                        solver
% 7.65/1.50  --inst_lit_activity_flag                true
% 7.65/1.50  --inst_restr_to_given                   false
% 7.65/1.50  --inst_activity_threshold               500
% 7.65/1.50  --inst_out_proof                        true
% 7.65/1.50  
% 7.65/1.50  ------ Resolution Options
% 7.65/1.50  
% 7.65/1.50  --resolution_flag                       false
% 7.65/1.50  --res_lit_sel                           adaptive
% 7.65/1.50  --res_lit_sel_side                      none
% 7.65/1.50  --res_ordering                          kbo
% 7.65/1.50  --res_to_prop_solver                    active
% 7.65/1.50  --res_prop_simpl_new                    false
% 7.65/1.50  --res_prop_simpl_given                  true
% 7.65/1.50  --res_passive_queue_type                priority_queues
% 7.65/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.65/1.50  --res_passive_queues_freq               [15;5]
% 7.65/1.50  --res_forward_subs                      full
% 7.65/1.50  --res_backward_subs                     full
% 7.65/1.50  --res_forward_subs_resolution           true
% 7.65/1.50  --res_backward_subs_resolution          true
% 7.65/1.50  --res_orphan_elimination                true
% 7.65/1.50  --res_time_limit                        2.
% 7.65/1.50  --res_out_proof                         true
% 7.65/1.50  
% 7.65/1.50  ------ Superposition Options
% 7.65/1.50  
% 7.65/1.50  --superposition_flag                    true
% 7.65/1.50  --sup_passive_queue_type                priority_queues
% 7.65/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.65/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.65/1.50  --demod_completeness_check              fast
% 7.65/1.50  --demod_use_ground                      true
% 7.65/1.50  --sup_to_prop_solver                    passive
% 7.65/1.50  --sup_prop_simpl_new                    true
% 7.65/1.50  --sup_prop_simpl_given                  true
% 7.65/1.50  --sup_fun_splitting                     true
% 7.65/1.50  --sup_smt_interval                      50000
% 7.65/1.50  
% 7.65/1.50  ------ Superposition Simplification Setup
% 7.65/1.50  
% 7.65/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.65/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.65/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.65/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.65/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.65/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.65/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.65/1.50  --sup_immed_triv                        [TrivRules]
% 7.65/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.65/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.65/1.50  --sup_immed_bw_main                     []
% 7.65/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.65/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.65/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.65/1.50  --sup_input_bw                          []
% 7.65/1.50  
% 7.65/1.50  ------ Combination Options
% 7.65/1.50  
% 7.65/1.50  --comb_res_mult                         3
% 7.65/1.50  --comb_sup_mult                         2
% 7.65/1.50  --comb_inst_mult                        10
% 7.65/1.50  
% 7.65/1.50  ------ Debug Options
% 7.65/1.50  
% 7.65/1.50  --dbg_backtrace                         false
% 7.65/1.50  --dbg_dump_prop_clauses                 false
% 7.65/1.50  --dbg_dump_prop_clauses_file            -
% 7.65/1.50  --dbg_out_stat                          false
% 7.65/1.50  
% 7.65/1.50  
% 7.65/1.50  
% 7.65/1.50  
% 7.65/1.50  ------ Proving...
% 7.65/1.50  
% 7.65/1.50  
% 7.65/1.50  % SZS status Theorem for theBenchmark.p
% 7.65/1.50  
% 7.65/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.65/1.50  
% 7.65/1.50  fof(f4,axiom,(
% 7.65/1.50    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 7.65/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f48,plain,(
% 7.65/1.50    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 7.65/1.50    inference(cnf_transformation,[],[f4])).
% 7.65/1.50  
% 7.65/1.50  fof(f12,axiom,(
% 7.65/1.50    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 7.65/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f59,plain,(
% 7.65/1.50    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 7.65/1.50    inference(cnf_transformation,[],[f12])).
% 7.65/1.50  
% 7.65/1.50  fof(f81,plain,(
% 7.65/1.50    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 7.65/1.50    inference(definition_unfolding,[],[f48,f59])).
% 7.65/1.50  
% 7.65/1.50  fof(f8,axiom,(
% 7.65/1.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 7.65/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f25,plain,(
% 7.65/1.50    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 7.65/1.50    inference(ennf_transformation,[],[f8])).
% 7.65/1.50  
% 7.65/1.50  fof(f26,plain,(
% 7.65/1.50    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.65/1.50    inference(flattening,[],[f25])).
% 7.65/1.50  
% 7.65/1.50  fof(f39,plain,(
% 7.65/1.50    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.65/1.50    inference(nnf_transformation,[],[f26])).
% 7.65/1.50  
% 7.65/1.50  fof(f53,plain,(
% 7.65/1.50    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.65/1.50    inference(cnf_transformation,[],[f39])).
% 7.65/1.50  
% 7.65/1.50  fof(f16,conjecture,(
% 7.65/1.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 7.65/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f17,negated_conjecture,(
% 7.65/1.50    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 7.65/1.50    inference(negated_conjecture,[],[f16])).
% 7.65/1.50  
% 7.65/1.50  fof(f37,plain,(
% 7.65/1.50    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 7.65/1.50    inference(ennf_transformation,[],[f17])).
% 7.65/1.50  
% 7.65/1.50  fof(f38,plain,(
% 7.65/1.50    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 7.65/1.50    inference(flattening,[],[f37])).
% 7.65/1.50  
% 7.65/1.50  fof(f41,plain,(
% 7.65/1.50    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 7.65/1.50    introduced(choice_axiom,[])).
% 7.65/1.50  
% 7.65/1.50  fof(f40,plain,(
% 7.65/1.50    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 7.65/1.50    introduced(choice_axiom,[])).
% 7.65/1.50  
% 7.65/1.50  fof(f42,plain,(
% 7.65/1.50    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 7.65/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f38,f41,f40])).
% 7.65/1.50  
% 7.65/1.50  fof(f74,plain,(
% 7.65/1.50    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 7.65/1.50    inference(cnf_transformation,[],[f42])).
% 7.65/1.50  
% 7.65/1.50  fof(f10,axiom,(
% 7.65/1.50    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 7.65/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f18,plain,(
% 7.65/1.50    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 7.65/1.50    inference(pure_predicate_removal,[],[f10])).
% 7.65/1.50  
% 7.65/1.50  fof(f57,plain,(
% 7.65/1.50    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 7.65/1.50    inference(cnf_transformation,[],[f18])).
% 7.65/1.50  
% 7.65/1.50  fof(f67,plain,(
% 7.65/1.50    v1_funct_1(sK2)),
% 7.65/1.50    inference(cnf_transformation,[],[f42])).
% 7.65/1.50  
% 7.65/1.50  fof(f69,plain,(
% 7.65/1.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 7.65/1.50    inference(cnf_transformation,[],[f42])).
% 7.65/1.50  
% 7.65/1.50  fof(f70,plain,(
% 7.65/1.50    v1_funct_1(sK3)),
% 7.65/1.50    inference(cnf_transformation,[],[f42])).
% 7.65/1.50  
% 7.65/1.50  fof(f72,plain,(
% 7.65/1.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 7.65/1.50    inference(cnf_transformation,[],[f42])).
% 7.65/1.50  
% 7.65/1.50  fof(f9,axiom,(
% 7.65/1.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 7.65/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f27,plain,(
% 7.65/1.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 7.65/1.50    inference(ennf_transformation,[],[f9])).
% 7.65/1.50  
% 7.65/1.50  fof(f28,plain,(
% 7.65/1.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 7.65/1.50    inference(flattening,[],[f27])).
% 7.65/1.50  
% 7.65/1.50  fof(f56,plain,(
% 7.65/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 7.65/1.50    inference(cnf_transformation,[],[f28])).
% 7.65/1.50  
% 7.65/1.50  fof(f73,plain,(
% 7.65/1.50    k2_relset_1(sK0,sK1,sK2) = sK1),
% 7.65/1.50    inference(cnf_transformation,[],[f42])).
% 7.65/1.50  
% 7.65/1.50  fof(f14,axiom,(
% 7.65/1.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 7.65/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f33,plain,(
% 7.65/1.50    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 7.65/1.50    inference(ennf_transformation,[],[f14])).
% 7.65/1.50  
% 7.65/1.50  fof(f34,plain,(
% 7.65/1.50    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 7.65/1.50    inference(flattening,[],[f33])).
% 7.65/1.50  
% 7.65/1.50  fof(f63,plain,(
% 7.65/1.50    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X4) | k1_xboole_0 = X2 | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 7.65/1.50    inference(cnf_transformation,[],[f34])).
% 7.65/1.50  
% 7.65/1.50  fof(f68,plain,(
% 7.65/1.50    v1_funct_2(sK2,sK0,sK1)),
% 7.65/1.50    inference(cnf_transformation,[],[f42])).
% 7.65/1.50  
% 7.65/1.50  fof(f71,plain,(
% 7.65/1.50    v1_funct_2(sK3,sK1,sK0)),
% 7.65/1.50    inference(cnf_transformation,[],[f42])).
% 7.65/1.50  
% 7.65/1.50  fof(f76,plain,(
% 7.65/1.50    k1_xboole_0 != sK0),
% 7.65/1.50    inference(cnf_transformation,[],[f42])).
% 7.65/1.50  
% 7.65/1.50  fof(f5,axiom,(
% 7.65/1.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)))))),
% 7.65/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f20,plain,(
% 7.65/1.50    ! [X0] : (((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.65/1.50    inference(ennf_transformation,[],[f5])).
% 7.65/1.50  
% 7.65/1.50  fof(f21,plain,(
% 7.65/1.50    ! [X0] : ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.65/1.50    inference(flattening,[],[f20])).
% 7.65/1.50  
% 7.65/1.50  fof(f49,plain,(
% 7.65/1.50    ( ! [X0] : (k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.65/1.50    inference(cnf_transformation,[],[f21])).
% 7.65/1.50  
% 7.65/1.50  fof(f84,plain,(
% 7.65/1.50    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.65/1.50    inference(definition_unfolding,[],[f49,f59])).
% 7.65/1.50  
% 7.65/1.50  fof(f2,axiom,(
% 7.65/1.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 7.65/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f44,plain,(
% 7.65/1.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 7.65/1.50    inference(cnf_transformation,[],[f2])).
% 7.65/1.50  
% 7.65/1.50  fof(f1,axiom,(
% 7.65/1.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 7.65/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f19,plain,(
% 7.65/1.50    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 7.65/1.50    inference(ennf_transformation,[],[f1])).
% 7.65/1.50  
% 7.65/1.50  fof(f43,plain,(
% 7.65/1.50    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 7.65/1.50    inference(cnf_transformation,[],[f19])).
% 7.65/1.50  
% 7.65/1.50  fof(f6,axiom,(
% 7.65/1.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 7.65/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f22,plain,(
% 7.65/1.50    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.65/1.50    inference(ennf_transformation,[],[f6])).
% 7.65/1.50  
% 7.65/1.50  fof(f23,plain,(
% 7.65/1.50    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.65/1.50    inference(flattening,[],[f22])).
% 7.65/1.50  
% 7.65/1.50  fof(f51,plain,(
% 7.65/1.50    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.65/1.50    inference(cnf_transformation,[],[f23])).
% 7.65/1.50  
% 7.65/1.50  fof(f85,plain,(
% 7.65/1.50    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.65/1.50    inference(definition_unfolding,[],[f51,f59])).
% 7.65/1.50  
% 7.65/1.50  fof(f7,axiom,(
% 7.65/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 7.65/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f24,plain,(
% 7.65/1.50    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.65/1.50    inference(ennf_transformation,[],[f7])).
% 7.65/1.50  
% 7.65/1.50  fof(f52,plain,(
% 7.65/1.50    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.65/1.50    inference(cnf_transformation,[],[f24])).
% 7.65/1.50  
% 7.65/1.50  fof(f13,axiom,(
% 7.65/1.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 7.65/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f31,plain,(
% 7.65/1.50    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 7.65/1.50    inference(ennf_transformation,[],[f13])).
% 7.65/1.50  
% 7.65/1.50  fof(f32,plain,(
% 7.65/1.50    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.65/1.50    inference(flattening,[],[f31])).
% 7.65/1.50  
% 7.65/1.50  fof(f60,plain,(
% 7.65/1.50    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.65/1.50    inference(cnf_transformation,[],[f32])).
% 7.65/1.50  
% 7.65/1.50  fof(f75,plain,(
% 7.65/1.50    v2_funct_1(sK2)),
% 7.65/1.50    inference(cnf_transformation,[],[f42])).
% 7.65/1.50  
% 7.65/1.50  fof(f11,axiom,(
% 7.65/1.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 7.65/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f29,plain,(
% 7.65/1.50    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 7.65/1.50    inference(ennf_transformation,[],[f11])).
% 7.65/1.50  
% 7.65/1.50  fof(f30,plain,(
% 7.65/1.50    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 7.65/1.50    inference(flattening,[],[f29])).
% 7.65/1.50  
% 7.65/1.50  fof(f58,plain,(
% 7.65/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 7.65/1.50    inference(cnf_transformation,[],[f30])).
% 7.65/1.50  
% 7.65/1.50  fof(f15,axiom,(
% 7.65/1.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 7.65/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f35,plain,(
% 7.65/1.50    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 7.65/1.50    inference(ennf_transformation,[],[f15])).
% 7.65/1.50  
% 7.65/1.50  fof(f36,plain,(
% 7.65/1.50    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.65/1.50    inference(flattening,[],[f35])).
% 7.65/1.50  
% 7.65/1.50  fof(f65,plain,(
% 7.65/1.50    ( ! [X2,X0,X1] : (k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.65/1.50    inference(cnf_transformation,[],[f36])).
% 7.65/1.50  
% 7.65/1.50  fof(f3,axiom,(
% 7.65/1.50    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 7.65/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f46,plain,(
% 7.65/1.50    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 7.65/1.50    inference(cnf_transformation,[],[f3])).
% 7.65/1.50  
% 7.65/1.50  fof(f79,plain,(
% 7.65/1.50    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 7.65/1.50    inference(definition_unfolding,[],[f46,f59])).
% 7.65/1.50  
% 7.65/1.50  fof(f77,plain,(
% 7.65/1.50    k1_xboole_0 != sK1),
% 7.65/1.50    inference(cnf_transformation,[],[f42])).
% 7.65/1.50  
% 7.65/1.50  fof(f78,plain,(
% 7.65/1.50    k2_funct_1(sK2) != sK3),
% 7.65/1.50    inference(cnf_transformation,[],[f42])).
% 7.65/1.50  
% 7.65/1.50  cnf(c_4,plain,
% 7.65/1.50      ( v2_funct_1(k6_partfun1(X0)) ),
% 7.65/1.50      inference(cnf_transformation,[],[f81]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1115,plain,
% 7.65/1.50      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_11,plain,
% 7.65/1.50      ( ~ r2_relset_1(X0,X1,X2,X3)
% 7.65/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.65/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.65/1.50      | X3 = X2 ),
% 7.65/1.50      inference(cnf_transformation,[],[f53]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_27,negated_conjecture,
% 7.65/1.50      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 7.65/1.50      inference(cnf_transformation,[],[f74]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_362,plain,
% 7.65/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.65/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.65/1.50      | X3 = X0
% 7.65/1.50      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 7.65/1.50      | k6_partfun1(sK0) != X3
% 7.65/1.50      | sK0 != X2
% 7.65/1.50      | sK0 != X1 ),
% 7.65/1.50      inference(resolution_lifted,[status(thm)],[c_11,c_27]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_363,plain,
% 7.65/1.50      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.65/1.50      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.65/1.50      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.65/1.50      inference(unflattening,[status(thm)],[c_362]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_14,plain,
% 7.65/1.50      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 7.65/1.50      inference(cnf_transformation,[],[f57]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_371,plain,
% 7.65/1.50      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.65/1.50      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.65/1.50      inference(forward_subsumption_resolution,
% 7.65/1.50                [status(thm)],
% 7.65/1.50                [c_363,c_14]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1091,plain,
% 7.65/1.50      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.65/1.50      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_371]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_34,negated_conjecture,
% 7.65/1.50      ( v1_funct_1(sK2) ),
% 7.65/1.50      inference(cnf_transformation,[],[f67]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_32,negated_conjecture,
% 7.65/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 7.65/1.50      inference(cnf_transformation,[],[f69]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_31,negated_conjecture,
% 7.65/1.50      ( v1_funct_1(sK3) ),
% 7.65/1.50      inference(cnf_transformation,[],[f70]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_29,negated_conjecture,
% 7.65/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 7.65/1.50      inference(cnf_transformation,[],[f72]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_12,plain,
% 7.65/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.65/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.65/1.50      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.65/1.50      | ~ v1_funct_1(X0)
% 7.65/1.50      | ~ v1_funct_1(X3) ),
% 7.65/1.50      inference(cnf_transformation,[],[f56]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1200,plain,
% 7.65/1.50      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.65/1.50      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 7.65/1.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.65/1.50      | ~ v1_funct_1(sK3)
% 7.65/1.50      | ~ v1_funct_1(sK2) ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_12]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1787,plain,
% 7.65/1.50      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.65/1.50      inference(global_propositional_subsumption,
% 7.65/1.50                [status(thm)],
% 7.65/1.50                [c_1091,c_34,c_32,c_31,c_29,c_371,c_1200]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_28,negated_conjecture,
% 7.65/1.50      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 7.65/1.50      inference(cnf_transformation,[],[f73]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_18,plain,
% 7.65/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.65/1.50      | ~ v1_funct_2(X3,X2,X4)
% 7.65/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.65/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
% 7.65/1.50      | ~ v1_funct_1(X3)
% 7.65/1.50      | ~ v1_funct_1(X0)
% 7.65/1.50      | v2_funct_1(X3)
% 7.65/1.50      | ~ v2_funct_1(k1_partfun1(X1,X2,X2,X4,X0,X3))
% 7.65/1.50      | k2_relset_1(X1,X2,X0) != X2
% 7.65/1.50      | k1_xboole_0 = X4 ),
% 7.65/1.50      inference(cnf_transformation,[],[f63]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1104,plain,
% 7.65/1.50      ( k2_relset_1(X0,X1,X2) != X1
% 7.65/1.50      | k1_xboole_0 = X3
% 7.65/1.50      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.65/1.50      | v1_funct_2(X4,X1,X3) != iProver_top
% 7.65/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.65/1.50      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
% 7.65/1.50      | v1_funct_1(X2) != iProver_top
% 7.65/1.50      | v1_funct_1(X4) != iProver_top
% 7.65/1.50      | v2_funct_1(X4) = iProver_top
% 7.65/1.50      | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_4653,plain,
% 7.65/1.50      ( k1_xboole_0 = X0
% 7.65/1.50      | v1_funct_2(X1,sK1,X0) != iProver_top
% 7.65/1.50      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 7.65/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 7.65/1.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.65/1.50      | v1_funct_1(X1) != iProver_top
% 7.65/1.50      | v1_funct_1(sK2) != iProver_top
% 7.65/1.50      | v2_funct_1(X1) = iProver_top
% 7.65/1.50      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_28,c_1104]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_35,plain,
% 7.65/1.50      ( v1_funct_1(sK2) = iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_33,negated_conjecture,
% 7.65/1.50      ( v1_funct_2(sK2,sK0,sK1) ),
% 7.65/1.50      inference(cnf_transformation,[],[f68]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_36,plain,
% 7.65/1.50      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_37,plain,
% 7.65/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_4846,plain,
% 7.65/1.50      ( v1_funct_1(X1) != iProver_top
% 7.65/1.50      | v1_funct_2(X1,sK1,X0) != iProver_top
% 7.65/1.50      | k1_xboole_0 = X0
% 7.65/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 7.65/1.50      | v2_funct_1(X1) = iProver_top
% 7.65/1.50      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
% 7.65/1.50      inference(global_propositional_subsumption,
% 7.65/1.50                [status(thm)],
% 7.65/1.50                [c_4653,c_35,c_36,c_37]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_4847,plain,
% 7.65/1.50      ( k1_xboole_0 = X0
% 7.65/1.50      | v1_funct_2(X1,sK1,X0) != iProver_top
% 7.65/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 7.65/1.50      | v1_funct_1(X1) != iProver_top
% 7.65/1.50      | v2_funct_1(X1) = iProver_top
% 7.65/1.50      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
% 7.65/1.50      inference(renaming,[status(thm)],[c_4846]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_4850,plain,
% 7.65/1.50      ( sK0 = k1_xboole_0
% 7.65/1.50      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 7.65/1.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 7.65/1.50      | v1_funct_1(sK3) != iProver_top
% 7.65/1.50      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 7.65/1.50      | v2_funct_1(sK3) = iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_1787,c_4847]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_38,plain,
% 7.65/1.50      ( v1_funct_1(sK3) = iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_30,negated_conjecture,
% 7.65/1.50      ( v1_funct_2(sK3,sK1,sK0) ),
% 7.65/1.50      inference(cnf_transformation,[],[f71]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_39,plain,
% 7.65/1.50      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_40,plain,
% 7.65/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_25,negated_conjecture,
% 7.65/1.50      ( k1_xboole_0 != sK0 ),
% 7.65/1.50      inference(cnf_transformation,[],[f76]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_621,plain,( X0 = X0 ),theory(equality) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_652,plain,
% 7.65/1.50      ( k1_xboole_0 = k1_xboole_0 ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_621]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_622,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1198,plain,
% 7.65/1.50      ( sK0 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK0 ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_622]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1199,plain,
% 7.65/1.50      ( sK0 != k1_xboole_0
% 7.65/1.50      | k1_xboole_0 = sK0
% 7.65/1.50      | k1_xboole_0 != k1_xboole_0 ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_1198]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_4970,plain,
% 7.65/1.50      ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 7.65/1.50      | v2_funct_1(sK3) = iProver_top ),
% 7.65/1.50      inference(global_propositional_subsumption,
% 7.65/1.50                [status(thm)],
% 7.65/1.50                [c_4850,c_38,c_39,c_40,c_25,c_652,c_1199]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_4974,plain,
% 7.65/1.50      ( v2_funct_1(sK3) = iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_1115,c_4970]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1096,plain,
% 7.65/1.50      ( v1_funct_1(sK3) = iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_7,plain,
% 7.65/1.50      ( ~ v1_funct_1(X0)
% 7.65/1.50      | ~ v2_funct_1(X0)
% 7.65/1.50      | ~ v1_relat_1(X0)
% 7.65/1.50      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
% 7.65/1.50      inference(cnf_transformation,[],[f84]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1112,plain,
% 7.65/1.50      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
% 7.65/1.50      | v1_funct_1(X0) != iProver_top
% 7.65/1.50      | v2_funct_1(X0) != iProver_top
% 7.65/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_2505,plain,
% 7.65/1.50      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
% 7.65/1.50      | v2_funct_1(sK3) != iProver_top
% 7.65/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_1096,c_1112]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1,plain,
% 7.65/1.50      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 7.65/1.50      inference(cnf_transformation,[],[f44]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1116,plain,
% 7.65/1.50      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1098,plain,
% 7.65/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_0,plain,
% 7.65/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.65/1.50      | ~ v1_relat_1(X1)
% 7.65/1.50      | v1_relat_1(X0) ),
% 7.65/1.50      inference(cnf_transformation,[],[f43]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1117,plain,
% 7.65/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.65/1.50      | v1_relat_1(X1) != iProver_top
% 7.65/1.50      | v1_relat_1(X0) = iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_2285,plain,
% 7.65/1.50      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 7.65/1.50      | v1_relat_1(sK3) = iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_1098,c_1117]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_2401,plain,
% 7.65/1.50      ( v1_relat_1(sK3) = iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_1116,c_2285]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_2570,plain,
% 7.65/1.50      ( v2_funct_1(sK3) != iProver_top
% 7.65/1.50      | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3)) ),
% 7.65/1.50      inference(global_propositional_subsumption,
% 7.65/1.50                [status(thm)],
% 7.65/1.50                [c_2505,c_2401]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_2571,plain,
% 7.65/1.50      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
% 7.65/1.50      | v2_funct_1(sK3) != iProver_top ),
% 7.65/1.50      inference(renaming,[status(thm)],[c_2570]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_4984,plain,
% 7.65/1.50      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3)) ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_4974,c_2571]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_8,plain,
% 7.65/1.50      ( ~ v1_funct_1(X0)
% 7.65/1.50      | ~ v1_funct_1(X1)
% 7.65/1.50      | ~ v2_funct_1(X0)
% 7.65/1.50      | ~ v1_relat_1(X0)
% 7.65/1.50      | ~ v1_relat_1(X1)
% 7.65/1.50      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
% 7.65/1.50      | k2_funct_1(X0) = X1
% 7.65/1.50      | k1_relat_1(X0) != k2_relat_1(X1) ),
% 7.65/1.50      inference(cnf_transformation,[],[f85]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1111,plain,
% 7.65/1.50      ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 7.65/1.50      | k2_funct_1(X1) = X0
% 7.65/1.50      | k1_relat_1(X1) != k2_relat_1(X0)
% 7.65/1.50      | v1_funct_1(X1) != iProver_top
% 7.65/1.50      | v1_funct_1(X0) != iProver_top
% 7.65/1.50      | v2_funct_1(X1) != iProver_top
% 7.65/1.50      | v1_relat_1(X1) != iProver_top
% 7.65/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_4985,plain,
% 7.65/1.50      ( k2_funct_1(k2_funct_1(sK3)) = sK3
% 7.65/1.50      | k1_relat_1(k2_funct_1(sK3)) != k2_relat_1(sK3)
% 7.65/1.50      | k6_partfun1(k2_relat_1(k2_funct_1(sK3))) != k6_partfun1(k1_relat_1(sK3))
% 7.65/1.50      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 7.65/1.50      | v1_funct_1(sK3) != iProver_top
% 7.65/1.50      | v2_funct_1(k2_funct_1(sK3)) != iProver_top
% 7.65/1.50      | v1_relat_1(k2_funct_1(sK3)) != iProver_top
% 7.65/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_4984,c_1111]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_9,plain,
% 7.65/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.65/1.50      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 7.65/1.50      inference(cnf_transformation,[],[f52]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1110,plain,
% 7.65/1.50      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 7.65/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1988,plain,
% 7.65/1.50      ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_1098,c_1110]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_16,plain,
% 7.65/1.50      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 7.65/1.50      | ~ v1_funct_2(X2,X0,X1)
% 7.65/1.50      | ~ v1_funct_2(X3,X1,X0)
% 7.65/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 7.65/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.65/1.50      | ~ v1_funct_1(X2)
% 7.65/1.50      | ~ v1_funct_1(X3)
% 7.65/1.50      | k2_relset_1(X1,X0,X3) = X0 ),
% 7.65/1.50      inference(cnf_transformation,[],[f60]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_375,plain,
% 7.65/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.65/1.50      | ~ v1_funct_2(X3,X2,X1)
% 7.65/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 7.65/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.65/1.50      | ~ v1_funct_1(X3)
% 7.65/1.50      | ~ v1_funct_1(X0)
% 7.65/1.50      | k1_partfun1(X1,X2,X2,X1,X0,X3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.65/1.50      | k2_relset_1(X2,X1,X3) = X1
% 7.65/1.50      | k6_partfun1(X1) != k6_partfun1(sK0)
% 7.65/1.50      | sK0 != X1 ),
% 7.65/1.50      inference(resolution_lifted,[status(thm)],[c_16,c_27]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_376,plain,
% 7.65/1.50      ( ~ v1_funct_2(X0,X1,sK0)
% 7.65/1.50      | ~ v1_funct_2(X2,sK0,X1)
% 7.65/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 7.65/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 7.65/1.50      | ~ v1_funct_1(X2)
% 7.65/1.50      | ~ v1_funct_1(X0)
% 7.65/1.50      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.65/1.50      | k2_relset_1(X1,sK0,X0) = sK0
% 7.65/1.50      | k6_partfun1(sK0) != k6_partfun1(sK0) ),
% 7.65/1.50      inference(unflattening,[status(thm)],[c_375]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_458,plain,
% 7.65/1.50      ( ~ v1_funct_2(X0,X1,sK0)
% 7.65/1.50      | ~ v1_funct_2(X2,sK0,X1)
% 7.65/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 7.65/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 7.65/1.50      | ~ v1_funct_1(X0)
% 7.65/1.50      | ~ v1_funct_1(X2)
% 7.65/1.50      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.65/1.50      | k2_relset_1(X1,sK0,X0) = sK0 ),
% 7.65/1.50      inference(equality_resolution_simp,[status(thm)],[c_376]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1090,plain,
% 7.65/1.50      ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.65/1.50      | k2_relset_1(X0,sK0,X2) = sK0
% 7.65/1.50      | v1_funct_2(X2,X0,sK0) != iProver_top
% 7.65/1.50      | v1_funct_2(X1,sK0,X0) != iProver_top
% 7.65/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 7.65/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 7.65/1.50      | v1_funct_1(X2) != iProver_top
% 7.65/1.50      | v1_funct_1(X1) != iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_458]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1637,plain,
% 7.65/1.50      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 7.65/1.50      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 7.65/1.50      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 7.65/1.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 7.65/1.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.65/1.50      | v1_funct_1(sK3) != iProver_top
% 7.65/1.50      | v1_funct_1(sK2) != iProver_top ),
% 7.65/1.50      inference(equality_resolution,[status(thm)],[c_1090]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1794,plain,
% 7.65/1.50      ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 7.65/1.50      inference(global_propositional_subsumption,
% 7.65/1.50                [status(thm)],
% 7.65/1.50                [c_1637,c_35,c_36,c_37,c_38,c_39,c_40]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1991,plain,
% 7.65/1.50      ( k2_relat_1(sK3) = sK0 ),
% 7.65/1.50      inference(light_normalisation,[status(thm)],[c_1988,c_1794]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_4986,plain,
% 7.65/1.50      ( k2_funct_1(k2_funct_1(sK3)) = sK3
% 7.65/1.50      | k1_relat_1(k2_funct_1(sK3)) != sK0
% 7.65/1.50      | k6_partfun1(k2_relat_1(k2_funct_1(sK3))) != k6_partfun1(k1_relat_1(sK3))
% 7.65/1.50      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 7.65/1.50      | v1_funct_1(sK3) != iProver_top
% 7.65/1.50      | v2_funct_1(k2_funct_1(sK3)) != iProver_top
% 7.65/1.50      | v1_relat_1(k2_funct_1(sK3)) != iProver_top
% 7.65/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.65/1.50      inference(light_normalisation,[status(thm)],[c_4985,c_1991]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_26,negated_conjecture,
% 7.65/1.50      ( v2_funct_1(sK2) ),
% 7.65/1.50      inference(cnf_transformation,[],[f75]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_42,plain,
% 7.65/1.50      ( v2_funct_1(sK2) = iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1095,plain,
% 7.65/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_2286,plain,
% 7.65/1.50      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 7.65/1.50      | v1_relat_1(sK2) = iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_1095,c_1117]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_2404,plain,
% 7.65/1.50      ( v1_relat_1(sK2) = iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_1116,c_2286]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_15,plain,
% 7.65/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.65/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.65/1.50      | ~ v1_funct_1(X0)
% 7.65/1.50      | ~ v1_funct_1(X3)
% 7.65/1.50      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 7.65/1.50      inference(cnf_transformation,[],[f58]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1106,plain,
% 7.65/1.50      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 7.65/1.50      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 7.65/1.50      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.65/1.50      | v1_funct_1(X5) != iProver_top
% 7.65/1.50      | v1_funct_1(X4) != iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_2673,plain,
% 7.65/1.50      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 7.65/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.65/1.50      | v1_funct_1(X2) != iProver_top
% 7.65/1.50      | v1_funct_1(sK3) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_1098,c_1106]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_3260,plain,
% 7.65/1.50      ( v1_funct_1(X2) != iProver_top
% 7.65/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.65/1.50      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 7.65/1.50      inference(global_propositional_subsumption,
% 7.65/1.50                [status(thm)],
% 7.65/1.50                [c_2673,c_38]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_3261,plain,
% 7.65/1.50      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 7.65/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.65/1.50      | v1_funct_1(X2) != iProver_top ),
% 7.65/1.50      inference(renaming,[status(thm)],[c_3260]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_3269,plain,
% 7.65/1.50      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 7.65/1.50      | v1_funct_1(sK2) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_1095,c_3261]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_3270,plain,
% 7.65/1.50      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 7.65/1.50      | v1_funct_1(sK2) != iProver_top ),
% 7.65/1.50      inference(light_normalisation,[status(thm)],[c_3269,c_1787]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_4279,plain,
% 7.65/1.50      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 7.65/1.50      inference(global_propositional_subsumption,
% 7.65/1.50                [status(thm)],
% 7.65/1.50                [c_3270,c_35]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_4281,plain,
% 7.65/1.50      ( k2_funct_1(sK3) = sK2
% 7.65/1.50      | k1_relat_1(sK3) != k2_relat_1(sK2)
% 7.65/1.50      | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
% 7.65/1.50      | v1_funct_1(sK3) != iProver_top
% 7.65/1.50      | v1_funct_1(sK2) != iProver_top
% 7.65/1.50      | v2_funct_1(sK3) != iProver_top
% 7.65/1.50      | v1_relat_1(sK3) != iProver_top
% 7.65/1.50      | v1_relat_1(sK2) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_4279,c_1111]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1989,plain,
% 7.65/1.50      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_1095,c_1110]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1990,plain,
% 7.65/1.50      ( k2_relat_1(sK2) = sK1 ),
% 7.65/1.50      inference(light_normalisation,[status(thm)],[c_1989,c_28]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_4282,plain,
% 7.65/1.50      ( k2_funct_1(sK3) = sK2
% 7.65/1.50      | k1_relat_1(sK3) != sK1
% 7.65/1.50      | k6_partfun1(sK0) != k6_partfun1(sK0)
% 7.65/1.50      | v1_funct_1(sK3) != iProver_top
% 7.65/1.50      | v1_funct_1(sK2) != iProver_top
% 7.65/1.50      | v2_funct_1(sK3) != iProver_top
% 7.65/1.50      | v1_relat_1(sK3) != iProver_top
% 7.65/1.50      | v1_relat_1(sK2) != iProver_top ),
% 7.65/1.50      inference(light_normalisation,[status(thm)],[c_4281,c_1990,c_1991]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_4283,plain,
% 7.65/1.50      ( k2_funct_1(sK3) = sK2
% 7.65/1.50      | k1_relat_1(sK3) != sK1
% 7.65/1.50      | v1_funct_1(sK3) != iProver_top
% 7.65/1.50      | v1_funct_1(sK2) != iProver_top
% 7.65/1.50      | v2_funct_1(sK3) != iProver_top
% 7.65/1.50      | v1_relat_1(sK3) != iProver_top
% 7.65/1.50      | v1_relat_1(sK2) != iProver_top ),
% 7.65/1.50      inference(equality_resolution_simp,[status(thm)],[c_4282]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_5426,plain,
% 7.65/1.50      ( k1_relat_1(sK3) != sK1 | k2_funct_1(sK3) = sK2 ),
% 7.65/1.50      inference(global_propositional_subsumption,
% 7.65/1.50                [status(thm)],
% 7.65/1.50                [c_4283,c_35,c_38,c_2401,c_2404,c_4974]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_5427,plain,
% 7.65/1.50      ( k2_funct_1(sK3) = sK2 | k1_relat_1(sK3) != sK1 ),
% 7.65/1.50      inference(renaming,[status(thm)],[c_5426]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_22,plain,
% 7.65/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.65/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.65/1.50      | ~ v1_funct_1(X0)
% 7.65/1.50      | ~ v2_funct_1(X0)
% 7.65/1.50      | k2_relset_1(X1,X2,X0) != X2
% 7.65/1.50      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 7.65/1.50      | k1_xboole_0 = X2 ),
% 7.65/1.50      inference(cnf_transformation,[],[f65]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1100,plain,
% 7.65/1.50      ( k2_relset_1(X0,X1,X2) != X1
% 7.65/1.50      | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
% 7.65/1.50      | k1_xboole_0 = X1
% 7.65/1.50      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.65/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.65/1.50      | v1_funct_1(X2) != iProver_top
% 7.65/1.50      | v2_funct_1(X2) != iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_2595,plain,
% 7.65/1.50      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
% 7.65/1.50      | sK0 = k1_xboole_0
% 7.65/1.50      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 7.65/1.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 7.65/1.50      | v1_funct_1(sK3) != iProver_top
% 7.65/1.50      | v2_funct_1(sK3) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_1794,c_1100]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_5312,plain,
% 7.65/1.50      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
% 7.65/1.50      inference(global_propositional_subsumption,
% 7.65/1.50                [status(thm)],
% 7.65/1.50                [c_2595,c_38,c_39,c_40,c_25,c_652,c_1199,c_4974]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_5314,plain,
% 7.65/1.50      ( k6_partfun1(k1_relat_1(sK3)) = k6_partfun1(sK1) ),
% 7.65/1.50      inference(demodulation,[status(thm)],[c_5312,c_4984]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_2,plain,
% 7.65/1.50      ( k2_relat_1(k6_partfun1(X0)) = X0 ),
% 7.65/1.50      inference(cnf_transformation,[],[f79]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_5772,plain,
% 7.65/1.50      ( k2_relat_1(k6_partfun1(sK1)) = k1_relat_1(sK3) ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_5314,c_2]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_5773,plain,
% 7.65/1.50      ( k1_relat_1(sK3) = sK1 ),
% 7.65/1.50      inference(demodulation,[status(thm)],[c_5772,c_2]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_633,plain,
% 7.65/1.50      ( ~ v1_funct_1(X0) | v1_funct_1(X1) | X1 != X0 ),
% 7.65/1.50      theory(equality) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1377,plain,
% 7.65/1.50      ( v1_funct_1(X0) | ~ v1_funct_1(sK2) | X0 != sK2 ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_633]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1462,plain,
% 7.65/1.50      ( v1_funct_1(k2_funct_1(X0))
% 7.65/1.50      | ~ v1_funct_1(sK2)
% 7.65/1.50      | k2_funct_1(X0) != sK2 ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_1377]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_7784,plain,
% 7.65/1.50      ( v1_funct_1(k2_funct_1(sK3))
% 7.65/1.50      | ~ v1_funct_1(sK2)
% 7.65/1.50      | k2_funct_1(sK3) != sK2 ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_1462]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_7785,plain,
% 7.65/1.50      ( k2_funct_1(sK3) != sK2
% 7.65/1.50      | v1_funct_1(k2_funct_1(sK3)) = iProver_top
% 7.65/1.50      | v1_funct_1(sK2) != iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_7784]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_630,plain,
% 7.65/1.50      ( ~ v2_funct_1(X0) | v2_funct_1(X1) | X1 != X0 ),
% 7.65/1.50      theory(equality) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_2525,plain,
% 7.65/1.50      ( v2_funct_1(X0) | ~ v2_funct_1(sK2) | X0 != sK2 ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_630]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_4251,plain,
% 7.65/1.50      ( v2_funct_1(k2_funct_1(X0))
% 7.65/1.50      | ~ v2_funct_1(sK2)
% 7.65/1.50      | k2_funct_1(X0) != sK2 ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_2525]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_8469,plain,
% 7.65/1.50      ( v2_funct_1(k2_funct_1(sK3))
% 7.65/1.50      | ~ v2_funct_1(sK2)
% 7.65/1.50      | k2_funct_1(sK3) != sK2 ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_4251]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_8470,plain,
% 7.65/1.50      ( k2_funct_1(sK3) != sK2
% 7.65/1.50      | v2_funct_1(k2_funct_1(sK3)) = iProver_top
% 7.65/1.50      | v2_funct_1(sK2) != iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_8469]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_623,plain,
% 7.65/1.50      ( ~ v1_relat_1(X0) | v1_relat_1(X1) | X1 != X0 ),
% 7.65/1.50      theory(equality) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_2558,plain,
% 7.65/1.50      ( v1_relat_1(X0) | ~ v1_relat_1(sK2) | X0 != sK2 ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_623]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_4948,plain,
% 7.65/1.50      ( v1_relat_1(k2_funct_1(X0))
% 7.65/1.50      | ~ v1_relat_1(sK2)
% 7.65/1.50      | k2_funct_1(X0) != sK2 ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_2558]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_8854,plain,
% 7.65/1.50      ( v1_relat_1(k2_funct_1(sK3))
% 7.65/1.50      | ~ v1_relat_1(sK2)
% 7.65/1.50      | k2_funct_1(sK3) != sK2 ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_4948]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_8855,plain,
% 7.65/1.50      ( k2_funct_1(sK3) != sK2
% 7.65/1.50      | v1_relat_1(k2_funct_1(sK3)) = iProver_top
% 7.65/1.50      | v1_relat_1(sK2) != iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_8854]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_15802,plain,
% 7.65/1.50      ( k6_partfun1(k2_relat_1(k2_funct_1(sK3))) != k6_partfun1(k1_relat_1(sK3))
% 7.65/1.50      | k1_relat_1(k2_funct_1(sK3)) != sK0
% 7.65/1.50      | k2_funct_1(k2_funct_1(sK3)) = sK3 ),
% 7.65/1.50      inference(global_propositional_subsumption,
% 7.65/1.50                [status(thm)],
% 7.65/1.50                [c_4986,c_35,c_38,c_42,c_2401,c_2404,c_4283,c_4974,
% 7.65/1.50                 c_5773,c_7785,c_8470,c_8855]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_15803,plain,
% 7.65/1.50      ( k2_funct_1(k2_funct_1(sK3)) = sK3
% 7.65/1.50      | k1_relat_1(k2_funct_1(sK3)) != sK0
% 7.65/1.50      | k6_partfun1(k2_relat_1(k2_funct_1(sK3))) != k6_partfun1(k1_relat_1(sK3)) ),
% 7.65/1.50      inference(renaming,[status(thm)],[c_15802]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_2594,plain,
% 7.65/1.50      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
% 7.65/1.50      | sK1 = k1_xboole_0
% 7.65/1.50      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 7.65/1.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.65/1.50      | v1_funct_1(sK2) != iProver_top
% 7.65/1.50      | v2_funct_1(sK2) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_28,c_1100]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1093,plain,
% 7.65/1.50      ( v1_funct_1(sK2) = iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_2506,plain,
% 7.65/1.50      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
% 7.65/1.50      | v2_funct_1(sK2) != iProver_top
% 7.65/1.50      | v1_relat_1(sK2) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_1093,c_1112]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_2575,plain,
% 7.65/1.50      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
% 7.65/1.50      inference(global_propositional_subsumption,
% 7.65/1.50                [status(thm)],
% 7.65/1.50                [c_2506,c_42,c_2404]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_2597,plain,
% 7.65/1.50      ( k6_partfun1(k1_relat_1(sK2)) = k6_partfun1(sK0)
% 7.65/1.50      | sK1 = k1_xboole_0
% 7.65/1.50      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 7.65/1.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.65/1.50      | v1_funct_1(sK2) != iProver_top
% 7.65/1.50      | v2_funct_1(sK2) != iProver_top ),
% 7.65/1.50      inference(demodulation,[status(thm)],[c_2594,c_2575]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_24,negated_conjecture,
% 7.65/1.50      ( k1_xboole_0 != sK1 ),
% 7.65/1.50      inference(cnf_transformation,[],[f77]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1178,plain,
% 7.65/1.50      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_622]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1179,plain,
% 7.65/1.50      ( sK1 != k1_xboole_0
% 7.65/1.50      | k1_xboole_0 = sK1
% 7.65/1.50      | k1_xboole_0 != k1_xboole_0 ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_1178]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_3507,plain,
% 7.65/1.50      ( k6_partfun1(k1_relat_1(sK2)) = k6_partfun1(sK0) ),
% 7.65/1.50      inference(global_propositional_subsumption,
% 7.65/1.50                [status(thm)],
% 7.65/1.50                [c_2597,c_35,c_36,c_37,c_42,c_24,c_652,c_1179]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_3515,plain,
% 7.65/1.50      ( k2_relat_1(k6_partfun1(sK0)) = k1_relat_1(sK2) ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_3507,c_2]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_3516,plain,
% 7.65/1.50      ( k1_relat_1(sK2) = sK0 ),
% 7.65/1.50      inference(demodulation,[status(thm)],[c_3515,c_2]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_5803,plain,
% 7.65/1.50      ( k2_funct_1(sK3) = sK2 | sK1 != sK1 ),
% 7.65/1.50      inference(demodulation,[status(thm)],[c_5773,c_5427]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_5814,plain,
% 7.65/1.50      ( k2_funct_1(sK3) = sK2 ),
% 7.65/1.50      inference(equality_resolution_simp,[status(thm)],[c_5803]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_15804,plain,
% 7.65/1.50      ( k2_funct_1(sK2) = sK3
% 7.65/1.50      | k6_partfun1(sK1) != k6_partfun1(sK1)
% 7.65/1.50      | sK0 != sK0 ),
% 7.65/1.50      inference(light_normalisation,
% 7.65/1.50                [status(thm)],
% 7.65/1.50                [c_15803,c_1990,c_3516,c_5773,c_5814]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_15805,plain,
% 7.65/1.50      ( k2_funct_1(sK2) = sK3 ),
% 7.65/1.50      inference(equality_resolution_simp,[status(thm)],[c_15804]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_23,negated_conjecture,
% 7.65/1.50      ( k2_funct_1(sK2) != sK3 ),
% 7.65/1.50      inference(cnf_transformation,[],[f78]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(contradiction,plain,
% 7.65/1.50      ( $false ),
% 7.65/1.50      inference(minisat,[status(thm)],[c_15805,c_23]) ).
% 7.65/1.50  
% 7.65/1.50  
% 7.65/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.65/1.50  
% 7.65/1.50  ------                               Statistics
% 7.65/1.50  
% 7.65/1.50  ------ General
% 7.65/1.50  
% 7.65/1.50  abstr_ref_over_cycles:                  0
% 7.65/1.50  abstr_ref_under_cycles:                 0
% 7.65/1.50  gc_basic_clause_elim:                   0
% 7.65/1.50  forced_gc_time:                         0
% 7.65/1.50  parsing_time:                           0.013
% 7.65/1.50  unif_index_cands_time:                  0.
% 7.65/1.50  unif_index_add_time:                    0.
% 7.65/1.50  orderings_time:                         0.
% 7.65/1.50  out_proof_time:                         0.016
% 7.65/1.50  total_time:                             0.69
% 7.65/1.50  num_of_symbols:                         51
% 7.65/1.50  num_of_terms:                           24945
% 7.65/1.50  
% 7.65/1.50  ------ Preprocessing
% 7.65/1.50  
% 7.65/1.50  num_of_splits:                          0
% 7.65/1.50  num_of_split_atoms:                     0
% 7.65/1.50  num_of_reused_defs:                     0
% 7.65/1.50  num_eq_ax_congr_red:                    0
% 7.65/1.50  num_of_sem_filtered_clauses:            1
% 7.65/1.50  num_of_subtypes:                        0
% 7.65/1.50  monotx_restored_types:                  0
% 7.65/1.50  sat_num_of_epr_types:                   0
% 7.65/1.50  sat_num_of_non_cyclic_types:            0
% 7.65/1.50  sat_guarded_non_collapsed_types:        0
% 7.65/1.50  num_pure_diseq_elim:                    0
% 7.65/1.50  simp_replaced_by:                       0
% 7.65/1.50  res_preprocessed:                       170
% 7.65/1.50  prep_upred:                             0
% 7.65/1.50  prep_unflattend:                        12
% 7.65/1.50  smt_new_axioms:                         0
% 7.65/1.50  pred_elim_cands:                        5
% 7.65/1.50  pred_elim:                              1
% 7.65/1.50  pred_elim_cl:                           1
% 7.65/1.50  pred_elim_cycles:                       3
% 7.65/1.50  merged_defs:                            0
% 7.65/1.50  merged_defs_ncl:                        0
% 7.65/1.50  bin_hyper_res:                          0
% 7.65/1.50  prep_cycles:                            4
% 7.65/1.50  pred_elim_time:                         0.004
% 7.65/1.50  splitting_time:                         0.
% 7.65/1.50  sem_filter_time:                        0.
% 7.65/1.50  monotx_time:                            0.001
% 7.65/1.50  subtype_inf_time:                       0.
% 7.65/1.50  
% 7.65/1.50  ------ Problem properties
% 7.65/1.50  
% 7.65/1.50  clauses:                                34
% 7.65/1.50  conjectures:                            11
% 7.65/1.50  epr:                                    7
% 7.65/1.50  horn:                                   30
% 7.65/1.50  ground:                                 12
% 7.65/1.50  unary:                                  17
% 7.65/1.50  binary:                                 2
% 7.65/1.50  lits:                                   123
% 7.65/1.50  lits_eq:                                30
% 7.65/1.50  fd_pure:                                0
% 7.65/1.50  fd_pseudo:                              0
% 7.65/1.50  fd_cond:                                4
% 7.65/1.50  fd_pseudo_cond:                         1
% 7.65/1.50  ac_symbols:                             0
% 7.65/1.50  
% 7.65/1.50  ------ Propositional Solver
% 7.65/1.50  
% 7.65/1.50  prop_solver_calls:                      32
% 7.65/1.50  prop_fast_solver_calls:                 2626
% 7.65/1.50  smt_solver_calls:                       0
% 7.65/1.50  smt_fast_solver_calls:                  0
% 7.65/1.50  prop_num_of_clauses:                    8557
% 7.65/1.50  prop_preprocess_simplified:             13369
% 7.65/1.50  prop_fo_subsumed:                       416
% 7.65/1.50  prop_solver_time:                       0.
% 7.65/1.50  smt_solver_time:                        0.
% 7.65/1.50  smt_fast_solver_time:                   0.
% 7.65/1.50  prop_fast_solver_time:                  0.
% 7.65/1.50  prop_unsat_core_time:                   0.001
% 7.65/1.50  
% 7.65/1.50  ------ QBF
% 7.65/1.50  
% 7.65/1.50  qbf_q_res:                              0
% 7.65/1.50  qbf_num_tautologies:                    0
% 7.65/1.50  qbf_prep_cycles:                        0
% 7.65/1.50  
% 7.65/1.50  ------ BMC1
% 7.65/1.50  
% 7.65/1.50  bmc1_current_bound:                     -1
% 7.65/1.50  bmc1_last_solved_bound:                 -1
% 7.65/1.50  bmc1_unsat_core_size:                   -1
% 7.65/1.50  bmc1_unsat_core_parents_size:           -1
% 7.65/1.50  bmc1_merge_next_fun:                    0
% 7.65/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.65/1.50  
% 7.65/1.50  ------ Instantiation
% 7.65/1.50  
% 7.65/1.50  inst_num_of_clauses:                    1966
% 7.65/1.50  inst_num_in_passive:                    401
% 7.65/1.50  inst_num_in_active:                     1244
% 7.65/1.50  inst_num_in_unprocessed:                321
% 7.65/1.50  inst_num_of_loops:                      1430
% 7.65/1.50  inst_num_of_learning_restarts:          0
% 7.65/1.50  inst_num_moves_active_passive:          182
% 7.65/1.50  inst_lit_activity:                      0
% 7.65/1.50  inst_lit_activity_moves:                1
% 7.65/1.50  inst_num_tautologies:                   0
% 7.65/1.50  inst_num_prop_implied:                  0
% 7.65/1.50  inst_num_existing_simplified:           0
% 7.65/1.50  inst_num_eq_res_simplified:             0
% 7.65/1.50  inst_num_child_elim:                    0
% 7.65/1.50  inst_num_of_dismatching_blockings:      418
% 7.65/1.50  inst_num_of_non_proper_insts:           2210
% 7.65/1.50  inst_num_of_duplicates:                 0
% 7.65/1.50  inst_inst_num_from_inst_to_res:         0
% 7.65/1.50  inst_dismatching_checking_time:         0.
% 7.65/1.50  
% 7.65/1.50  ------ Resolution
% 7.65/1.50  
% 7.65/1.50  res_num_of_clauses:                     0
% 7.65/1.50  res_num_in_passive:                     0
% 7.65/1.50  res_num_in_active:                      0
% 7.65/1.50  res_num_of_loops:                       174
% 7.65/1.50  res_forward_subset_subsumed:            154
% 7.65/1.50  res_backward_subset_subsumed:           0
% 7.65/1.50  res_forward_subsumed:                   0
% 7.65/1.50  res_backward_subsumed:                  0
% 7.65/1.50  res_forward_subsumption_resolution:     2
% 7.65/1.50  res_backward_subsumption_resolution:    0
% 7.65/1.50  res_clause_to_clause_subsumption:       1863
% 7.65/1.50  res_orphan_elimination:                 0
% 7.65/1.50  res_tautology_del:                      116
% 7.65/1.50  res_num_eq_res_simplified:              1
% 7.65/1.50  res_num_sel_changes:                    0
% 7.65/1.50  res_moves_from_active_to_pass:          0
% 7.65/1.50  
% 7.65/1.50  ------ Superposition
% 7.65/1.50  
% 7.65/1.50  sup_time_total:                         0.
% 7.65/1.50  sup_time_generating:                    0.
% 7.65/1.50  sup_time_sim_full:                      0.
% 7.65/1.50  sup_time_sim_immed:                     0.
% 7.65/1.50  
% 7.65/1.50  sup_num_of_clauses:                     832
% 7.65/1.50  sup_num_in_active:                      249
% 7.65/1.50  sup_num_in_passive:                     583
% 7.65/1.50  sup_num_of_loops:                       284
% 7.65/1.50  sup_fw_superposition:                   367
% 7.65/1.50  sup_bw_superposition:                   584
% 7.65/1.50  sup_immediate_simplified:               322
% 7.65/1.50  sup_given_eliminated:                   2
% 7.65/1.50  comparisons_done:                       0
% 7.65/1.50  comparisons_avoided:                    4
% 7.65/1.50  
% 7.65/1.50  ------ Simplifications
% 7.65/1.50  
% 7.65/1.50  
% 7.65/1.50  sim_fw_subset_subsumed:                 19
% 7.65/1.50  sim_bw_subset_subsumed:                 43
% 7.65/1.50  sim_fw_subsumed:                        35
% 7.65/1.50  sim_bw_subsumed:                        25
% 7.65/1.50  sim_fw_subsumption_res:                 0
% 7.65/1.50  sim_bw_subsumption_res:                 0
% 7.65/1.50  sim_tautology_del:                      0
% 7.65/1.50  sim_eq_tautology_del:                   26
% 7.65/1.50  sim_eq_res_simp:                        3
% 7.65/1.50  sim_fw_demodulated:                     36
% 7.65/1.50  sim_bw_demodulated:                     7
% 7.65/1.50  sim_light_normalised:                   286
% 7.65/1.50  sim_joinable_taut:                      0
% 7.65/1.50  sim_joinable_simp:                      0
% 7.65/1.50  sim_ac_normalised:                      0
% 7.65/1.50  sim_smt_subsumption:                    0
% 7.65/1.50  
%------------------------------------------------------------------------------
