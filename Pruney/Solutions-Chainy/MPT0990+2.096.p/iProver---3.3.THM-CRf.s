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

% Result     : Theorem 11.62s
% Output     : CNFRefutation 11.62s
% Verified   : 
% Statistics : Number of formulae       :  205 (4678 expanded)
%              Number of clauses        :  132 (1175 expanded)
%              Number of leaves         :   22 (1268 expanded)
%              Depth                    :   24
%              Number of atoms          :  820 (40683 expanded)
%              Number of equality atoms :  406 (14368 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f26])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

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
    inference(ennf_transformation,[],[f18])).

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
     => ( k2_funct_1(X2) != sK4
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & v2_funct_1(X2)
        & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK4),k6_partfun1(X0))
        & k2_relset_1(X0,X1,X2) = X1
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(sK4,X1,X0)
        & v1_funct_1(sK4) ) ) ),
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
          ( k2_funct_1(sK3) != X3
          & k1_xboole_0 != sK2
          & k1_xboole_0 != sK1
          & v2_funct_1(sK3)
          & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,X3),k6_partfun1(sK1))
          & k2_relset_1(sK1,sK2,sK3) = sK2
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
          & v1_funct_2(X3,sK2,sK1)
          & v1_funct_1(X3) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( k2_funct_1(sK3) != sK4
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & v2_funct_1(sK3)
    & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1))
    & k2_relset_1(sK1,sK2,sK3) = sK2
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    & v1_funct_2(sK4,sK2,sK1)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f39,f44,f43])).

fof(f78,plain,(
    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f45])).

fof(f10,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f10])).

fof(f13,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f88,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f59,f63])).

fof(f71,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f73,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f45])).

fof(f74,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f45])).

fof(f76,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f45])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f28])).

fof(f61,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f29])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f14])).

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
    inference(flattening,[],[f32])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f72,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f75,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
            & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f16])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f80,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f45])).

fof(f4,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f85,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f51,f63])).

fof(f77,plain,(
    k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f45])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f15])).

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
    inference(flattening,[],[f34])).

fof(f67,plain,(
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
    inference(cnf_transformation,[],[f35])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f54,plain,(
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
    inference(definition_unfolding,[],[f54,f63])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f79,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f30])).

fof(f62,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f53,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f83,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f49,f63])).

fof(f81,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f45])).

fof(f52,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f48,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f84,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f48,f63])).

fof(f82,plain,(
    k2_funct_1(sK3) != sK4 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_12,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_28,negated_conjecture,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_382,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) != X0
    | k6_partfun1(sK1) != X3
    | sK1 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_28])).

cnf(c_383,plain,
    ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
    inference(unflattening,[status(thm)],[c_382])).

cnf(c_13,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_391,plain,
    ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_383,c_13])).

cnf(c_1095,plain,
    ( k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_391])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1202,plain,
    ( m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1787,plain,
    ( k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1095,c_35,c_33,c_32,c_30,c_391,c_1202])).

cnf(c_17,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_395,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X2,X1,X1,X2,X3,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | k2_relset_1(X1,X2,X0) = X2
    | k6_partfun1(X2) != k6_partfun1(sK1)
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_28])).

cnf(c_396,plain,
    ( ~ v1_funct_2(X0,X1,sK1)
    | ~ v1_funct_2(X2,sK1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK1,X1,X1,sK1,X2,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | k2_relset_1(X1,sK1,X0) = sK1
    | k6_partfun1(sK1) != k6_partfun1(sK1) ),
    inference(unflattening,[status(thm)],[c_395])).

cnf(c_477,plain,
    ( ~ v1_funct_2(X0,X1,sK1)
    | ~ v1_funct_2(X2,sK1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK1,X1,X1,sK1,X2,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | k2_relset_1(X1,sK1,X0) = sK1 ),
    inference(equality_resolution_simp,[status(thm)],[c_396])).

cnf(c_1094,plain,
    ( k1_partfun1(sK1,X0,X0,sK1,X1,X2) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | k2_relset_1(X0,sK1,X2) = sK1
    | v1_funct_2(X2,X0,sK1) != iProver_top
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_477])).

cnf(c_1790,plain,
    ( k1_partfun1(sK1,X0,X0,sK1,X1,X2) != k6_partfun1(sK1)
    | k2_relset_1(X0,sK1,X2) = sK1
    | v1_funct_2(X2,X0,sK1) != iProver_top
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1094,c_1787])).

cnf(c_1794,plain,
    ( k2_relset_1(sK2,sK1,sK4) = sK1
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | v1_funct_2(sK3,sK1,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1787,c_1790])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1210,plain,
    ( ~ v1_funct_2(X0,sK1,X1)
    | ~ v1_funct_2(sK4,X1,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK4)
    | k1_partfun1(sK1,X1,X1,sK1,X0,sK4) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | k2_relset_1(X1,sK1,sK4) = sK1 ),
    inference(instantiation,[status(thm)],[c_477])).

cnf(c_1323,plain,
    ( ~ v1_funct_2(sK4,X0,sK1)
    | ~ v1_funct_2(sK3,sK1,X0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(sK1,X0,X0,sK1,sK3,sK4) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | k2_relset_1(X0,sK1,sK4) = sK1 ),
    inference(instantiation,[status(thm)],[c_1210])).

cnf(c_1526,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_2(sK3,sK1,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
    | k2_relset_1(sK2,sK1,sK4) = sK1 ),
    inference(instantiation,[status(thm)],[c_1323])).

cnf(c_636,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1672,plain,
    ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_636])).

cnf(c_1861,plain,
    ( k2_relset_1(sK2,sK1,sK4) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1794,c_35,c_34,c_33,c_32,c_31,c_30,c_1526,c_1672])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1104,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2651,plain,
    ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(sK2)
    | sK1 = k1_xboole_0
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1861,c_1104])).

cnf(c_39,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_40,plain,
    ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_41,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_26,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_667,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_636])).

cnf(c_637,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1200,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_637])).

cnf(c_1201,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1200])).

cnf(c_4,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_4825,plain,
    ( v2_funct_1(k6_partfun1(sK1)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_4826,plain,
    ( v2_funct_1(k6_partfun1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4825])).

cnf(c_29,negated_conjecture,
    ( k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_19,plain,
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
    inference(cnf_transformation,[],[f67])).

cnf(c_1108,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4971,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,sK2,X0) != iProver_top
    | v1_funct_2(sK3,sK1,sK2) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK1,sK2,sK2,X0,sK3,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_29,c_1108])).

cnf(c_36,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_37,plain,
    ( v1_funct_2(sK3,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_38,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_4978,plain,
    ( v1_funct_1(X1) != iProver_top
    | v1_funct_2(X1,sK2,X0) != iProver_top
    | k1_xboole_0 = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK1,sK2,sK2,X0,sK3,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4971,c_36,c_37,c_38])).

cnf(c_4979,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,sK2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK1,sK2,sK2,X0,sK3,X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4978])).

cnf(c_4982,plain,
    ( sK1 = k1_xboole_0
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_funct_1(k6_partfun1(sK1)) != iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1787,c_4979])).

cnf(c_5280,plain,
    ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2651,c_39,c_40,c_41,c_26,c_667,c_1201,c_4826,c_4982])).

cnf(c_8,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v2_funct_1(X0)
    | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
    | k2_funct_1(X0) = X1
    | k1_relat_1(X0) != k2_relat_1(X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1116,plain,
    ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k1_relat_1(X1) != k2_relat_1(X0)
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v2_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_5286,plain,
    ( k2_funct_1(k2_funct_1(sK4)) = sK4
    | k1_relat_1(k2_funct_1(sK4)) != k2_relat_1(sK4)
    | k6_partfun1(k2_relat_1(k2_funct_1(sK4))) != k6_partfun1(sK2)
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v2_funct_1(k2_funct_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5280,c_1116])).

cnf(c_1102,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1114,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2004,plain,
    ( k2_relset_1(sK2,sK1,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1102,c_1114])).

cnf(c_2007,plain,
    ( k2_relat_1(sK4) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2004,c_1861])).

cnf(c_5287,plain,
    ( k2_funct_1(k2_funct_1(sK4)) = sK4
    | k1_relat_1(k2_funct_1(sK4)) != sK1
    | k6_partfun1(k2_relat_1(k2_funct_1(sK4))) != k6_partfun1(sK2)
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v2_funct_1(k2_funct_1(sK4)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5286,c_2007])).

cnf(c_27,negated_conjecture,
    ( v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1242,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1601,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1242])).

cnf(c_1713,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1099,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1110,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2754,plain,
    ( k1_partfun1(X0,X1,sK2,sK1,X2,sK4) = k5_relat_1(X2,sK4)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1102,c_1110])).

cnf(c_2766,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK2,sK1,X2,sK4) = k5_relat_1(X2,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2754,c_39])).

cnf(c_2767,plain,
    ( k1_partfun1(X0,X1,sK2,sK1,X2,sK4) = k5_relat_1(X2,sK4)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_2766])).

cnf(c_2774,plain,
    ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k5_relat_1(sK3,sK4)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1099,c_2767])).

cnf(c_2775,plain,
    ( k5_relat_1(sK3,sK4) = k6_partfun1(sK1)
    | v1_funct_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2774,c_1787])).

cnf(c_3494,plain,
    ( k5_relat_1(sK3,sK4) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2775,c_36])).

cnf(c_4002,plain,
    ( k2_funct_1(sK4) = sK3
    | k1_relat_1(sK4) != k2_relat_1(sK3)
    | k6_partfun1(k2_relat_1(sK4)) != k6_partfun1(sK1)
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v2_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3494,c_1116])).

cnf(c_2005,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1099,c_1114])).

cnf(c_2006,plain,
    ( k2_relat_1(sK3) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_2005,c_29])).

cnf(c_4003,plain,
    ( k2_funct_1(sK4) = sK3
    | k1_relat_1(sK4) != sK2
    | k6_partfun1(sK1) != k6_partfun1(sK1)
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v2_funct_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4002,c_2006,c_2007])).

cnf(c_4004,plain,
    ( k2_funct_1(sK4) = sK3
    | k1_relat_1(sK4) != sK2
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v2_funct_1(sK4) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4003])).

cnf(c_1602,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1601])).

cnf(c_1714,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1713])).

cnf(c_5233,plain,
    ( k1_relat_1(sK4) != sK2
    | k2_funct_1(sK4) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4004,c_36,c_38,c_39,c_40,c_41,c_26,c_667,c_1201,c_1602,c_1714,c_4826,c_4982])).

cnf(c_5234,plain,
    ( k2_funct_1(sK4) = sK3
    | k1_relat_1(sK4) != sK2 ),
    inference(renaming,[status(thm)],[c_5233])).

cnf(c_5055,plain,
    ( v2_funct_1(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4982,c_39,c_40,c_41,c_26,c_667,c_1201,c_4826])).

cnf(c_1100,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_6,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1118,plain,
    ( k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2272,plain,
    ( k2_relat_1(k5_relat_1(sK4,k2_funct_1(sK4))) = k1_relat_1(sK4)
    | v1_relat_1(sK4) != iProver_top
    | v2_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1100,c_1118])).

cnf(c_2607,plain,
    ( k2_relat_1(k5_relat_1(sK4,k2_funct_1(sK4))) = k1_relat_1(sK4)
    | v2_funct_1(sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2272,c_41,c_1602])).

cnf(c_5059,plain,
    ( k2_relat_1(k5_relat_1(sK4,k2_funct_1(sK4))) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_5055,c_2607])).

cnf(c_5283,plain,
    ( k2_relat_1(k6_partfun1(sK2)) = k1_relat_1(sK4) ),
    inference(demodulation,[status(thm)],[c_5280,c_5059])).

cnf(c_2,plain,
    ( k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_5284,plain,
    ( k1_relat_1(sK4) = sK2 ),
    inference(demodulation,[status(thm)],[c_5283,c_2])).

cnf(c_5288,plain,
    ( ~ v1_funct_1(k2_funct_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(k2_funct_1(sK4))
    | ~ v1_relat_1(sK4)
    | ~ v2_funct_1(k2_funct_1(sK4))
    | k2_funct_1(k2_funct_1(sK4)) = sK4
    | k1_relat_1(k2_funct_1(sK4)) != sK1
    | k6_partfun1(k2_relat_1(k2_funct_1(sK4))) != k6_partfun1(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5287])).

cnf(c_645,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1379,plain,
    ( v1_funct_1(X0)
    | ~ v1_funct_1(sK3)
    | X0 != sK3 ),
    inference(instantiation,[status(thm)],[c_645])).

cnf(c_1458,plain,
    ( v1_funct_1(k2_funct_1(X0))
    | ~ v1_funct_1(sK3)
    | k2_funct_1(X0) != sK3 ),
    inference(instantiation,[status(thm)],[c_1379])).

cnf(c_8389,plain,
    ( v1_funct_1(k2_funct_1(sK4))
    | ~ v1_funct_1(sK3)
    | k2_funct_1(sK4) != sK3 ),
    inference(instantiation,[status(thm)],[c_1458])).

cnf(c_642,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1766,plain,
    ( v1_relat_1(X0)
    | ~ v1_relat_1(sK3)
    | X0 != sK3 ),
    inference(instantiation,[status(thm)],[c_642])).

cnf(c_2252,plain,
    ( v1_relat_1(k2_funct_1(X0))
    | ~ v1_relat_1(sK3)
    | k2_funct_1(X0) != sK3 ),
    inference(instantiation,[status(thm)],[c_1766])).

cnf(c_8387,plain,
    ( v1_relat_1(k2_funct_1(sK4))
    | ~ v1_relat_1(sK3)
    | k2_funct_1(sK4) != sK3 ),
    inference(instantiation,[status(thm)],[c_2252])).

cnf(c_641,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2286,plain,
    ( v2_funct_1(X0)
    | ~ v2_funct_1(sK3)
    | X0 != sK3 ),
    inference(instantiation,[status(thm)],[c_641])).

cnf(c_2527,plain,
    ( v2_funct_1(k2_funct_1(X0))
    | ~ v2_funct_1(sK3)
    | k2_funct_1(X0) != sK3 ),
    inference(instantiation,[status(thm)],[c_2286])).

cnf(c_8386,plain,
    ( v2_funct_1(k2_funct_1(sK4))
    | ~ v2_funct_1(sK3)
    | k2_funct_1(sK4) != sK3 ),
    inference(instantiation,[status(thm)],[c_2527])).

cnf(c_24522,plain,
    ( k6_partfun1(k2_relat_1(k2_funct_1(sK4))) != k6_partfun1(sK2)
    | k1_relat_1(k2_funct_1(sK4)) != sK1
    | k2_funct_1(k2_funct_1(sK4)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5287,c_35,c_36,c_33,c_38,c_32,c_39,c_40,c_30,c_41,c_27,c_26,c_667,c_1201,c_1601,c_1602,c_1713,c_1714,c_4004,c_4826,c_4982,c_5284,c_5288,c_8389,c_8387,c_8386])).

cnf(c_24523,plain,
    ( k2_funct_1(k2_funct_1(sK4)) = sK4
    | k1_relat_1(k2_funct_1(sK4)) != sK1
    | k6_partfun1(k2_relat_1(k2_funct_1(sK4))) != k6_partfun1(sK2) ),
    inference(renaming,[status(thm)],[c_24522])).

cnf(c_2650,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | sK2 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_29,c_1104])).

cnf(c_25,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1165,plain,
    ( ~ v1_funct_2(X0,X1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,sK2,X0) != sK2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_1293,plain,
    ( ~ v1_funct_2(sK3,X0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | k2_relset_1(X0,sK2,sK3) != sK2
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(X0)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_1165])).

cnf(c_1510,plain,
    ( ~ v1_funct_2(sK3,sK1,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | k2_relset_1(sK1,sK2,sK3) != sK2
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_1293])).

cnf(c_2657,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2650,c_35,c_34,c_33,c_29,c_27,c_25,c_1510])).

cnf(c_1097,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_7,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v2_funct_1(X0)
    | k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1117,plain,
    ( k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2054,plain,
    ( k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) = k1_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1097,c_1117])).

cnf(c_43,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_2224,plain,
    ( k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2054,c_38,c_43,c_1714])).

cnf(c_2660,plain,
    ( k1_relat_1(k6_partfun1(sK1)) = k1_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_2657,c_2224])).

cnf(c_3,plain,
    ( k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2661,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(demodulation,[status(thm)],[c_2660,c_3])).

cnf(c_5372,plain,
    ( k2_funct_1(sK4) = sK3
    | sK2 != sK2 ),
    inference(demodulation,[status(thm)],[c_5284,c_5234])).

cnf(c_5523,plain,
    ( k2_funct_1(sK4) = sK3 ),
    inference(equality_resolution_simp,[status(thm)],[c_5372])).

cnf(c_24524,plain,
    ( k2_funct_1(sK3) = sK4
    | k6_partfun1(sK2) != k6_partfun1(sK2)
    | sK1 != sK1 ),
    inference(light_normalisation,[status(thm)],[c_24523,c_2006,c_2661,c_5523])).

cnf(c_24525,plain,
    ( k2_funct_1(sK3) = sK4 ),
    inference(equality_resolution_simp,[status(thm)],[c_24524])).

cnf(c_24,negated_conjecture,
    ( k2_funct_1(sK3) != sK4 ),
    inference(cnf_transformation,[],[f82])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_24525,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:36:02 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 11.62/1.93  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.62/1.93  
% 11.62/1.93  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.62/1.93  
% 11.62/1.93  ------  iProver source info
% 11.62/1.93  
% 11.62/1.93  git: date: 2020-06-30 10:37:57 +0100
% 11.62/1.93  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.62/1.93  git: non_committed_changes: false
% 11.62/1.93  git: last_make_outside_of_git: false
% 11.62/1.93  
% 11.62/1.93  ------ 
% 11.62/1.93  
% 11.62/1.93  ------ Input Options
% 11.62/1.93  
% 11.62/1.93  --out_options                           all
% 11.62/1.93  --tptp_safe_out                         true
% 11.62/1.93  --problem_path                          ""
% 11.62/1.93  --include_path                          ""
% 11.62/1.93  --clausifier                            res/vclausify_rel
% 11.62/1.93  --clausifier_options                    ""
% 11.62/1.93  --stdin                                 false
% 11.62/1.93  --stats_out                             all
% 11.62/1.93  
% 11.62/1.93  ------ General Options
% 11.62/1.93  
% 11.62/1.93  --fof                                   false
% 11.62/1.93  --time_out_real                         305.
% 11.62/1.93  --time_out_virtual                      -1.
% 11.62/1.93  --symbol_type_check                     false
% 11.62/1.93  --clausify_out                          false
% 11.62/1.93  --sig_cnt_out                           false
% 11.62/1.93  --trig_cnt_out                          false
% 11.62/1.93  --trig_cnt_out_tolerance                1.
% 11.62/1.93  --trig_cnt_out_sk_spl                   false
% 11.62/1.93  --abstr_cl_out                          false
% 11.62/1.93  
% 11.62/1.93  ------ Global Options
% 11.62/1.93  
% 11.62/1.93  --schedule                              default
% 11.62/1.93  --add_important_lit                     false
% 11.62/1.93  --prop_solver_per_cl                    1000
% 11.62/1.93  --min_unsat_core                        false
% 11.62/1.93  --soft_assumptions                      false
% 11.62/1.93  --soft_lemma_size                       3
% 11.62/1.93  --prop_impl_unit_size                   0
% 11.62/1.93  --prop_impl_unit                        []
% 11.62/1.93  --share_sel_clauses                     true
% 11.62/1.93  --reset_solvers                         false
% 11.62/1.93  --bc_imp_inh                            [conj_cone]
% 11.62/1.93  --conj_cone_tolerance                   3.
% 11.62/1.93  --extra_neg_conj                        none
% 11.62/1.93  --large_theory_mode                     true
% 11.62/1.93  --prolific_symb_bound                   200
% 11.62/1.93  --lt_threshold                          2000
% 11.62/1.93  --clause_weak_htbl                      true
% 11.62/1.93  --gc_record_bc_elim                     false
% 11.62/1.93  
% 11.62/1.93  ------ Preprocessing Options
% 11.62/1.93  
% 11.62/1.93  --preprocessing_flag                    true
% 11.62/1.93  --time_out_prep_mult                    0.1
% 11.62/1.93  --splitting_mode                        input
% 11.62/1.93  --splitting_grd                         true
% 11.62/1.93  --splitting_cvd                         false
% 11.62/1.93  --splitting_cvd_svl                     false
% 11.62/1.93  --splitting_nvd                         32
% 11.62/1.93  --sub_typing                            true
% 11.62/1.93  --prep_gs_sim                           true
% 11.62/1.93  --prep_unflatten                        true
% 11.62/1.93  --prep_res_sim                          true
% 11.62/1.93  --prep_upred                            true
% 11.62/1.93  --prep_sem_filter                       exhaustive
% 11.62/1.93  --prep_sem_filter_out                   false
% 11.62/1.93  --pred_elim                             true
% 11.62/1.93  --res_sim_input                         true
% 11.62/1.93  --eq_ax_congr_red                       true
% 11.62/1.93  --pure_diseq_elim                       true
% 11.62/1.93  --brand_transform                       false
% 11.62/1.93  --non_eq_to_eq                          false
% 11.62/1.93  --prep_def_merge                        true
% 11.62/1.93  --prep_def_merge_prop_impl              false
% 11.62/1.93  --prep_def_merge_mbd                    true
% 11.62/1.93  --prep_def_merge_tr_red                 false
% 11.62/1.93  --prep_def_merge_tr_cl                  false
% 11.62/1.93  --smt_preprocessing                     true
% 11.62/1.93  --smt_ac_axioms                         fast
% 11.62/1.93  --preprocessed_out                      false
% 11.62/1.93  --preprocessed_stats                    false
% 11.62/1.93  
% 11.62/1.93  ------ Abstraction refinement Options
% 11.62/1.93  
% 11.62/1.93  --abstr_ref                             []
% 11.62/1.93  --abstr_ref_prep                        false
% 11.62/1.93  --abstr_ref_until_sat                   false
% 11.62/1.93  --abstr_ref_sig_restrict                funpre
% 11.62/1.93  --abstr_ref_af_restrict_to_split_sk     false
% 11.62/1.93  --abstr_ref_under                       []
% 11.62/1.93  
% 11.62/1.93  ------ SAT Options
% 11.62/1.93  
% 11.62/1.93  --sat_mode                              false
% 11.62/1.93  --sat_fm_restart_options                ""
% 11.62/1.93  --sat_gr_def                            false
% 11.62/1.93  --sat_epr_types                         true
% 11.62/1.93  --sat_non_cyclic_types                  false
% 11.62/1.93  --sat_finite_models                     false
% 11.62/1.93  --sat_fm_lemmas                         false
% 11.62/1.93  --sat_fm_prep                           false
% 11.62/1.93  --sat_fm_uc_incr                        true
% 11.62/1.93  --sat_out_model                         small
% 11.62/1.93  --sat_out_clauses                       false
% 11.62/1.93  
% 11.62/1.93  ------ QBF Options
% 11.62/1.93  
% 11.62/1.93  --qbf_mode                              false
% 11.62/1.93  --qbf_elim_univ                         false
% 11.62/1.93  --qbf_dom_inst                          none
% 11.62/1.93  --qbf_dom_pre_inst                      false
% 11.62/1.93  --qbf_sk_in                             false
% 11.62/1.93  --qbf_pred_elim                         true
% 11.62/1.93  --qbf_split                             512
% 11.62/1.93  
% 11.62/1.93  ------ BMC1 Options
% 11.62/1.93  
% 11.62/1.93  --bmc1_incremental                      false
% 11.62/1.93  --bmc1_axioms                           reachable_all
% 11.62/1.93  --bmc1_min_bound                        0
% 11.62/1.93  --bmc1_max_bound                        -1
% 11.62/1.93  --bmc1_max_bound_default                -1
% 11.62/1.93  --bmc1_symbol_reachability              true
% 11.62/1.93  --bmc1_property_lemmas                  false
% 11.62/1.93  --bmc1_k_induction                      false
% 11.62/1.93  --bmc1_non_equiv_states                 false
% 11.62/1.93  --bmc1_deadlock                         false
% 11.62/1.93  --bmc1_ucm                              false
% 11.62/1.93  --bmc1_add_unsat_core                   none
% 11.62/1.93  --bmc1_unsat_core_children              false
% 11.62/1.93  --bmc1_unsat_core_extrapolate_axioms    false
% 11.62/1.93  --bmc1_out_stat                         full
% 11.62/1.93  --bmc1_ground_init                      false
% 11.62/1.93  --bmc1_pre_inst_next_state              false
% 11.62/1.93  --bmc1_pre_inst_state                   false
% 11.62/1.93  --bmc1_pre_inst_reach_state             false
% 11.62/1.93  --bmc1_out_unsat_core                   false
% 11.62/1.93  --bmc1_aig_witness_out                  false
% 11.62/1.93  --bmc1_verbose                          false
% 11.62/1.93  --bmc1_dump_clauses_tptp                false
% 11.62/1.93  --bmc1_dump_unsat_core_tptp             false
% 11.62/1.93  --bmc1_dump_file                        -
% 11.62/1.93  --bmc1_ucm_expand_uc_limit              128
% 11.62/1.93  --bmc1_ucm_n_expand_iterations          6
% 11.62/1.93  --bmc1_ucm_extend_mode                  1
% 11.62/1.93  --bmc1_ucm_init_mode                    2
% 11.62/1.93  --bmc1_ucm_cone_mode                    none
% 11.62/1.93  --bmc1_ucm_reduced_relation_type        0
% 11.62/1.93  --bmc1_ucm_relax_model                  4
% 11.62/1.93  --bmc1_ucm_full_tr_after_sat            true
% 11.62/1.93  --bmc1_ucm_expand_neg_assumptions       false
% 11.62/1.93  --bmc1_ucm_layered_model                none
% 11.62/1.93  --bmc1_ucm_max_lemma_size               10
% 11.62/1.93  
% 11.62/1.93  ------ AIG Options
% 11.62/1.93  
% 11.62/1.93  --aig_mode                              false
% 11.62/1.93  
% 11.62/1.93  ------ Instantiation Options
% 11.62/1.93  
% 11.62/1.93  --instantiation_flag                    true
% 11.62/1.93  --inst_sos_flag                         true
% 11.62/1.93  --inst_sos_phase                        true
% 11.62/1.93  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.62/1.93  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.62/1.93  --inst_lit_sel_side                     num_symb
% 11.62/1.93  --inst_solver_per_active                1400
% 11.62/1.93  --inst_solver_calls_frac                1.
% 11.62/1.93  --inst_passive_queue_type               priority_queues
% 11.62/1.93  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.62/1.93  --inst_passive_queues_freq              [25;2]
% 11.62/1.93  --inst_dismatching                      true
% 11.62/1.93  --inst_eager_unprocessed_to_passive     true
% 11.62/1.93  --inst_prop_sim_given                   true
% 11.62/1.93  --inst_prop_sim_new                     false
% 11.62/1.93  --inst_subs_new                         false
% 11.62/1.93  --inst_eq_res_simp                      false
% 11.62/1.93  --inst_subs_given                       false
% 11.62/1.93  --inst_orphan_elimination               true
% 11.62/1.93  --inst_learning_loop_flag               true
% 11.62/1.93  --inst_learning_start                   3000
% 11.62/1.93  --inst_learning_factor                  2
% 11.62/1.93  --inst_start_prop_sim_after_learn       3
% 11.62/1.93  --inst_sel_renew                        solver
% 11.62/1.93  --inst_lit_activity_flag                true
% 11.62/1.93  --inst_restr_to_given                   false
% 11.62/1.93  --inst_activity_threshold               500
% 11.62/1.93  --inst_out_proof                        true
% 11.62/1.93  
% 11.62/1.93  ------ Resolution Options
% 11.62/1.93  
% 11.62/1.93  --resolution_flag                       true
% 11.62/1.93  --res_lit_sel                           adaptive
% 11.62/1.93  --res_lit_sel_side                      none
% 11.62/1.93  --res_ordering                          kbo
% 11.62/1.93  --res_to_prop_solver                    active
% 11.62/1.93  --res_prop_simpl_new                    false
% 11.62/1.93  --res_prop_simpl_given                  true
% 11.62/1.93  --res_passive_queue_type                priority_queues
% 11.62/1.93  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.62/1.93  --res_passive_queues_freq               [15;5]
% 11.62/1.93  --res_forward_subs                      full
% 11.62/1.93  --res_backward_subs                     full
% 11.62/1.93  --res_forward_subs_resolution           true
% 11.62/1.93  --res_backward_subs_resolution          true
% 11.62/1.93  --res_orphan_elimination                true
% 11.62/1.93  --res_time_limit                        2.
% 11.62/1.93  --res_out_proof                         true
% 11.62/1.93  
% 11.62/1.93  ------ Superposition Options
% 11.62/1.93  
% 11.62/1.93  --superposition_flag                    true
% 11.62/1.93  --sup_passive_queue_type                priority_queues
% 11.62/1.93  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.62/1.93  --sup_passive_queues_freq               [8;1;4]
% 11.62/1.93  --demod_completeness_check              fast
% 11.62/1.93  --demod_use_ground                      true
% 11.62/1.93  --sup_to_prop_solver                    passive
% 11.62/1.93  --sup_prop_simpl_new                    true
% 11.62/1.93  --sup_prop_simpl_given                  true
% 11.62/1.93  --sup_fun_splitting                     true
% 11.62/1.93  --sup_smt_interval                      50000
% 11.62/1.93  
% 11.62/1.93  ------ Superposition Simplification Setup
% 11.62/1.93  
% 11.62/1.93  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.62/1.93  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.62/1.93  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.62/1.93  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.62/1.93  --sup_full_triv                         [TrivRules;PropSubs]
% 11.62/1.93  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.62/1.93  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.62/1.93  --sup_immed_triv                        [TrivRules]
% 11.62/1.93  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.62/1.93  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.62/1.93  --sup_immed_bw_main                     []
% 11.62/1.93  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.62/1.93  --sup_input_triv                        [Unflattening;TrivRules]
% 11.62/1.93  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.62/1.93  --sup_input_bw                          []
% 11.62/1.93  
% 11.62/1.93  ------ Combination Options
% 11.62/1.93  
% 11.62/1.93  --comb_res_mult                         3
% 11.62/1.93  --comb_sup_mult                         2
% 11.62/1.93  --comb_inst_mult                        10
% 11.62/1.93  
% 11.62/1.93  ------ Debug Options
% 11.62/1.93  
% 11.62/1.93  --dbg_backtrace                         false
% 11.62/1.93  --dbg_dump_prop_clauses                 false
% 11.62/1.93  --dbg_dump_prop_clauses_file            -
% 11.62/1.93  --dbg_out_stat                          false
% 11.62/1.93  ------ Parsing...
% 11.62/1.93  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.62/1.93  
% 11.62/1.93  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 11.62/1.93  
% 11.62/1.93  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.62/1.93  
% 11.62/1.93  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.62/1.93  ------ Proving...
% 11.62/1.93  ------ Problem Properties 
% 11.62/1.93  
% 11.62/1.93  
% 11.62/1.93  clauses                                 34
% 11.62/1.93  conjectures                             11
% 11.62/1.93  EPR                                     8
% 11.62/1.93  Horn                                    30
% 11.62/1.93  unary                                   17
% 11.62/1.93  binary                                  3
% 11.62/1.93  lits                                    122
% 11.62/1.93  lits eq                                 31
% 11.62/1.93  fd_pure                                 0
% 11.62/1.93  fd_pseudo                               0
% 11.62/1.93  fd_cond                                 4
% 11.62/1.93  fd_pseudo_cond                          1
% 11.62/1.93  AC symbols                              0
% 11.62/1.93  
% 11.62/1.93  ------ Schedule dynamic 5 is on 
% 11.62/1.93  
% 11.62/1.93  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.62/1.93  
% 11.62/1.93  
% 11.62/1.93  ------ 
% 11.62/1.93  Current options:
% 11.62/1.93  ------ 
% 11.62/1.93  
% 11.62/1.93  ------ Input Options
% 11.62/1.93  
% 11.62/1.93  --out_options                           all
% 11.62/1.93  --tptp_safe_out                         true
% 11.62/1.93  --problem_path                          ""
% 11.62/1.93  --include_path                          ""
% 11.62/1.93  --clausifier                            res/vclausify_rel
% 11.62/1.93  --clausifier_options                    ""
% 11.62/1.93  --stdin                                 false
% 11.62/1.93  --stats_out                             all
% 11.62/1.93  
% 11.62/1.93  ------ General Options
% 11.62/1.93  
% 11.62/1.93  --fof                                   false
% 11.62/1.93  --time_out_real                         305.
% 11.62/1.93  --time_out_virtual                      -1.
% 11.62/1.93  --symbol_type_check                     false
% 11.62/1.93  --clausify_out                          false
% 11.62/1.93  --sig_cnt_out                           false
% 11.62/1.93  --trig_cnt_out                          false
% 11.62/1.93  --trig_cnt_out_tolerance                1.
% 11.62/1.93  --trig_cnt_out_sk_spl                   false
% 11.62/1.93  --abstr_cl_out                          false
% 11.62/1.93  
% 11.62/1.93  ------ Global Options
% 11.62/1.93  
% 11.62/1.93  --schedule                              default
% 11.62/1.93  --add_important_lit                     false
% 11.62/1.93  --prop_solver_per_cl                    1000
% 11.62/1.93  --min_unsat_core                        false
% 11.62/1.93  --soft_assumptions                      false
% 11.62/1.93  --soft_lemma_size                       3
% 11.62/1.93  --prop_impl_unit_size                   0
% 11.62/1.93  --prop_impl_unit                        []
% 11.62/1.93  --share_sel_clauses                     true
% 11.62/1.93  --reset_solvers                         false
% 11.62/1.93  --bc_imp_inh                            [conj_cone]
% 11.62/1.93  --conj_cone_tolerance                   3.
% 11.62/1.93  --extra_neg_conj                        none
% 11.62/1.93  --large_theory_mode                     true
% 11.62/1.93  --prolific_symb_bound                   200
% 11.62/1.93  --lt_threshold                          2000
% 11.62/1.93  --clause_weak_htbl                      true
% 11.62/1.93  --gc_record_bc_elim                     false
% 11.62/1.93  
% 11.62/1.93  ------ Preprocessing Options
% 11.62/1.93  
% 11.62/1.93  --preprocessing_flag                    true
% 11.62/1.93  --time_out_prep_mult                    0.1
% 11.62/1.93  --splitting_mode                        input
% 11.62/1.93  --splitting_grd                         true
% 11.62/1.93  --splitting_cvd                         false
% 11.62/1.93  --splitting_cvd_svl                     false
% 11.62/1.93  --splitting_nvd                         32
% 11.62/1.93  --sub_typing                            true
% 11.62/1.93  --prep_gs_sim                           true
% 11.62/1.93  --prep_unflatten                        true
% 11.62/1.93  --prep_res_sim                          true
% 11.62/1.93  --prep_upred                            true
% 11.62/1.93  --prep_sem_filter                       exhaustive
% 11.62/1.93  --prep_sem_filter_out                   false
% 11.62/1.93  --pred_elim                             true
% 11.62/1.93  --res_sim_input                         true
% 11.62/1.93  --eq_ax_congr_red                       true
% 11.62/1.93  --pure_diseq_elim                       true
% 11.62/1.93  --brand_transform                       false
% 11.62/1.93  --non_eq_to_eq                          false
% 11.62/1.93  --prep_def_merge                        true
% 11.62/1.93  --prep_def_merge_prop_impl              false
% 11.62/1.93  --prep_def_merge_mbd                    true
% 11.62/1.93  --prep_def_merge_tr_red                 false
% 11.62/1.93  --prep_def_merge_tr_cl                  false
% 11.62/1.93  --smt_preprocessing                     true
% 11.62/1.93  --smt_ac_axioms                         fast
% 11.62/1.93  --preprocessed_out                      false
% 11.62/1.93  --preprocessed_stats                    false
% 11.62/1.93  
% 11.62/1.93  ------ Abstraction refinement Options
% 11.62/1.93  
% 11.62/1.93  --abstr_ref                             []
% 11.62/1.93  --abstr_ref_prep                        false
% 11.62/1.93  --abstr_ref_until_sat                   false
% 11.62/1.93  --abstr_ref_sig_restrict                funpre
% 11.62/1.93  --abstr_ref_af_restrict_to_split_sk     false
% 11.62/1.93  --abstr_ref_under                       []
% 11.62/1.93  
% 11.62/1.93  ------ SAT Options
% 11.62/1.93  
% 11.62/1.93  --sat_mode                              false
% 11.62/1.93  --sat_fm_restart_options                ""
% 11.62/1.93  --sat_gr_def                            false
% 11.62/1.93  --sat_epr_types                         true
% 11.62/1.93  --sat_non_cyclic_types                  false
% 11.62/1.93  --sat_finite_models                     false
% 11.62/1.93  --sat_fm_lemmas                         false
% 11.62/1.93  --sat_fm_prep                           false
% 11.62/1.93  --sat_fm_uc_incr                        true
% 11.62/1.93  --sat_out_model                         small
% 11.62/1.93  --sat_out_clauses                       false
% 11.62/1.93  
% 11.62/1.93  ------ QBF Options
% 11.62/1.93  
% 11.62/1.93  --qbf_mode                              false
% 11.62/1.93  --qbf_elim_univ                         false
% 11.62/1.93  --qbf_dom_inst                          none
% 11.62/1.93  --qbf_dom_pre_inst                      false
% 11.62/1.93  --qbf_sk_in                             false
% 11.62/1.93  --qbf_pred_elim                         true
% 11.62/1.93  --qbf_split                             512
% 11.62/1.93  
% 11.62/1.93  ------ BMC1 Options
% 11.62/1.93  
% 11.62/1.93  --bmc1_incremental                      false
% 11.62/1.93  --bmc1_axioms                           reachable_all
% 11.62/1.93  --bmc1_min_bound                        0
% 11.62/1.93  --bmc1_max_bound                        -1
% 11.62/1.93  --bmc1_max_bound_default                -1
% 11.62/1.93  --bmc1_symbol_reachability              true
% 11.62/1.93  --bmc1_property_lemmas                  false
% 11.62/1.93  --bmc1_k_induction                      false
% 11.62/1.93  --bmc1_non_equiv_states                 false
% 11.62/1.93  --bmc1_deadlock                         false
% 11.62/1.93  --bmc1_ucm                              false
% 11.62/1.93  --bmc1_add_unsat_core                   none
% 11.62/1.93  --bmc1_unsat_core_children              false
% 11.62/1.93  --bmc1_unsat_core_extrapolate_axioms    false
% 11.62/1.93  --bmc1_out_stat                         full
% 11.62/1.93  --bmc1_ground_init                      false
% 11.62/1.93  --bmc1_pre_inst_next_state              false
% 11.62/1.93  --bmc1_pre_inst_state                   false
% 11.62/1.93  --bmc1_pre_inst_reach_state             false
% 11.62/1.93  --bmc1_out_unsat_core                   false
% 11.62/1.93  --bmc1_aig_witness_out                  false
% 11.62/1.93  --bmc1_verbose                          false
% 11.62/1.93  --bmc1_dump_clauses_tptp                false
% 11.62/1.93  --bmc1_dump_unsat_core_tptp             false
% 11.62/1.93  --bmc1_dump_file                        -
% 11.62/1.93  --bmc1_ucm_expand_uc_limit              128
% 11.62/1.93  --bmc1_ucm_n_expand_iterations          6
% 11.62/1.93  --bmc1_ucm_extend_mode                  1
% 11.62/1.93  --bmc1_ucm_init_mode                    2
% 11.62/1.93  --bmc1_ucm_cone_mode                    none
% 11.62/1.93  --bmc1_ucm_reduced_relation_type        0
% 11.62/1.93  --bmc1_ucm_relax_model                  4
% 11.62/1.93  --bmc1_ucm_full_tr_after_sat            true
% 11.62/1.93  --bmc1_ucm_expand_neg_assumptions       false
% 11.62/1.93  --bmc1_ucm_layered_model                none
% 11.62/1.93  --bmc1_ucm_max_lemma_size               10
% 11.62/1.93  
% 11.62/1.93  ------ AIG Options
% 11.62/1.93  
% 11.62/1.93  --aig_mode                              false
% 11.62/1.93  
% 11.62/1.93  ------ Instantiation Options
% 11.62/1.93  
% 11.62/1.93  --instantiation_flag                    true
% 11.62/1.93  --inst_sos_flag                         true
% 11.62/1.93  --inst_sos_phase                        true
% 11.62/1.93  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.62/1.93  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.62/1.93  --inst_lit_sel_side                     none
% 11.62/1.93  --inst_solver_per_active                1400
% 11.62/1.93  --inst_solver_calls_frac                1.
% 11.62/1.93  --inst_passive_queue_type               priority_queues
% 11.62/1.93  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.62/1.93  --inst_passive_queues_freq              [25;2]
% 11.62/1.93  --inst_dismatching                      true
% 11.62/1.93  --inst_eager_unprocessed_to_passive     true
% 11.62/1.93  --inst_prop_sim_given                   true
% 11.62/1.93  --inst_prop_sim_new                     false
% 11.62/1.93  --inst_subs_new                         false
% 11.62/1.93  --inst_eq_res_simp                      false
% 11.62/1.93  --inst_subs_given                       false
% 11.62/1.93  --inst_orphan_elimination               true
% 11.62/1.93  --inst_learning_loop_flag               true
% 11.62/1.93  --inst_learning_start                   3000
% 11.62/1.93  --inst_learning_factor                  2
% 11.62/1.93  --inst_start_prop_sim_after_learn       3
% 11.62/1.93  --inst_sel_renew                        solver
% 11.62/1.93  --inst_lit_activity_flag                true
% 11.62/1.93  --inst_restr_to_given                   false
% 11.62/1.93  --inst_activity_threshold               500
% 11.62/1.93  --inst_out_proof                        true
% 11.62/1.93  
% 11.62/1.93  ------ Resolution Options
% 11.62/1.93  
% 11.62/1.93  --resolution_flag                       false
% 11.62/1.93  --res_lit_sel                           adaptive
% 11.62/1.93  --res_lit_sel_side                      none
% 11.62/1.93  --res_ordering                          kbo
% 11.62/1.93  --res_to_prop_solver                    active
% 11.62/1.93  --res_prop_simpl_new                    false
% 11.62/1.93  --res_prop_simpl_given                  true
% 11.62/1.93  --res_passive_queue_type                priority_queues
% 11.62/1.93  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.62/1.93  --res_passive_queues_freq               [15;5]
% 11.62/1.93  --res_forward_subs                      full
% 11.62/1.93  --res_backward_subs                     full
% 11.62/1.93  --res_forward_subs_resolution           true
% 11.62/1.93  --res_backward_subs_resolution          true
% 11.62/1.93  --res_orphan_elimination                true
% 11.62/1.93  --res_time_limit                        2.
% 11.62/1.93  --res_out_proof                         true
% 11.62/1.93  
% 11.62/1.93  ------ Superposition Options
% 11.62/1.93  
% 11.62/1.93  --superposition_flag                    true
% 11.62/1.93  --sup_passive_queue_type                priority_queues
% 11.62/1.93  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.62/1.93  --sup_passive_queues_freq               [8;1;4]
% 11.62/1.93  --demod_completeness_check              fast
% 11.62/1.93  --demod_use_ground                      true
% 11.62/1.93  --sup_to_prop_solver                    passive
% 11.62/1.93  --sup_prop_simpl_new                    true
% 11.62/1.93  --sup_prop_simpl_given                  true
% 11.62/1.93  --sup_fun_splitting                     true
% 11.62/1.93  --sup_smt_interval                      50000
% 11.62/1.93  
% 11.62/1.93  ------ Superposition Simplification Setup
% 11.62/1.93  
% 11.62/1.93  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.62/1.93  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.62/1.93  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.62/1.93  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.62/1.93  --sup_full_triv                         [TrivRules;PropSubs]
% 11.62/1.93  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.62/1.93  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.62/1.93  --sup_immed_triv                        [TrivRules]
% 11.62/1.93  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.62/1.93  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.62/1.93  --sup_immed_bw_main                     []
% 11.62/1.93  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.62/1.93  --sup_input_triv                        [Unflattening;TrivRules]
% 11.62/1.93  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.62/1.93  --sup_input_bw                          []
% 11.62/1.93  
% 11.62/1.93  ------ Combination Options
% 11.62/1.93  
% 11.62/1.93  --comb_res_mult                         3
% 11.62/1.93  --comb_sup_mult                         2
% 11.62/1.93  --comb_inst_mult                        10
% 11.62/1.93  
% 11.62/1.93  ------ Debug Options
% 11.62/1.93  
% 11.62/1.93  --dbg_backtrace                         false
% 11.62/1.93  --dbg_dump_prop_clauses                 false
% 11.62/1.93  --dbg_dump_prop_clauses_file            -
% 11.62/1.93  --dbg_out_stat                          false
% 11.62/1.93  
% 11.62/1.93  
% 11.62/1.93  
% 11.62/1.93  
% 11.62/1.93  ------ Proving...
% 11.62/1.93  
% 11.62/1.93  
% 11.62/1.93  % SZS status Theorem for theBenchmark.p
% 11.62/1.93  
% 11.62/1.93  % SZS output start CNFRefutation for theBenchmark.p
% 11.62/1.93  
% 11.62/1.93  fof(f9,axiom,(
% 11.62/1.93    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 11.62/1.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.62/1.93  
% 11.62/1.93  fof(f26,plain,(
% 11.62/1.93    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 11.62/1.93    inference(ennf_transformation,[],[f9])).
% 11.62/1.93  
% 11.62/1.93  fof(f27,plain,(
% 11.62/1.93    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.62/1.93    inference(flattening,[],[f26])).
% 11.62/1.93  
% 11.62/1.93  fof(f42,plain,(
% 11.62/1.93    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.62/1.93    inference(nnf_transformation,[],[f27])).
% 11.62/1.93  
% 11.62/1.93  fof(f57,plain,(
% 11.62/1.93    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.62/1.93    inference(cnf_transformation,[],[f42])).
% 11.62/1.93  
% 11.62/1.93  fof(f17,conjecture,(
% 11.62/1.93    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 11.62/1.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.62/1.93  
% 11.62/1.93  fof(f18,negated_conjecture,(
% 11.62/1.93    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 11.62/1.93    inference(negated_conjecture,[],[f17])).
% 11.62/1.93  
% 11.62/1.93  fof(f38,plain,(
% 11.62/1.93    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 11.62/1.93    inference(ennf_transformation,[],[f18])).
% 11.62/1.93  
% 11.62/1.93  fof(f39,plain,(
% 11.62/1.93    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 11.62/1.93    inference(flattening,[],[f38])).
% 11.62/1.93  
% 11.62/1.93  fof(f44,plain,(
% 11.62/1.93    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK4 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK4),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK4,X1,X0) & v1_funct_1(sK4))) )),
% 11.62/1.93    introduced(choice_axiom,[])).
% 11.62/1.93  
% 11.62/1.93  fof(f43,plain,(
% 11.62/1.93    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK3) != X3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & v2_funct_1(sK3) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,X3),k6_partfun1(sK1)) & k2_relset_1(sK1,sK2,sK3) = sK2 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(X3,sK2,sK1) & v1_funct_1(X3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 11.62/1.93    introduced(choice_axiom,[])).
% 11.62/1.93  
% 11.62/1.93  fof(f45,plain,(
% 11.62/1.93    (k2_funct_1(sK3) != sK4 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & v2_funct_1(sK3) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) & k2_relset_1(sK1,sK2,sK3) = sK2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 11.62/1.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f39,f44,f43])).
% 11.62/1.93  
% 11.62/1.93  fof(f78,plain,(
% 11.62/1.93    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1))),
% 11.62/1.93    inference(cnf_transformation,[],[f45])).
% 11.62/1.93  
% 11.62/1.93  fof(f10,axiom,(
% 11.62/1.93    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 11.62/1.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.62/1.93  
% 11.62/1.93  fof(f59,plain,(
% 11.62/1.93    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 11.62/1.93    inference(cnf_transformation,[],[f10])).
% 11.62/1.93  
% 11.62/1.93  fof(f13,axiom,(
% 11.62/1.93    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 11.62/1.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.62/1.93  
% 11.62/1.93  fof(f63,plain,(
% 11.62/1.93    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 11.62/1.93    inference(cnf_transformation,[],[f13])).
% 11.62/1.93  
% 11.62/1.93  fof(f88,plain,(
% 11.62/1.93    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 11.62/1.93    inference(definition_unfolding,[],[f59,f63])).
% 11.62/1.93  
% 11.62/1.93  fof(f71,plain,(
% 11.62/1.93    v1_funct_1(sK3)),
% 11.62/1.93    inference(cnf_transformation,[],[f45])).
% 11.62/1.93  
% 11.62/1.93  fof(f73,plain,(
% 11.62/1.93    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 11.62/1.93    inference(cnf_transformation,[],[f45])).
% 11.62/1.93  
% 11.62/1.93  fof(f74,plain,(
% 11.62/1.93    v1_funct_1(sK4)),
% 11.62/1.93    inference(cnf_transformation,[],[f45])).
% 11.62/1.93  
% 11.62/1.93  fof(f76,plain,(
% 11.62/1.93    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 11.62/1.93    inference(cnf_transformation,[],[f45])).
% 11.62/1.93  
% 11.62/1.93  fof(f11,axiom,(
% 11.62/1.93    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 11.62/1.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.62/1.93  
% 11.62/1.93  fof(f28,plain,(
% 11.62/1.93    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 11.62/1.93    inference(ennf_transformation,[],[f11])).
% 11.62/1.93  
% 11.62/1.93  fof(f29,plain,(
% 11.62/1.93    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 11.62/1.93    inference(flattening,[],[f28])).
% 11.62/1.93  
% 11.62/1.93  fof(f61,plain,(
% 11.62/1.93    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 11.62/1.93    inference(cnf_transformation,[],[f29])).
% 11.62/1.93  
% 11.62/1.93  fof(f14,axiom,(
% 11.62/1.93    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 11.62/1.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.62/1.93  
% 11.62/1.93  fof(f32,plain,(
% 11.62/1.93    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 11.62/1.93    inference(ennf_transformation,[],[f14])).
% 11.62/1.93  
% 11.62/1.93  fof(f33,plain,(
% 11.62/1.93    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 11.62/1.93    inference(flattening,[],[f32])).
% 11.62/1.93  
% 11.62/1.93  fof(f64,plain,(
% 11.62/1.93    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 11.62/1.93    inference(cnf_transformation,[],[f33])).
% 11.62/1.93  
% 11.62/1.93  fof(f72,plain,(
% 11.62/1.93    v1_funct_2(sK3,sK1,sK2)),
% 11.62/1.93    inference(cnf_transformation,[],[f45])).
% 11.62/1.93  
% 11.62/1.93  fof(f75,plain,(
% 11.62/1.93    v1_funct_2(sK4,sK2,sK1)),
% 11.62/1.93    inference(cnf_transformation,[],[f45])).
% 11.62/1.93  
% 11.62/1.93  fof(f16,axiom,(
% 11.62/1.93    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 11.62/1.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.62/1.93  
% 11.62/1.93  fof(f36,plain,(
% 11.62/1.93    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 11.62/1.93    inference(ennf_transformation,[],[f16])).
% 11.62/1.93  
% 11.62/1.93  fof(f37,plain,(
% 11.62/1.93    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 11.62/1.93    inference(flattening,[],[f36])).
% 11.62/1.93  
% 11.62/1.93  fof(f69,plain,(
% 11.62/1.93    ( ! [X2,X0,X1] : (k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 11.62/1.93    inference(cnf_transformation,[],[f37])).
% 11.62/1.93  
% 11.62/1.93  fof(f80,plain,(
% 11.62/1.93    k1_xboole_0 != sK1),
% 11.62/1.93    inference(cnf_transformation,[],[f45])).
% 11.62/1.93  
% 11.62/1.93  fof(f4,axiom,(
% 11.62/1.93    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 11.62/1.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.62/1.93  
% 11.62/1.93  fof(f51,plain,(
% 11.62/1.93    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 11.62/1.93    inference(cnf_transformation,[],[f4])).
% 11.62/1.93  
% 11.62/1.93  fof(f85,plain,(
% 11.62/1.93    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 11.62/1.93    inference(definition_unfolding,[],[f51,f63])).
% 11.62/1.93  
% 11.62/1.93  fof(f77,plain,(
% 11.62/1.93    k2_relset_1(sK1,sK2,sK3) = sK2),
% 11.62/1.93    inference(cnf_transformation,[],[f45])).
% 11.62/1.93  
% 11.62/1.93  fof(f15,axiom,(
% 11.62/1.93    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 11.62/1.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.62/1.93  
% 11.62/1.93  fof(f34,plain,(
% 11.62/1.93    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 11.62/1.93    inference(ennf_transformation,[],[f15])).
% 11.62/1.93  
% 11.62/1.93  fof(f35,plain,(
% 11.62/1.93    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 11.62/1.93    inference(flattening,[],[f34])).
% 11.62/1.93  
% 11.62/1.93  fof(f67,plain,(
% 11.62/1.93    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X4) | k1_xboole_0 = X2 | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 11.62/1.93    inference(cnf_transformation,[],[f35])).
% 11.62/1.93  
% 11.62/1.93  fof(f6,axiom,(
% 11.62/1.93    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 11.62/1.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.62/1.93  
% 11.62/1.93  fof(f22,plain,(
% 11.62/1.93    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.62/1.93    inference(ennf_transformation,[],[f6])).
% 11.62/1.93  
% 11.62/1.93  fof(f23,plain,(
% 11.62/1.93    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.62/1.93    inference(flattening,[],[f22])).
% 11.62/1.93  
% 11.62/1.93  fof(f54,plain,(
% 11.62/1.93    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.62/1.93    inference(cnf_transformation,[],[f23])).
% 11.62/1.93  
% 11.62/1.93  fof(f87,plain,(
% 11.62/1.93    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.62/1.93    inference(definition_unfolding,[],[f54,f63])).
% 11.62/1.93  
% 11.62/1.93  fof(f8,axiom,(
% 11.62/1.93    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 11.62/1.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.62/1.93  
% 11.62/1.93  fof(f25,plain,(
% 11.62/1.93    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.62/1.93    inference(ennf_transformation,[],[f8])).
% 11.62/1.93  
% 11.62/1.93  fof(f56,plain,(
% 11.62/1.93    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.62/1.93    inference(cnf_transformation,[],[f25])).
% 11.62/1.93  
% 11.62/1.93  fof(f79,plain,(
% 11.62/1.93    v2_funct_1(sK3)),
% 11.62/1.93    inference(cnf_transformation,[],[f45])).
% 11.62/1.93  
% 11.62/1.93  fof(f7,axiom,(
% 11.62/1.93    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 11.62/1.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.62/1.93  
% 11.62/1.93  fof(f24,plain,(
% 11.62/1.93    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.62/1.93    inference(ennf_transformation,[],[f7])).
% 11.62/1.93  
% 11.62/1.93  fof(f55,plain,(
% 11.62/1.93    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.62/1.93    inference(cnf_transformation,[],[f24])).
% 11.62/1.93  
% 11.62/1.93  fof(f12,axiom,(
% 11.62/1.93    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 11.62/1.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.62/1.93  
% 11.62/1.93  fof(f30,plain,(
% 11.62/1.93    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 11.62/1.93    inference(ennf_transformation,[],[f12])).
% 11.62/1.93  
% 11.62/1.93  fof(f31,plain,(
% 11.62/1.93    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 11.62/1.93    inference(flattening,[],[f30])).
% 11.62/1.93  
% 11.62/1.93  fof(f62,plain,(
% 11.62/1.93    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 11.62/1.93    inference(cnf_transformation,[],[f31])).
% 11.62/1.93  
% 11.62/1.93  fof(f5,axiom,(
% 11.62/1.93    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 11.62/1.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.62/1.93  
% 11.62/1.93  fof(f20,plain,(
% 11.62/1.93    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.62/1.93    inference(ennf_transformation,[],[f5])).
% 11.62/1.93  
% 11.62/1.93  fof(f21,plain,(
% 11.62/1.93    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.62/1.93    inference(flattening,[],[f20])).
% 11.62/1.93  
% 11.62/1.93  fof(f53,plain,(
% 11.62/1.93    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.62/1.93    inference(cnf_transformation,[],[f21])).
% 11.62/1.93  
% 11.62/1.93  fof(f3,axiom,(
% 11.62/1.93    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 11.62/1.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.62/1.93  
% 11.62/1.93  fof(f49,plain,(
% 11.62/1.93    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 11.62/1.93    inference(cnf_transformation,[],[f3])).
% 11.62/1.93  
% 11.62/1.93  fof(f83,plain,(
% 11.62/1.93    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 11.62/1.93    inference(definition_unfolding,[],[f49,f63])).
% 11.62/1.93  
% 11.62/1.93  fof(f81,plain,(
% 11.62/1.93    k1_xboole_0 != sK2),
% 11.62/1.93    inference(cnf_transformation,[],[f45])).
% 11.62/1.93  
% 11.62/1.93  fof(f52,plain,(
% 11.62/1.93    ( ! [X0] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.62/1.93    inference(cnf_transformation,[],[f21])).
% 11.62/1.93  
% 11.62/1.93  fof(f48,plain,(
% 11.62/1.93    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 11.62/1.93    inference(cnf_transformation,[],[f3])).
% 11.62/1.93  
% 11.62/1.93  fof(f84,plain,(
% 11.62/1.93    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 11.62/1.93    inference(definition_unfolding,[],[f48,f63])).
% 11.62/1.93  
% 11.62/1.93  fof(f82,plain,(
% 11.62/1.93    k2_funct_1(sK3) != sK4),
% 11.62/1.93    inference(cnf_transformation,[],[f45])).
% 11.62/1.93  
% 11.62/1.93  cnf(c_12,plain,
% 11.62/1.93      ( ~ r2_relset_1(X0,X1,X2,X3)
% 11.62/1.93      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.62/1.93      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.62/1.93      | X3 = X2 ),
% 11.62/1.93      inference(cnf_transformation,[],[f57]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_28,negated_conjecture,
% 11.62/1.93      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) ),
% 11.62/1.93      inference(cnf_transformation,[],[f78]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_382,plain,
% 11.62/1.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.62/1.93      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.62/1.93      | X3 = X0
% 11.62/1.93      | k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) != X0
% 11.62/1.93      | k6_partfun1(sK1) != X3
% 11.62/1.93      | sK1 != X2
% 11.62/1.93      | sK1 != X1 ),
% 11.62/1.93      inference(resolution_lifted,[status(thm)],[c_12,c_28]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_383,plain,
% 11.62/1.93      ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 11.62/1.93      | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 11.62/1.93      | k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
% 11.62/1.93      inference(unflattening,[status(thm)],[c_382]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_13,plain,
% 11.62/1.93      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 11.62/1.93      inference(cnf_transformation,[],[f88]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_391,plain,
% 11.62/1.93      ( ~ m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 11.62/1.93      | k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
% 11.62/1.93      inference(forward_subsumption_resolution,
% 11.62/1.93                [status(thm)],
% 11.62/1.93                [c_383,c_13]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_1095,plain,
% 11.62/1.93      ( k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 11.62/1.93      | m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
% 11.62/1.93      inference(predicate_to_equality,[status(thm)],[c_391]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_35,negated_conjecture,
% 11.62/1.93      ( v1_funct_1(sK3) ),
% 11.62/1.93      inference(cnf_transformation,[],[f71]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_33,negated_conjecture,
% 11.62/1.93      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 11.62/1.93      inference(cnf_transformation,[],[f73]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_32,negated_conjecture,
% 11.62/1.93      ( v1_funct_1(sK4) ),
% 11.62/1.93      inference(cnf_transformation,[],[f74]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_30,negated_conjecture,
% 11.62/1.93      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 11.62/1.93      inference(cnf_transformation,[],[f76]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_14,plain,
% 11.62/1.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.62/1.93      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 11.62/1.93      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 11.62/1.93      | ~ v1_funct_1(X0)
% 11.62/1.93      | ~ v1_funct_1(X3) ),
% 11.62/1.93      inference(cnf_transformation,[],[f61]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_1202,plain,
% 11.62/1.93      ( m1_subset_1(k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 11.62/1.93      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 11.62/1.93      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 11.62/1.93      | ~ v1_funct_1(sK4)
% 11.62/1.93      | ~ v1_funct_1(sK3) ),
% 11.62/1.93      inference(instantiation,[status(thm)],[c_14]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_1787,plain,
% 11.62/1.93      ( k6_partfun1(sK1) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
% 11.62/1.93      inference(global_propositional_subsumption,
% 11.62/1.93                [status(thm)],
% 11.62/1.93                [c_1095,c_35,c_33,c_32,c_30,c_391,c_1202]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_17,plain,
% 11.62/1.93      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 11.62/1.93      | ~ v1_funct_2(X2,X0,X1)
% 11.62/1.93      | ~ v1_funct_2(X3,X1,X0)
% 11.62/1.93      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 11.62/1.93      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.62/1.93      | ~ v1_funct_1(X2)
% 11.62/1.93      | ~ v1_funct_1(X3)
% 11.62/1.93      | k2_relset_1(X1,X0,X3) = X0 ),
% 11.62/1.93      inference(cnf_transformation,[],[f64]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_395,plain,
% 11.62/1.93      ( ~ v1_funct_2(X0,X1,X2)
% 11.62/1.93      | ~ v1_funct_2(X3,X2,X1)
% 11.62/1.93      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 11.62/1.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.62/1.93      | ~ v1_funct_1(X0)
% 11.62/1.93      | ~ v1_funct_1(X3)
% 11.62/1.93      | k1_partfun1(X2,X1,X1,X2,X3,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 11.62/1.93      | k2_relset_1(X1,X2,X0) = X2
% 11.62/1.93      | k6_partfun1(X2) != k6_partfun1(sK1)
% 11.62/1.93      | sK1 != X2 ),
% 11.62/1.93      inference(resolution_lifted,[status(thm)],[c_17,c_28]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_396,plain,
% 11.62/1.93      ( ~ v1_funct_2(X0,X1,sK1)
% 11.62/1.93      | ~ v1_funct_2(X2,sK1,X1)
% 11.62/1.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 11.62/1.93      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
% 11.62/1.93      | ~ v1_funct_1(X0)
% 11.62/1.93      | ~ v1_funct_1(X2)
% 11.62/1.93      | k1_partfun1(sK1,X1,X1,sK1,X2,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 11.62/1.93      | k2_relset_1(X1,sK1,X0) = sK1
% 11.62/1.93      | k6_partfun1(sK1) != k6_partfun1(sK1) ),
% 11.62/1.93      inference(unflattening,[status(thm)],[c_395]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_477,plain,
% 11.62/1.93      ( ~ v1_funct_2(X0,X1,sK1)
% 11.62/1.93      | ~ v1_funct_2(X2,sK1,X1)
% 11.62/1.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 11.62/1.93      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
% 11.62/1.93      | ~ v1_funct_1(X0)
% 11.62/1.93      | ~ v1_funct_1(X2)
% 11.62/1.93      | k1_partfun1(sK1,X1,X1,sK1,X2,X0) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 11.62/1.93      | k2_relset_1(X1,sK1,X0) = sK1 ),
% 11.62/1.93      inference(equality_resolution_simp,[status(thm)],[c_396]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_1094,plain,
% 11.62/1.93      ( k1_partfun1(sK1,X0,X0,sK1,X1,X2) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 11.62/1.93      | k2_relset_1(X0,sK1,X2) = sK1
% 11.62/1.93      | v1_funct_2(X2,X0,sK1) != iProver_top
% 11.62/1.93      | v1_funct_2(X1,sK1,X0) != iProver_top
% 11.62/1.93      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 11.62/1.93      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 11.62/1.93      | v1_funct_1(X2) != iProver_top
% 11.62/1.93      | v1_funct_1(X1) != iProver_top ),
% 11.62/1.93      inference(predicate_to_equality,[status(thm)],[c_477]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_1790,plain,
% 11.62/1.93      ( k1_partfun1(sK1,X0,X0,sK1,X1,X2) != k6_partfun1(sK1)
% 11.62/1.93      | k2_relset_1(X0,sK1,X2) = sK1
% 11.62/1.93      | v1_funct_2(X2,X0,sK1) != iProver_top
% 11.62/1.93      | v1_funct_2(X1,sK1,X0) != iProver_top
% 11.62/1.93      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 11.62/1.93      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 11.62/1.93      | v1_funct_1(X2) != iProver_top
% 11.62/1.93      | v1_funct_1(X1) != iProver_top ),
% 11.62/1.93      inference(light_normalisation,[status(thm)],[c_1094,c_1787]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_1794,plain,
% 11.62/1.93      ( k2_relset_1(sK2,sK1,sK4) = sK1
% 11.62/1.93      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 11.62/1.93      | v1_funct_2(sK3,sK1,sK2) != iProver_top
% 11.62/1.93      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 11.62/1.93      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 11.62/1.93      | v1_funct_1(sK4) != iProver_top
% 11.62/1.93      | v1_funct_1(sK3) != iProver_top ),
% 11.62/1.93      inference(superposition,[status(thm)],[c_1787,c_1790]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_34,negated_conjecture,
% 11.62/1.93      ( v1_funct_2(sK3,sK1,sK2) ),
% 11.62/1.93      inference(cnf_transformation,[],[f72]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_31,negated_conjecture,
% 11.62/1.93      ( v1_funct_2(sK4,sK2,sK1) ),
% 11.62/1.93      inference(cnf_transformation,[],[f75]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_1210,plain,
% 11.62/1.93      ( ~ v1_funct_2(X0,sK1,X1)
% 11.62/1.93      | ~ v1_funct_2(sK4,X1,sK1)
% 11.62/1.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
% 11.62/1.93      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 11.62/1.93      | ~ v1_funct_1(X0)
% 11.62/1.93      | ~ v1_funct_1(sK4)
% 11.62/1.93      | k1_partfun1(sK1,X1,X1,sK1,X0,sK4) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 11.62/1.93      | k2_relset_1(X1,sK1,sK4) = sK1 ),
% 11.62/1.93      inference(instantiation,[status(thm)],[c_477]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_1323,plain,
% 11.62/1.93      ( ~ v1_funct_2(sK4,X0,sK1)
% 11.62/1.93      | ~ v1_funct_2(sK3,sK1,X0)
% 11.62/1.93      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
% 11.62/1.93      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
% 11.62/1.93      | ~ v1_funct_1(sK4)
% 11.62/1.93      | ~ v1_funct_1(sK3)
% 11.62/1.93      | k1_partfun1(sK1,X0,X0,sK1,sK3,sK4) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 11.62/1.93      | k2_relset_1(X0,sK1,sK4) = sK1 ),
% 11.62/1.93      inference(instantiation,[status(thm)],[c_1210]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_1526,plain,
% 11.62/1.93      ( ~ v1_funct_2(sK4,sK2,sK1)
% 11.62/1.93      | ~ v1_funct_2(sK3,sK1,sK2)
% 11.62/1.93      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 11.62/1.93      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 11.62/1.93      | ~ v1_funct_1(sK4)
% 11.62/1.93      | ~ v1_funct_1(sK3)
% 11.62/1.93      | k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) != k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4)
% 11.62/1.93      | k2_relset_1(sK2,sK1,sK4) = sK1 ),
% 11.62/1.93      inference(instantiation,[status(thm)],[c_1323]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_636,plain,( X0 = X0 ),theory(equality) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_1672,plain,
% 11.62/1.93      ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) ),
% 11.62/1.93      inference(instantiation,[status(thm)],[c_636]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_1861,plain,
% 11.62/1.93      ( k2_relset_1(sK2,sK1,sK4) = sK1 ),
% 11.62/1.93      inference(global_propositional_subsumption,
% 11.62/1.93                [status(thm)],
% 11.62/1.93                [c_1794,c_35,c_34,c_33,c_32,c_31,c_30,c_1526,c_1672]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_23,plain,
% 11.62/1.93      ( ~ v1_funct_2(X0,X1,X2)
% 11.62/1.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.62/1.93      | ~ v1_funct_1(X0)
% 11.62/1.93      | ~ v2_funct_1(X0)
% 11.62/1.93      | k2_relset_1(X1,X2,X0) != X2
% 11.62/1.93      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 11.62/1.93      | k1_xboole_0 = X2 ),
% 11.62/1.93      inference(cnf_transformation,[],[f69]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_1104,plain,
% 11.62/1.93      ( k2_relset_1(X0,X1,X2) != X1
% 11.62/1.93      | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
% 11.62/1.93      | k1_xboole_0 = X1
% 11.62/1.93      | v1_funct_2(X2,X0,X1) != iProver_top
% 11.62/1.93      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.62/1.93      | v1_funct_1(X2) != iProver_top
% 11.62/1.93      | v2_funct_1(X2) != iProver_top ),
% 11.62/1.93      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_2651,plain,
% 11.62/1.93      ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(sK2)
% 11.62/1.93      | sK1 = k1_xboole_0
% 11.62/1.93      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 11.62/1.93      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 11.62/1.93      | v1_funct_1(sK4) != iProver_top
% 11.62/1.93      | v2_funct_1(sK4) != iProver_top ),
% 11.62/1.93      inference(superposition,[status(thm)],[c_1861,c_1104]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_39,plain,
% 11.62/1.93      ( v1_funct_1(sK4) = iProver_top ),
% 11.62/1.93      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_40,plain,
% 11.62/1.93      ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
% 11.62/1.93      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_41,plain,
% 11.62/1.93      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 11.62/1.93      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_26,negated_conjecture,
% 11.62/1.93      ( k1_xboole_0 != sK1 ),
% 11.62/1.93      inference(cnf_transformation,[],[f80]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_667,plain,
% 11.62/1.93      ( k1_xboole_0 = k1_xboole_0 ),
% 11.62/1.93      inference(instantiation,[status(thm)],[c_636]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_637,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_1200,plain,
% 11.62/1.93      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 11.62/1.93      inference(instantiation,[status(thm)],[c_637]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_1201,plain,
% 11.62/1.93      ( sK1 != k1_xboole_0
% 11.62/1.93      | k1_xboole_0 = sK1
% 11.62/1.93      | k1_xboole_0 != k1_xboole_0 ),
% 11.62/1.93      inference(instantiation,[status(thm)],[c_1200]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_4,plain,
% 11.62/1.93      ( v2_funct_1(k6_partfun1(X0)) ),
% 11.62/1.93      inference(cnf_transformation,[],[f85]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_4825,plain,
% 11.62/1.93      ( v2_funct_1(k6_partfun1(sK1)) ),
% 11.62/1.93      inference(instantiation,[status(thm)],[c_4]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_4826,plain,
% 11.62/1.93      ( v2_funct_1(k6_partfun1(sK1)) = iProver_top ),
% 11.62/1.93      inference(predicate_to_equality,[status(thm)],[c_4825]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_29,negated_conjecture,
% 11.62/1.93      ( k2_relset_1(sK1,sK2,sK3) = sK2 ),
% 11.62/1.93      inference(cnf_transformation,[],[f77]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_19,plain,
% 11.62/1.93      ( ~ v1_funct_2(X0,X1,X2)
% 11.62/1.93      | ~ v1_funct_2(X3,X4,X1)
% 11.62/1.93      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 11.62/1.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.62/1.93      | ~ v1_funct_1(X0)
% 11.62/1.93      | ~ v1_funct_1(X3)
% 11.62/1.93      | v2_funct_1(X0)
% 11.62/1.93      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 11.62/1.93      | k2_relset_1(X4,X1,X3) != X1
% 11.62/1.93      | k1_xboole_0 = X2 ),
% 11.62/1.93      inference(cnf_transformation,[],[f67]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_1108,plain,
% 11.62/1.93      ( k2_relset_1(X0,X1,X2) != X1
% 11.62/1.93      | k1_xboole_0 = X3
% 11.62/1.93      | v1_funct_2(X4,X1,X3) != iProver_top
% 11.62/1.93      | v1_funct_2(X2,X0,X1) != iProver_top
% 11.62/1.93      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
% 11.62/1.93      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.62/1.93      | v1_funct_1(X4) != iProver_top
% 11.62/1.93      | v1_funct_1(X2) != iProver_top
% 11.62/1.93      | v2_funct_1(X4) = iProver_top
% 11.62/1.93      | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top ),
% 11.62/1.93      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_4971,plain,
% 11.62/1.93      ( k1_xboole_0 = X0
% 11.62/1.93      | v1_funct_2(X1,sK2,X0) != iProver_top
% 11.62/1.93      | v1_funct_2(sK3,sK1,sK2) != iProver_top
% 11.62/1.93      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
% 11.62/1.93      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 11.62/1.93      | v1_funct_1(X1) != iProver_top
% 11.62/1.93      | v1_funct_1(sK3) != iProver_top
% 11.62/1.93      | v2_funct_1(X1) = iProver_top
% 11.62/1.93      | v2_funct_1(k1_partfun1(sK1,sK2,sK2,X0,sK3,X1)) != iProver_top ),
% 11.62/1.93      inference(superposition,[status(thm)],[c_29,c_1108]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_36,plain,
% 11.62/1.93      ( v1_funct_1(sK3) = iProver_top ),
% 11.62/1.93      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_37,plain,
% 11.62/1.93      ( v1_funct_2(sK3,sK1,sK2) = iProver_top ),
% 11.62/1.93      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_38,plain,
% 11.62/1.93      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 11.62/1.93      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_4978,plain,
% 11.62/1.93      ( v1_funct_1(X1) != iProver_top
% 11.62/1.93      | v1_funct_2(X1,sK2,X0) != iProver_top
% 11.62/1.93      | k1_xboole_0 = X0
% 11.62/1.93      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
% 11.62/1.93      | v2_funct_1(X1) = iProver_top
% 11.62/1.93      | v2_funct_1(k1_partfun1(sK1,sK2,sK2,X0,sK3,X1)) != iProver_top ),
% 11.62/1.93      inference(global_propositional_subsumption,
% 11.62/1.93                [status(thm)],
% 11.62/1.93                [c_4971,c_36,c_37,c_38]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_4979,plain,
% 11.62/1.93      ( k1_xboole_0 = X0
% 11.62/1.93      | v1_funct_2(X1,sK2,X0) != iProver_top
% 11.62/1.93      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
% 11.62/1.93      | v1_funct_1(X1) != iProver_top
% 11.62/1.93      | v2_funct_1(X1) = iProver_top
% 11.62/1.93      | v2_funct_1(k1_partfun1(sK1,sK2,sK2,X0,sK3,X1)) != iProver_top ),
% 11.62/1.93      inference(renaming,[status(thm)],[c_4978]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_4982,plain,
% 11.62/1.93      ( sK1 = k1_xboole_0
% 11.62/1.93      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 11.62/1.93      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 11.62/1.93      | v1_funct_1(sK4) != iProver_top
% 11.62/1.93      | v2_funct_1(k6_partfun1(sK1)) != iProver_top
% 11.62/1.93      | v2_funct_1(sK4) = iProver_top ),
% 11.62/1.93      inference(superposition,[status(thm)],[c_1787,c_4979]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_5280,plain,
% 11.62/1.93      ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_partfun1(sK2) ),
% 11.62/1.93      inference(global_propositional_subsumption,
% 11.62/1.93                [status(thm)],
% 11.62/1.93                [c_2651,c_39,c_40,c_41,c_26,c_667,c_1201,c_4826,c_4982]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_8,plain,
% 11.62/1.93      ( ~ v1_funct_1(X0)
% 11.62/1.93      | ~ v1_funct_1(X1)
% 11.62/1.93      | ~ v1_relat_1(X0)
% 11.62/1.93      | ~ v1_relat_1(X1)
% 11.62/1.93      | ~ v2_funct_1(X0)
% 11.62/1.93      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
% 11.62/1.93      | k2_funct_1(X0) = X1
% 11.62/1.93      | k1_relat_1(X0) != k2_relat_1(X1) ),
% 11.62/1.93      inference(cnf_transformation,[],[f87]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_1116,plain,
% 11.62/1.93      ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 11.62/1.93      | k2_funct_1(X1) = X0
% 11.62/1.93      | k1_relat_1(X1) != k2_relat_1(X0)
% 11.62/1.93      | v1_funct_1(X1) != iProver_top
% 11.62/1.93      | v1_funct_1(X0) != iProver_top
% 11.62/1.93      | v1_relat_1(X1) != iProver_top
% 11.62/1.93      | v1_relat_1(X0) != iProver_top
% 11.62/1.93      | v2_funct_1(X1) != iProver_top ),
% 11.62/1.93      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_5286,plain,
% 11.62/1.93      ( k2_funct_1(k2_funct_1(sK4)) = sK4
% 11.62/1.93      | k1_relat_1(k2_funct_1(sK4)) != k2_relat_1(sK4)
% 11.62/1.93      | k6_partfun1(k2_relat_1(k2_funct_1(sK4))) != k6_partfun1(sK2)
% 11.62/1.93      | v1_funct_1(k2_funct_1(sK4)) != iProver_top
% 11.62/1.93      | v1_funct_1(sK4) != iProver_top
% 11.62/1.93      | v1_relat_1(k2_funct_1(sK4)) != iProver_top
% 11.62/1.93      | v1_relat_1(sK4) != iProver_top
% 11.62/1.93      | v2_funct_1(k2_funct_1(sK4)) != iProver_top ),
% 11.62/1.93      inference(superposition,[status(thm)],[c_5280,c_1116]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_1102,plain,
% 11.62/1.93      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 11.62/1.93      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_10,plain,
% 11.62/1.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.62/1.93      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 11.62/1.93      inference(cnf_transformation,[],[f56]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_1114,plain,
% 11.62/1.93      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 11.62/1.93      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 11.62/1.93      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_2004,plain,
% 11.62/1.93      ( k2_relset_1(sK2,sK1,sK4) = k2_relat_1(sK4) ),
% 11.62/1.93      inference(superposition,[status(thm)],[c_1102,c_1114]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_2007,plain,
% 11.62/1.93      ( k2_relat_1(sK4) = sK1 ),
% 11.62/1.93      inference(light_normalisation,[status(thm)],[c_2004,c_1861]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_5287,plain,
% 11.62/1.93      ( k2_funct_1(k2_funct_1(sK4)) = sK4
% 11.62/1.93      | k1_relat_1(k2_funct_1(sK4)) != sK1
% 11.62/1.93      | k6_partfun1(k2_relat_1(k2_funct_1(sK4))) != k6_partfun1(sK2)
% 11.62/1.93      | v1_funct_1(k2_funct_1(sK4)) != iProver_top
% 11.62/1.93      | v1_funct_1(sK4) != iProver_top
% 11.62/1.93      | v1_relat_1(k2_funct_1(sK4)) != iProver_top
% 11.62/1.93      | v1_relat_1(sK4) != iProver_top
% 11.62/1.93      | v2_funct_1(k2_funct_1(sK4)) != iProver_top ),
% 11.62/1.93      inference(light_normalisation,[status(thm)],[c_5286,c_2007]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_27,negated_conjecture,
% 11.62/1.93      ( v2_funct_1(sK3) ),
% 11.62/1.93      inference(cnf_transformation,[],[f79]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_9,plain,
% 11.62/1.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.62/1.93      | v1_relat_1(X0) ),
% 11.62/1.93      inference(cnf_transformation,[],[f55]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_1242,plain,
% 11.62/1.93      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.62/1.93      | v1_relat_1(sK4) ),
% 11.62/1.93      inference(instantiation,[status(thm)],[c_9]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_1601,plain,
% 11.62/1.93      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 11.62/1.93      | v1_relat_1(sK4) ),
% 11.62/1.93      inference(instantiation,[status(thm)],[c_1242]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_1713,plain,
% 11.62/1.93      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 11.62/1.93      | v1_relat_1(sK3) ),
% 11.62/1.93      inference(instantiation,[status(thm)],[c_9]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_1099,plain,
% 11.62/1.93      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 11.62/1.93      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_16,plain,
% 11.62/1.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.62/1.93      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 11.62/1.93      | ~ v1_funct_1(X0)
% 11.62/1.93      | ~ v1_funct_1(X3)
% 11.62/1.93      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 11.62/1.93      inference(cnf_transformation,[],[f62]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_1110,plain,
% 11.62/1.93      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 11.62/1.93      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 11.62/1.93      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.62/1.93      | v1_funct_1(X5) != iProver_top
% 11.62/1.93      | v1_funct_1(X4) != iProver_top ),
% 11.62/1.93      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_2754,plain,
% 11.62/1.93      ( k1_partfun1(X0,X1,sK2,sK1,X2,sK4) = k5_relat_1(X2,sK4)
% 11.62/1.93      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.62/1.93      | v1_funct_1(X2) != iProver_top
% 11.62/1.93      | v1_funct_1(sK4) != iProver_top ),
% 11.62/1.93      inference(superposition,[status(thm)],[c_1102,c_1110]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_2766,plain,
% 11.62/1.93      ( v1_funct_1(X2) != iProver_top
% 11.62/1.93      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.62/1.93      | k1_partfun1(X0,X1,sK2,sK1,X2,sK4) = k5_relat_1(X2,sK4) ),
% 11.62/1.93      inference(global_propositional_subsumption,
% 11.62/1.93                [status(thm)],
% 11.62/1.93                [c_2754,c_39]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_2767,plain,
% 11.62/1.93      ( k1_partfun1(X0,X1,sK2,sK1,X2,sK4) = k5_relat_1(X2,sK4)
% 11.62/1.93      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.62/1.93      | v1_funct_1(X2) != iProver_top ),
% 11.62/1.93      inference(renaming,[status(thm)],[c_2766]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_2774,plain,
% 11.62/1.93      ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k5_relat_1(sK3,sK4)
% 11.62/1.93      | v1_funct_1(sK3) != iProver_top ),
% 11.62/1.93      inference(superposition,[status(thm)],[c_1099,c_2767]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_2775,plain,
% 11.62/1.93      ( k5_relat_1(sK3,sK4) = k6_partfun1(sK1)
% 11.62/1.93      | v1_funct_1(sK3) != iProver_top ),
% 11.62/1.93      inference(light_normalisation,[status(thm)],[c_2774,c_1787]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_3494,plain,
% 11.62/1.93      ( k5_relat_1(sK3,sK4) = k6_partfun1(sK1) ),
% 11.62/1.93      inference(global_propositional_subsumption,
% 11.62/1.93                [status(thm)],
% 11.62/1.93                [c_2775,c_36]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_4002,plain,
% 11.62/1.93      ( k2_funct_1(sK4) = sK3
% 11.62/1.93      | k1_relat_1(sK4) != k2_relat_1(sK3)
% 11.62/1.93      | k6_partfun1(k2_relat_1(sK4)) != k6_partfun1(sK1)
% 11.62/1.93      | v1_funct_1(sK4) != iProver_top
% 11.62/1.93      | v1_funct_1(sK3) != iProver_top
% 11.62/1.93      | v1_relat_1(sK4) != iProver_top
% 11.62/1.93      | v1_relat_1(sK3) != iProver_top
% 11.62/1.93      | v2_funct_1(sK4) != iProver_top ),
% 11.62/1.93      inference(superposition,[status(thm)],[c_3494,c_1116]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_2005,plain,
% 11.62/1.93      ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
% 11.62/1.93      inference(superposition,[status(thm)],[c_1099,c_1114]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_2006,plain,
% 11.62/1.93      ( k2_relat_1(sK3) = sK2 ),
% 11.62/1.93      inference(light_normalisation,[status(thm)],[c_2005,c_29]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_4003,plain,
% 11.62/1.93      ( k2_funct_1(sK4) = sK3
% 11.62/1.93      | k1_relat_1(sK4) != sK2
% 11.62/1.93      | k6_partfun1(sK1) != k6_partfun1(sK1)
% 11.62/1.93      | v1_funct_1(sK4) != iProver_top
% 11.62/1.93      | v1_funct_1(sK3) != iProver_top
% 11.62/1.93      | v1_relat_1(sK4) != iProver_top
% 11.62/1.93      | v1_relat_1(sK3) != iProver_top
% 11.62/1.93      | v2_funct_1(sK4) != iProver_top ),
% 11.62/1.93      inference(light_normalisation,[status(thm)],[c_4002,c_2006,c_2007]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_4004,plain,
% 11.62/1.93      ( k2_funct_1(sK4) = sK3
% 11.62/1.93      | k1_relat_1(sK4) != sK2
% 11.62/1.93      | v1_funct_1(sK4) != iProver_top
% 11.62/1.93      | v1_funct_1(sK3) != iProver_top
% 11.62/1.93      | v1_relat_1(sK4) != iProver_top
% 11.62/1.93      | v1_relat_1(sK3) != iProver_top
% 11.62/1.93      | v2_funct_1(sK4) != iProver_top ),
% 11.62/1.93      inference(equality_resolution_simp,[status(thm)],[c_4003]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_1602,plain,
% 11.62/1.93      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 11.62/1.93      | v1_relat_1(sK4) = iProver_top ),
% 11.62/1.93      inference(predicate_to_equality,[status(thm)],[c_1601]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_1714,plain,
% 11.62/1.93      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 11.62/1.93      | v1_relat_1(sK3) = iProver_top ),
% 11.62/1.93      inference(predicate_to_equality,[status(thm)],[c_1713]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_5233,plain,
% 11.62/1.93      ( k1_relat_1(sK4) != sK2 | k2_funct_1(sK4) = sK3 ),
% 11.62/1.93      inference(global_propositional_subsumption,
% 11.62/1.93                [status(thm)],
% 11.62/1.93                [c_4004,c_36,c_38,c_39,c_40,c_41,c_26,c_667,c_1201,
% 11.62/1.93                 c_1602,c_1714,c_4826,c_4982]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_5234,plain,
% 11.62/1.93      ( k2_funct_1(sK4) = sK3 | k1_relat_1(sK4) != sK2 ),
% 11.62/1.93      inference(renaming,[status(thm)],[c_5233]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_5055,plain,
% 11.62/1.93      ( v2_funct_1(sK4) = iProver_top ),
% 11.62/1.93      inference(global_propositional_subsumption,
% 11.62/1.93                [status(thm)],
% 11.62/1.93                [c_4982,c_39,c_40,c_41,c_26,c_667,c_1201,c_4826]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_1100,plain,
% 11.62/1.93      ( v1_funct_1(sK4) = iProver_top ),
% 11.62/1.93      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_6,plain,
% 11.62/1.93      ( ~ v1_funct_1(X0)
% 11.62/1.93      | ~ v1_relat_1(X0)
% 11.62/1.93      | ~ v2_funct_1(X0)
% 11.62/1.93      | k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) ),
% 11.62/1.93      inference(cnf_transformation,[],[f53]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_1118,plain,
% 11.62/1.93      ( k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
% 11.62/1.93      | v1_funct_1(X0) != iProver_top
% 11.62/1.93      | v1_relat_1(X0) != iProver_top
% 11.62/1.93      | v2_funct_1(X0) != iProver_top ),
% 11.62/1.93      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_2272,plain,
% 11.62/1.93      ( k2_relat_1(k5_relat_1(sK4,k2_funct_1(sK4))) = k1_relat_1(sK4)
% 11.62/1.93      | v1_relat_1(sK4) != iProver_top
% 11.62/1.93      | v2_funct_1(sK4) != iProver_top ),
% 11.62/1.93      inference(superposition,[status(thm)],[c_1100,c_1118]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_2607,plain,
% 11.62/1.93      ( k2_relat_1(k5_relat_1(sK4,k2_funct_1(sK4))) = k1_relat_1(sK4)
% 11.62/1.93      | v2_funct_1(sK4) != iProver_top ),
% 11.62/1.93      inference(global_propositional_subsumption,
% 11.62/1.93                [status(thm)],
% 11.62/1.93                [c_2272,c_41,c_1602]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_5059,plain,
% 11.62/1.93      ( k2_relat_1(k5_relat_1(sK4,k2_funct_1(sK4))) = k1_relat_1(sK4) ),
% 11.62/1.93      inference(superposition,[status(thm)],[c_5055,c_2607]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_5283,plain,
% 11.62/1.93      ( k2_relat_1(k6_partfun1(sK2)) = k1_relat_1(sK4) ),
% 11.62/1.93      inference(demodulation,[status(thm)],[c_5280,c_5059]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_2,plain,
% 11.62/1.93      ( k2_relat_1(k6_partfun1(X0)) = X0 ),
% 11.62/1.93      inference(cnf_transformation,[],[f83]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_5284,plain,
% 11.62/1.93      ( k1_relat_1(sK4) = sK2 ),
% 11.62/1.93      inference(demodulation,[status(thm)],[c_5283,c_2]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_5288,plain,
% 11.62/1.93      ( ~ v1_funct_1(k2_funct_1(sK4))
% 11.62/1.93      | ~ v1_funct_1(sK4)
% 11.62/1.93      | ~ v1_relat_1(k2_funct_1(sK4))
% 11.62/1.93      | ~ v1_relat_1(sK4)
% 11.62/1.93      | ~ v2_funct_1(k2_funct_1(sK4))
% 11.62/1.93      | k2_funct_1(k2_funct_1(sK4)) = sK4
% 11.62/1.93      | k1_relat_1(k2_funct_1(sK4)) != sK1
% 11.62/1.93      | k6_partfun1(k2_relat_1(k2_funct_1(sK4))) != k6_partfun1(sK2) ),
% 11.62/1.93      inference(predicate_to_equality_rev,[status(thm)],[c_5287]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_645,plain,
% 11.62/1.93      ( ~ v1_funct_1(X0) | v1_funct_1(X1) | X1 != X0 ),
% 11.62/1.93      theory(equality) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_1379,plain,
% 11.62/1.93      ( v1_funct_1(X0) | ~ v1_funct_1(sK3) | X0 != sK3 ),
% 11.62/1.93      inference(instantiation,[status(thm)],[c_645]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_1458,plain,
% 11.62/1.93      ( v1_funct_1(k2_funct_1(X0))
% 11.62/1.93      | ~ v1_funct_1(sK3)
% 11.62/1.93      | k2_funct_1(X0) != sK3 ),
% 11.62/1.93      inference(instantiation,[status(thm)],[c_1379]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_8389,plain,
% 11.62/1.93      ( v1_funct_1(k2_funct_1(sK4))
% 11.62/1.93      | ~ v1_funct_1(sK3)
% 11.62/1.93      | k2_funct_1(sK4) != sK3 ),
% 11.62/1.93      inference(instantiation,[status(thm)],[c_1458]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_642,plain,
% 11.62/1.93      ( ~ v1_relat_1(X0) | v1_relat_1(X1) | X1 != X0 ),
% 11.62/1.93      theory(equality) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_1766,plain,
% 11.62/1.93      ( v1_relat_1(X0) | ~ v1_relat_1(sK3) | X0 != sK3 ),
% 11.62/1.93      inference(instantiation,[status(thm)],[c_642]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_2252,plain,
% 11.62/1.93      ( v1_relat_1(k2_funct_1(X0))
% 11.62/1.93      | ~ v1_relat_1(sK3)
% 11.62/1.93      | k2_funct_1(X0) != sK3 ),
% 11.62/1.93      inference(instantiation,[status(thm)],[c_1766]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_8387,plain,
% 11.62/1.93      ( v1_relat_1(k2_funct_1(sK4))
% 11.62/1.93      | ~ v1_relat_1(sK3)
% 11.62/1.93      | k2_funct_1(sK4) != sK3 ),
% 11.62/1.93      inference(instantiation,[status(thm)],[c_2252]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_641,plain,
% 11.62/1.93      ( ~ v2_funct_1(X0) | v2_funct_1(X1) | X1 != X0 ),
% 11.62/1.93      theory(equality) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_2286,plain,
% 11.62/1.93      ( v2_funct_1(X0) | ~ v2_funct_1(sK3) | X0 != sK3 ),
% 11.62/1.93      inference(instantiation,[status(thm)],[c_641]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_2527,plain,
% 11.62/1.93      ( v2_funct_1(k2_funct_1(X0))
% 11.62/1.93      | ~ v2_funct_1(sK3)
% 11.62/1.93      | k2_funct_1(X0) != sK3 ),
% 11.62/1.93      inference(instantiation,[status(thm)],[c_2286]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_8386,plain,
% 11.62/1.93      ( v2_funct_1(k2_funct_1(sK4))
% 11.62/1.93      | ~ v2_funct_1(sK3)
% 11.62/1.93      | k2_funct_1(sK4) != sK3 ),
% 11.62/1.93      inference(instantiation,[status(thm)],[c_2527]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_24522,plain,
% 11.62/1.93      ( k6_partfun1(k2_relat_1(k2_funct_1(sK4))) != k6_partfun1(sK2)
% 11.62/1.93      | k1_relat_1(k2_funct_1(sK4)) != sK1
% 11.62/1.93      | k2_funct_1(k2_funct_1(sK4)) = sK4 ),
% 11.62/1.93      inference(global_propositional_subsumption,
% 11.62/1.93                [status(thm)],
% 11.62/1.93                [c_5287,c_35,c_36,c_33,c_38,c_32,c_39,c_40,c_30,c_41,
% 11.62/1.93                 c_27,c_26,c_667,c_1201,c_1601,c_1602,c_1713,c_1714,
% 11.62/1.93                 c_4004,c_4826,c_4982,c_5284,c_5288,c_8389,c_8387,c_8386]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_24523,plain,
% 11.62/1.93      ( k2_funct_1(k2_funct_1(sK4)) = sK4
% 11.62/1.93      | k1_relat_1(k2_funct_1(sK4)) != sK1
% 11.62/1.93      | k6_partfun1(k2_relat_1(k2_funct_1(sK4))) != k6_partfun1(sK2) ),
% 11.62/1.93      inference(renaming,[status(thm)],[c_24522]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_2650,plain,
% 11.62/1.93      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
% 11.62/1.93      | sK2 = k1_xboole_0
% 11.62/1.93      | v1_funct_2(sK3,sK1,sK2) != iProver_top
% 11.62/1.93      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 11.62/1.93      | v1_funct_1(sK3) != iProver_top
% 11.62/1.93      | v2_funct_1(sK3) != iProver_top ),
% 11.62/1.93      inference(superposition,[status(thm)],[c_29,c_1104]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_25,negated_conjecture,
% 11.62/1.93      ( k1_xboole_0 != sK2 ),
% 11.62/1.93      inference(cnf_transformation,[],[f81]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_1165,plain,
% 11.62/1.93      ( ~ v1_funct_2(X0,X1,sK2)
% 11.62/1.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK2)))
% 11.62/1.93      | ~ v1_funct_1(X0)
% 11.62/1.93      | ~ v2_funct_1(X0)
% 11.62/1.93      | k2_relset_1(X1,sK2,X0) != sK2
% 11.62/1.93      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 11.62/1.93      | k1_xboole_0 = sK2 ),
% 11.62/1.93      inference(instantiation,[status(thm)],[c_23]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_1293,plain,
% 11.62/1.93      ( ~ v1_funct_2(sK3,X0,sK2)
% 11.62/1.93      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
% 11.62/1.93      | ~ v1_funct_1(sK3)
% 11.62/1.93      | ~ v2_funct_1(sK3)
% 11.62/1.93      | k2_relset_1(X0,sK2,sK3) != sK2
% 11.62/1.93      | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(X0)
% 11.62/1.93      | k1_xboole_0 = sK2 ),
% 11.62/1.93      inference(instantiation,[status(thm)],[c_1165]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_1510,plain,
% 11.62/1.93      ( ~ v1_funct_2(sK3,sK1,sK2)
% 11.62/1.93      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 11.62/1.93      | ~ v1_funct_1(sK3)
% 11.62/1.93      | ~ v2_funct_1(sK3)
% 11.62/1.93      | k2_relset_1(sK1,sK2,sK3) != sK2
% 11.62/1.93      | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
% 11.62/1.93      | k1_xboole_0 = sK2 ),
% 11.62/1.93      inference(instantiation,[status(thm)],[c_1293]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_2657,plain,
% 11.62/1.93      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
% 11.62/1.93      inference(global_propositional_subsumption,
% 11.62/1.93                [status(thm)],
% 11.62/1.93                [c_2650,c_35,c_34,c_33,c_29,c_27,c_25,c_1510]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_1097,plain,
% 11.62/1.93      ( v1_funct_1(sK3) = iProver_top ),
% 11.62/1.93      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_7,plain,
% 11.62/1.93      ( ~ v1_funct_1(X0)
% 11.62/1.93      | ~ v1_relat_1(X0)
% 11.62/1.93      | ~ v2_funct_1(X0)
% 11.62/1.93      | k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) ),
% 11.62/1.93      inference(cnf_transformation,[],[f52]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_1117,plain,
% 11.62/1.93      ( k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
% 11.62/1.93      | v1_funct_1(X0) != iProver_top
% 11.62/1.93      | v1_relat_1(X0) != iProver_top
% 11.62/1.93      | v2_funct_1(X0) != iProver_top ),
% 11.62/1.93      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_2054,plain,
% 11.62/1.93      ( k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) = k1_relat_1(sK3)
% 11.62/1.93      | v1_relat_1(sK3) != iProver_top
% 11.62/1.93      | v2_funct_1(sK3) != iProver_top ),
% 11.62/1.93      inference(superposition,[status(thm)],[c_1097,c_1117]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_43,plain,
% 11.62/1.93      ( v2_funct_1(sK3) = iProver_top ),
% 11.62/1.93      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_2224,plain,
% 11.62/1.93      ( k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) = k1_relat_1(sK3) ),
% 11.62/1.93      inference(global_propositional_subsumption,
% 11.62/1.93                [status(thm)],
% 11.62/1.93                [c_2054,c_38,c_43,c_1714]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_2660,plain,
% 11.62/1.93      ( k1_relat_1(k6_partfun1(sK1)) = k1_relat_1(sK3) ),
% 11.62/1.93      inference(demodulation,[status(thm)],[c_2657,c_2224]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_3,plain,
% 11.62/1.93      ( k1_relat_1(k6_partfun1(X0)) = X0 ),
% 11.62/1.93      inference(cnf_transformation,[],[f84]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_2661,plain,
% 11.62/1.93      ( k1_relat_1(sK3) = sK1 ),
% 11.62/1.93      inference(demodulation,[status(thm)],[c_2660,c_3]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_5372,plain,
% 11.62/1.93      ( k2_funct_1(sK4) = sK3 | sK2 != sK2 ),
% 11.62/1.93      inference(demodulation,[status(thm)],[c_5284,c_5234]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_5523,plain,
% 11.62/1.93      ( k2_funct_1(sK4) = sK3 ),
% 11.62/1.93      inference(equality_resolution_simp,[status(thm)],[c_5372]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_24524,plain,
% 11.62/1.93      ( k2_funct_1(sK3) = sK4
% 11.62/1.93      | k6_partfun1(sK2) != k6_partfun1(sK2)
% 11.62/1.93      | sK1 != sK1 ),
% 11.62/1.93      inference(light_normalisation,
% 11.62/1.93                [status(thm)],
% 11.62/1.93                [c_24523,c_2006,c_2661,c_5523]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_24525,plain,
% 11.62/1.93      ( k2_funct_1(sK3) = sK4 ),
% 11.62/1.93      inference(equality_resolution_simp,[status(thm)],[c_24524]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(c_24,negated_conjecture,
% 11.62/1.93      ( k2_funct_1(sK3) != sK4 ),
% 11.62/1.93      inference(cnf_transformation,[],[f82]) ).
% 11.62/1.93  
% 11.62/1.93  cnf(contradiction,plain,
% 11.62/1.93      ( $false ),
% 11.62/1.93      inference(minisat,[status(thm)],[c_24525,c_24]) ).
% 11.62/1.93  
% 11.62/1.93  
% 11.62/1.93  % SZS output end CNFRefutation for theBenchmark.p
% 11.62/1.93  
% 11.62/1.93  ------                               Statistics
% 11.62/1.93  
% 11.62/1.93  ------ General
% 11.62/1.93  
% 11.62/1.93  abstr_ref_over_cycles:                  0
% 11.62/1.93  abstr_ref_under_cycles:                 0
% 11.62/1.93  gc_basic_clause_elim:                   0
% 11.62/1.93  forced_gc_time:                         0
% 11.62/1.93  parsing_time:                           0.01
% 11.62/1.93  unif_index_cands_time:                  0.
% 11.62/1.93  unif_index_add_time:                    0.
% 11.62/1.93  orderings_time:                         0.
% 11.62/1.93  out_proof_time:                         0.015
% 11.62/1.93  total_time:                             1.111
% 11.62/1.93  num_of_symbols:                         53
% 11.62/1.93  num_of_terms:                           36944
% 11.62/1.93  
% 11.62/1.93  ------ Preprocessing
% 11.62/1.93  
% 11.62/1.93  num_of_splits:                          0
% 11.62/1.93  num_of_split_atoms:                     0
% 11.62/1.93  num_of_reused_defs:                     0
% 11.62/1.93  num_eq_ax_congr_red:                    0
% 11.62/1.93  num_of_sem_filtered_clauses:            1
% 11.62/1.93  num_of_subtypes:                        0
% 11.62/1.93  monotx_restored_types:                  0
% 11.62/1.93  sat_num_of_epr_types:                   0
% 11.62/1.93  sat_num_of_non_cyclic_types:            0
% 11.62/1.93  sat_guarded_non_collapsed_types:        0
% 11.62/1.93  num_pure_diseq_elim:                    0
% 11.62/1.93  simp_replaced_by:                       0
% 11.62/1.93  res_preprocessed:                       171
% 11.62/1.93  prep_upred:                             0
% 11.62/1.93  prep_unflattend:                        13
% 11.62/1.93  smt_new_axioms:                         0
% 11.62/1.93  pred_elim_cands:                        5
% 11.62/1.93  pred_elim:                              2
% 11.62/1.93  pred_elim_cl:                           2
% 11.62/1.93  pred_elim_cycles:                       4
% 11.62/1.93  merged_defs:                            0
% 11.62/1.93  merged_defs_ncl:                        0
% 11.62/1.93  bin_hyper_res:                          0
% 11.62/1.93  prep_cycles:                            4
% 11.62/1.93  pred_elim_time:                         0.005
% 11.62/1.93  splitting_time:                         0.
% 11.62/1.93  sem_filter_time:                        0.
% 11.62/1.93  monotx_time:                            0.001
% 11.62/1.93  subtype_inf_time:                       0.
% 11.62/1.93  
% 11.62/1.93  ------ Problem properties
% 11.62/1.93  
% 11.62/1.93  clauses:                                34
% 11.62/1.93  conjectures:                            11
% 11.62/1.93  epr:                                    8
% 11.62/1.93  horn:                                   30
% 11.62/1.93  ground:                                 13
% 11.62/1.93  unary:                                  17
% 11.62/1.93  binary:                                 3
% 11.62/1.93  lits:                                   122
% 11.62/1.93  lits_eq:                                31
% 11.62/1.93  fd_pure:                                0
% 11.62/1.93  fd_pseudo:                              0
% 11.62/1.93  fd_cond:                                4
% 11.62/1.93  fd_pseudo_cond:                         1
% 11.62/1.93  ac_symbols:                             0
% 11.62/1.93  
% 11.62/1.93  ------ Propositional Solver
% 11.62/1.93  
% 11.62/1.93  prop_solver_calls:                      33
% 11.62/1.93  prop_fast_solver_calls:                 2963
% 11.62/1.93  smt_solver_calls:                       0
% 11.62/1.93  smt_fast_solver_calls:                  0
% 11.62/1.93  prop_num_of_clauses:                    12885
% 11.62/1.93  prop_preprocess_simplified:             21429
% 11.62/1.93  prop_fo_subsumed:                       596
% 11.62/1.93  prop_solver_time:                       0.
% 11.62/1.93  smt_solver_time:                        0.
% 11.62/1.93  smt_fast_solver_time:                   0.
% 11.62/1.93  prop_fast_solver_time:                  0.
% 11.62/1.93  prop_unsat_core_time:                   0.002
% 11.62/1.93  
% 11.62/1.93  ------ QBF
% 11.62/1.93  
% 11.62/1.93  qbf_q_res:                              0
% 11.62/1.93  qbf_num_tautologies:                    0
% 11.62/1.93  qbf_prep_cycles:                        0
% 11.62/1.93  
% 11.62/1.93  ------ BMC1
% 11.62/1.93  
% 11.62/1.93  bmc1_current_bound:                     -1
% 11.62/1.93  bmc1_last_solved_bound:                 -1
% 11.62/1.93  bmc1_unsat_core_size:                   -1
% 11.62/1.93  bmc1_unsat_core_parents_size:           -1
% 11.62/1.93  bmc1_merge_next_fun:                    0
% 11.62/1.93  bmc1_unsat_core_clauses_time:           0.
% 11.62/1.93  
% 11.62/1.93  ------ Instantiation
% 11.62/1.93  
% 11.62/1.93  inst_num_of_clauses:                    3227
% 11.62/1.93  inst_num_in_passive:                    480
% 11.62/1.93  inst_num_in_active:                     1712
% 11.62/1.93  inst_num_in_unprocessed:                1035
% 11.62/1.93  inst_num_of_loops:                      1870
% 11.62/1.93  inst_num_of_learning_restarts:          0
% 11.62/1.93  inst_num_moves_active_passive:          155
% 11.62/1.93  inst_lit_activity:                      0
% 11.62/1.93  inst_lit_activity_moves:                1
% 11.62/1.93  inst_num_tautologies:                   0
% 11.62/1.93  inst_num_prop_implied:                  0
% 11.62/1.93  inst_num_existing_simplified:           0
% 11.62/1.93  inst_num_eq_res_simplified:             0
% 11.62/1.93  inst_num_child_elim:                    0
% 11.62/1.93  inst_num_of_dismatching_blockings:      1209
% 11.62/1.93  inst_num_of_non_proper_insts:           2841
% 11.62/1.93  inst_num_of_duplicates:                 0
% 11.62/1.93  inst_inst_num_from_inst_to_res:         0
% 11.62/1.93  inst_dismatching_checking_time:         0.
% 11.62/1.93  
% 11.62/1.93  ------ Resolution
% 11.62/1.93  
% 11.62/1.93  res_num_of_clauses:                     0
% 11.62/1.93  res_num_in_passive:                     0
% 11.62/1.93  res_num_in_active:                      0
% 11.62/1.93  res_num_of_loops:                       175
% 11.62/1.93  res_forward_subset_subsumed:            270
% 11.62/1.93  res_backward_subset_subsumed:           0
% 11.62/1.93  res_forward_subsumed:                   0
% 11.62/1.93  res_backward_subsumed:                  0
% 11.62/1.93  res_forward_subsumption_resolution:     2
% 11.62/1.93  res_backward_subsumption_resolution:    0
% 11.62/1.93  res_clause_to_clause_subsumption:       2719
% 11.62/1.93  res_orphan_elimination:                 0
% 11.62/1.93  res_tautology_del:                      258
% 11.62/1.93  res_num_eq_res_simplified:              1
% 11.62/1.93  res_num_sel_changes:                    0
% 11.62/1.93  res_moves_from_active_to_pass:          0
% 11.62/1.93  
% 11.62/1.93  ------ Superposition
% 11.62/1.93  
% 11.62/1.93  sup_time_total:                         0.
% 11.62/1.93  sup_time_generating:                    0.
% 11.62/1.93  sup_time_sim_full:                      0.
% 11.62/1.93  sup_time_sim_immed:                     0.
% 11.62/1.93  
% 11.62/1.93  sup_num_of_clauses:                     1259
% 11.62/1.93  sup_num_in_active:                      342
% 11.62/1.93  sup_num_in_passive:                     917
% 11.62/1.93  sup_num_of_loops:                       373
% 11.62/1.93  sup_fw_superposition:                   508
% 11.62/1.93  sup_bw_superposition:                   884
% 11.62/1.93  sup_immediate_simplified:               392
% 11.62/1.93  sup_given_eliminated:                   0
% 11.62/1.93  comparisons_done:                       0
% 11.62/1.93  comparisons_avoided:                    4
% 11.62/1.93  
% 11.62/1.93  ------ Simplifications
% 11.62/1.93  
% 11.62/1.93  
% 11.62/1.93  sim_fw_subset_subsumed:                 26
% 11.62/1.93  sim_bw_subset_subsumed:                 43
% 11.62/1.93  sim_fw_subsumed:                        22
% 11.62/1.93  sim_bw_subsumed:                        25
% 11.62/1.93  sim_fw_subsumption_res:                 0
% 11.62/1.93  sim_bw_subsumption_res:                 0
% 11.62/1.93  sim_tautology_del:                      0
% 11.62/1.93  sim_eq_tautology_del:                   23
% 11.62/1.93  sim_eq_res_simp:                        3
% 11.62/1.93  sim_fw_demodulated:                     35
% 11.62/1.93  sim_bw_demodulated:                     6
% 11.62/1.93  sim_light_normalised:                   365
% 11.62/1.93  sim_joinable_taut:                      0
% 11.62/1.93  sim_joinable_simp:                      0
% 11.62/1.93  sim_ac_normalised:                      0
% 11.62/1.93  sim_smt_subsumption:                    0
% 11.62/1.93  
%------------------------------------------------------------------------------
