%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:02 EST 2020

% Result     : Theorem 1.84s
% Output     : CNFRefutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :  190 ( 720 expanded)
%              Number of clauses        :  111 ( 194 expanded)
%              Number of leaves         :   19 ( 188 expanded)
%              Depth                    :   22
%              Number of atoms          :  670 (6243 expanded)
%              Number of equality atoms :  327 (2287 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    5 (   2 average)

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

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f48,plain,(
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

fof(f47,plain,
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

fof(f49,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f44,f48,f47])).

fof(f84,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f49])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f81,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f49])).

fof(f79,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f55,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f80,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f17,axiom,(
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

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f41])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f87,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f85,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f49])).

fof(f89,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f49])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f12,axiom,(
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

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f83,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f88,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f49])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f53,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f16,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f93,plain,(
    ! [X0] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f53,f76])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f54,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f94,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f54,f76])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f29,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f60,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f2,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f91,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f52,f76])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f27,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f58,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f13,axiom,(
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
    inference(ennf_transformation,[],[f13])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f37])).

fof(f73,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f33])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f86,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f49])).

fof(f14,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f74,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f82,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f15,axiom,(
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
    inference(ennf_transformation,[],[f15])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f39])).

fof(f75,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f90,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1529,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1536,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3348,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1529,c_1536])).

cnf(c_37,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1527,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_3349,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1527,c_1536])).

cnf(c_39,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1526,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_6,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1537,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k5_relat_1(k5_relat_1(X2,X1),X0) = k5_relat_1(X2,k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1541,plain,
    ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4777,plain,
    ( k5_relat_1(k2_funct_1(X0),k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(k2_funct_1(X0),X1),X2)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1537,c_1541])).

cnf(c_9768,plain,
    ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1526,c_4777])).

cnf(c_42,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_1821,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1822,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1821])).

cnf(c_10891,plain,
    ( v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9768,c_42,c_1822])).

cnf(c_10892,plain,
    ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_10891])).

cnf(c_10901,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3349,c_10892])).

cnf(c_38,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_31,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_436,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_31])).

cnf(c_437,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(X1)
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_436])).

cnf(c_441,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(sK2,X0,X1)
    | k2_relset_1(X0,X1,sK2) != X1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(X1)
    | k1_xboole_0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_437,c_39])).

cnf(c_442,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_relset_1(X0,X1,sK2) != X1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(X1)
    | k1_xboole_0 = X1 ),
    inference(renaming,[status(thm)],[c_441])).

cnf(c_759,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_relset_1(X0,X1,sK2) != X1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(X1)
    | sK0 != X0
    | sK1 != X1
    | sK2 != sK2
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_38,c_442])).

cnf(c_760,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k2_relset_1(sK0,sK1,sK2) != sK1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_759])).

cnf(c_33,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_29,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_762,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_760,c_37,c_33,c_29])).

cnf(c_10932,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k6_partfun1(sK1),X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10901,c_762])).

cnf(c_10966,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
    inference(superposition,[status(thm)],[c_3348,c_10932])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1535,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4138,plain,
    ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1529,c_1535])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_35,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_665,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK0 != X2
    | sK1 != X1
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_35])).

cnf(c_666,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k1_relset_1(sK1,sK0,sK3) = sK1
    | k1_xboole_0 = sK0 ),
    inference(unflattening,[status(thm)],[c_665])).

cnf(c_30,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_668,plain,
    ( k1_relset_1(sK1,sK0,sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_666,c_34,c_30])).

cnf(c_4143,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_4138,c_668])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1540,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3415,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1(sK3)),sK3) = sK3 ),
    inference(superposition,[status(thm)],[c_3348,c_1540])).

cnf(c_4150,plain,
    ( k5_relat_1(k6_partfun1(sK1),sK3) = sK3 ),
    inference(demodulation,[status(thm)],[c_4143,c_3415])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1539,plain,
    ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4526,plain,
    ( k5_relat_1(k2_funct_1(X0),k6_partfun1(k2_relat_1(k2_funct_1(X0)))) = k2_funct_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1537,c_1539])).

cnf(c_6314,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(k2_relat_1(k2_funct_1(sK2)))) = k2_funct_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1526,c_4526])).

cnf(c_9,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_477,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_31])).

cnf(c_478,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_477])).

cnf(c_480,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_478,c_39])).

cnf(c_1523,plain,
    ( k2_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_480])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_409,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_31])).

cnf(c_410,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_409])).

cnf(c_414,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(sK2,X0,X1)
    | k2_relset_1(X0,X1,sK2) != X1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
    | k1_xboole_0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_410,c_39])).

cnf(c_415,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_relset_1(X0,X1,sK2) != X1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
    | k1_xboole_0 = X1 ),
    inference(renaming,[status(thm)],[c_414])).

cnf(c_767,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_relset_1(X0,X1,sK2) != X1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
    | sK0 != X0
    | sK1 != X1
    | sK2 != sK2
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_38,c_415])).

cnf(c_768,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k2_relset_1(sK0,sK1,sK2) != sK1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_767])).

cnf(c_770,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_768,c_37,c_33,c_29])).

cnf(c_1588,plain,
    ( k2_relat_1(k6_partfun1(sK0)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1523,c_770])).

cnf(c_1,plain,
    ( k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1589,plain,
    ( k1_relat_1(sK2) = sK0
    | v1_relat_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1588,c_1])).

cnf(c_1737,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = sK0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1589])).

cnf(c_2733,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1589,c_37,c_1737,c_1821])).

cnf(c_7,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_505,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_31])).

cnf(c_506,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_505])).

cnf(c_508,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_506,c_39])).

cnf(c_1521,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_508])).

cnf(c_2165,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1521,c_39,c_37,c_506,c_1821])).

cnf(c_2736,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = sK0 ),
    inference(demodulation,[status(thm)],[c_2733,c_2165])).

cnf(c_6317,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k2_funct_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6314,c_2736])).

cnf(c_8154,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6317,c_42,c_1822])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1533,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_15,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_32,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_393,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_32])).

cnf(c_394,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_393])).

cnf(c_24,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_402,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_394,c_24])).

cnf(c_1525,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_402])).

cnf(c_4383,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1533,c_1525])).

cnf(c_40,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_36,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_43,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_45,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_8965,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4383,c_40,c_42,c_43,c_45])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1530,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_5441,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1529,c_1530])).

cnf(c_7346,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5441,c_43])).

cnf(c_7347,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_7346])).

cnf(c_7358,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1527,c_7347])).

cnf(c_1905,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(X1,X2,X3,X4,X0,sK3) = k5_relat_1(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_2217,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(X2,X3,X0,X1,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1905])).

cnf(c_2725,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(X0,X1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_2217])).

cnf(c_4123,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_2725])).

cnf(c_7640,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7358,c_39,c_37,c_36,c_34,c_4123])).

cnf(c_8968,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(demodulation,[status(thm)],[c_8965,c_7640])).

cnf(c_10985,plain,
    ( k2_funct_1(sK2) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_10966,c_4150,c_8154,c_8968])).

cnf(c_28,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f90])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10985,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:49:26 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.84/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.02  
% 1.84/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.84/1.02  
% 1.84/1.02  ------  iProver source info
% 1.84/1.02  
% 1.84/1.02  git: date: 2020-06-30 10:37:57 +0100
% 1.84/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.84/1.02  git: non_committed_changes: false
% 1.84/1.02  git: last_make_outside_of_git: false
% 1.84/1.02  
% 1.84/1.02  ------ 
% 1.84/1.02  
% 1.84/1.02  ------ Input Options
% 1.84/1.02  
% 1.84/1.02  --out_options                           all
% 1.84/1.02  --tptp_safe_out                         true
% 1.84/1.02  --problem_path                          ""
% 1.84/1.02  --include_path                          ""
% 1.84/1.02  --clausifier                            res/vclausify_rel
% 1.84/1.02  --clausifier_options                    --mode clausify
% 1.84/1.02  --stdin                                 false
% 1.84/1.02  --stats_out                             all
% 1.84/1.02  
% 1.84/1.02  ------ General Options
% 1.84/1.02  
% 1.84/1.02  --fof                                   false
% 1.84/1.02  --time_out_real                         305.
% 1.84/1.02  --time_out_virtual                      -1.
% 1.84/1.02  --symbol_type_check                     false
% 1.84/1.02  --clausify_out                          false
% 1.84/1.02  --sig_cnt_out                           false
% 1.84/1.02  --trig_cnt_out                          false
% 1.84/1.02  --trig_cnt_out_tolerance                1.
% 1.84/1.02  --trig_cnt_out_sk_spl                   false
% 1.84/1.02  --abstr_cl_out                          false
% 1.84/1.02  
% 1.84/1.02  ------ Global Options
% 1.84/1.02  
% 1.84/1.02  --schedule                              default
% 1.84/1.02  --add_important_lit                     false
% 1.84/1.02  --prop_solver_per_cl                    1000
% 1.84/1.02  --min_unsat_core                        false
% 1.84/1.02  --soft_assumptions                      false
% 1.84/1.02  --soft_lemma_size                       3
% 1.84/1.02  --prop_impl_unit_size                   0
% 1.84/1.02  --prop_impl_unit                        []
% 1.84/1.02  --share_sel_clauses                     true
% 1.84/1.02  --reset_solvers                         false
% 1.84/1.02  --bc_imp_inh                            [conj_cone]
% 1.84/1.02  --conj_cone_tolerance                   3.
% 1.84/1.02  --extra_neg_conj                        none
% 1.84/1.02  --large_theory_mode                     true
% 1.84/1.02  --prolific_symb_bound                   200
% 1.84/1.02  --lt_threshold                          2000
% 1.84/1.02  --clause_weak_htbl                      true
% 1.84/1.02  --gc_record_bc_elim                     false
% 1.84/1.02  
% 1.84/1.02  ------ Preprocessing Options
% 1.84/1.02  
% 1.84/1.02  --preprocessing_flag                    true
% 1.84/1.02  --time_out_prep_mult                    0.1
% 1.84/1.02  --splitting_mode                        input
% 1.84/1.02  --splitting_grd                         true
% 1.84/1.02  --splitting_cvd                         false
% 1.84/1.02  --splitting_cvd_svl                     false
% 1.84/1.02  --splitting_nvd                         32
% 1.84/1.02  --sub_typing                            true
% 1.84/1.02  --prep_gs_sim                           true
% 1.84/1.02  --prep_unflatten                        true
% 1.84/1.02  --prep_res_sim                          true
% 1.84/1.02  --prep_upred                            true
% 1.84/1.02  --prep_sem_filter                       exhaustive
% 1.84/1.02  --prep_sem_filter_out                   false
% 1.84/1.02  --pred_elim                             true
% 1.84/1.02  --res_sim_input                         true
% 1.84/1.02  --eq_ax_congr_red                       true
% 1.84/1.02  --pure_diseq_elim                       true
% 1.84/1.02  --brand_transform                       false
% 1.84/1.02  --non_eq_to_eq                          false
% 1.84/1.02  --prep_def_merge                        true
% 1.84/1.02  --prep_def_merge_prop_impl              false
% 1.84/1.02  --prep_def_merge_mbd                    true
% 1.84/1.02  --prep_def_merge_tr_red                 false
% 1.84/1.02  --prep_def_merge_tr_cl                  false
% 1.84/1.02  --smt_preprocessing                     true
% 1.84/1.02  --smt_ac_axioms                         fast
% 1.84/1.02  --preprocessed_out                      false
% 1.84/1.02  --preprocessed_stats                    false
% 1.84/1.02  
% 1.84/1.02  ------ Abstraction refinement Options
% 1.84/1.02  
% 1.84/1.02  --abstr_ref                             []
% 1.84/1.02  --abstr_ref_prep                        false
% 1.84/1.02  --abstr_ref_until_sat                   false
% 1.84/1.02  --abstr_ref_sig_restrict                funpre
% 1.84/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 1.84/1.02  --abstr_ref_under                       []
% 1.84/1.02  
% 1.84/1.02  ------ SAT Options
% 1.84/1.02  
% 1.84/1.02  --sat_mode                              false
% 1.84/1.02  --sat_fm_restart_options                ""
% 1.84/1.02  --sat_gr_def                            false
% 1.84/1.02  --sat_epr_types                         true
% 1.84/1.02  --sat_non_cyclic_types                  false
% 1.84/1.02  --sat_finite_models                     false
% 1.84/1.02  --sat_fm_lemmas                         false
% 1.84/1.02  --sat_fm_prep                           false
% 1.84/1.02  --sat_fm_uc_incr                        true
% 1.84/1.02  --sat_out_model                         small
% 1.84/1.02  --sat_out_clauses                       false
% 1.84/1.02  
% 1.84/1.02  ------ QBF Options
% 1.84/1.02  
% 1.84/1.02  --qbf_mode                              false
% 1.84/1.02  --qbf_elim_univ                         false
% 1.84/1.02  --qbf_dom_inst                          none
% 1.84/1.02  --qbf_dom_pre_inst                      false
% 1.84/1.02  --qbf_sk_in                             false
% 1.84/1.02  --qbf_pred_elim                         true
% 1.84/1.02  --qbf_split                             512
% 1.84/1.02  
% 1.84/1.02  ------ BMC1 Options
% 1.84/1.02  
% 1.84/1.02  --bmc1_incremental                      false
% 1.84/1.02  --bmc1_axioms                           reachable_all
% 1.84/1.02  --bmc1_min_bound                        0
% 1.84/1.02  --bmc1_max_bound                        -1
% 1.84/1.02  --bmc1_max_bound_default                -1
% 1.84/1.02  --bmc1_symbol_reachability              true
% 1.84/1.02  --bmc1_property_lemmas                  false
% 1.84/1.02  --bmc1_k_induction                      false
% 1.84/1.02  --bmc1_non_equiv_states                 false
% 1.84/1.02  --bmc1_deadlock                         false
% 1.84/1.02  --bmc1_ucm                              false
% 1.84/1.02  --bmc1_add_unsat_core                   none
% 1.84/1.02  --bmc1_unsat_core_children              false
% 1.84/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 1.84/1.02  --bmc1_out_stat                         full
% 1.84/1.02  --bmc1_ground_init                      false
% 1.84/1.02  --bmc1_pre_inst_next_state              false
% 1.84/1.02  --bmc1_pre_inst_state                   false
% 1.84/1.02  --bmc1_pre_inst_reach_state             false
% 1.84/1.02  --bmc1_out_unsat_core                   false
% 1.84/1.02  --bmc1_aig_witness_out                  false
% 1.84/1.02  --bmc1_verbose                          false
% 1.84/1.02  --bmc1_dump_clauses_tptp                false
% 1.84/1.02  --bmc1_dump_unsat_core_tptp             false
% 1.84/1.02  --bmc1_dump_file                        -
% 1.84/1.02  --bmc1_ucm_expand_uc_limit              128
% 1.84/1.02  --bmc1_ucm_n_expand_iterations          6
% 1.84/1.02  --bmc1_ucm_extend_mode                  1
% 1.84/1.02  --bmc1_ucm_init_mode                    2
% 1.84/1.02  --bmc1_ucm_cone_mode                    none
% 1.84/1.02  --bmc1_ucm_reduced_relation_type        0
% 1.84/1.02  --bmc1_ucm_relax_model                  4
% 1.84/1.02  --bmc1_ucm_full_tr_after_sat            true
% 1.84/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 1.84/1.02  --bmc1_ucm_layered_model                none
% 1.84/1.02  --bmc1_ucm_max_lemma_size               10
% 1.84/1.02  
% 1.84/1.02  ------ AIG Options
% 1.84/1.02  
% 1.84/1.02  --aig_mode                              false
% 1.84/1.02  
% 1.84/1.02  ------ Instantiation Options
% 1.84/1.02  
% 1.84/1.02  --instantiation_flag                    true
% 1.84/1.02  --inst_sos_flag                         false
% 1.84/1.02  --inst_sos_phase                        true
% 1.84/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.84/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.84/1.02  --inst_lit_sel_side                     num_symb
% 1.84/1.02  --inst_solver_per_active                1400
% 1.84/1.02  --inst_solver_calls_frac                1.
% 1.84/1.02  --inst_passive_queue_type               priority_queues
% 1.84/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.84/1.02  --inst_passive_queues_freq              [25;2]
% 1.84/1.02  --inst_dismatching                      true
% 1.84/1.02  --inst_eager_unprocessed_to_passive     true
% 1.84/1.02  --inst_prop_sim_given                   true
% 1.84/1.02  --inst_prop_sim_new                     false
% 1.84/1.02  --inst_subs_new                         false
% 1.84/1.02  --inst_eq_res_simp                      false
% 1.84/1.02  --inst_subs_given                       false
% 1.84/1.02  --inst_orphan_elimination               true
% 1.84/1.02  --inst_learning_loop_flag               true
% 1.84/1.02  --inst_learning_start                   3000
% 1.84/1.02  --inst_learning_factor                  2
% 1.84/1.02  --inst_start_prop_sim_after_learn       3
% 1.84/1.02  --inst_sel_renew                        solver
% 1.84/1.02  --inst_lit_activity_flag                true
% 1.84/1.02  --inst_restr_to_given                   false
% 1.84/1.02  --inst_activity_threshold               500
% 1.84/1.02  --inst_out_proof                        true
% 1.84/1.02  
% 1.84/1.02  ------ Resolution Options
% 1.84/1.02  
% 1.84/1.02  --resolution_flag                       true
% 1.84/1.02  --res_lit_sel                           adaptive
% 1.84/1.02  --res_lit_sel_side                      none
% 1.84/1.02  --res_ordering                          kbo
% 1.84/1.02  --res_to_prop_solver                    active
% 1.84/1.02  --res_prop_simpl_new                    false
% 1.84/1.02  --res_prop_simpl_given                  true
% 1.84/1.02  --res_passive_queue_type                priority_queues
% 1.84/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.84/1.02  --res_passive_queues_freq               [15;5]
% 1.84/1.02  --res_forward_subs                      full
% 1.84/1.02  --res_backward_subs                     full
% 1.84/1.02  --res_forward_subs_resolution           true
% 1.84/1.02  --res_backward_subs_resolution          true
% 1.84/1.02  --res_orphan_elimination                true
% 1.84/1.02  --res_time_limit                        2.
% 1.84/1.02  --res_out_proof                         true
% 1.84/1.02  
% 1.84/1.02  ------ Superposition Options
% 1.84/1.02  
% 1.84/1.02  --superposition_flag                    true
% 1.84/1.02  --sup_passive_queue_type                priority_queues
% 1.84/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.84/1.02  --sup_passive_queues_freq               [8;1;4]
% 1.84/1.02  --demod_completeness_check              fast
% 1.84/1.02  --demod_use_ground                      true
% 1.84/1.02  --sup_to_prop_solver                    passive
% 1.84/1.02  --sup_prop_simpl_new                    true
% 1.84/1.02  --sup_prop_simpl_given                  true
% 1.84/1.02  --sup_fun_splitting                     false
% 1.84/1.02  --sup_smt_interval                      50000
% 1.84/1.02  
% 1.84/1.02  ------ Superposition Simplification Setup
% 1.84/1.02  
% 1.84/1.02  --sup_indices_passive                   []
% 1.84/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.84/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.84/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.84/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 1.84/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.84/1.02  --sup_full_bw                           [BwDemod]
% 1.84/1.02  --sup_immed_triv                        [TrivRules]
% 1.84/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.84/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.84/1.02  --sup_immed_bw_main                     []
% 1.84/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.84/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 1.84/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.84/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.84/1.02  
% 1.84/1.02  ------ Combination Options
% 1.84/1.02  
% 1.84/1.02  --comb_res_mult                         3
% 1.84/1.02  --comb_sup_mult                         2
% 1.84/1.02  --comb_inst_mult                        10
% 1.84/1.02  
% 1.84/1.02  ------ Debug Options
% 1.84/1.02  
% 1.84/1.02  --dbg_backtrace                         false
% 1.84/1.02  --dbg_dump_prop_clauses                 false
% 1.84/1.02  --dbg_dump_prop_clauses_file            -
% 1.84/1.02  --dbg_out_stat                          false
% 1.84/1.02  ------ Parsing...
% 1.84/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.84/1.02  
% 1.84/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 1.84/1.02  
% 1.84/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.84/1.02  
% 1.84/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.84/1.02  ------ Proving...
% 1.84/1.02  ------ Problem Properties 
% 1.84/1.02  
% 1.84/1.02  
% 1.84/1.02  clauses                                 39
% 1.84/1.02  conjectures                             8
% 1.84/1.02  EPR                                     4
% 1.84/1.02  Horn                                    37
% 1.84/1.02  unary                                   15
% 1.84/1.02  binary                                  10
% 1.84/1.02  lits                                    90
% 1.84/1.02  lits eq                                 43
% 1.84/1.02  fd_pure                                 0
% 1.84/1.02  fd_pseudo                               0
% 1.84/1.02  fd_cond                                 2
% 1.84/1.02  fd_pseudo_cond                          0
% 1.84/1.02  AC symbols                              0
% 1.84/1.02  
% 1.84/1.02  ------ Schedule dynamic 5 is on 
% 1.84/1.02  
% 1.84/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.84/1.02  
% 1.84/1.02  
% 1.84/1.02  ------ 
% 1.84/1.02  Current options:
% 1.84/1.02  ------ 
% 1.84/1.02  
% 1.84/1.02  ------ Input Options
% 1.84/1.02  
% 1.84/1.02  --out_options                           all
% 1.84/1.02  --tptp_safe_out                         true
% 1.84/1.02  --problem_path                          ""
% 1.84/1.02  --include_path                          ""
% 1.84/1.02  --clausifier                            res/vclausify_rel
% 1.84/1.02  --clausifier_options                    --mode clausify
% 1.84/1.02  --stdin                                 false
% 1.84/1.02  --stats_out                             all
% 1.84/1.02  
% 1.84/1.02  ------ General Options
% 1.84/1.02  
% 1.84/1.02  --fof                                   false
% 1.84/1.02  --time_out_real                         305.
% 1.84/1.02  --time_out_virtual                      -1.
% 1.84/1.02  --symbol_type_check                     false
% 1.84/1.02  --clausify_out                          false
% 1.84/1.02  --sig_cnt_out                           false
% 1.84/1.02  --trig_cnt_out                          false
% 1.84/1.02  --trig_cnt_out_tolerance                1.
% 1.84/1.02  --trig_cnt_out_sk_spl                   false
% 1.84/1.02  --abstr_cl_out                          false
% 1.84/1.02  
% 1.84/1.02  ------ Global Options
% 1.84/1.02  
% 1.84/1.02  --schedule                              default
% 1.84/1.02  --add_important_lit                     false
% 1.84/1.02  --prop_solver_per_cl                    1000
% 1.84/1.02  --min_unsat_core                        false
% 1.84/1.02  --soft_assumptions                      false
% 1.84/1.02  --soft_lemma_size                       3
% 1.84/1.02  --prop_impl_unit_size                   0
% 1.84/1.02  --prop_impl_unit                        []
% 1.84/1.02  --share_sel_clauses                     true
% 1.84/1.02  --reset_solvers                         false
% 1.84/1.02  --bc_imp_inh                            [conj_cone]
% 1.84/1.02  --conj_cone_tolerance                   3.
% 1.84/1.02  --extra_neg_conj                        none
% 1.84/1.02  --large_theory_mode                     true
% 1.84/1.02  --prolific_symb_bound                   200
% 1.84/1.02  --lt_threshold                          2000
% 1.84/1.02  --clause_weak_htbl                      true
% 1.84/1.02  --gc_record_bc_elim                     false
% 1.84/1.02  
% 1.84/1.02  ------ Preprocessing Options
% 1.84/1.02  
% 1.84/1.02  --preprocessing_flag                    true
% 1.84/1.02  --time_out_prep_mult                    0.1
% 1.84/1.02  --splitting_mode                        input
% 1.84/1.02  --splitting_grd                         true
% 1.84/1.02  --splitting_cvd                         false
% 1.84/1.02  --splitting_cvd_svl                     false
% 1.84/1.02  --splitting_nvd                         32
% 1.84/1.02  --sub_typing                            true
% 1.84/1.02  --prep_gs_sim                           true
% 1.84/1.02  --prep_unflatten                        true
% 1.84/1.02  --prep_res_sim                          true
% 1.84/1.02  --prep_upred                            true
% 1.84/1.02  --prep_sem_filter                       exhaustive
% 1.84/1.02  --prep_sem_filter_out                   false
% 1.84/1.02  --pred_elim                             true
% 1.84/1.02  --res_sim_input                         true
% 1.84/1.02  --eq_ax_congr_red                       true
% 1.84/1.02  --pure_diseq_elim                       true
% 1.84/1.02  --brand_transform                       false
% 1.84/1.02  --non_eq_to_eq                          false
% 1.84/1.02  --prep_def_merge                        true
% 1.84/1.02  --prep_def_merge_prop_impl              false
% 1.84/1.02  --prep_def_merge_mbd                    true
% 1.84/1.02  --prep_def_merge_tr_red                 false
% 1.84/1.02  --prep_def_merge_tr_cl                  false
% 1.84/1.02  --smt_preprocessing                     true
% 1.84/1.02  --smt_ac_axioms                         fast
% 1.84/1.02  --preprocessed_out                      false
% 1.84/1.02  --preprocessed_stats                    false
% 1.84/1.02  
% 1.84/1.02  ------ Abstraction refinement Options
% 1.84/1.02  
% 1.84/1.02  --abstr_ref                             []
% 1.84/1.02  --abstr_ref_prep                        false
% 1.84/1.02  --abstr_ref_until_sat                   false
% 1.84/1.02  --abstr_ref_sig_restrict                funpre
% 1.84/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 1.84/1.02  --abstr_ref_under                       []
% 1.84/1.02  
% 1.84/1.02  ------ SAT Options
% 1.84/1.02  
% 1.84/1.02  --sat_mode                              false
% 1.84/1.02  --sat_fm_restart_options                ""
% 1.84/1.02  --sat_gr_def                            false
% 1.84/1.02  --sat_epr_types                         true
% 1.84/1.02  --sat_non_cyclic_types                  false
% 1.84/1.02  --sat_finite_models                     false
% 1.84/1.02  --sat_fm_lemmas                         false
% 1.84/1.02  --sat_fm_prep                           false
% 1.84/1.02  --sat_fm_uc_incr                        true
% 1.84/1.02  --sat_out_model                         small
% 1.84/1.02  --sat_out_clauses                       false
% 1.84/1.02  
% 1.84/1.02  ------ QBF Options
% 1.84/1.02  
% 1.84/1.02  --qbf_mode                              false
% 1.84/1.02  --qbf_elim_univ                         false
% 1.84/1.02  --qbf_dom_inst                          none
% 1.84/1.02  --qbf_dom_pre_inst                      false
% 1.84/1.02  --qbf_sk_in                             false
% 1.84/1.02  --qbf_pred_elim                         true
% 1.84/1.02  --qbf_split                             512
% 1.84/1.02  
% 1.84/1.02  ------ BMC1 Options
% 1.84/1.02  
% 1.84/1.02  --bmc1_incremental                      false
% 1.84/1.02  --bmc1_axioms                           reachable_all
% 1.84/1.02  --bmc1_min_bound                        0
% 1.84/1.02  --bmc1_max_bound                        -1
% 1.84/1.02  --bmc1_max_bound_default                -1
% 1.84/1.02  --bmc1_symbol_reachability              true
% 1.84/1.02  --bmc1_property_lemmas                  false
% 1.84/1.02  --bmc1_k_induction                      false
% 1.84/1.02  --bmc1_non_equiv_states                 false
% 1.84/1.02  --bmc1_deadlock                         false
% 1.84/1.02  --bmc1_ucm                              false
% 1.84/1.02  --bmc1_add_unsat_core                   none
% 1.84/1.02  --bmc1_unsat_core_children              false
% 1.84/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 1.84/1.02  --bmc1_out_stat                         full
% 1.84/1.02  --bmc1_ground_init                      false
% 1.84/1.02  --bmc1_pre_inst_next_state              false
% 1.84/1.02  --bmc1_pre_inst_state                   false
% 1.84/1.02  --bmc1_pre_inst_reach_state             false
% 1.84/1.02  --bmc1_out_unsat_core                   false
% 1.84/1.02  --bmc1_aig_witness_out                  false
% 1.84/1.02  --bmc1_verbose                          false
% 1.84/1.02  --bmc1_dump_clauses_tptp                false
% 1.84/1.02  --bmc1_dump_unsat_core_tptp             false
% 1.84/1.02  --bmc1_dump_file                        -
% 1.84/1.02  --bmc1_ucm_expand_uc_limit              128
% 1.84/1.02  --bmc1_ucm_n_expand_iterations          6
% 1.84/1.02  --bmc1_ucm_extend_mode                  1
% 1.84/1.02  --bmc1_ucm_init_mode                    2
% 1.84/1.02  --bmc1_ucm_cone_mode                    none
% 1.84/1.02  --bmc1_ucm_reduced_relation_type        0
% 1.84/1.02  --bmc1_ucm_relax_model                  4
% 1.84/1.02  --bmc1_ucm_full_tr_after_sat            true
% 1.84/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 1.84/1.02  --bmc1_ucm_layered_model                none
% 1.84/1.02  --bmc1_ucm_max_lemma_size               10
% 1.84/1.02  
% 1.84/1.02  ------ AIG Options
% 1.84/1.02  
% 1.84/1.02  --aig_mode                              false
% 1.84/1.02  
% 1.84/1.02  ------ Instantiation Options
% 1.84/1.02  
% 1.84/1.02  --instantiation_flag                    true
% 1.84/1.02  --inst_sos_flag                         false
% 1.84/1.02  --inst_sos_phase                        true
% 1.84/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.84/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.84/1.02  --inst_lit_sel_side                     none
% 1.84/1.02  --inst_solver_per_active                1400
% 1.84/1.02  --inst_solver_calls_frac                1.
% 1.84/1.02  --inst_passive_queue_type               priority_queues
% 1.84/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.84/1.02  --inst_passive_queues_freq              [25;2]
% 1.84/1.02  --inst_dismatching                      true
% 1.84/1.02  --inst_eager_unprocessed_to_passive     true
% 1.84/1.02  --inst_prop_sim_given                   true
% 1.84/1.02  --inst_prop_sim_new                     false
% 1.84/1.02  --inst_subs_new                         false
% 1.84/1.02  --inst_eq_res_simp                      false
% 1.84/1.02  --inst_subs_given                       false
% 1.84/1.02  --inst_orphan_elimination               true
% 1.84/1.02  --inst_learning_loop_flag               true
% 1.84/1.02  --inst_learning_start                   3000
% 1.84/1.02  --inst_learning_factor                  2
% 1.84/1.02  --inst_start_prop_sim_after_learn       3
% 1.84/1.02  --inst_sel_renew                        solver
% 1.84/1.02  --inst_lit_activity_flag                true
% 1.84/1.02  --inst_restr_to_given                   false
% 1.84/1.02  --inst_activity_threshold               500
% 1.84/1.02  --inst_out_proof                        true
% 1.84/1.02  
% 1.84/1.02  ------ Resolution Options
% 1.84/1.02  
% 1.84/1.02  --resolution_flag                       false
% 1.84/1.02  --res_lit_sel                           adaptive
% 1.84/1.02  --res_lit_sel_side                      none
% 1.84/1.02  --res_ordering                          kbo
% 1.84/1.02  --res_to_prop_solver                    active
% 1.84/1.02  --res_prop_simpl_new                    false
% 1.84/1.02  --res_prop_simpl_given                  true
% 1.84/1.02  --res_passive_queue_type                priority_queues
% 1.84/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.84/1.02  --res_passive_queues_freq               [15;5]
% 1.84/1.02  --res_forward_subs                      full
% 1.84/1.02  --res_backward_subs                     full
% 1.84/1.02  --res_forward_subs_resolution           true
% 1.84/1.02  --res_backward_subs_resolution          true
% 1.84/1.02  --res_orphan_elimination                true
% 1.84/1.02  --res_time_limit                        2.
% 1.84/1.02  --res_out_proof                         true
% 1.84/1.02  
% 1.84/1.02  ------ Superposition Options
% 1.84/1.02  
% 1.84/1.02  --superposition_flag                    true
% 1.84/1.02  --sup_passive_queue_type                priority_queues
% 1.84/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.84/1.02  --sup_passive_queues_freq               [8;1;4]
% 1.84/1.02  --demod_completeness_check              fast
% 1.84/1.02  --demod_use_ground                      true
% 1.84/1.02  --sup_to_prop_solver                    passive
% 1.84/1.02  --sup_prop_simpl_new                    true
% 1.84/1.02  --sup_prop_simpl_given                  true
% 1.84/1.02  --sup_fun_splitting                     false
% 1.84/1.02  --sup_smt_interval                      50000
% 1.84/1.02  
% 1.84/1.02  ------ Superposition Simplification Setup
% 1.84/1.02  
% 1.84/1.02  --sup_indices_passive                   []
% 1.84/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.84/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.84/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.84/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 1.84/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.84/1.02  --sup_full_bw                           [BwDemod]
% 1.84/1.02  --sup_immed_triv                        [TrivRules]
% 1.84/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.84/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.84/1.02  --sup_immed_bw_main                     []
% 1.84/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.84/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 1.84/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.84/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.84/1.02  
% 1.84/1.02  ------ Combination Options
% 1.84/1.02  
% 1.84/1.02  --comb_res_mult                         3
% 1.84/1.02  --comb_sup_mult                         2
% 1.84/1.02  --comb_inst_mult                        10
% 1.84/1.02  
% 1.84/1.02  ------ Debug Options
% 1.84/1.02  
% 1.84/1.02  --dbg_backtrace                         false
% 1.84/1.02  --dbg_dump_prop_clauses                 false
% 1.84/1.02  --dbg_dump_prop_clauses_file            -
% 1.84/1.02  --dbg_out_stat                          false
% 1.84/1.02  
% 1.84/1.02  
% 1.84/1.02  
% 1.84/1.02  
% 1.84/1.02  ------ Proving...
% 1.84/1.02  
% 1.84/1.02  
% 1.84/1.02  % SZS status Theorem for theBenchmark.p
% 1.84/1.02  
% 1.84/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 1.84/1.02  
% 1.84/1.02  fof(f18,conjecture,(
% 1.84/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.84/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.84/1.02  
% 1.84/1.02  fof(f19,negated_conjecture,(
% 1.84/1.02    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.84/1.02    inference(negated_conjecture,[],[f18])).
% 1.84/1.02  
% 1.84/1.02  fof(f43,plain,(
% 1.84/1.02    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.84/1.02    inference(ennf_transformation,[],[f19])).
% 1.84/1.02  
% 1.84/1.02  fof(f44,plain,(
% 1.84/1.02    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.84/1.02    inference(flattening,[],[f43])).
% 1.84/1.02  
% 1.84/1.02  fof(f48,plain,(
% 1.84/1.02    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 1.84/1.02    introduced(choice_axiom,[])).
% 1.84/1.02  
% 1.84/1.02  fof(f47,plain,(
% 1.84/1.02    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.84/1.02    introduced(choice_axiom,[])).
% 1.84/1.02  
% 1.84/1.02  fof(f49,plain,(
% 1.84/1.02    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.84/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f44,f48,f47])).
% 1.84/1.02  
% 1.84/1.02  fof(f84,plain,(
% 1.84/1.02    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.84/1.02    inference(cnf_transformation,[],[f49])).
% 1.84/1.02  
% 1.84/1.02  fof(f8,axiom,(
% 1.84/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.84/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.84/1.02  
% 1.84/1.02  fof(f30,plain,(
% 1.84/1.02    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.84/1.02    inference(ennf_transformation,[],[f8])).
% 1.84/1.02  
% 1.84/1.02  fof(f61,plain,(
% 1.84/1.02    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.84/1.02    inference(cnf_transformation,[],[f30])).
% 1.84/1.02  
% 1.84/1.02  fof(f81,plain,(
% 1.84/1.02    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.84/1.02    inference(cnf_transformation,[],[f49])).
% 1.84/1.02  
% 1.84/1.02  fof(f79,plain,(
% 1.84/1.02    v1_funct_1(sK2)),
% 1.84/1.02    inference(cnf_transformation,[],[f49])).
% 1.84/1.02  
% 1.84/1.02  fof(f5,axiom,(
% 1.84/1.02    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.84/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.84/1.02  
% 1.84/1.02  fof(f24,plain,(
% 1.84/1.02    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.84/1.02    inference(ennf_transformation,[],[f5])).
% 1.84/1.02  
% 1.84/1.02  fof(f25,plain,(
% 1.84/1.02    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.84/1.02    inference(flattening,[],[f24])).
% 1.84/1.02  
% 1.84/1.02  fof(f55,plain,(
% 1.84/1.02    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.84/1.02    inference(cnf_transformation,[],[f25])).
% 1.84/1.02  
% 1.84/1.02  fof(f1,axiom,(
% 1.84/1.02    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2))))),
% 1.84/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.84/1.02  
% 1.84/1.02  fof(f21,plain,(
% 1.84/1.02    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.84/1.02    inference(ennf_transformation,[],[f1])).
% 1.84/1.02  
% 1.84/1.02  fof(f50,plain,(
% 1.84/1.02    ( ! [X2,X0,X1] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.84/1.02    inference(cnf_transformation,[],[f21])).
% 1.84/1.02  
% 1.84/1.02  fof(f80,plain,(
% 1.84/1.02    v1_funct_2(sK2,sK0,sK1)),
% 1.84/1.02    inference(cnf_transformation,[],[f49])).
% 1.84/1.02  
% 1.84/1.02  fof(f17,axiom,(
% 1.84/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 1.84/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.84/1.02  
% 1.84/1.02  fof(f41,plain,(
% 1.84/1.02    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.84/1.02    inference(ennf_transformation,[],[f17])).
% 1.84/1.02  
% 1.84/1.02  fof(f42,plain,(
% 1.84/1.02    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.84/1.02    inference(flattening,[],[f41])).
% 1.84/1.02  
% 1.84/1.02  fof(f78,plain,(
% 1.84/1.02    ( ! [X2,X0,X1] : (k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.84/1.02    inference(cnf_transformation,[],[f42])).
% 1.84/1.02  
% 1.84/1.02  fof(f87,plain,(
% 1.84/1.02    v2_funct_1(sK2)),
% 1.84/1.02    inference(cnf_transformation,[],[f49])).
% 1.84/1.02  
% 1.84/1.02  fof(f85,plain,(
% 1.84/1.02    k2_relset_1(sK0,sK1,sK2) = sK1),
% 1.84/1.02    inference(cnf_transformation,[],[f49])).
% 1.84/1.02  
% 1.84/1.02  fof(f89,plain,(
% 1.84/1.02    k1_xboole_0 != sK1),
% 1.84/1.02    inference(cnf_transformation,[],[f49])).
% 1.84/1.02  
% 1.84/1.02  fof(f9,axiom,(
% 1.84/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.84/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.84/1.02  
% 1.84/1.02  fof(f31,plain,(
% 1.84/1.02    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.84/1.02    inference(ennf_transformation,[],[f9])).
% 1.84/1.02  
% 1.84/1.02  fof(f62,plain,(
% 1.84/1.02    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.84/1.02    inference(cnf_transformation,[],[f31])).
% 1.84/1.02  
% 1.84/1.02  fof(f12,axiom,(
% 1.84/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.84/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.84/1.02  
% 1.84/1.02  fof(f35,plain,(
% 1.84/1.02    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.84/1.02    inference(ennf_transformation,[],[f12])).
% 1.84/1.02  
% 1.84/1.02  fof(f36,plain,(
% 1.84/1.02    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.84/1.02    inference(flattening,[],[f35])).
% 1.84/1.02  
% 1.84/1.02  fof(f46,plain,(
% 1.84/1.02    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.84/1.02    inference(nnf_transformation,[],[f36])).
% 1.84/1.02  
% 1.84/1.02  fof(f66,plain,(
% 1.84/1.02    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.84/1.02    inference(cnf_transformation,[],[f46])).
% 1.84/1.02  
% 1.84/1.02  fof(f83,plain,(
% 1.84/1.02    v1_funct_2(sK3,sK1,sK0)),
% 1.84/1.02    inference(cnf_transformation,[],[f49])).
% 1.84/1.02  
% 1.84/1.02  fof(f88,plain,(
% 1.84/1.02    k1_xboole_0 != sK0),
% 1.84/1.02    inference(cnf_transformation,[],[f49])).
% 1.84/1.02  
% 1.84/1.02  fof(f3,axiom,(
% 1.84/1.02    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 1.84/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.84/1.02  
% 1.84/1.02  fof(f22,plain,(
% 1.84/1.02    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 1.84/1.02    inference(ennf_transformation,[],[f3])).
% 1.84/1.02  
% 1.84/1.02  fof(f53,plain,(
% 1.84/1.02    ( ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 1.84/1.02    inference(cnf_transformation,[],[f22])).
% 1.84/1.02  
% 1.84/1.02  fof(f16,axiom,(
% 1.84/1.02    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.84/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.84/1.02  
% 1.84/1.02  fof(f76,plain,(
% 1.84/1.02    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.84/1.02    inference(cnf_transformation,[],[f16])).
% 1.84/1.02  
% 1.84/1.02  fof(f93,plain,(
% 1.84/1.02    ( ! [X0] : (k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 1.84/1.02    inference(definition_unfolding,[],[f53,f76])).
% 1.84/1.02  
% 1.84/1.02  fof(f4,axiom,(
% 1.84/1.02    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 1.84/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.84/1.02  
% 1.84/1.02  fof(f23,plain,(
% 1.84/1.02    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 1.84/1.02    inference(ennf_transformation,[],[f4])).
% 1.84/1.02  
% 1.84/1.02  fof(f54,plain,(
% 1.84/1.02    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 1.84/1.02    inference(cnf_transformation,[],[f23])).
% 1.84/1.02  
% 1.84/1.02  fof(f94,plain,(
% 1.84/1.02    ( ! [X0] : (k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 1.84/1.02    inference(definition_unfolding,[],[f54,f76])).
% 1.84/1.02  
% 1.84/1.02  fof(f7,axiom,(
% 1.84/1.02    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 1.84/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.84/1.02  
% 1.84/1.02  fof(f28,plain,(
% 1.84/1.02    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.84/1.02    inference(ennf_transformation,[],[f7])).
% 1.84/1.02  
% 1.84/1.02  fof(f29,plain,(
% 1.84/1.02    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.84/1.02    inference(flattening,[],[f28])).
% 1.84/1.02  
% 1.84/1.02  fof(f60,plain,(
% 1.84/1.02    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.84/1.02    inference(cnf_transformation,[],[f29])).
% 1.84/1.02  
% 1.84/1.02  fof(f77,plain,(
% 1.84/1.02    ( ! [X2,X0,X1] : (k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.84/1.02    inference(cnf_transformation,[],[f42])).
% 1.84/1.02  
% 1.84/1.02  fof(f2,axiom,(
% 1.84/1.02    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.84/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.84/1.02  
% 1.84/1.02  fof(f52,plain,(
% 1.84/1.02    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.84/1.02    inference(cnf_transformation,[],[f2])).
% 1.84/1.02  
% 1.84/1.02  fof(f91,plain,(
% 1.84/1.02    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 1.84/1.02    inference(definition_unfolding,[],[f52,f76])).
% 1.84/1.02  
% 1.84/1.02  fof(f6,axiom,(
% 1.84/1.02    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 1.84/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.84/1.02  
% 1.84/1.02  fof(f26,plain,(
% 1.84/1.02    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.84/1.02    inference(ennf_transformation,[],[f6])).
% 1.84/1.02  
% 1.84/1.02  fof(f27,plain,(
% 1.84/1.02    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.84/1.02    inference(flattening,[],[f26])).
% 1.84/1.02  
% 1.84/1.02  fof(f58,plain,(
% 1.84/1.02    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.84/1.02    inference(cnf_transformation,[],[f27])).
% 1.84/1.02  
% 1.84/1.02  fof(f13,axiom,(
% 1.84/1.02    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.84/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.84/1.02  
% 1.84/1.02  fof(f37,plain,(
% 1.84/1.02    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.84/1.02    inference(ennf_transformation,[],[f13])).
% 1.84/1.02  
% 1.84/1.02  fof(f38,plain,(
% 1.84/1.02    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.84/1.02    inference(flattening,[],[f37])).
% 1.84/1.02  
% 1.84/1.02  fof(f73,plain,(
% 1.84/1.02    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.84/1.02    inference(cnf_transformation,[],[f38])).
% 1.84/1.02  
% 1.84/1.02  fof(f11,axiom,(
% 1.84/1.02    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.84/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.84/1.02  
% 1.84/1.02  fof(f33,plain,(
% 1.84/1.02    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.84/1.02    inference(ennf_transformation,[],[f11])).
% 1.84/1.02  
% 1.84/1.02  fof(f34,plain,(
% 1.84/1.02    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.84/1.02    inference(flattening,[],[f33])).
% 1.84/1.02  
% 1.84/1.02  fof(f45,plain,(
% 1.84/1.02    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.84/1.02    inference(nnf_transformation,[],[f34])).
% 1.84/1.02  
% 1.84/1.02  fof(f64,plain,(
% 1.84/1.02    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.84/1.02    inference(cnf_transformation,[],[f45])).
% 1.84/1.02  
% 1.84/1.02  fof(f86,plain,(
% 1.84/1.02    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.84/1.02    inference(cnf_transformation,[],[f49])).
% 1.84/1.02  
% 1.84/1.02  fof(f14,axiom,(
% 1.84/1.02    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 1.84/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.84/1.02  
% 1.84/1.02  fof(f20,plain,(
% 1.84/1.02    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.84/1.02    inference(pure_predicate_removal,[],[f14])).
% 1.84/1.02  
% 1.84/1.02  fof(f74,plain,(
% 1.84/1.02    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.84/1.02    inference(cnf_transformation,[],[f20])).
% 1.84/1.02  
% 1.84/1.02  fof(f82,plain,(
% 1.84/1.02    v1_funct_1(sK3)),
% 1.84/1.02    inference(cnf_transformation,[],[f49])).
% 1.84/1.02  
% 1.84/1.02  fof(f15,axiom,(
% 1.84/1.02    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 1.84/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.84/1.02  
% 1.84/1.02  fof(f39,plain,(
% 1.84/1.02    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.84/1.02    inference(ennf_transformation,[],[f15])).
% 1.84/1.02  
% 1.84/1.02  fof(f40,plain,(
% 1.84/1.02    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.84/1.02    inference(flattening,[],[f39])).
% 1.84/1.02  
% 1.84/1.02  fof(f75,plain,(
% 1.84/1.02    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.84/1.02    inference(cnf_transformation,[],[f40])).
% 1.84/1.02  
% 1.84/1.02  fof(f90,plain,(
% 1.84/1.02    k2_funct_1(sK2) != sK3),
% 1.84/1.02    inference(cnf_transformation,[],[f49])).
% 1.84/1.02  
% 1.84/1.02  cnf(c_34,negated_conjecture,
% 1.84/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 1.84/1.02      inference(cnf_transformation,[],[f84]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_1529,plain,
% 1.84/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 1.84/1.02      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_11,plain,
% 1.84/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.84/1.02      | v1_relat_1(X0) ),
% 1.84/1.02      inference(cnf_transformation,[],[f61]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_1536,plain,
% 1.84/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 1.84/1.02      | v1_relat_1(X0) = iProver_top ),
% 1.84/1.02      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_3348,plain,
% 1.84/1.02      ( v1_relat_1(sK3) = iProver_top ),
% 1.84/1.02      inference(superposition,[status(thm)],[c_1529,c_1536]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_37,negated_conjecture,
% 1.84/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 1.84/1.02      inference(cnf_transformation,[],[f81]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_1527,plain,
% 1.84/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 1.84/1.02      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_3349,plain,
% 1.84/1.02      ( v1_relat_1(sK2) = iProver_top ),
% 1.84/1.02      inference(superposition,[status(thm)],[c_1527,c_1536]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_39,negated_conjecture,
% 1.84/1.02      ( v1_funct_1(sK2) ),
% 1.84/1.02      inference(cnf_transformation,[],[f79]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_1526,plain,
% 1.84/1.02      ( v1_funct_1(sK2) = iProver_top ),
% 1.84/1.02      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_6,plain,
% 1.84/1.02      ( ~ v1_funct_1(X0)
% 1.84/1.02      | ~ v1_relat_1(X0)
% 1.84/1.02      | v1_relat_1(k2_funct_1(X0)) ),
% 1.84/1.02      inference(cnf_transformation,[],[f55]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_1537,plain,
% 1.84/1.02      ( v1_funct_1(X0) != iProver_top
% 1.84/1.02      | v1_relat_1(X0) != iProver_top
% 1.84/1.02      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 1.84/1.02      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_0,plain,
% 1.84/1.02      ( ~ v1_relat_1(X0)
% 1.84/1.02      | ~ v1_relat_1(X1)
% 1.84/1.02      | ~ v1_relat_1(X2)
% 1.84/1.02      | k5_relat_1(k5_relat_1(X2,X1),X0) = k5_relat_1(X2,k5_relat_1(X1,X0)) ),
% 1.84/1.02      inference(cnf_transformation,[],[f50]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_1541,plain,
% 1.84/1.02      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
% 1.84/1.02      | v1_relat_1(X2) != iProver_top
% 1.84/1.02      | v1_relat_1(X1) != iProver_top
% 1.84/1.02      | v1_relat_1(X0) != iProver_top ),
% 1.84/1.02      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_4777,plain,
% 1.84/1.02      ( k5_relat_1(k2_funct_1(X0),k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(k2_funct_1(X0),X1),X2)
% 1.84/1.02      | v1_funct_1(X0) != iProver_top
% 1.84/1.02      | v1_relat_1(X0) != iProver_top
% 1.84/1.02      | v1_relat_1(X1) != iProver_top
% 1.84/1.02      | v1_relat_1(X2) != iProver_top ),
% 1.84/1.02      inference(superposition,[status(thm)],[c_1537,c_1541]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_9768,plain,
% 1.84/1.02      ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1))
% 1.84/1.02      | v1_relat_1(X0) != iProver_top
% 1.84/1.02      | v1_relat_1(X1) != iProver_top
% 1.84/1.02      | v1_relat_1(sK2) != iProver_top ),
% 1.84/1.02      inference(superposition,[status(thm)],[c_1526,c_4777]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_42,plain,
% 1.84/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 1.84/1.02      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_1821,plain,
% 1.84/1.02      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 1.84/1.02      | v1_relat_1(sK2) ),
% 1.84/1.02      inference(instantiation,[status(thm)],[c_11]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_1822,plain,
% 1.84/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 1.84/1.02      | v1_relat_1(sK2) = iProver_top ),
% 1.84/1.02      inference(predicate_to_equality,[status(thm)],[c_1821]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_10891,plain,
% 1.84/1.02      ( v1_relat_1(X1) != iProver_top
% 1.84/1.02      | v1_relat_1(X0) != iProver_top
% 1.84/1.02      | k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1)) ),
% 1.84/1.02      inference(global_propositional_subsumption,
% 1.84/1.02                [status(thm)],
% 1.84/1.02                [c_9768,c_42,c_1822]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_10892,plain,
% 1.84/1.02      ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1))
% 1.84/1.02      | v1_relat_1(X0) != iProver_top
% 1.84/1.02      | v1_relat_1(X1) != iProver_top ),
% 1.84/1.02      inference(renaming,[status(thm)],[c_10891]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_10901,plain,
% 1.84/1.02      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),X0)
% 1.84/1.02      | v1_relat_1(X0) != iProver_top ),
% 1.84/1.02      inference(superposition,[status(thm)],[c_3349,c_10892]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_38,negated_conjecture,
% 1.84/1.02      ( v1_funct_2(sK2,sK0,sK1) ),
% 1.84/1.02      inference(cnf_transformation,[],[f80]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_26,plain,
% 1.84/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 1.84/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.84/1.02      | ~ v2_funct_1(X0)
% 1.84/1.02      | ~ v1_funct_1(X0)
% 1.84/1.02      | k2_relset_1(X1,X2,X0) != X2
% 1.84/1.02      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
% 1.84/1.02      | k1_xboole_0 = X2 ),
% 1.84/1.02      inference(cnf_transformation,[],[f78]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_31,negated_conjecture,
% 1.84/1.02      ( v2_funct_1(sK2) ),
% 1.84/1.02      inference(cnf_transformation,[],[f87]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_436,plain,
% 1.84/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 1.84/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.84/1.02      | ~ v1_funct_1(X0)
% 1.84/1.02      | k2_relset_1(X1,X2,X0) != X2
% 1.84/1.02      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
% 1.84/1.02      | sK2 != X0
% 1.84/1.02      | k1_xboole_0 = X2 ),
% 1.84/1.02      inference(resolution_lifted,[status(thm)],[c_26,c_31]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_437,plain,
% 1.84/1.02      ( ~ v1_funct_2(sK2,X0,X1)
% 1.84/1.02      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.84/1.02      | ~ v1_funct_1(sK2)
% 1.84/1.02      | k2_relset_1(X0,X1,sK2) != X1
% 1.84/1.02      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(X1)
% 1.84/1.02      | k1_xboole_0 = X1 ),
% 1.84/1.02      inference(unflattening,[status(thm)],[c_436]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_441,plain,
% 1.84/1.02      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.84/1.02      | ~ v1_funct_2(sK2,X0,X1)
% 1.84/1.02      | k2_relset_1(X0,X1,sK2) != X1
% 1.84/1.02      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(X1)
% 1.84/1.02      | k1_xboole_0 = X1 ),
% 1.84/1.02      inference(global_propositional_subsumption,
% 1.84/1.02                [status(thm)],
% 1.84/1.02                [c_437,c_39]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_442,plain,
% 1.84/1.02      ( ~ v1_funct_2(sK2,X0,X1)
% 1.84/1.02      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.84/1.02      | k2_relset_1(X0,X1,sK2) != X1
% 1.84/1.02      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(X1)
% 1.84/1.02      | k1_xboole_0 = X1 ),
% 1.84/1.02      inference(renaming,[status(thm)],[c_441]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_759,plain,
% 1.84/1.02      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.84/1.02      | k2_relset_1(X0,X1,sK2) != X1
% 1.84/1.02      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(X1)
% 1.84/1.02      | sK0 != X0
% 1.84/1.02      | sK1 != X1
% 1.84/1.02      | sK2 != sK2
% 1.84/1.02      | k1_xboole_0 = X1 ),
% 1.84/1.02      inference(resolution_lifted,[status(thm)],[c_38,c_442]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_760,plain,
% 1.84/1.02      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 1.84/1.02      | k2_relset_1(sK0,sK1,sK2) != sK1
% 1.84/1.02      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 1.84/1.02      | k1_xboole_0 = sK1 ),
% 1.84/1.02      inference(unflattening,[status(thm)],[c_759]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_33,negated_conjecture,
% 1.84/1.02      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 1.84/1.02      inference(cnf_transformation,[],[f85]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_29,negated_conjecture,
% 1.84/1.02      ( k1_xboole_0 != sK1 ),
% 1.84/1.02      inference(cnf_transformation,[],[f89]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_762,plain,
% 1.84/1.02      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
% 1.84/1.02      inference(global_propositional_subsumption,
% 1.84/1.02                [status(thm)],
% 1.84/1.02                [c_760,c_37,c_33,c_29]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_10932,plain,
% 1.84/1.02      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k6_partfun1(sK1),X0)
% 1.84/1.02      | v1_relat_1(X0) != iProver_top ),
% 1.84/1.02      inference(light_normalisation,[status(thm)],[c_10901,c_762]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_10966,plain,
% 1.84/1.02      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
% 1.84/1.02      inference(superposition,[status(thm)],[c_3348,c_10932]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_12,plain,
% 1.84/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.84/1.02      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 1.84/1.02      inference(cnf_transformation,[],[f62]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_1535,plain,
% 1.84/1.02      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 1.84/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 1.84/1.02      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_4138,plain,
% 1.84/1.02      ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
% 1.84/1.02      inference(superposition,[status(thm)],[c_1529,c_1535]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_21,plain,
% 1.84/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 1.84/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.84/1.02      | k1_relset_1(X1,X2,X0) = X1
% 1.84/1.02      | k1_xboole_0 = X2 ),
% 1.84/1.02      inference(cnf_transformation,[],[f66]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_35,negated_conjecture,
% 1.84/1.02      ( v1_funct_2(sK3,sK1,sK0) ),
% 1.84/1.02      inference(cnf_transformation,[],[f83]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_665,plain,
% 1.84/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.84/1.02      | k1_relset_1(X1,X2,X0) = X1
% 1.84/1.02      | sK0 != X2
% 1.84/1.02      | sK1 != X1
% 1.84/1.02      | sK3 != X0
% 1.84/1.02      | k1_xboole_0 = X2 ),
% 1.84/1.02      inference(resolution_lifted,[status(thm)],[c_21,c_35]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_666,plain,
% 1.84/1.02      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 1.84/1.02      | k1_relset_1(sK1,sK0,sK3) = sK1
% 1.84/1.02      | k1_xboole_0 = sK0 ),
% 1.84/1.02      inference(unflattening,[status(thm)],[c_665]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_30,negated_conjecture,
% 1.84/1.02      ( k1_xboole_0 != sK0 ),
% 1.84/1.02      inference(cnf_transformation,[],[f88]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_668,plain,
% 1.84/1.02      ( k1_relset_1(sK1,sK0,sK3) = sK1 ),
% 1.84/1.02      inference(global_propositional_subsumption,
% 1.84/1.02                [status(thm)],
% 1.84/1.02                [c_666,c_34,c_30]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_4143,plain,
% 1.84/1.02      ( k1_relat_1(sK3) = sK1 ),
% 1.84/1.02      inference(light_normalisation,[status(thm)],[c_4138,c_668]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_3,plain,
% 1.84/1.02      ( ~ v1_relat_1(X0)
% 1.84/1.02      | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 ),
% 1.84/1.02      inference(cnf_transformation,[],[f93]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_1540,plain,
% 1.84/1.02      ( k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0
% 1.84/1.02      | v1_relat_1(X0) != iProver_top ),
% 1.84/1.02      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_3415,plain,
% 1.84/1.02      ( k5_relat_1(k6_partfun1(k1_relat_1(sK3)),sK3) = sK3 ),
% 1.84/1.02      inference(superposition,[status(thm)],[c_3348,c_1540]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_4150,plain,
% 1.84/1.02      ( k5_relat_1(k6_partfun1(sK1),sK3) = sK3 ),
% 1.84/1.02      inference(demodulation,[status(thm)],[c_4143,c_3415]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_4,plain,
% 1.84/1.02      ( ~ v1_relat_1(X0)
% 1.84/1.02      | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ),
% 1.84/1.02      inference(cnf_transformation,[],[f94]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_1539,plain,
% 1.84/1.02      ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
% 1.84/1.02      | v1_relat_1(X0) != iProver_top ),
% 1.84/1.02      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_4526,plain,
% 1.84/1.02      ( k5_relat_1(k2_funct_1(X0),k6_partfun1(k2_relat_1(k2_funct_1(X0)))) = k2_funct_1(X0)
% 1.84/1.02      | v1_funct_1(X0) != iProver_top
% 1.84/1.02      | v1_relat_1(X0) != iProver_top ),
% 1.84/1.02      inference(superposition,[status(thm)],[c_1537,c_1539]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_6314,plain,
% 1.84/1.02      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(k2_relat_1(k2_funct_1(sK2)))) = k2_funct_1(sK2)
% 1.84/1.02      | v1_relat_1(sK2) != iProver_top ),
% 1.84/1.02      inference(superposition,[status(thm)],[c_1526,c_4526]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_9,plain,
% 1.84/1.02      ( ~ v2_funct_1(X0)
% 1.84/1.02      | ~ v1_funct_1(X0)
% 1.84/1.02      | ~ v1_relat_1(X0)
% 1.84/1.02      | k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) ),
% 1.84/1.02      inference(cnf_transformation,[],[f60]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_477,plain,
% 1.84/1.02      ( ~ v1_funct_1(X0)
% 1.84/1.02      | ~ v1_relat_1(X0)
% 1.84/1.02      | k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
% 1.84/1.02      | sK2 != X0 ),
% 1.84/1.02      inference(resolution_lifted,[status(thm)],[c_9,c_31]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_478,plain,
% 1.84/1.02      ( ~ v1_funct_1(sK2)
% 1.84/1.02      | ~ v1_relat_1(sK2)
% 1.84/1.02      | k2_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) = k1_relat_1(sK2) ),
% 1.84/1.02      inference(unflattening,[status(thm)],[c_477]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_480,plain,
% 1.84/1.02      ( ~ v1_relat_1(sK2)
% 1.84/1.02      | k2_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) = k1_relat_1(sK2) ),
% 1.84/1.02      inference(global_propositional_subsumption,
% 1.84/1.02                [status(thm)],
% 1.84/1.02                [c_478,c_39]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_1523,plain,
% 1.84/1.02      ( k2_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) = k1_relat_1(sK2)
% 1.84/1.02      | v1_relat_1(sK2) != iProver_top ),
% 1.84/1.02      inference(predicate_to_equality,[status(thm)],[c_480]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_27,plain,
% 1.84/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 1.84/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.84/1.02      | ~ v2_funct_1(X0)
% 1.84/1.02      | ~ v1_funct_1(X0)
% 1.84/1.02      | k2_relset_1(X1,X2,X0) != X2
% 1.84/1.02      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 1.84/1.02      | k1_xboole_0 = X2 ),
% 1.84/1.02      inference(cnf_transformation,[],[f77]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_409,plain,
% 1.84/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 1.84/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.84/1.02      | ~ v1_funct_1(X0)
% 1.84/1.02      | k2_relset_1(X1,X2,X0) != X2
% 1.84/1.02      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 1.84/1.02      | sK2 != X0
% 1.84/1.02      | k1_xboole_0 = X2 ),
% 1.84/1.02      inference(resolution_lifted,[status(thm)],[c_27,c_31]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_410,plain,
% 1.84/1.02      ( ~ v1_funct_2(sK2,X0,X1)
% 1.84/1.02      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.84/1.02      | ~ v1_funct_1(sK2)
% 1.84/1.02      | k2_relset_1(X0,X1,sK2) != X1
% 1.84/1.02      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
% 1.84/1.02      | k1_xboole_0 = X1 ),
% 1.84/1.02      inference(unflattening,[status(thm)],[c_409]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_414,plain,
% 1.84/1.02      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.84/1.02      | ~ v1_funct_2(sK2,X0,X1)
% 1.84/1.02      | k2_relset_1(X0,X1,sK2) != X1
% 1.84/1.02      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
% 1.84/1.02      | k1_xboole_0 = X1 ),
% 1.84/1.02      inference(global_propositional_subsumption,
% 1.84/1.02                [status(thm)],
% 1.84/1.02                [c_410,c_39]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_415,plain,
% 1.84/1.02      ( ~ v1_funct_2(sK2,X0,X1)
% 1.84/1.02      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.84/1.02      | k2_relset_1(X0,X1,sK2) != X1
% 1.84/1.02      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
% 1.84/1.02      | k1_xboole_0 = X1 ),
% 1.84/1.02      inference(renaming,[status(thm)],[c_414]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_767,plain,
% 1.84/1.02      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.84/1.02      | k2_relset_1(X0,X1,sK2) != X1
% 1.84/1.02      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
% 1.84/1.02      | sK0 != X0
% 1.84/1.02      | sK1 != X1
% 1.84/1.02      | sK2 != sK2
% 1.84/1.02      | k1_xboole_0 = X1 ),
% 1.84/1.02      inference(resolution_lifted,[status(thm)],[c_38,c_415]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_768,plain,
% 1.84/1.02      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 1.84/1.02      | k2_relset_1(sK0,sK1,sK2) != sK1
% 1.84/1.02      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
% 1.84/1.02      | k1_xboole_0 = sK1 ),
% 1.84/1.02      inference(unflattening,[status(thm)],[c_767]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_770,plain,
% 1.84/1.02      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
% 1.84/1.02      inference(global_propositional_subsumption,
% 1.84/1.02                [status(thm)],
% 1.84/1.02                [c_768,c_37,c_33,c_29]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_1588,plain,
% 1.84/1.02      ( k2_relat_1(k6_partfun1(sK0)) = k1_relat_1(sK2)
% 1.84/1.02      | v1_relat_1(sK2) != iProver_top ),
% 1.84/1.02      inference(light_normalisation,[status(thm)],[c_1523,c_770]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_1,plain,
% 1.84/1.02      ( k2_relat_1(k6_partfun1(X0)) = X0 ),
% 1.84/1.02      inference(cnf_transformation,[],[f91]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_1589,plain,
% 1.84/1.02      ( k1_relat_1(sK2) = sK0 | v1_relat_1(sK2) != iProver_top ),
% 1.84/1.02      inference(demodulation,[status(thm)],[c_1588,c_1]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_1737,plain,
% 1.84/1.02      ( ~ v1_relat_1(sK2) | k1_relat_1(sK2) = sK0 ),
% 1.84/1.02      inference(predicate_to_equality_rev,[status(thm)],[c_1589]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_2733,plain,
% 1.84/1.02      ( k1_relat_1(sK2) = sK0 ),
% 1.84/1.02      inference(global_propositional_subsumption,
% 1.84/1.02                [status(thm)],
% 1.84/1.02                [c_1589,c_37,c_1737,c_1821]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_7,plain,
% 1.84/1.02      ( ~ v2_funct_1(X0)
% 1.84/1.02      | ~ v1_funct_1(X0)
% 1.84/1.02      | ~ v1_relat_1(X0)
% 1.84/1.02      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 1.84/1.02      inference(cnf_transformation,[],[f58]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_505,plain,
% 1.84/1.02      ( ~ v1_funct_1(X0)
% 1.84/1.02      | ~ v1_relat_1(X0)
% 1.84/1.02      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 1.84/1.02      | sK2 != X0 ),
% 1.84/1.02      inference(resolution_lifted,[status(thm)],[c_7,c_31]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_506,plain,
% 1.84/1.02      ( ~ v1_funct_1(sK2)
% 1.84/1.02      | ~ v1_relat_1(sK2)
% 1.84/1.02      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 1.84/1.02      inference(unflattening,[status(thm)],[c_505]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_508,plain,
% 1.84/1.02      ( ~ v1_relat_1(sK2)
% 1.84/1.02      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 1.84/1.02      inference(global_propositional_subsumption,
% 1.84/1.02                [status(thm)],
% 1.84/1.02                [c_506,c_39]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_1521,plain,
% 1.84/1.02      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 1.84/1.02      | v1_relat_1(sK2) != iProver_top ),
% 1.84/1.02      inference(predicate_to_equality,[status(thm)],[c_508]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_2165,plain,
% 1.84/1.02      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 1.84/1.02      inference(global_propositional_subsumption,
% 1.84/1.02                [status(thm)],
% 1.84/1.02                [c_1521,c_39,c_37,c_506,c_1821]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_2736,plain,
% 1.84/1.02      ( k2_relat_1(k2_funct_1(sK2)) = sK0 ),
% 1.84/1.02      inference(demodulation,[status(thm)],[c_2733,c_2165]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_6317,plain,
% 1.84/1.02      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k2_funct_1(sK2)
% 1.84/1.02      | v1_relat_1(sK2) != iProver_top ),
% 1.84/1.02      inference(light_normalisation,[status(thm)],[c_6314,c_2736]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_8154,plain,
% 1.84/1.02      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k2_funct_1(sK2) ),
% 1.84/1.02      inference(global_propositional_subsumption,
% 1.84/1.02                [status(thm)],
% 1.84/1.02                [c_6317,c_42,c_1822]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_22,plain,
% 1.84/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.84/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 1.84/1.02      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 1.84/1.02      | ~ v1_funct_1(X0)
% 1.84/1.02      | ~ v1_funct_1(X3) ),
% 1.84/1.02      inference(cnf_transformation,[],[f73]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_1533,plain,
% 1.84/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 1.84/1.02      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 1.84/1.02      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 1.84/1.02      | v1_funct_1(X0) != iProver_top
% 1.84/1.02      | v1_funct_1(X3) != iProver_top ),
% 1.84/1.02      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_15,plain,
% 1.84/1.02      ( ~ r2_relset_1(X0,X1,X2,X3)
% 1.84/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.84/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.84/1.02      | X3 = X2 ),
% 1.84/1.02      inference(cnf_transformation,[],[f64]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_32,negated_conjecture,
% 1.84/1.02      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 1.84/1.02      inference(cnf_transformation,[],[f86]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_393,plain,
% 1.84/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.84/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.84/1.02      | X3 = X0
% 1.84/1.02      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 1.84/1.02      | k6_partfun1(sK0) != X3
% 1.84/1.02      | sK0 != X2
% 1.84/1.02      | sK0 != X1 ),
% 1.84/1.02      inference(resolution_lifted,[status(thm)],[c_15,c_32]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_394,plain,
% 1.84/1.02      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 1.84/1.02      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 1.84/1.02      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 1.84/1.02      inference(unflattening,[status(thm)],[c_393]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_24,plain,
% 1.84/1.02      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 1.84/1.02      inference(cnf_transformation,[],[f74]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_402,plain,
% 1.84/1.02      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 1.84/1.02      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 1.84/1.02      inference(forward_subsumption_resolution,
% 1.84/1.02                [status(thm)],
% 1.84/1.02                [c_394,c_24]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_1525,plain,
% 1.84/1.02      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 1.84/1.02      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 1.84/1.02      inference(predicate_to_equality,[status(thm)],[c_402]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_4383,plain,
% 1.84/1.02      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
% 1.84/1.02      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 1.84/1.02      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 1.84/1.02      | v1_funct_1(sK3) != iProver_top
% 1.84/1.02      | v1_funct_1(sK2) != iProver_top ),
% 1.84/1.02      inference(superposition,[status(thm)],[c_1533,c_1525]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_40,plain,
% 1.84/1.02      ( v1_funct_1(sK2) = iProver_top ),
% 1.84/1.02      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_36,negated_conjecture,
% 1.84/1.02      ( v1_funct_1(sK3) ),
% 1.84/1.02      inference(cnf_transformation,[],[f82]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_43,plain,
% 1.84/1.02      ( v1_funct_1(sK3) = iProver_top ),
% 1.84/1.02      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_45,plain,
% 1.84/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 1.84/1.02      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_8965,plain,
% 1.84/1.02      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
% 1.84/1.02      inference(global_propositional_subsumption,
% 1.84/1.02                [status(thm)],
% 1.84/1.02                [c_4383,c_40,c_42,c_43,c_45]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_25,plain,
% 1.84/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.84/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 1.84/1.02      | ~ v1_funct_1(X0)
% 1.84/1.02      | ~ v1_funct_1(X3)
% 1.84/1.02      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 1.84/1.02      inference(cnf_transformation,[],[f75]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_1530,plain,
% 1.84/1.02      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 1.84/1.02      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 1.84/1.02      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 1.84/1.02      | v1_funct_1(X5) != iProver_top
% 1.84/1.02      | v1_funct_1(X4) != iProver_top ),
% 1.84/1.02      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_5441,plain,
% 1.84/1.02      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 1.84/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 1.84/1.02      | v1_funct_1(X2) != iProver_top
% 1.84/1.02      | v1_funct_1(sK3) != iProver_top ),
% 1.84/1.02      inference(superposition,[status(thm)],[c_1529,c_1530]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_7346,plain,
% 1.84/1.02      ( v1_funct_1(X2) != iProver_top
% 1.84/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 1.84/1.02      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 1.84/1.02      inference(global_propositional_subsumption,
% 1.84/1.02                [status(thm)],
% 1.84/1.02                [c_5441,c_43]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_7347,plain,
% 1.84/1.02      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 1.84/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 1.84/1.02      | v1_funct_1(X2) != iProver_top ),
% 1.84/1.02      inference(renaming,[status(thm)],[c_7346]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_7358,plain,
% 1.84/1.02      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 1.84/1.02      | v1_funct_1(sK2) != iProver_top ),
% 1.84/1.02      inference(superposition,[status(thm)],[c_1527,c_7347]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_1905,plain,
% 1.84/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.84/1.02      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 1.84/1.02      | ~ v1_funct_1(X0)
% 1.84/1.02      | ~ v1_funct_1(sK3)
% 1.84/1.02      | k1_partfun1(X1,X2,X3,X4,X0,sK3) = k5_relat_1(X0,sK3) ),
% 1.84/1.02      inference(instantiation,[status(thm)],[c_25]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_2217,plain,
% 1.84/1.02      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.84/1.02      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 1.84/1.02      | ~ v1_funct_1(sK3)
% 1.84/1.02      | ~ v1_funct_1(sK2)
% 1.84/1.02      | k1_partfun1(X2,X3,X0,X1,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 1.84/1.02      inference(instantiation,[status(thm)],[c_1905]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_2725,plain,
% 1.84/1.02      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 1.84/1.02      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.84/1.02      | ~ v1_funct_1(sK3)
% 1.84/1.02      | ~ v1_funct_1(sK2)
% 1.84/1.02      | k1_partfun1(X0,X1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 1.84/1.02      inference(instantiation,[status(thm)],[c_2217]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_4123,plain,
% 1.84/1.02      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 1.84/1.02      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 1.84/1.02      | ~ v1_funct_1(sK3)
% 1.84/1.02      | ~ v1_funct_1(sK2)
% 1.84/1.02      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 1.84/1.02      inference(instantiation,[status(thm)],[c_2725]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_7640,plain,
% 1.84/1.02      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 1.84/1.02      inference(global_propositional_subsumption,
% 1.84/1.02                [status(thm)],
% 1.84/1.02                [c_7358,c_39,c_37,c_36,c_34,c_4123]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_8968,plain,
% 1.84/1.02      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 1.84/1.02      inference(demodulation,[status(thm)],[c_8965,c_7640]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_10985,plain,
% 1.84/1.02      ( k2_funct_1(sK2) = sK3 ),
% 1.84/1.02      inference(light_normalisation,
% 1.84/1.02                [status(thm)],
% 1.84/1.02                [c_10966,c_4150,c_8154,c_8968]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(c_28,negated_conjecture,
% 1.84/1.02      ( k2_funct_1(sK2) != sK3 ),
% 1.84/1.02      inference(cnf_transformation,[],[f90]) ).
% 1.84/1.02  
% 1.84/1.02  cnf(contradiction,plain,
% 1.84/1.02      ( $false ),
% 1.84/1.02      inference(minisat,[status(thm)],[c_10985,c_28]) ).
% 1.84/1.02  
% 1.84/1.02  
% 1.84/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 1.84/1.02  
% 1.84/1.02  ------                               Statistics
% 1.84/1.02  
% 1.84/1.02  ------ General
% 1.84/1.02  
% 1.84/1.02  abstr_ref_over_cycles:                  0
% 1.84/1.02  abstr_ref_under_cycles:                 0
% 1.84/1.02  gc_basic_clause_elim:                   0
% 1.84/1.02  forced_gc_time:                         0
% 1.84/1.02  parsing_time:                           0.009
% 1.84/1.02  unif_index_cands_time:                  0.
% 1.84/1.02  unif_index_add_time:                    0.
% 1.84/1.02  orderings_time:                         0.
% 1.84/1.02  out_proof_time:                         0.01
% 1.84/1.02  total_time:                             0.329
% 1.84/1.02  num_of_symbols:                         52
% 1.84/1.02  num_of_terms:                           12630
% 1.84/1.02  
% 1.84/1.02  ------ Preprocessing
% 1.84/1.02  
% 1.84/1.02  num_of_splits:                          0
% 1.84/1.02  num_of_split_atoms:                     0
% 1.84/1.02  num_of_reused_defs:                     0
% 1.84/1.02  num_eq_ax_congr_red:                    2
% 1.84/1.02  num_of_sem_filtered_clauses:            1
% 1.84/1.02  num_of_subtypes:                        0
% 1.84/1.02  monotx_restored_types:                  0
% 1.84/1.02  sat_num_of_epr_types:                   0
% 1.84/1.02  sat_num_of_non_cyclic_types:            0
% 1.84/1.02  sat_guarded_non_collapsed_types:        0
% 1.84/1.02  num_pure_diseq_elim:                    0
% 1.84/1.02  simp_replaced_by:                       0
% 1.84/1.02  res_preprocessed:                       188
% 1.84/1.02  prep_upred:                             0
% 1.84/1.02  prep_unflattend:                        72
% 1.84/1.02  smt_new_axioms:                         0
% 1.84/1.02  pred_elim_cands:                        3
% 1.84/1.02  pred_elim:                              3
% 1.84/1.02  pred_elim_cl:                           1
% 1.84/1.02  pred_elim_cycles:                       5
% 1.84/1.02  merged_defs:                            0
% 1.84/1.02  merged_defs_ncl:                        0
% 1.84/1.02  bin_hyper_res:                          0
% 1.84/1.02  prep_cycles:                            4
% 1.84/1.02  pred_elim_time:                         0.012
% 1.84/1.02  splitting_time:                         0.
% 1.84/1.02  sem_filter_time:                        0.
% 1.84/1.02  monotx_time:                            0.001
% 1.84/1.02  subtype_inf_time:                       0.
% 1.84/1.02  
% 1.84/1.02  ------ Problem properties
% 1.84/1.02  
% 1.84/1.02  clauses:                                39
% 1.84/1.02  conjectures:                            8
% 1.84/1.02  epr:                                    4
% 1.84/1.02  horn:                                   37
% 1.84/1.02  ground:                                 23
% 1.84/1.02  unary:                                  15
% 1.84/1.02  binary:                                 10
% 1.84/1.02  lits:                                   90
% 1.84/1.02  lits_eq:                                43
% 1.84/1.02  fd_pure:                                0
% 1.84/1.02  fd_pseudo:                              0
% 1.84/1.02  fd_cond:                                2
% 1.84/1.02  fd_pseudo_cond:                         0
% 1.84/1.02  ac_symbols:                             0
% 1.84/1.02  
% 1.84/1.02  ------ Propositional Solver
% 1.84/1.02  
% 1.84/1.02  prop_solver_calls:                      28
% 1.84/1.02  prop_fast_solver_calls:                 1377
% 1.84/1.02  smt_solver_calls:                       0
% 1.84/1.02  smt_fast_solver_calls:                  0
% 1.84/1.02  prop_num_of_clauses:                    5394
% 1.84/1.02  prop_preprocess_simplified:             11570
% 1.84/1.02  prop_fo_subsumed:                       70
% 1.84/1.02  prop_solver_time:                       0.
% 1.84/1.02  smt_solver_time:                        0.
% 1.84/1.02  smt_fast_solver_time:                   0.
% 1.84/1.02  prop_fast_solver_time:                  0.
% 1.84/1.02  prop_unsat_core_time:                   0.
% 1.84/1.02  
% 1.84/1.02  ------ QBF
% 1.84/1.02  
% 1.84/1.02  qbf_q_res:                              0
% 1.84/1.02  qbf_num_tautologies:                    0
% 1.84/1.02  qbf_prep_cycles:                        0
% 1.84/1.02  
% 1.84/1.02  ------ BMC1
% 1.84/1.02  
% 1.84/1.02  bmc1_current_bound:                     -1
% 1.84/1.02  bmc1_last_solved_bound:                 -1
% 1.84/1.02  bmc1_unsat_core_size:                   -1
% 1.84/1.02  bmc1_unsat_core_parents_size:           -1
% 1.84/1.02  bmc1_merge_next_fun:                    0
% 1.84/1.02  bmc1_unsat_core_clauses_time:           0.
% 1.84/1.02  
% 1.84/1.02  ------ Instantiation
% 1.84/1.02  
% 1.84/1.02  inst_num_of_clauses:                    1473
% 1.84/1.02  inst_num_in_passive:                    397
% 1.84/1.02  inst_num_in_active:                     535
% 1.84/1.02  inst_num_in_unprocessed:                541
% 1.84/1.02  inst_num_of_loops:                      590
% 1.84/1.02  inst_num_of_learning_restarts:          0
% 1.84/1.02  inst_num_moves_active_passive:          54
% 1.84/1.02  inst_lit_activity:                      0
% 1.84/1.02  inst_lit_activity_moves:                2
% 1.84/1.02  inst_num_tautologies:                   0
% 1.84/1.02  inst_num_prop_implied:                  0
% 1.84/1.02  inst_num_existing_simplified:           0
% 1.84/1.02  inst_num_eq_res_simplified:             0
% 1.84/1.02  inst_num_child_elim:                    0
% 1.84/1.02  inst_num_of_dismatching_blockings:      6
% 1.84/1.02  inst_num_of_non_proper_insts:           686
% 1.84/1.02  inst_num_of_duplicates:                 0
% 1.84/1.02  inst_inst_num_from_inst_to_res:         0
% 1.84/1.02  inst_dismatching_checking_time:         0.
% 1.84/1.02  
% 1.84/1.02  ------ Resolution
% 1.84/1.02  
% 1.84/1.02  res_num_of_clauses:                     0
% 1.84/1.02  res_num_in_passive:                     0
% 1.84/1.02  res_num_in_active:                      0
% 1.84/1.02  res_num_of_loops:                       192
% 1.84/1.02  res_forward_subset_subsumed:            20
% 1.84/1.02  res_backward_subset_subsumed:           0
% 1.84/1.02  res_forward_subsumed:                   0
% 1.84/1.02  res_backward_subsumed:                  2
% 1.84/1.02  res_forward_subsumption_resolution:     1
% 1.84/1.02  res_backward_subsumption_resolution:    0
% 1.84/1.02  res_clause_to_clause_subsumption:       625
% 1.84/1.02  res_orphan_elimination:                 0
% 1.84/1.02  res_tautology_del:                      33
% 1.84/1.02  res_num_eq_res_simplified:              0
% 1.84/1.02  res_num_sel_changes:                    0
% 1.84/1.02  res_moves_from_active_to_pass:          0
% 1.84/1.02  
% 1.84/1.02  ------ Superposition
% 1.84/1.02  
% 1.84/1.02  sup_time_total:                         0.
% 1.84/1.02  sup_time_generating:                    0.
% 1.84/1.02  sup_time_sim_full:                      0.
% 1.84/1.02  sup_time_sim_immed:                     0.
% 1.84/1.02  
% 1.84/1.02  sup_num_of_clauses:                     216
% 1.84/1.02  sup_num_in_active:                      103
% 1.84/1.02  sup_num_in_passive:                     113
% 1.84/1.02  sup_num_of_loops:                       116
% 1.84/1.02  sup_fw_superposition:                   141
% 1.84/1.02  sup_bw_superposition:                   56
% 1.84/1.02  sup_immediate_simplified:               29
% 1.84/1.02  sup_given_eliminated:                   1
% 1.84/1.02  comparisons_done:                       0
% 1.84/1.02  comparisons_avoided:                    0
% 1.84/1.02  
% 1.84/1.02  ------ Simplifications
% 1.84/1.02  
% 1.84/1.02  
% 1.84/1.02  sim_fw_subset_subsumed:                 0
% 1.84/1.02  sim_bw_subset_subsumed:                 2
% 1.84/1.02  sim_fw_subsumed:                        2
% 1.84/1.02  sim_bw_subsumed:                        0
% 1.84/1.02  sim_fw_subsumption_res:                 0
% 1.84/1.02  sim_bw_subsumption_res:                 0
% 1.84/1.02  sim_tautology_del:                      0
% 1.84/1.02  sim_eq_tautology_del:                   5
% 1.84/1.02  sim_eq_res_simp:                        0
% 1.84/1.02  sim_fw_demodulated:                     7
% 1.84/1.02  sim_bw_demodulated:                     18
% 1.84/1.02  sim_light_normalised:                   32
% 1.84/1.02  sim_joinable_taut:                      0
% 1.84/1.02  sim_joinable_simp:                      0
% 1.84/1.02  sim_ac_normalised:                      0
% 1.84/1.02  sim_smt_subsumption:                    0
% 1.84/1.02  
%------------------------------------------------------------------------------
