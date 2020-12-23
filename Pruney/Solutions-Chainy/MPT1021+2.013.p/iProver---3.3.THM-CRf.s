%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:19 EST 2020

% Result     : Theorem 3.06s
% Output     : CNFRefutation 3.06s
% Verified   : 
% Statistics : Number of formulae       :  253 (17490 expanded)
%              Number of clauses        :  170 (5262 expanded)
%              Number of leaves         :   20 (3397 expanded)
%              Depth                    :   32
%              Number of atoms          :  781 (82906 expanded)
%              Number of equality atoms :  354 (8813 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   13 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f45,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f46,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f45])).

fof(f53,plain,
    ( ? [X0,X1] :
        ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
        | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v3_funct_2(sK1,sK0,sK0)
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) )
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK1,sK0,sK0)
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f46,f53])).

fof(f93,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f54])).

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

fof(f51,plain,(
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

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f91,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_1(X1) = k2_funct_2(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f43])).

fof(f88,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f90,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f92,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f39])).

fof(f85,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f41])).

fof(f87,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f82,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k2_funct_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f27,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f65,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f18,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f89,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f18])).

fof(f96,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f65,f89])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f33])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f66,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f95,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f66,f89])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f94,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f54])).

fof(f15,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f86,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f31])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f64,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f84,plain,(
    ! [X0,X1] :
      ( v3_funct_2(k2_funct_2(X0,X1),X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f47])).

fof(f57,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1874,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1883,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_4471,plain,
    ( k1_relset_1(sK0,sK0,sK1) = sK0
    | sK0 = k1_xboole_0
    | v1_funct_2(sK1,sK0,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1874,c_1883])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1891,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3064,plain,
    ( k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_1874,c_1891])).

cnf(c_4475,plain,
    ( k1_relat_1(sK1) = sK0
    | sK0 = k1_xboole_0
    | v1_funct_2(sK1,sK0,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4471,c_3064])).

cnf(c_37,negated_conjecture,
    ( v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_40,plain,
    ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_4779,plain,
    ( sK0 = k1_xboole_0
    | k1_relat_1(sK1) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4475,c_40])).

cnf(c_4780,plain,
    ( k1_relat_1(sK1) = sK0
    | sK0 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_4779])).

cnf(c_33,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1876,plain,
    ( k2_funct_2(X0,X1) = k2_funct_1(X1)
    | v1_funct_2(X1,X0,X0) != iProver_top
    | v3_funct_2(X1,X0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_4971,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1874,c_1876])).

cnf(c_38,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_36,negated_conjecture,
    ( v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_2275,plain,
    ( ~ v1_funct_2(sK1,X0,X0)
    | ~ v3_funct_2(sK1,X0,X0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ v1_funct_1(sK1)
    | k2_funct_2(X0,sK1) = k2_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_2453,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_2275])).

cnf(c_5630,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4971,c_38,c_37,c_36,c_35,c_2453])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1882,plain,
    ( v1_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(X0,X1,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_5653,plain,
    ( v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5630,c_1882])).

cnf(c_39,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_41,plain,
    ( v3_funct_2(sK1,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_42,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_6894,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5653,c_39,c_40,c_41,c_42])).

cnf(c_32,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1877,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_6912,plain,
    ( k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6894,c_1877])).

cnf(c_30,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_2(X1,X0)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1879,plain,
    ( v1_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(X0,X1,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_2(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_3482,plain,
    ( v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(k2_funct_2(sK0,sK1)) = iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1874,c_1879])).

cnf(c_2260,plain,
    ( ~ v1_funct_2(sK1,X0,X0)
    | ~ v3_funct_2(sK1,X0,X0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | v1_funct_1(k2_funct_2(X0,sK1))
    | ~ v1_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_2450,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v1_funct_1(k2_funct_2(sK0,sK1))
    | ~ v1_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_2260])).

cnf(c_2451,plain,
    ( v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(k2_funct_2(sK0,sK1)) = iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2450])).

cnf(c_3963,plain,
    ( v1_funct_1(k2_funct_2(sK0,sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3482,c_39,c_40,c_41,c_42,c_2451])).

cnf(c_5636,plain,
    ( v1_funct_1(k2_funct_1(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5630,c_3963])).

cnf(c_8926,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6912,c_5636])).

cnf(c_8927,plain,
    ( k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_8926])).

cnf(c_8938,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k5_relat_1(sK1,k2_funct_1(sK1))
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1874,c_8927])).

cnf(c_1871,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_11,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1893,plain,
    ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3820,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
    | v2_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1871,c_1893])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2180,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2204,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_17,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2227,plain,
    ( ~ v3_funct_2(sK1,X0,X1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK1)
    | v2_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2368,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | v2_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_2227])).

cnf(c_3959,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3820,c_38,c_36,c_35,c_2180,c_2204,c_2368])).

cnf(c_8951,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
    | v1_funct_1(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8938,c_3959])).

cnf(c_9204,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8951,c_39])).

cnf(c_5390,plain,
    ( k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1874,c_1877])).

cnf(c_5813,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5390,c_39])).

cnf(c_5814,plain,
    ( k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_5813])).

cnf(c_5823,plain,
    ( k1_partfun1(X0,X0,sK0,sK0,k2_funct_2(X0,X1),sK1) = k5_relat_1(k2_funct_2(X0,X1),sK1)
    | v1_funct_2(X1,X0,X0) != iProver_top
    | v3_funct_2(X1,X0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(k2_funct_2(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1882,c_5814])).

cnf(c_7013,plain,
    ( k1_partfun1(X0,X0,sK0,sK0,k2_funct_2(X0,X1),sK1) = k5_relat_1(k2_funct_2(X0,X1),sK1)
    | v1_funct_2(X1,X0,X0) != iProver_top
    | v3_funct_2(X1,X0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5823,c_1879])).

cnf(c_7020,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1) = k5_relat_1(k2_funct_2(sK0,sK1),sK1)
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1874,c_7013])).

cnf(c_10,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1894,plain,
    ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4374,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1))
    | v2_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1871,c_1894])).

cnf(c_16,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | v2_funct_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_26,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_501,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ v5_relat_1(X3,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X3)
    | X3 != X0
    | X4 != X2
    | k2_relat_1(X3) = X4 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_26])).

cnf(c_502,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ v5_relat_1(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(unflattening,[status(thm)],[c_501])).

cnf(c_506,plain,
    ( ~ v1_funct_1(X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v5_relat_1(X0,X2)
    | ~ v3_funct_2(X0,X1,X2)
    | k2_relat_1(X0) = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_502,c_12])).

cnf(c_507,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ v5_relat_1(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(renaming,[status(thm)],[c_506])).

cnf(c_13,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_522,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_507,c_13])).

cnf(c_1870,plain,
    ( k2_relat_1(X0) = X1
    | v3_funct_2(X0,X2,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_522])).

cnf(c_2897,plain,
    ( k2_relat_1(sK1) = sK0
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1874,c_1870])).

cnf(c_2239,plain,
    ( ~ v3_funct_2(sK1,X0,X1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK1)
    | k2_relat_1(sK1) = X1 ),
    inference(instantiation,[status(thm)],[c_522])).

cnf(c_2371,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | k2_relat_1(sK1) = sK0 ),
    inference(instantiation,[status(thm)],[c_2239])).

cnf(c_3261,plain,
    ( k2_relat_1(sK1) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2897,c_38,c_36,c_35,c_2371])).

cnf(c_4385,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
    | v2_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4374,c_3261])).

cnf(c_2181,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2180])).

cnf(c_2369,plain,
    ( v3_funct_2(sK1,sK0,sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v2_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2368])).

cnf(c_4693,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4385,c_39,c_41,c_42,c_2181,c_2369])).

cnf(c_7043,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7020,c_4693,c_5630])).

cnf(c_6900,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k5_relat_1(k2_funct_1(sK1),sK1)
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6894,c_5814])).

cnf(c_6984,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6900,c_4693])).

cnf(c_7359,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7043,c_5636,c_6984])).

cnf(c_34,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1875,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) != iProver_top
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_5637,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) != iProver_top
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5630,c_1875])).

cnf(c_7362,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top
    | r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7359,c_5637])).

cnf(c_31,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_2360,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_2363,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2360])).

cnf(c_15,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2245,plain,
    ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_2835,plain,
    ( r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_2245])).

cnf(c_2836,plain,
    ( r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) = iProver_top
    | m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2835])).

cnf(c_8058,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7362,c_42,c_2363,c_2836])).

cnf(c_9207,plain,
    ( r2_relset_1(sK0,sK0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9204,c_8058])).

cnf(c_9211,plain,
    ( sK0 = k1_xboole_0
    | r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4780,c_9207])).

cnf(c_9314,plain,
    ( sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9211,c_42,c_2363,c_2836])).

cnf(c_9317,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9314,c_9207])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1896,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3265,plain,
    ( sK1 = k1_xboole_0
    | sK0 != k1_xboole_0
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3261,c_1896])).

cnf(c_3266,plain,
    ( ~ v1_relat_1(sK1)
    | sK1 = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3265])).

cnf(c_3312,plain,
    ( sK0 != k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3265,c_35,c_2180,c_3266])).

cnf(c_3313,plain,
    ( sK1 = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_3312])).

cnf(c_9348,plain,
    ( sK1 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_9314,c_3313])).

cnf(c_9372,plain,
    ( sK1 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_9348])).

cnf(c_9318,plain,
    ( k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
    inference(demodulation,[status(thm)],[c_9314,c_9204])).

cnf(c_6907,plain,
    ( k2_relat_1(k2_funct_1(sK1)) = sK0
    | v3_funct_2(k2_funct_1(sK1),sK0,sK0) != iProver_top
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6894,c_1870])).

cnf(c_28,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | v3_funct_2(k2_funct_2(X1,X0),X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1881,plain,
    ( v1_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(k2_funct_2(X1,X0),X1,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_4856,plain,
    ( v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0) = iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1874,c_1881])).

cnf(c_2285,plain,
    ( ~ v1_funct_2(sK1,X0,X0)
    | v3_funct_2(k2_funct_2(X0,sK1),X0,X0)
    | ~ v3_funct_2(sK1,X0,X0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ v1_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_2459,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_2285])).

cnf(c_2460,plain,
    ( v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0) = iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2459])).

cnf(c_5805,plain,
    ( v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4856,c_39,c_40,c_41,c_42,c_2460])).

cnf(c_5809,plain,
    ( v3_funct_2(k2_funct_1(sK1),sK0,sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5805,c_5630])).

cnf(c_8299,plain,
    ( k2_relat_1(k2_funct_1(sK1)) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6907,c_5636,c_5809])).

cnf(c_8306,plain,
    ( k2_funct_1(sK1) = k1_xboole_0
    | sK0 != k1_xboole_0
    | v1_relat_1(k2_funct_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8299,c_1896])).

cnf(c_1892,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_6905,plain,
    ( v1_relat_1(k2_funct_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6894,c_1892])).

cnf(c_9052,plain,
    ( sK0 != k1_xboole_0
    | k2_funct_1(sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8306,c_6905])).

cnf(c_9053,plain,
    ( k2_funct_1(sK1) = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_9052])).

cnf(c_9319,plain,
    ( k2_funct_1(sK1) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_9314,c_9053])).

cnf(c_9499,plain,
    ( k2_funct_1(sK1) = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_9319])).

cnf(c_9500,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_9499,c_9372])).

cnf(c_9346,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_9314,c_4693])).

cnf(c_9388,plain,
    ( k5_relat_1(k2_funct_1(k1_xboole_0),k1_xboole_0) = k6_partfun1(k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_9346,c_9372])).

cnf(c_1878,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_7,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_537,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_13,c_7])).

cnf(c_541,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_537,c_12])).

cnf(c_542,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_541])).

cnf(c_1869,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_542])).

cnf(c_2307,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1(X0)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1878,c_1869])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1899,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1901,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3172,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1899,c_1901])).

cnf(c_4178,plain,
    ( k2_relat_1(k6_partfun1(k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2307,c_3172])).

cnf(c_4261,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0
    | v1_relat_1(k6_partfun1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4178,c_1896])).

cnf(c_50,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_52,plain,
    ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_50])).

cnf(c_2175,plain,
    ( ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | v1_relat_1(k6_partfun1(X0)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2176,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_relat_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2175])).

cnf(c_2178,plain,
    ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_relat_1(k6_partfun1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2176])).

cnf(c_4270,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4261,c_52,c_2178])).

cnf(c_9390,plain,
    ( k5_relat_1(k2_funct_1(k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_9388,c_4270])).

cnf(c_9517,plain,
    ( k5_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_9500,c_9390])).

cnf(c_5825,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK1) = k5_relat_1(sK1,sK1)
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1874,c_5814])).

cnf(c_5929,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK1) = k5_relat_1(sK1,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5825,c_39])).

cnf(c_9341,plain,
    ( k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK1,sK1) = k5_relat_1(sK1,sK1) ),
    inference(demodulation,[status(thm)],[c_9314,c_5929])).

cnf(c_9405,plain,
    ( k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k5_relat_1(k1_xboole_0,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_9341,c_9372])).

cnf(c_9521,plain,
    ( k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_9517,c_9405])).

cnf(c_9531,plain,
    ( k6_partfun1(k1_relat_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_9318,c_9372,c_9500,c_9521])).

cnf(c_9534,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9317,c_9372,c_9531])).

cnf(c_9536,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9534,c_4270])).

cnf(c_2634,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2637,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2634])).

cnf(c_2639,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2637])).

cnf(c_4,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2170,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2171,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2170])).

cnf(c_2173,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
    | r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2171])).

cnf(c_96,plain,
    ( r2_relset_1(X0,X1,X2,X2) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_98,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_96])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9536,c_2639,c_2173,c_98])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:44:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.06/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.06/0.99  
% 3.06/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.06/0.99  
% 3.06/0.99  ------  iProver source info
% 3.06/0.99  
% 3.06/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.06/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.06/0.99  git: non_committed_changes: false
% 3.06/0.99  git: last_make_outside_of_git: false
% 3.06/0.99  
% 3.06/0.99  ------ 
% 3.06/0.99  
% 3.06/0.99  ------ Input Options
% 3.06/0.99  
% 3.06/0.99  --out_options                           all
% 3.06/0.99  --tptp_safe_out                         true
% 3.06/0.99  --problem_path                          ""
% 3.06/0.99  --include_path                          ""
% 3.06/0.99  --clausifier                            res/vclausify_rel
% 3.06/0.99  --clausifier_options                    --mode clausify
% 3.06/0.99  --stdin                                 false
% 3.06/0.99  --stats_out                             all
% 3.06/0.99  
% 3.06/0.99  ------ General Options
% 3.06/0.99  
% 3.06/0.99  --fof                                   false
% 3.06/0.99  --time_out_real                         305.
% 3.06/0.99  --time_out_virtual                      -1.
% 3.06/0.99  --symbol_type_check                     false
% 3.06/0.99  --clausify_out                          false
% 3.06/0.99  --sig_cnt_out                           false
% 3.06/0.99  --trig_cnt_out                          false
% 3.06/0.99  --trig_cnt_out_tolerance                1.
% 3.06/0.99  --trig_cnt_out_sk_spl                   false
% 3.06/0.99  --abstr_cl_out                          false
% 3.06/0.99  
% 3.06/0.99  ------ Global Options
% 3.06/0.99  
% 3.06/0.99  --schedule                              default
% 3.06/0.99  --add_important_lit                     false
% 3.06/0.99  --prop_solver_per_cl                    1000
% 3.06/0.99  --min_unsat_core                        false
% 3.06/0.99  --soft_assumptions                      false
% 3.06/0.99  --soft_lemma_size                       3
% 3.06/0.99  --prop_impl_unit_size                   0
% 3.06/0.99  --prop_impl_unit                        []
% 3.06/0.99  --share_sel_clauses                     true
% 3.06/0.99  --reset_solvers                         false
% 3.06/0.99  --bc_imp_inh                            [conj_cone]
% 3.06/0.99  --conj_cone_tolerance                   3.
% 3.06/0.99  --extra_neg_conj                        none
% 3.06/0.99  --large_theory_mode                     true
% 3.06/0.99  --prolific_symb_bound                   200
% 3.06/0.99  --lt_threshold                          2000
% 3.06/0.99  --clause_weak_htbl                      true
% 3.06/0.99  --gc_record_bc_elim                     false
% 3.06/0.99  
% 3.06/0.99  ------ Preprocessing Options
% 3.06/0.99  
% 3.06/0.99  --preprocessing_flag                    true
% 3.06/0.99  --time_out_prep_mult                    0.1
% 3.06/0.99  --splitting_mode                        input
% 3.06/0.99  --splitting_grd                         true
% 3.06/0.99  --splitting_cvd                         false
% 3.06/0.99  --splitting_cvd_svl                     false
% 3.06/0.99  --splitting_nvd                         32
% 3.06/0.99  --sub_typing                            true
% 3.06/0.99  --prep_gs_sim                           true
% 3.06/0.99  --prep_unflatten                        true
% 3.06/0.99  --prep_res_sim                          true
% 3.06/0.99  --prep_upred                            true
% 3.06/0.99  --prep_sem_filter                       exhaustive
% 3.06/0.99  --prep_sem_filter_out                   false
% 3.06/0.99  --pred_elim                             true
% 3.06/0.99  --res_sim_input                         true
% 3.06/0.99  --eq_ax_congr_red                       true
% 3.06/0.99  --pure_diseq_elim                       true
% 3.06/0.99  --brand_transform                       false
% 3.06/0.99  --non_eq_to_eq                          false
% 3.06/0.99  --prep_def_merge                        true
% 3.06/0.99  --prep_def_merge_prop_impl              false
% 3.06/0.99  --prep_def_merge_mbd                    true
% 3.06/0.99  --prep_def_merge_tr_red                 false
% 3.06/0.99  --prep_def_merge_tr_cl                  false
% 3.06/0.99  --smt_preprocessing                     true
% 3.06/0.99  --smt_ac_axioms                         fast
% 3.06/0.99  --preprocessed_out                      false
% 3.06/0.99  --preprocessed_stats                    false
% 3.06/0.99  
% 3.06/0.99  ------ Abstraction refinement Options
% 3.06/0.99  
% 3.06/0.99  --abstr_ref                             []
% 3.06/0.99  --abstr_ref_prep                        false
% 3.06/0.99  --abstr_ref_until_sat                   false
% 3.06/0.99  --abstr_ref_sig_restrict                funpre
% 3.06/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.06/0.99  --abstr_ref_under                       []
% 3.06/0.99  
% 3.06/0.99  ------ SAT Options
% 3.06/0.99  
% 3.06/0.99  --sat_mode                              false
% 3.06/0.99  --sat_fm_restart_options                ""
% 3.06/0.99  --sat_gr_def                            false
% 3.06/0.99  --sat_epr_types                         true
% 3.06/0.99  --sat_non_cyclic_types                  false
% 3.06/0.99  --sat_finite_models                     false
% 3.06/0.99  --sat_fm_lemmas                         false
% 3.06/0.99  --sat_fm_prep                           false
% 3.06/0.99  --sat_fm_uc_incr                        true
% 3.06/0.99  --sat_out_model                         small
% 3.06/0.99  --sat_out_clauses                       false
% 3.06/0.99  
% 3.06/0.99  ------ QBF Options
% 3.06/0.99  
% 3.06/0.99  --qbf_mode                              false
% 3.06/0.99  --qbf_elim_univ                         false
% 3.06/0.99  --qbf_dom_inst                          none
% 3.06/0.99  --qbf_dom_pre_inst                      false
% 3.06/0.99  --qbf_sk_in                             false
% 3.06/0.99  --qbf_pred_elim                         true
% 3.06/0.99  --qbf_split                             512
% 3.06/0.99  
% 3.06/0.99  ------ BMC1 Options
% 3.06/0.99  
% 3.06/0.99  --bmc1_incremental                      false
% 3.06/0.99  --bmc1_axioms                           reachable_all
% 3.06/0.99  --bmc1_min_bound                        0
% 3.06/0.99  --bmc1_max_bound                        -1
% 3.06/0.99  --bmc1_max_bound_default                -1
% 3.06/0.99  --bmc1_symbol_reachability              true
% 3.06/0.99  --bmc1_property_lemmas                  false
% 3.06/0.99  --bmc1_k_induction                      false
% 3.06/0.99  --bmc1_non_equiv_states                 false
% 3.06/0.99  --bmc1_deadlock                         false
% 3.06/0.99  --bmc1_ucm                              false
% 3.06/0.99  --bmc1_add_unsat_core                   none
% 3.06/0.99  --bmc1_unsat_core_children              false
% 3.06/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.06/0.99  --bmc1_out_stat                         full
% 3.06/0.99  --bmc1_ground_init                      false
% 3.06/0.99  --bmc1_pre_inst_next_state              false
% 3.06/0.99  --bmc1_pre_inst_state                   false
% 3.06/0.99  --bmc1_pre_inst_reach_state             false
% 3.06/0.99  --bmc1_out_unsat_core                   false
% 3.06/0.99  --bmc1_aig_witness_out                  false
% 3.06/0.99  --bmc1_verbose                          false
% 3.06/0.99  --bmc1_dump_clauses_tptp                false
% 3.06/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.06/0.99  --bmc1_dump_file                        -
% 3.06/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.06/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.06/0.99  --bmc1_ucm_extend_mode                  1
% 3.06/0.99  --bmc1_ucm_init_mode                    2
% 3.06/0.99  --bmc1_ucm_cone_mode                    none
% 3.06/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.06/0.99  --bmc1_ucm_relax_model                  4
% 3.06/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.06/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.06/0.99  --bmc1_ucm_layered_model                none
% 3.06/0.99  --bmc1_ucm_max_lemma_size               10
% 3.06/0.99  
% 3.06/0.99  ------ AIG Options
% 3.06/0.99  
% 3.06/0.99  --aig_mode                              false
% 3.06/0.99  
% 3.06/0.99  ------ Instantiation Options
% 3.06/0.99  
% 3.06/0.99  --instantiation_flag                    true
% 3.06/0.99  --inst_sos_flag                         false
% 3.06/0.99  --inst_sos_phase                        true
% 3.06/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.06/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.06/0.99  --inst_lit_sel_side                     num_symb
% 3.06/0.99  --inst_solver_per_active                1400
% 3.06/0.99  --inst_solver_calls_frac                1.
% 3.06/0.99  --inst_passive_queue_type               priority_queues
% 3.06/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.06/0.99  --inst_passive_queues_freq              [25;2]
% 3.06/0.99  --inst_dismatching                      true
% 3.06/0.99  --inst_eager_unprocessed_to_passive     true
% 3.06/0.99  --inst_prop_sim_given                   true
% 3.06/0.99  --inst_prop_sim_new                     false
% 3.06/0.99  --inst_subs_new                         false
% 3.06/0.99  --inst_eq_res_simp                      false
% 3.06/0.99  --inst_subs_given                       false
% 3.06/0.99  --inst_orphan_elimination               true
% 3.06/0.99  --inst_learning_loop_flag               true
% 3.06/0.99  --inst_learning_start                   3000
% 3.06/0.99  --inst_learning_factor                  2
% 3.06/0.99  --inst_start_prop_sim_after_learn       3
% 3.06/0.99  --inst_sel_renew                        solver
% 3.06/0.99  --inst_lit_activity_flag                true
% 3.06/0.99  --inst_restr_to_given                   false
% 3.06/0.99  --inst_activity_threshold               500
% 3.06/0.99  --inst_out_proof                        true
% 3.06/0.99  
% 3.06/0.99  ------ Resolution Options
% 3.06/0.99  
% 3.06/0.99  --resolution_flag                       true
% 3.06/0.99  --res_lit_sel                           adaptive
% 3.06/0.99  --res_lit_sel_side                      none
% 3.06/0.99  --res_ordering                          kbo
% 3.06/0.99  --res_to_prop_solver                    active
% 3.06/0.99  --res_prop_simpl_new                    false
% 3.06/0.99  --res_prop_simpl_given                  true
% 3.06/0.99  --res_passive_queue_type                priority_queues
% 3.06/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.06/0.99  --res_passive_queues_freq               [15;5]
% 3.06/0.99  --res_forward_subs                      full
% 3.06/0.99  --res_backward_subs                     full
% 3.06/0.99  --res_forward_subs_resolution           true
% 3.06/0.99  --res_backward_subs_resolution          true
% 3.06/0.99  --res_orphan_elimination                true
% 3.06/0.99  --res_time_limit                        2.
% 3.06/0.99  --res_out_proof                         true
% 3.06/0.99  
% 3.06/0.99  ------ Superposition Options
% 3.06/0.99  
% 3.06/0.99  --superposition_flag                    true
% 3.06/0.99  --sup_passive_queue_type                priority_queues
% 3.06/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.06/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.06/0.99  --demod_completeness_check              fast
% 3.06/0.99  --demod_use_ground                      true
% 3.06/0.99  --sup_to_prop_solver                    passive
% 3.06/0.99  --sup_prop_simpl_new                    true
% 3.06/0.99  --sup_prop_simpl_given                  true
% 3.06/0.99  --sup_fun_splitting                     false
% 3.06/0.99  --sup_smt_interval                      50000
% 3.06/0.99  
% 3.06/0.99  ------ Superposition Simplification Setup
% 3.06/0.99  
% 3.06/0.99  --sup_indices_passive                   []
% 3.06/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.06/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.06/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.06/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.06/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.06/0.99  --sup_full_bw                           [BwDemod]
% 3.06/0.99  --sup_immed_triv                        [TrivRules]
% 3.06/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.06/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.06/0.99  --sup_immed_bw_main                     []
% 3.06/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.06/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.06/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.06/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.06/0.99  
% 3.06/0.99  ------ Combination Options
% 3.06/0.99  
% 3.06/0.99  --comb_res_mult                         3
% 3.06/0.99  --comb_sup_mult                         2
% 3.06/0.99  --comb_inst_mult                        10
% 3.06/0.99  
% 3.06/0.99  ------ Debug Options
% 3.06/0.99  
% 3.06/0.99  --dbg_backtrace                         false
% 3.06/0.99  --dbg_dump_prop_clauses                 false
% 3.06/0.99  --dbg_dump_prop_clauses_file            -
% 3.06/0.99  --dbg_out_stat                          false
% 3.06/0.99  ------ Parsing...
% 3.06/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.06/0.99  
% 3.06/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.06/0.99  
% 3.06/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.06/0.99  
% 3.06/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.06/0.99  ------ Proving...
% 3.06/0.99  ------ Problem Properties 
% 3.06/0.99  
% 3.06/0.99  
% 3.06/0.99  clauses                                 33
% 3.06/0.99  conjectures                             5
% 3.06/0.99  EPR                                     6
% 3.06/0.99  Horn                                    29
% 3.06/0.99  unary                                   7
% 3.06/0.99  binary                                  6
% 3.06/0.99  lits                                    98
% 3.06/0.99  lits eq                                 20
% 3.06/0.99  fd_pure                                 0
% 3.06/0.99  fd_pseudo                               0
% 3.06/0.99  fd_cond                                 5
% 3.06/0.99  fd_pseudo_cond                          2
% 3.06/0.99  AC symbols                              0
% 3.06/0.99  
% 3.06/0.99  ------ Schedule dynamic 5 is on 
% 3.06/0.99  
% 3.06/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.06/0.99  
% 3.06/0.99  
% 3.06/0.99  ------ 
% 3.06/0.99  Current options:
% 3.06/0.99  ------ 
% 3.06/0.99  
% 3.06/0.99  ------ Input Options
% 3.06/0.99  
% 3.06/0.99  --out_options                           all
% 3.06/0.99  --tptp_safe_out                         true
% 3.06/0.99  --problem_path                          ""
% 3.06/0.99  --include_path                          ""
% 3.06/0.99  --clausifier                            res/vclausify_rel
% 3.06/0.99  --clausifier_options                    --mode clausify
% 3.06/0.99  --stdin                                 false
% 3.06/0.99  --stats_out                             all
% 3.06/0.99  
% 3.06/0.99  ------ General Options
% 3.06/0.99  
% 3.06/0.99  --fof                                   false
% 3.06/0.99  --time_out_real                         305.
% 3.06/0.99  --time_out_virtual                      -1.
% 3.06/0.99  --symbol_type_check                     false
% 3.06/0.99  --clausify_out                          false
% 3.06/0.99  --sig_cnt_out                           false
% 3.06/0.99  --trig_cnt_out                          false
% 3.06/0.99  --trig_cnt_out_tolerance                1.
% 3.06/0.99  --trig_cnt_out_sk_spl                   false
% 3.06/0.99  --abstr_cl_out                          false
% 3.06/0.99  
% 3.06/0.99  ------ Global Options
% 3.06/0.99  
% 3.06/0.99  --schedule                              default
% 3.06/0.99  --add_important_lit                     false
% 3.06/0.99  --prop_solver_per_cl                    1000
% 3.06/0.99  --min_unsat_core                        false
% 3.06/0.99  --soft_assumptions                      false
% 3.06/0.99  --soft_lemma_size                       3
% 3.06/0.99  --prop_impl_unit_size                   0
% 3.06/0.99  --prop_impl_unit                        []
% 3.06/0.99  --share_sel_clauses                     true
% 3.06/0.99  --reset_solvers                         false
% 3.06/0.99  --bc_imp_inh                            [conj_cone]
% 3.06/0.99  --conj_cone_tolerance                   3.
% 3.06/0.99  --extra_neg_conj                        none
% 3.06/0.99  --large_theory_mode                     true
% 3.06/0.99  --prolific_symb_bound                   200
% 3.06/0.99  --lt_threshold                          2000
% 3.06/0.99  --clause_weak_htbl                      true
% 3.06/0.99  --gc_record_bc_elim                     false
% 3.06/0.99  
% 3.06/0.99  ------ Preprocessing Options
% 3.06/0.99  
% 3.06/0.99  --preprocessing_flag                    true
% 3.06/0.99  --time_out_prep_mult                    0.1
% 3.06/0.99  --splitting_mode                        input
% 3.06/0.99  --splitting_grd                         true
% 3.06/0.99  --splitting_cvd                         false
% 3.06/0.99  --splitting_cvd_svl                     false
% 3.06/0.99  --splitting_nvd                         32
% 3.06/0.99  --sub_typing                            true
% 3.06/0.99  --prep_gs_sim                           true
% 3.06/0.99  --prep_unflatten                        true
% 3.06/0.99  --prep_res_sim                          true
% 3.06/0.99  --prep_upred                            true
% 3.06/0.99  --prep_sem_filter                       exhaustive
% 3.06/0.99  --prep_sem_filter_out                   false
% 3.06/0.99  --pred_elim                             true
% 3.06/0.99  --res_sim_input                         true
% 3.06/0.99  --eq_ax_congr_red                       true
% 3.06/0.99  --pure_diseq_elim                       true
% 3.06/0.99  --brand_transform                       false
% 3.06/0.99  --non_eq_to_eq                          false
% 3.06/0.99  --prep_def_merge                        true
% 3.06/0.99  --prep_def_merge_prop_impl              false
% 3.06/0.99  --prep_def_merge_mbd                    true
% 3.06/0.99  --prep_def_merge_tr_red                 false
% 3.06/0.99  --prep_def_merge_tr_cl                  false
% 3.06/0.99  --smt_preprocessing                     true
% 3.06/0.99  --smt_ac_axioms                         fast
% 3.06/0.99  --preprocessed_out                      false
% 3.06/0.99  --preprocessed_stats                    false
% 3.06/0.99  
% 3.06/0.99  ------ Abstraction refinement Options
% 3.06/0.99  
% 3.06/0.99  --abstr_ref                             []
% 3.06/0.99  --abstr_ref_prep                        false
% 3.06/0.99  --abstr_ref_until_sat                   false
% 3.06/0.99  --abstr_ref_sig_restrict                funpre
% 3.06/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.06/0.99  --abstr_ref_under                       []
% 3.06/0.99  
% 3.06/0.99  ------ SAT Options
% 3.06/0.99  
% 3.06/0.99  --sat_mode                              false
% 3.06/0.99  --sat_fm_restart_options                ""
% 3.06/0.99  --sat_gr_def                            false
% 3.06/0.99  --sat_epr_types                         true
% 3.06/0.99  --sat_non_cyclic_types                  false
% 3.06/0.99  --sat_finite_models                     false
% 3.06/0.99  --sat_fm_lemmas                         false
% 3.06/0.99  --sat_fm_prep                           false
% 3.06/0.99  --sat_fm_uc_incr                        true
% 3.06/0.99  --sat_out_model                         small
% 3.06/0.99  --sat_out_clauses                       false
% 3.06/0.99  
% 3.06/0.99  ------ QBF Options
% 3.06/0.99  
% 3.06/0.99  --qbf_mode                              false
% 3.06/0.99  --qbf_elim_univ                         false
% 3.06/0.99  --qbf_dom_inst                          none
% 3.06/0.99  --qbf_dom_pre_inst                      false
% 3.06/0.99  --qbf_sk_in                             false
% 3.06/0.99  --qbf_pred_elim                         true
% 3.06/0.99  --qbf_split                             512
% 3.06/0.99  
% 3.06/0.99  ------ BMC1 Options
% 3.06/0.99  
% 3.06/0.99  --bmc1_incremental                      false
% 3.06/0.99  --bmc1_axioms                           reachable_all
% 3.06/0.99  --bmc1_min_bound                        0
% 3.06/0.99  --bmc1_max_bound                        -1
% 3.06/0.99  --bmc1_max_bound_default                -1
% 3.06/0.99  --bmc1_symbol_reachability              true
% 3.06/0.99  --bmc1_property_lemmas                  false
% 3.06/0.99  --bmc1_k_induction                      false
% 3.06/0.99  --bmc1_non_equiv_states                 false
% 3.06/0.99  --bmc1_deadlock                         false
% 3.06/0.99  --bmc1_ucm                              false
% 3.06/0.99  --bmc1_add_unsat_core                   none
% 3.06/0.99  --bmc1_unsat_core_children              false
% 3.06/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.06/0.99  --bmc1_out_stat                         full
% 3.06/0.99  --bmc1_ground_init                      false
% 3.06/0.99  --bmc1_pre_inst_next_state              false
% 3.06/0.99  --bmc1_pre_inst_state                   false
% 3.06/0.99  --bmc1_pre_inst_reach_state             false
% 3.06/0.99  --bmc1_out_unsat_core                   false
% 3.06/0.99  --bmc1_aig_witness_out                  false
% 3.06/0.99  --bmc1_verbose                          false
% 3.06/0.99  --bmc1_dump_clauses_tptp                false
% 3.06/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.06/0.99  --bmc1_dump_file                        -
% 3.06/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.06/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.06/0.99  --bmc1_ucm_extend_mode                  1
% 3.06/0.99  --bmc1_ucm_init_mode                    2
% 3.06/0.99  --bmc1_ucm_cone_mode                    none
% 3.06/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.06/0.99  --bmc1_ucm_relax_model                  4
% 3.06/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.06/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.06/0.99  --bmc1_ucm_layered_model                none
% 3.06/0.99  --bmc1_ucm_max_lemma_size               10
% 3.06/0.99  
% 3.06/0.99  ------ AIG Options
% 3.06/0.99  
% 3.06/0.99  --aig_mode                              false
% 3.06/0.99  
% 3.06/0.99  ------ Instantiation Options
% 3.06/0.99  
% 3.06/0.99  --instantiation_flag                    true
% 3.06/0.99  --inst_sos_flag                         false
% 3.06/0.99  --inst_sos_phase                        true
% 3.06/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.06/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.06/0.99  --inst_lit_sel_side                     none
% 3.06/0.99  --inst_solver_per_active                1400
% 3.06/0.99  --inst_solver_calls_frac                1.
% 3.06/0.99  --inst_passive_queue_type               priority_queues
% 3.06/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.06/0.99  --inst_passive_queues_freq              [25;2]
% 3.06/0.99  --inst_dismatching                      true
% 3.06/0.99  --inst_eager_unprocessed_to_passive     true
% 3.06/0.99  --inst_prop_sim_given                   true
% 3.06/0.99  --inst_prop_sim_new                     false
% 3.06/0.99  --inst_subs_new                         false
% 3.06/0.99  --inst_eq_res_simp                      false
% 3.06/0.99  --inst_subs_given                       false
% 3.06/0.99  --inst_orphan_elimination               true
% 3.06/0.99  --inst_learning_loop_flag               true
% 3.06/0.99  --inst_learning_start                   3000
% 3.06/0.99  --inst_learning_factor                  2
% 3.06/0.99  --inst_start_prop_sim_after_learn       3
% 3.06/0.99  --inst_sel_renew                        solver
% 3.06/0.99  --inst_lit_activity_flag                true
% 3.06/0.99  --inst_restr_to_given                   false
% 3.06/0.99  --inst_activity_threshold               500
% 3.06/0.99  --inst_out_proof                        true
% 3.06/0.99  
% 3.06/0.99  ------ Resolution Options
% 3.06/0.99  
% 3.06/0.99  --resolution_flag                       false
% 3.06/0.99  --res_lit_sel                           adaptive
% 3.06/0.99  --res_lit_sel_side                      none
% 3.06/0.99  --res_ordering                          kbo
% 3.06/0.99  --res_to_prop_solver                    active
% 3.06/0.99  --res_prop_simpl_new                    false
% 3.06/0.99  --res_prop_simpl_given                  true
% 3.06/0.99  --res_passive_queue_type                priority_queues
% 3.06/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.06/0.99  --res_passive_queues_freq               [15;5]
% 3.06/0.99  --res_forward_subs                      full
% 3.06/0.99  --res_backward_subs                     full
% 3.06/0.99  --res_forward_subs_resolution           true
% 3.06/0.99  --res_backward_subs_resolution          true
% 3.06/0.99  --res_orphan_elimination                true
% 3.06/0.99  --res_time_limit                        2.
% 3.06/0.99  --res_out_proof                         true
% 3.06/0.99  
% 3.06/0.99  ------ Superposition Options
% 3.06/0.99  
% 3.06/0.99  --superposition_flag                    true
% 3.06/0.99  --sup_passive_queue_type                priority_queues
% 3.06/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.06/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.06/0.99  --demod_completeness_check              fast
% 3.06/0.99  --demod_use_ground                      true
% 3.06/0.99  --sup_to_prop_solver                    passive
% 3.06/0.99  --sup_prop_simpl_new                    true
% 3.06/0.99  --sup_prop_simpl_given                  true
% 3.06/0.99  --sup_fun_splitting                     false
% 3.06/0.99  --sup_smt_interval                      50000
% 3.06/0.99  
% 3.06/0.99  ------ Superposition Simplification Setup
% 3.06/0.99  
% 3.06/0.99  --sup_indices_passive                   []
% 3.06/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.06/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.06/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.06/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.06/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.06/0.99  --sup_full_bw                           [BwDemod]
% 3.06/0.99  --sup_immed_triv                        [TrivRules]
% 3.06/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.06/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.06/0.99  --sup_immed_bw_main                     []
% 3.06/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.06/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.06/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.06/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.06/0.99  
% 3.06/0.99  ------ Combination Options
% 3.06/0.99  
% 3.06/0.99  --comb_res_mult                         3
% 3.06/0.99  --comb_sup_mult                         2
% 3.06/0.99  --comb_inst_mult                        10
% 3.06/0.99  
% 3.06/0.99  ------ Debug Options
% 3.06/0.99  
% 3.06/0.99  --dbg_backtrace                         false
% 3.06/0.99  --dbg_dump_prop_clauses                 false
% 3.06/0.99  --dbg_dump_prop_clauses_file            -
% 3.06/0.99  --dbg_out_stat                          false
% 3.06/0.99  
% 3.06/0.99  
% 3.06/0.99  
% 3.06/0.99  
% 3.06/0.99  ------ Proving...
% 3.06/0.99  
% 3.06/0.99  
% 3.06/0.99  % SZS status Theorem for theBenchmark.p
% 3.06/0.99  
% 3.06/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.06/0.99  
% 3.06/0.99  fof(f19,conjecture,(
% 3.06/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 3.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/0.99  
% 3.06/0.99  fof(f20,negated_conjecture,(
% 3.06/0.99    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 3.06/0.99    inference(negated_conjecture,[],[f19])).
% 3.06/0.99  
% 3.06/0.99  fof(f45,plain,(
% 3.06/0.99    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 3.06/0.99    inference(ennf_transformation,[],[f20])).
% 3.06/0.99  
% 3.06/0.99  fof(f46,plain,(
% 3.06/0.99    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 3.06/0.99    inference(flattening,[],[f45])).
% 3.06/0.99  
% 3.06/0.99  fof(f53,plain,(
% 3.06/0.99    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 3.06/0.99    introduced(choice_axiom,[])).
% 3.06/0.99  
% 3.06/0.99  fof(f54,plain,(
% 3.06/0.99    (~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 3.06/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f46,f53])).
% 3.06/0.99  
% 3.06/0.99  fof(f93,plain,(
% 3.06/0.99    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.06/0.99    inference(cnf_transformation,[],[f54])).
% 3.06/0.99  
% 3.06/0.99  fof(f12,axiom,(
% 3.06/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/0.99  
% 3.06/0.99  fof(f35,plain,(
% 3.06/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.06/0.99    inference(ennf_transformation,[],[f12])).
% 3.06/0.99  
% 3.06/0.99  fof(f36,plain,(
% 3.06/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.06/0.99    inference(flattening,[],[f35])).
% 3.06/0.99  
% 3.06/0.99  fof(f51,plain,(
% 3.06/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.06/0.99    inference(nnf_transformation,[],[f36])).
% 3.06/0.99  
% 3.06/0.99  fof(f74,plain,(
% 3.06/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.06/0.99    inference(cnf_transformation,[],[f51])).
% 3.06/0.99  
% 3.06/0.99  fof(f9,axiom,(
% 3.06/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/0.99  
% 3.06/0.99  fof(f30,plain,(
% 3.06/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.06/0.99    inference(ennf_transformation,[],[f9])).
% 3.06/0.99  
% 3.06/0.99  fof(f69,plain,(
% 3.06/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.06/0.99    inference(cnf_transformation,[],[f30])).
% 3.06/0.99  
% 3.06/0.99  fof(f91,plain,(
% 3.06/0.99    v1_funct_2(sK1,sK0,sK0)),
% 3.06/0.99    inference(cnf_transformation,[],[f54])).
% 3.06/0.99  
% 3.06/0.99  fof(f17,axiom,(
% 3.06/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_1(X1) = k2_funct_2(X0,X1))),
% 3.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/0.99  
% 3.06/0.99  fof(f43,plain,(
% 3.06/0.99    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.06/0.99    inference(ennf_transformation,[],[f17])).
% 3.06/0.99  
% 3.06/0.99  fof(f44,plain,(
% 3.06/0.99    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.06/0.99    inference(flattening,[],[f43])).
% 3.06/0.99  
% 3.06/0.99  fof(f88,plain,(
% 3.06/0.99    ( ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.06/0.99    inference(cnf_transformation,[],[f44])).
% 3.06/0.99  
% 3.06/0.99  fof(f90,plain,(
% 3.06/0.99    v1_funct_1(sK1)),
% 3.06/0.99    inference(cnf_transformation,[],[f54])).
% 3.06/0.99  
% 3.06/0.99  fof(f92,plain,(
% 3.06/0.99    v3_funct_2(sK1,sK0,sK0)),
% 3.06/0.99    inference(cnf_transformation,[],[f54])).
% 3.06/0.99  
% 3.06/0.99  fof(f14,axiom,(
% 3.06/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 3.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/0.99  
% 3.06/0.99  fof(f39,plain,(
% 3.06/0.99    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.06/0.99    inference(ennf_transformation,[],[f14])).
% 3.06/0.99  
% 3.06/0.99  fof(f40,plain,(
% 3.06/0.99    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.06/0.99    inference(flattening,[],[f39])).
% 3.06/0.99  
% 3.06/0.99  fof(f85,plain,(
% 3.06/0.99    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.06/0.99    inference(cnf_transformation,[],[f40])).
% 3.06/0.99  
% 3.06/0.99  fof(f16,axiom,(
% 3.06/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/0.99  
% 3.06/0.99  fof(f41,plain,(
% 3.06/0.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.06/0.99    inference(ennf_transformation,[],[f16])).
% 3.06/0.99  
% 3.06/0.99  fof(f42,plain,(
% 3.06/0.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.06/0.99    inference(flattening,[],[f41])).
% 3.06/0.99  
% 3.06/0.99  fof(f87,plain,(
% 3.06/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.06/0.99    inference(cnf_transformation,[],[f42])).
% 3.06/0.99  
% 3.06/0.99  fof(f82,plain,(
% 3.06/0.99    ( ! [X0,X1] : (v1_funct_1(k2_funct_2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.06/0.99    inference(cnf_transformation,[],[f40])).
% 3.06/0.99  
% 3.06/0.99  fof(f6,axiom,(
% 3.06/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 3.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/0.99  
% 3.06/0.99  fof(f26,plain,(
% 3.06/0.99    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.06/0.99    inference(ennf_transformation,[],[f6])).
% 3.06/0.99  
% 3.06/0.99  fof(f27,plain,(
% 3.06/0.99    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.06/0.99    inference(flattening,[],[f26])).
% 3.06/0.99  
% 3.06/0.99  fof(f65,plain,(
% 3.06/0.99    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.06/0.99    inference(cnf_transformation,[],[f27])).
% 3.06/0.99  
% 3.06/0.99  fof(f18,axiom,(
% 3.06/0.99    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/0.99  
% 3.06/0.99  fof(f89,plain,(
% 3.06/0.99    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.06/0.99    inference(cnf_transformation,[],[f18])).
% 3.06/0.99  
% 3.06/0.99  fof(f96,plain,(
% 3.06/0.99    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.06/0.99    inference(definition_unfolding,[],[f65,f89])).
% 3.06/0.99  
% 3.06/0.99  fof(f7,axiom,(
% 3.06/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/0.99  
% 3.06/0.99  fof(f28,plain,(
% 3.06/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.06/0.99    inference(ennf_transformation,[],[f7])).
% 3.06/0.99  
% 3.06/0.99  fof(f67,plain,(
% 3.06/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.06/0.99    inference(cnf_transformation,[],[f28])).
% 3.06/0.99  
% 3.06/0.99  fof(f11,axiom,(
% 3.06/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 3.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/0.99  
% 3.06/0.99  fof(f33,plain,(
% 3.06/0.99    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.06/0.99    inference(ennf_transformation,[],[f11])).
% 3.06/0.99  
% 3.06/0.99  fof(f34,plain,(
% 3.06/0.99    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.06/0.99    inference(flattening,[],[f33])).
% 3.06/0.99  
% 3.06/0.99  fof(f72,plain,(
% 3.06/0.99    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.06/0.99    inference(cnf_transformation,[],[f34])).
% 3.06/0.99  
% 3.06/0.99  fof(f66,plain,(
% 3.06/0.99    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.06/0.99    inference(cnf_transformation,[],[f27])).
% 3.06/0.99  
% 3.06/0.99  fof(f95,plain,(
% 3.06/0.99    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.06/0.99    inference(definition_unfolding,[],[f66,f89])).
% 3.06/0.99  
% 3.06/0.99  fof(f73,plain,(
% 3.06/0.99    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.06/0.99    inference(cnf_transformation,[],[f34])).
% 3.06/0.99  
% 3.06/0.99  fof(f13,axiom,(
% 3.06/0.99    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 3.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/0.99  
% 3.06/0.99  fof(f37,plain,(
% 3.06/0.99    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.06/0.99    inference(ennf_transformation,[],[f13])).
% 3.06/0.99  
% 3.06/0.99  fof(f38,plain,(
% 3.06/0.99    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.06/0.99    inference(flattening,[],[f37])).
% 3.06/0.99  
% 3.06/0.99  fof(f52,plain,(
% 3.06/0.99    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.06/0.99    inference(nnf_transformation,[],[f38])).
% 3.06/0.99  
% 3.06/0.99  fof(f80,plain,(
% 3.06/0.99    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.06/0.99    inference(cnf_transformation,[],[f52])).
% 3.06/0.99  
% 3.06/0.99  fof(f8,axiom,(
% 3.06/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/0.99  
% 3.06/0.99  fof(f22,plain,(
% 3.06/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.06/0.99    inference(pure_predicate_removal,[],[f8])).
% 3.06/0.99  
% 3.06/0.99  fof(f29,plain,(
% 3.06/0.99    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.06/0.99    inference(ennf_transformation,[],[f22])).
% 3.06/0.99  
% 3.06/0.99  fof(f68,plain,(
% 3.06/0.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.06/0.99    inference(cnf_transformation,[],[f29])).
% 3.06/0.99  
% 3.06/0.99  fof(f94,plain,(
% 3.06/0.99    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))),
% 3.06/0.99    inference(cnf_transformation,[],[f54])).
% 3.06/0.99  
% 3.06/0.99  fof(f15,axiom,(
% 3.06/0.99    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 3.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/0.99  
% 3.06/0.99  fof(f21,plain,(
% 3.06/0.99    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.06/0.99    inference(pure_predicate_removal,[],[f15])).
% 3.06/0.99  
% 3.06/0.99  fof(f86,plain,(
% 3.06/0.99    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.06/0.99    inference(cnf_transformation,[],[f21])).
% 3.06/0.99  
% 3.06/0.99  fof(f10,axiom,(
% 3.06/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 3.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/0.99  
% 3.06/0.99  fof(f31,plain,(
% 3.06/0.99    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.06/0.99    inference(ennf_transformation,[],[f10])).
% 3.06/0.99  
% 3.06/0.99  fof(f32,plain,(
% 3.06/0.99    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.06/0.99    inference(flattening,[],[f31])).
% 3.06/0.99  
% 3.06/0.99  fof(f70,plain,(
% 3.06/0.99    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.06/0.99    inference(cnf_transformation,[],[f32])).
% 3.06/0.99  
% 3.06/0.99  fof(f5,axiom,(
% 3.06/0.99    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 3.06/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/1.00  
% 3.06/1.00  fof(f24,plain,(
% 3.06/1.00    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.06/1.00    inference(ennf_transformation,[],[f5])).
% 3.06/1.00  
% 3.06/1.00  fof(f25,plain,(
% 3.06/1.00    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.06/1.00    inference(flattening,[],[f24])).
% 3.06/1.00  
% 3.06/1.00  fof(f64,plain,(
% 3.06/1.00    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.06/1.00    inference(cnf_transformation,[],[f25])).
% 3.06/1.00  
% 3.06/1.00  fof(f84,plain,(
% 3.06/1.00    ( ! [X0,X1] : (v3_funct_2(k2_funct_2(X0,X1),X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.06/1.00    inference(cnf_transformation,[],[f40])).
% 3.06/1.00  
% 3.06/1.00  fof(f4,axiom,(
% 3.06/1.00    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.06/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/1.00  
% 3.06/1.00  fof(f23,plain,(
% 3.06/1.00    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.06/1.00    inference(ennf_transformation,[],[f4])).
% 3.06/1.00  
% 3.06/1.00  fof(f50,plain,(
% 3.06/1.00    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.06/1.00    inference(nnf_transformation,[],[f23])).
% 3.06/1.00  
% 3.06/1.00  fof(f61,plain,(
% 3.06/1.00    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.06/1.00    inference(cnf_transformation,[],[f50])).
% 3.06/1.00  
% 3.06/1.00  fof(f2,axiom,(
% 3.06/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.06/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/1.00  
% 3.06/1.00  fof(f58,plain,(
% 3.06/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.06/1.00    inference(cnf_transformation,[],[f2])).
% 3.06/1.00  
% 3.06/1.00  fof(f1,axiom,(
% 3.06/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.06/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/1.00  
% 3.06/1.00  fof(f47,plain,(
% 3.06/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.06/1.00    inference(nnf_transformation,[],[f1])).
% 3.06/1.00  
% 3.06/1.00  fof(f48,plain,(
% 3.06/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.06/1.00    inference(flattening,[],[f47])).
% 3.06/1.00  
% 3.06/1.00  fof(f57,plain,(
% 3.06/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.06/1.00    inference(cnf_transformation,[],[f48])).
% 3.06/1.00  
% 3.06/1.00  fof(f3,axiom,(
% 3.06/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.06/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/1.00  
% 3.06/1.00  fof(f49,plain,(
% 3.06/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.06/1.00    inference(nnf_transformation,[],[f3])).
% 3.06/1.00  
% 3.06/1.00  fof(f60,plain,(
% 3.06/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.06/1.00    inference(cnf_transformation,[],[f49])).
% 3.06/1.00  
% 3.06/1.00  cnf(c_35,negated_conjecture,
% 3.06/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.06/1.00      inference(cnf_transformation,[],[f93]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1874,plain,
% 3.06/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.06/1.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_24,plain,
% 3.06/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.06/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.06/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.06/1.00      | k1_xboole_0 = X2 ),
% 3.06/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1883,plain,
% 3.06/1.00      ( k1_relset_1(X0,X1,X2) = X0
% 3.06/1.00      | k1_xboole_0 = X1
% 3.06/1.00      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.06/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.06/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_4471,plain,
% 3.06/1.00      ( k1_relset_1(sK0,sK0,sK1) = sK0
% 3.06/1.00      | sK0 = k1_xboole_0
% 3.06/1.00      | v1_funct_2(sK1,sK0,sK0) != iProver_top ),
% 3.06/1.00      inference(superposition,[status(thm)],[c_1874,c_1883]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_14,plain,
% 3.06/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.06/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.06/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1891,plain,
% 3.06/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.06/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.06/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_3064,plain,
% 3.06/1.00      ( k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) ),
% 3.06/1.00      inference(superposition,[status(thm)],[c_1874,c_1891]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_4475,plain,
% 3.06/1.00      ( k1_relat_1(sK1) = sK0
% 3.06/1.00      | sK0 = k1_xboole_0
% 3.06/1.00      | v1_funct_2(sK1,sK0,sK0) != iProver_top ),
% 3.06/1.00      inference(demodulation,[status(thm)],[c_4471,c_3064]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_37,negated_conjecture,
% 3.06/1.00      ( v1_funct_2(sK1,sK0,sK0) ),
% 3.06/1.00      inference(cnf_transformation,[],[f91]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_40,plain,
% 3.06/1.00      ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
% 3.06/1.00      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_4779,plain,
% 3.06/1.00      ( sK0 = k1_xboole_0 | k1_relat_1(sK1) = sK0 ),
% 3.06/1.00      inference(global_propositional_subsumption,
% 3.06/1.00                [status(thm)],
% 3.06/1.00                [c_4475,c_40]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_4780,plain,
% 3.06/1.00      ( k1_relat_1(sK1) = sK0 | sK0 = k1_xboole_0 ),
% 3.06/1.00      inference(renaming,[status(thm)],[c_4779]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_33,plain,
% 3.06/1.00      ( ~ v1_funct_2(X0,X1,X1)
% 3.06/1.00      | ~ v3_funct_2(X0,X1,X1)
% 3.06/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.06/1.00      | ~ v1_funct_1(X0)
% 3.06/1.00      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 3.06/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1876,plain,
% 3.06/1.00      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
% 3.06/1.00      | v1_funct_2(X1,X0,X0) != iProver_top
% 3.06/1.00      | v3_funct_2(X1,X0,X0) != iProver_top
% 3.06/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 3.06/1.00      | v1_funct_1(X1) != iProver_top ),
% 3.06/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_4971,plain,
% 3.06/1.00      ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
% 3.06/1.00      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.06/1.00      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.06/1.00      | v1_funct_1(sK1) != iProver_top ),
% 3.06/1.00      inference(superposition,[status(thm)],[c_1874,c_1876]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_38,negated_conjecture,
% 3.06/1.00      ( v1_funct_1(sK1) ),
% 3.06/1.00      inference(cnf_transformation,[],[f90]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_36,negated_conjecture,
% 3.06/1.00      ( v3_funct_2(sK1,sK0,sK0) ),
% 3.06/1.00      inference(cnf_transformation,[],[f92]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_2275,plain,
% 3.06/1.00      ( ~ v1_funct_2(sK1,X0,X0)
% 3.06/1.00      | ~ v3_funct_2(sK1,X0,X0)
% 3.06/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 3.06/1.00      | ~ v1_funct_1(sK1)
% 3.06/1.00      | k2_funct_2(X0,sK1) = k2_funct_1(sK1) ),
% 3.06/1.00      inference(instantiation,[status(thm)],[c_33]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_2453,plain,
% 3.06/1.00      ( ~ v1_funct_2(sK1,sK0,sK0)
% 3.06/1.00      | ~ v3_funct_2(sK1,sK0,sK0)
% 3.06/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.06/1.00      | ~ v1_funct_1(sK1)
% 3.06/1.00      | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 3.06/1.00      inference(instantiation,[status(thm)],[c_2275]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_5630,plain,
% 3.06/1.00      ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 3.06/1.00      inference(global_propositional_subsumption,
% 3.06/1.00                [status(thm)],
% 3.06/1.00                [c_4971,c_38,c_37,c_36,c_35,c_2453]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_27,plain,
% 3.06/1.00      ( ~ v1_funct_2(X0,X1,X1)
% 3.06/1.00      | ~ v3_funct_2(X0,X1,X1)
% 3.06/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.06/1.00      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.06/1.00      | ~ v1_funct_1(X0) ),
% 3.06/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1882,plain,
% 3.06/1.00      ( v1_funct_2(X0,X1,X1) != iProver_top
% 3.06/1.00      | v3_funct_2(X0,X1,X1) != iProver_top
% 3.06/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 3.06/1.00      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) = iProver_top
% 3.06/1.00      | v1_funct_1(X0) != iProver_top ),
% 3.06/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_5653,plain,
% 3.06/1.00      ( v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.06/1.00      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.06/1.00      | m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 3.06/1.00      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.06/1.00      | v1_funct_1(sK1) != iProver_top ),
% 3.06/1.00      inference(superposition,[status(thm)],[c_5630,c_1882]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_39,plain,
% 3.06/1.00      ( v1_funct_1(sK1) = iProver_top ),
% 3.06/1.00      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_41,plain,
% 3.06/1.00      ( v3_funct_2(sK1,sK0,sK0) = iProver_top ),
% 3.06/1.00      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_42,plain,
% 3.06/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.06/1.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_6894,plain,
% 3.06/1.00      ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.06/1.00      inference(global_propositional_subsumption,
% 3.06/1.00                [status(thm)],
% 3.06/1.00                [c_5653,c_39,c_40,c_41,c_42]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_32,plain,
% 3.06/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.06/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.06/1.00      | ~ v1_funct_1(X0)
% 3.06/1.00      | ~ v1_funct_1(X3)
% 3.06/1.00      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.06/1.00      inference(cnf_transformation,[],[f87]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1877,plain,
% 3.06/1.00      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 3.06/1.00      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 3.06/1.00      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.06/1.00      | v1_funct_1(X5) != iProver_top
% 3.06/1.00      | v1_funct_1(X4) != iProver_top ),
% 3.06/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_6912,plain,
% 3.06/1.00      ( k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1))
% 3.06/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.06/1.00      | v1_funct_1(X2) != iProver_top
% 3.06/1.00      | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
% 3.06/1.00      inference(superposition,[status(thm)],[c_6894,c_1877]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_30,plain,
% 3.06/1.00      ( ~ v1_funct_2(X0,X1,X1)
% 3.06/1.00      | ~ v3_funct_2(X0,X1,X1)
% 3.06/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.06/1.00      | ~ v1_funct_1(X0)
% 3.06/1.00      | v1_funct_1(k2_funct_2(X1,X0)) ),
% 3.06/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1879,plain,
% 3.06/1.00      ( v1_funct_2(X0,X1,X1) != iProver_top
% 3.06/1.00      | v3_funct_2(X0,X1,X1) != iProver_top
% 3.06/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 3.06/1.00      | v1_funct_1(X0) != iProver_top
% 3.06/1.00      | v1_funct_1(k2_funct_2(X1,X0)) = iProver_top ),
% 3.06/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_3482,plain,
% 3.06/1.00      ( v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.06/1.00      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.06/1.00      | v1_funct_1(k2_funct_2(sK0,sK1)) = iProver_top
% 3.06/1.00      | v1_funct_1(sK1) != iProver_top ),
% 3.06/1.00      inference(superposition,[status(thm)],[c_1874,c_1879]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_2260,plain,
% 3.06/1.00      ( ~ v1_funct_2(sK1,X0,X0)
% 3.06/1.00      | ~ v3_funct_2(sK1,X0,X0)
% 3.06/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 3.06/1.00      | v1_funct_1(k2_funct_2(X0,sK1))
% 3.06/1.00      | ~ v1_funct_1(sK1) ),
% 3.06/1.00      inference(instantiation,[status(thm)],[c_30]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_2450,plain,
% 3.06/1.00      ( ~ v1_funct_2(sK1,sK0,sK0)
% 3.06/1.00      | ~ v3_funct_2(sK1,sK0,sK0)
% 3.06/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.06/1.00      | v1_funct_1(k2_funct_2(sK0,sK1))
% 3.06/1.00      | ~ v1_funct_1(sK1) ),
% 3.06/1.00      inference(instantiation,[status(thm)],[c_2260]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_2451,plain,
% 3.06/1.00      ( v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.06/1.00      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.06/1.00      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.06/1.00      | v1_funct_1(k2_funct_2(sK0,sK1)) = iProver_top
% 3.06/1.00      | v1_funct_1(sK1) != iProver_top ),
% 3.06/1.00      inference(predicate_to_equality,[status(thm)],[c_2450]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_3963,plain,
% 3.06/1.00      ( v1_funct_1(k2_funct_2(sK0,sK1)) = iProver_top ),
% 3.06/1.00      inference(global_propositional_subsumption,
% 3.06/1.00                [status(thm)],
% 3.06/1.00                [c_3482,c_39,c_40,c_41,c_42,c_2451]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_5636,plain,
% 3.06/1.00      ( v1_funct_1(k2_funct_1(sK1)) = iProver_top ),
% 3.06/1.00      inference(demodulation,[status(thm)],[c_5630,c_3963]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_8926,plain,
% 3.06/1.00      ( v1_funct_1(X2) != iProver_top
% 3.06/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.06/1.00      | k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1)) ),
% 3.06/1.00      inference(global_propositional_subsumption,
% 3.06/1.00                [status(thm)],
% 3.06/1.00                [c_6912,c_5636]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_8927,plain,
% 3.06/1.00      ( k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1))
% 3.06/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.06/1.00      | v1_funct_1(X2) != iProver_top ),
% 3.06/1.00      inference(renaming,[status(thm)],[c_8926]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_8938,plain,
% 3.06/1.00      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k5_relat_1(sK1,k2_funct_1(sK1))
% 3.06/1.00      | v1_funct_1(sK1) != iProver_top ),
% 3.06/1.00      inference(superposition,[status(thm)],[c_1874,c_8927]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1871,plain,
% 3.06/1.00      ( v1_funct_1(sK1) = iProver_top ),
% 3.06/1.00      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_11,plain,
% 3.06/1.00      ( ~ v1_funct_1(X0)
% 3.06/1.00      | ~ v2_funct_1(X0)
% 3.06/1.00      | ~ v1_relat_1(X0)
% 3.06/1.00      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
% 3.06/1.00      inference(cnf_transformation,[],[f96]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1893,plain,
% 3.06/1.00      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
% 3.06/1.00      | v1_funct_1(X0) != iProver_top
% 3.06/1.00      | v2_funct_1(X0) != iProver_top
% 3.06/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.06/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_3820,plain,
% 3.06/1.00      ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
% 3.06/1.00      | v2_funct_1(sK1) != iProver_top
% 3.06/1.00      | v1_relat_1(sK1) != iProver_top ),
% 3.06/1.00      inference(superposition,[status(thm)],[c_1871,c_1893]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_12,plain,
% 3.06/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.06/1.00      | v1_relat_1(X0) ),
% 3.06/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_2180,plain,
% 3.06/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.06/1.00      | v1_relat_1(sK1) ),
% 3.06/1.00      inference(instantiation,[status(thm)],[c_12]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_2204,plain,
% 3.06/1.00      ( ~ v1_funct_1(sK1)
% 3.06/1.00      | ~ v2_funct_1(sK1)
% 3.06/1.00      | ~ v1_relat_1(sK1)
% 3.06/1.00      | k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
% 3.06/1.00      inference(instantiation,[status(thm)],[c_11]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_17,plain,
% 3.06/1.00      ( ~ v3_funct_2(X0,X1,X2)
% 3.06/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.06/1.00      | ~ v1_funct_1(X0)
% 3.06/1.00      | v2_funct_1(X0) ),
% 3.06/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_2227,plain,
% 3.06/1.00      ( ~ v3_funct_2(sK1,X0,X1)
% 3.06/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.06/1.00      | ~ v1_funct_1(sK1)
% 3.06/1.00      | v2_funct_1(sK1) ),
% 3.06/1.00      inference(instantiation,[status(thm)],[c_17]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_2368,plain,
% 3.06/1.00      ( ~ v3_funct_2(sK1,sK0,sK0)
% 3.06/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.06/1.00      | ~ v1_funct_1(sK1)
% 3.06/1.00      | v2_funct_1(sK1) ),
% 3.06/1.00      inference(instantiation,[status(thm)],[c_2227]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_3959,plain,
% 3.06/1.00      ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
% 3.06/1.00      inference(global_propositional_subsumption,
% 3.06/1.00                [status(thm)],
% 3.06/1.00                [c_3820,c_38,c_36,c_35,c_2180,c_2204,c_2368]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_8951,plain,
% 3.06/1.00      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
% 3.06/1.00      | v1_funct_1(sK1) != iProver_top ),
% 3.06/1.00      inference(light_normalisation,[status(thm)],[c_8938,c_3959]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_9204,plain,
% 3.06/1.00      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
% 3.06/1.00      inference(global_propositional_subsumption,
% 3.06/1.00                [status(thm)],
% 3.06/1.00                [c_8951,c_39]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_5390,plain,
% 3.06/1.00      ( k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1)
% 3.06/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.06/1.00      | v1_funct_1(X2) != iProver_top
% 3.06/1.00      | v1_funct_1(sK1) != iProver_top ),
% 3.06/1.00      inference(superposition,[status(thm)],[c_1874,c_1877]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_5813,plain,
% 3.06/1.00      ( v1_funct_1(X2) != iProver_top
% 3.06/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.06/1.00      | k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1) ),
% 3.06/1.00      inference(global_propositional_subsumption,
% 3.06/1.00                [status(thm)],
% 3.06/1.00                [c_5390,c_39]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_5814,plain,
% 3.06/1.00      ( k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1)
% 3.06/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.06/1.00      | v1_funct_1(X2) != iProver_top ),
% 3.06/1.00      inference(renaming,[status(thm)],[c_5813]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_5823,plain,
% 3.06/1.00      ( k1_partfun1(X0,X0,sK0,sK0,k2_funct_2(X0,X1),sK1) = k5_relat_1(k2_funct_2(X0,X1),sK1)
% 3.06/1.00      | v1_funct_2(X1,X0,X0) != iProver_top
% 3.06/1.00      | v3_funct_2(X1,X0,X0) != iProver_top
% 3.06/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 3.06/1.00      | v1_funct_1(X1) != iProver_top
% 3.06/1.00      | v1_funct_1(k2_funct_2(X0,X1)) != iProver_top ),
% 3.06/1.00      inference(superposition,[status(thm)],[c_1882,c_5814]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_7013,plain,
% 3.06/1.00      ( k1_partfun1(X0,X0,sK0,sK0,k2_funct_2(X0,X1),sK1) = k5_relat_1(k2_funct_2(X0,X1),sK1)
% 3.06/1.00      | v1_funct_2(X1,X0,X0) != iProver_top
% 3.06/1.00      | v3_funct_2(X1,X0,X0) != iProver_top
% 3.06/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 3.06/1.00      | v1_funct_1(X1) != iProver_top ),
% 3.06/1.00      inference(forward_subsumption_resolution,
% 3.06/1.00                [status(thm)],
% 3.06/1.00                [c_5823,c_1879]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_7020,plain,
% 3.06/1.00      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1) = k5_relat_1(k2_funct_2(sK0,sK1),sK1)
% 3.06/1.00      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.06/1.00      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.06/1.00      | v1_funct_1(sK1) != iProver_top ),
% 3.06/1.00      inference(superposition,[status(thm)],[c_1874,c_7013]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_10,plain,
% 3.06/1.00      ( ~ v1_funct_1(X0)
% 3.06/1.00      | ~ v2_funct_1(X0)
% 3.06/1.00      | ~ v1_relat_1(X0)
% 3.06/1.00      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
% 3.06/1.00      inference(cnf_transformation,[],[f95]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1894,plain,
% 3.06/1.00      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
% 3.06/1.00      | v1_funct_1(X0) != iProver_top
% 3.06/1.00      | v2_funct_1(X0) != iProver_top
% 3.06/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.06/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_4374,plain,
% 3.06/1.00      ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1))
% 3.06/1.00      | v2_funct_1(sK1) != iProver_top
% 3.06/1.00      | v1_relat_1(sK1) != iProver_top ),
% 3.06/1.00      inference(superposition,[status(thm)],[c_1871,c_1894]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_16,plain,
% 3.06/1.00      ( ~ v3_funct_2(X0,X1,X2)
% 3.06/1.00      | v2_funct_2(X0,X2)
% 3.06/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.06/1.00      | ~ v1_funct_1(X0) ),
% 3.06/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_26,plain,
% 3.06/1.00      ( ~ v2_funct_2(X0,X1)
% 3.06/1.00      | ~ v5_relat_1(X0,X1)
% 3.06/1.00      | ~ v1_relat_1(X0)
% 3.06/1.00      | k2_relat_1(X0) = X1 ),
% 3.06/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_501,plain,
% 3.06/1.00      ( ~ v3_funct_2(X0,X1,X2)
% 3.06/1.00      | ~ v5_relat_1(X3,X4)
% 3.06/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.06/1.00      | ~ v1_funct_1(X0)
% 3.06/1.00      | ~ v1_relat_1(X3)
% 3.06/1.00      | X3 != X0
% 3.06/1.00      | X4 != X2
% 3.06/1.00      | k2_relat_1(X3) = X4 ),
% 3.06/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_26]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_502,plain,
% 3.06/1.00      ( ~ v3_funct_2(X0,X1,X2)
% 3.06/1.00      | ~ v5_relat_1(X0,X2)
% 3.06/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.06/1.00      | ~ v1_funct_1(X0)
% 3.06/1.00      | ~ v1_relat_1(X0)
% 3.06/1.00      | k2_relat_1(X0) = X2 ),
% 3.06/1.00      inference(unflattening,[status(thm)],[c_501]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_506,plain,
% 3.06/1.00      ( ~ v1_funct_1(X0)
% 3.06/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.06/1.00      | ~ v5_relat_1(X0,X2)
% 3.06/1.00      | ~ v3_funct_2(X0,X1,X2)
% 3.06/1.00      | k2_relat_1(X0) = X2 ),
% 3.06/1.00      inference(global_propositional_subsumption,
% 3.06/1.00                [status(thm)],
% 3.06/1.00                [c_502,c_12]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_507,plain,
% 3.06/1.00      ( ~ v3_funct_2(X0,X1,X2)
% 3.06/1.00      | ~ v5_relat_1(X0,X2)
% 3.06/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.06/1.00      | ~ v1_funct_1(X0)
% 3.06/1.00      | k2_relat_1(X0) = X2 ),
% 3.06/1.00      inference(renaming,[status(thm)],[c_506]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_13,plain,
% 3.06/1.00      ( v5_relat_1(X0,X1)
% 3.06/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.06/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_522,plain,
% 3.06/1.00      ( ~ v3_funct_2(X0,X1,X2)
% 3.06/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.06/1.00      | ~ v1_funct_1(X0)
% 3.06/1.00      | k2_relat_1(X0) = X2 ),
% 3.06/1.00      inference(forward_subsumption_resolution,
% 3.06/1.00                [status(thm)],
% 3.06/1.00                [c_507,c_13]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1870,plain,
% 3.06/1.00      ( k2_relat_1(X0) = X1
% 3.06/1.00      | v3_funct_2(X0,X2,X1) != iProver_top
% 3.06/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
% 3.06/1.00      | v1_funct_1(X0) != iProver_top ),
% 3.06/1.00      inference(predicate_to_equality,[status(thm)],[c_522]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_2897,plain,
% 3.06/1.00      ( k2_relat_1(sK1) = sK0
% 3.06/1.00      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.06/1.00      | v1_funct_1(sK1) != iProver_top ),
% 3.06/1.00      inference(superposition,[status(thm)],[c_1874,c_1870]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_2239,plain,
% 3.06/1.00      ( ~ v3_funct_2(sK1,X0,X1)
% 3.06/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.06/1.00      | ~ v1_funct_1(sK1)
% 3.06/1.00      | k2_relat_1(sK1) = X1 ),
% 3.06/1.00      inference(instantiation,[status(thm)],[c_522]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_2371,plain,
% 3.06/1.00      ( ~ v3_funct_2(sK1,sK0,sK0)
% 3.06/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.06/1.00      | ~ v1_funct_1(sK1)
% 3.06/1.00      | k2_relat_1(sK1) = sK0 ),
% 3.06/1.00      inference(instantiation,[status(thm)],[c_2239]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_3261,plain,
% 3.06/1.00      ( k2_relat_1(sK1) = sK0 ),
% 3.06/1.00      inference(global_propositional_subsumption,
% 3.06/1.00                [status(thm)],
% 3.06/1.00                [c_2897,c_38,c_36,c_35,c_2371]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_4385,plain,
% 3.06/1.00      ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
% 3.06/1.00      | v2_funct_1(sK1) != iProver_top
% 3.06/1.00      | v1_relat_1(sK1) != iProver_top ),
% 3.06/1.00      inference(light_normalisation,[status(thm)],[c_4374,c_3261]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_2181,plain,
% 3.06/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.06/1.00      | v1_relat_1(sK1) = iProver_top ),
% 3.06/1.00      inference(predicate_to_equality,[status(thm)],[c_2180]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_2369,plain,
% 3.06/1.00      ( v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.06/1.00      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.06/1.00      | v1_funct_1(sK1) != iProver_top
% 3.06/1.00      | v2_funct_1(sK1) = iProver_top ),
% 3.06/1.00      inference(predicate_to_equality,[status(thm)],[c_2368]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_4693,plain,
% 3.06/1.00      ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(sK0) ),
% 3.06/1.00      inference(global_propositional_subsumption,
% 3.06/1.00                [status(thm)],
% 3.06/1.00                [c_4385,c_39,c_41,c_42,c_2181,c_2369]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_7043,plain,
% 3.06/1.00      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
% 3.06/1.00      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.06/1.00      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.06/1.00      | v1_funct_1(sK1) != iProver_top ),
% 3.06/1.00      inference(light_normalisation,[status(thm)],[c_7020,c_4693,c_5630]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_6900,plain,
% 3.06/1.00      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k5_relat_1(k2_funct_1(sK1),sK1)
% 3.06/1.00      | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
% 3.06/1.00      inference(superposition,[status(thm)],[c_6894,c_5814]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_6984,plain,
% 3.06/1.00      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
% 3.06/1.00      | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
% 3.06/1.00      inference(light_normalisation,[status(thm)],[c_6900,c_4693]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_7359,plain,
% 3.06/1.00      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0) ),
% 3.06/1.00      inference(global_propositional_subsumption,
% 3.06/1.00                [status(thm)],
% 3.06/1.00                [c_7043,c_5636,c_6984]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_34,negated_conjecture,
% 3.06/1.00      ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
% 3.06/1.00      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
% 3.06/1.00      inference(cnf_transformation,[],[f94]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1875,plain,
% 3.06/1.00      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) != iProver_top
% 3.06/1.00      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) != iProver_top ),
% 3.06/1.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_5637,plain,
% 3.06/1.00      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) != iProver_top
% 3.06/1.00      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
% 3.06/1.00      inference(demodulation,[status(thm)],[c_5630,c_1875]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_7362,plain,
% 3.06/1.00      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top
% 3.06/1.00      | r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
% 3.06/1.00      inference(demodulation,[status(thm)],[c_7359,c_5637]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_31,plain,
% 3.06/1.00      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.06/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_2360,plain,
% 3.06/1.00      ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.06/1.00      inference(instantiation,[status(thm)],[c_31]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_2363,plain,
% 3.06/1.00      ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.06/1.00      inference(predicate_to_equality,[status(thm)],[c_2360]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_15,plain,
% 3.06/1.00      ( r2_relset_1(X0,X1,X2,X2)
% 3.06/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.06/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.06/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_2245,plain,
% 3.06/1.00      ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0))
% 3.06/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 3.06/1.00      | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.06/1.00      inference(instantiation,[status(thm)],[c_15]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_2835,plain,
% 3.06/1.00      ( r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))
% 3.06/1.00      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.06/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.06/1.00      inference(instantiation,[status(thm)],[c_2245]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_2836,plain,
% 3.06/1.00      ( r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) = iProver_top
% 3.06/1.00      | m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.06/1.00      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.06/1.00      inference(predicate_to_equality,[status(thm)],[c_2835]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_8058,plain,
% 3.06/1.00      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
% 3.06/1.00      inference(global_propositional_subsumption,
% 3.06/1.00                [status(thm)],
% 3.06/1.00                [c_7362,c_42,c_2363,c_2836]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_9207,plain,
% 3.06/1.00      ( r2_relset_1(sK0,sK0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
% 3.06/1.00      inference(demodulation,[status(thm)],[c_9204,c_8058]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_9211,plain,
% 3.06/1.00      ( sK0 = k1_xboole_0
% 3.06/1.00      | r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
% 3.06/1.00      inference(superposition,[status(thm)],[c_4780,c_9207]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_9314,plain,
% 3.06/1.00      ( sK0 = k1_xboole_0 ),
% 3.06/1.00      inference(global_propositional_subsumption,
% 3.06/1.00                [status(thm)],
% 3.06/1.00                [c_9211,c_42,c_2363,c_2836]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_9317,plain,
% 3.06/1.00      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(k1_xboole_0)) != iProver_top ),
% 3.06/1.00      inference(demodulation,[status(thm)],[c_9314,c_9207]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_8,plain,
% 3.06/1.00      ( ~ v1_relat_1(X0)
% 3.06/1.00      | k2_relat_1(X0) != k1_xboole_0
% 3.06/1.00      | k1_xboole_0 = X0 ),
% 3.06/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1896,plain,
% 3.06/1.00      ( k2_relat_1(X0) != k1_xboole_0
% 3.06/1.00      | k1_xboole_0 = X0
% 3.06/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.06/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_3265,plain,
% 3.06/1.00      ( sK1 = k1_xboole_0
% 3.06/1.00      | sK0 != k1_xboole_0
% 3.06/1.00      | v1_relat_1(sK1) != iProver_top ),
% 3.06/1.00      inference(superposition,[status(thm)],[c_3261,c_1896]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_3266,plain,
% 3.06/1.00      ( ~ v1_relat_1(sK1) | sK1 = k1_xboole_0 | sK0 != k1_xboole_0 ),
% 3.06/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_3265]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_3312,plain,
% 3.06/1.00      ( sK0 != k1_xboole_0 | sK1 = k1_xboole_0 ),
% 3.06/1.00      inference(global_propositional_subsumption,
% 3.06/1.00                [status(thm)],
% 3.06/1.00                [c_3265,c_35,c_2180,c_3266]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_3313,plain,
% 3.06/1.00      ( sK1 = k1_xboole_0 | sK0 != k1_xboole_0 ),
% 3.06/1.00      inference(renaming,[status(thm)],[c_3312]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_9348,plain,
% 3.06/1.00      ( sK1 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.06/1.00      inference(demodulation,[status(thm)],[c_9314,c_3313]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_9372,plain,
% 3.06/1.00      ( sK1 = k1_xboole_0 ),
% 3.06/1.00      inference(equality_resolution_simp,[status(thm)],[c_9348]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_9318,plain,
% 3.06/1.00      ( k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
% 3.06/1.00      inference(demodulation,[status(thm)],[c_9314,c_9204]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_6907,plain,
% 3.06/1.00      ( k2_relat_1(k2_funct_1(sK1)) = sK0
% 3.06/1.00      | v3_funct_2(k2_funct_1(sK1),sK0,sK0) != iProver_top
% 3.06/1.00      | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
% 3.06/1.00      inference(superposition,[status(thm)],[c_6894,c_1870]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_28,plain,
% 3.06/1.00      ( ~ v1_funct_2(X0,X1,X1)
% 3.06/1.00      | ~ v3_funct_2(X0,X1,X1)
% 3.06/1.00      | v3_funct_2(k2_funct_2(X1,X0),X1,X1)
% 3.06/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.06/1.00      | ~ v1_funct_1(X0) ),
% 3.06/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1881,plain,
% 3.06/1.00      ( v1_funct_2(X0,X1,X1) != iProver_top
% 3.06/1.00      | v3_funct_2(X0,X1,X1) != iProver_top
% 3.06/1.00      | v3_funct_2(k2_funct_2(X1,X0),X1,X1) = iProver_top
% 3.06/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 3.06/1.00      | v1_funct_1(X0) != iProver_top ),
% 3.06/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_4856,plain,
% 3.06/1.00      ( v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.06/1.00      | v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0) = iProver_top
% 3.06/1.00      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.06/1.00      | v1_funct_1(sK1) != iProver_top ),
% 3.06/1.00      inference(superposition,[status(thm)],[c_1874,c_1881]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_2285,plain,
% 3.06/1.00      ( ~ v1_funct_2(sK1,X0,X0)
% 3.06/1.00      | v3_funct_2(k2_funct_2(X0,sK1),X0,X0)
% 3.06/1.00      | ~ v3_funct_2(sK1,X0,X0)
% 3.06/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 3.06/1.00      | ~ v1_funct_1(sK1) ),
% 3.06/1.00      inference(instantiation,[status(thm)],[c_28]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_2459,plain,
% 3.06/1.00      ( ~ v1_funct_2(sK1,sK0,sK0)
% 3.06/1.00      | v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0)
% 3.06/1.00      | ~ v3_funct_2(sK1,sK0,sK0)
% 3.06/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.06/1.00      | ~ v1_funct_1(sK1) ),
% 3.06/1.00      inference(instantiation,[status(thm)],[c_2285]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_2460,plain,
% 3.06/1.00      ( v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.06/1.00      | v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0) = iProver_top
% 3.06/1.00      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.06/1.00      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.06/1.00      | v1_funct_1(sK1) != iProver_top ),
% 3.06/1.00      inference(predicate_to_equality,[status(thm)],[c_2459]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_5805,plain,
% 3.06/1.00      ( v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0) = iProver_top ),
% 3.06/1.00      inference(global_propositional_subsumption,
% 3.06/1.00                [status(thm)],
% 3.06/1.00                [c_4856,c_39,c_40,c_41,c_42,c_2460]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_5809,plain,
% 3.06/1.00      ( v3_funct_2(k2_funct_1(sK1),sK0,sK0) = iProver_top ),
% 3.06/1.00      inference(light_normalisation,[status(thm)],[c_5805,c_5630]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_8299,plain,
% 3.06/1.00      ( k2_relat_1(k2_funct_1(sK1)) = sK0 ),
% 3.06/1.00      inference(global_propositional_subsumption,
% 3.06/1.00                [status(thm)],
% 3.06/1.00                [c_6907,c_5636,c_5809]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_8306,plain,
% 3.06/1.00      ( k2_funct_1(sK1) = k1_xboole_0
% 3.06/1.00      | sK0 != k1_xboole_0
% 3.06/1.00      | v1_relat_1(k2_funct_1(sK1)) != iProver_top ),
% 3.06/1.00      inference(superposition,[status(thm)],[c_8299,c_1896]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1892,plain,
% 3.06/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.06/1.00      | v1_relat_1(X0) = iProver_top ),
% 3.06/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_6905,plain,
% 3.06/1.00      ( v1_relat_1(k2_funct_1(sK1)) = iProver_top ),
% 3.06/1.00      inference(superposition,[status(thm)],[c_6894,c_1892]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_9052,plain,
% 3.06/1.00      ( sK0 != k1_xboole_0 | k2_funct_1(sK1) = k1_xboole_0 ),
% 3.06/1.00      inference(global_propositional_subsumption,
% 3.06/1.00                [status(thm)],
% 3.06/1.00                [c_8306,c_6905]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_9053,plain,
% 3.06/1.00      ( k2_funct_1(sK1) = k1_xboole_0 | sK0 != k1_xboole_0 ),
% 3.06/1.00      inference(renaming,[status(thm)],[c_9052]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_9319,plain,
% 3.06/1.00      ( k2_funct_1(sK1) = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.06/1.00      inference(demodulation,[status(thm)],[c_9314,c_9053]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_9499,plain,
% 3.06/1.00      ( k2_funct_1(sK1) = k1_xboole_0 ),
% 3.06/1.00      inference(equality_resolution_simp,[status(thm)],[c_9319]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_9500,plain,
% 3.06/1.00      ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
% 3.06/1.00      inference(light_normalisation,[status(thm)],[c_9499,c_9372]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_9346,plain,
% 3.06/1.00      ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k1_xboole_0) ),
% 3.06/1.00      inference(demodulation,[status(thm)],[c_9314,c_4693]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_9388,plain,
% 3.06/1.00      ( k5_relat_1(k2_funct_1(k1_xboole_0),k1_xboole_0) = k6_partfun1(k1_xboole_0) ),
% 3.06/1.00      inference(light_normalisation,[status(thm)],[c_9346,c_9372]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1878,plain,
% 3.06/1.00      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 3.06/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_7,plain,
% 3.06/1.00      ( ~ v5_relat_1(X0,X1)
% 3.06/1.00      | r1_tarski(k2_relat_1(X0),X1)
% 3.06/1.00      | ~ v1_relat_1(X0) ),
% 3.06/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_537,plain,
% 3.06/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.06/1.00      | r1_tarski(k2_relat_1(X0),X2)
% 3.06/1.00      | ~ v1_relat_1(X0) ),
% 3.06/1.00      inference(resolution,[status(thm)],[c_13,c_7]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_541,plain,
% 3.06/1.00      ( r1_tarski(k2_relat_1(X0),X2)
% 3.06/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.06/1.00      inference(global_propositional_subsumption,
% 3.06/1.00                [status(thm)],
% 3.06/1.00                [c_537,c_12]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_542,plain,
% 3.06/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.06/1.00      | r1_tarski(k2_relat_1(X0),X2) ),
% 3.06/1.00      inference(renaming,[status(thm)],[c_541]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1869,plain,
% 3.06/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.06/1.00      | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
% 3.06/1.00      inference(predicate_to_equality,[status(thm)],[c_542]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_2307,plain,
% 3.06/1.00      ( r1_tarski(k2_relat_1(k6_partfun1(X0)),X0) = iProver_top ),
% 3.06/1.00      inference(superposition,[status(thm)],[c_1878,c_1869]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_3,plain,
% 3.06/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 3.06/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1899,plain,
% 3.06/1.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.06/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_0,plain,
% 3.06/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.06/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1901,plain,
% 3.06/1.00      ( X0 = X1
% 3.06/1.00      | r1_tarski(X0,X1) != iProver_top
% 3.06/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 3.06/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_3172,plain,
% 3.06/1.00      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.06/1.00      inference(superposition,[status(thm)],[c_1899,c_1901]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_4178,plain,
% 3.06/1.00      ( k2_relat_1(k6_partfun1(k1_xboole_0)) = k1_xboole_0 ),
% 3.06/1.00      inference(superposition,[status(thm)],[c_2307,c_3172]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_4261,plain,
% 3.06/1.00      ( k6_partfun1(k1_xboole_0) = k1_xboole_0
% 3.06/1.00      | v1_relat_1(k6_partfun1(k1_xboole_0)) != iProver_top ),
% 3.06/1.00      inference(superposition,[status(thm)],[c_4178,c_1896]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_50,plain,
% 3.06/1.00      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 3.06/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_52,plain,
% 3.06/1.00      ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 3.06/1.00      inference(instantiation,[status(thm)],[c_50]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_2175,plain,
% 3.06/1.00      ( ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 3.06/1.00      | v1_relat_1(k6_partfun1(X0)) ),
% 3.06/1.00      inference(instantiation,[status(thm)],[c_12]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_2176,plain,
% 3.06/1.00      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 3.06/1.00      | v1_relat_1(k6_partfun1(X0)) = iProver_top ),
% 3.06/1.00      inference(predicate_to_equality,[status(thm)],[c_2175]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_2178,plain,
% 3.06/1.00      ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 3.06/1.00      | v1_relat_1(k6_partfun1(k1_xboole_0)) = iProver_top ),
% 3.06/1.00      inference(instantiation,[status(thm)],[c_2176]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_4270,plain,
% 3.06/1.00      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 3.06/1.00      inference(global_propositional_subsumption,
% 3.06/1.00                [status(thm)],
% 3.06/1.00                [c_4261,c_52,c_2178]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_9390,plain,
% 3.06/1.00      ( k5_relat_1(k2_funct_1(k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
% 3.06/1.00      inference(light_normalisation,[status(thm)],[c_9388,c_4270]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_9517,plain,
% 3.06/1.00      ( k5_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.06/1.00      inference(demodulation,[status(thm)],[c_9500,c_9390]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_5825,plain,
% 3.06/1.00      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK1) = k5_relat_1(sK1,sK1)
% 3.06/1.00      | v1_funct_1(sK1) != iProver_top ),
% 3.06/1.00      inference(superposition,[status(thm)],[c_1874,c_5814]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_5929,plain,
% 3.06/1.00      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK1) = k5_relat_1(sK1,sK1) ),
% 3.06/1.00      inference(global_propositional_subsumption,
% 3.06/1.00                [status(thm)],
% 3.06/1.00                [c_5825,c_39]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_9341,plain,
% 3.06/1.00      ( k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK1,sK1) = k5_relat_1(sK1,sK1) ),
% 3.06/1.00      inference(demodulation,[status(thm)],[c_9314,c_5929]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_9405,plain,
% 3.06/1.00      ( k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k5_relat_1(k1_xboole_0,k1_xboole_0) ),
% 3.06/1.00      inference(light_normalisation,[status(thm)],[c_9341,c_9372]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_9521,plain,
% 3.06/1.00      ( k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.06/1.00      inference(demodulation,[status(thm)],[c_9517,c_9405]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_9531,plain,
% 3.06/1.00      ( k6_partfun1(k1_relat_1(k1_xboole_0)) = k1_xboole_0 ),
% 3.06/1.00      inference(light_normalisation,
% 3.06/1.00                [status(thm)],
% 3.06/1.00                [c_9318,c_9372,c_9500,c_9521]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_9534,plain,
% 3.06/1.00      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0)) != iProver_top ),
% 3.06/1.00      inference(light_normalisation,[status(thm)],[c_9317,c_9372,c_9531]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_9536,plain,
% 3.06/1.00      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.06/1.00      inference(light_normalisation,[status(thm)],[c_9534,c_4270]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_2634,plain,
% 3.06/1.00      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) ),
% 3.06/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_2637,plain,
% 3.06/1.00      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.06/1.00      inference(predicate_to_equality,[status(thm)],[c_2634]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_2639,plain,
% 3.06/1.00      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 3.06/1.00      inference(instantiation,[status(thm)],[c_2637]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_4,plain,
% 3.06/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.06/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_2170,plain,
% 3.06/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.06/1.00      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
% 3.06/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_2171,plain,
% 3.06/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 3.06/1.00      | r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
% 3.06/1.00      inference(predicate_to_equality,[status(thm)],[c_2170]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_2173,plain,
% 3.06/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
% 3.06/1.00      | r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 3.06/1.00      inference(instantiation,[status(thm)],[c_2171]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_96,plain,
% 3.06/1.00      ( r2_relset_1(X0,X1,X2,X2) = iProver_top
% 3.06/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.06/1.00      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.06/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_98,plain,
% 3.06/1.00      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top
% 3.06/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 3.06/1.00      inference(instantiation,[status(thm)],[c_96]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(contradiction,plain,
% 3.06/1.00      ( $false ),
% 3.06/1.00      inference(minisat,[status(thm)],[c_9536,c_2639,c_2173,c_98]) ).
% 3.06/1.00  
% 3.06/1.00  
% 3.06/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.06/1.00  
% 3.06/1.00  ------                               Statistics
% 3.06/1.00  
% 3.06/1.00  ------ General
% 3.06/1.00  
% 3.06/1.00  abstr_ref_over_cycles:                  0
% 3.06/1.00  abstr_ref_under_cycles:                 0
% 3.06/1.00  gc_basic_clause_elim:                   0
% 3.06/1.00  forced_gc_time:                         0
% 3.06/1.00  parsing_time:                           0.007
% 3.06/1.00  unif_index_cands_time:                  0.
% 3.06/1.00  unif_index_add_time:                    0.
% 3.06/1.00  orderings_time:                         0.
% 3.06/1.00  out_proof_time:                         0.017
% 3.06/1.00  total_time:                             0.241
% 3.06/1.00  num_of_symbols:                         54
% 3.06/1.00  num_of_terms:                           7970
% 3.06/1.00  
% 3.06/1.00  ------ Preprocessing
% 3.06/1.00  
% 3.06/1.00  num_of_splits:                          0
% 3.06/1.00  num_of_split_atoms:                     0
% 3.06/1.00  num_of_reused_defs:                     0
% 3.06/1.00  num_eq_ax_congr_red:                    26
% 3.06/1.00  num_of_sem_filtered_clauses:            1
% 3.06/1.00  num_of_subtypes:                        0
% 3.06/1.00  monotx_restored_types:                  0
% 3.06/1.00  sat_num_of_epr_types:                   0
% 3.06/1.00  sat_num_of_non_cyclic_types:            0
% 3.06/1.00  sat_guarded_non_collapsed_types:        0
% 3.06/1.00  num_pure_diseq_elim:                    0
% 3.06/1.00  simp_replaced_by:                       0
% 3.06/1.00  res_preprocessed:                       167
% 3.06/1.00  prep_upred:                             0
% 3.06/1.00  prep_unflattend:                        4
% 3.06/1.00  smt_new_axioms:                         0
% 3.06/1.00  pred_elim_cands:                        8
% 3.06/1.00  pred_elim:                              2
% 3.06/1.00  pred_elim_cl:                           4
% 3.06/1.00  pred_elim_cycles:                       6
% 3.06/1.00  merged_defs:                            8
% 3.06/1.00  merged_defs_ncl:                        0
% 3.06/1.00  bin_hyper_res:                          8
% 3.06/1.00  prep_cycles:                            4
% 3.06/1.00  pred_elim_time:                         0.004
% 3.06/1.00  splitting_time:                         0.
% 3.06/1.00  sem_filter_time:                        0.
% 3.06/1.00  monotx_time:                            0.
% 3.06/1.00  subtype_inf_time:                       0.
% 3.06/1.00  
% 3.06/1.00  ------ Problem properties
% 3.06/1.00  
% 3.06/1.00  clauses:                                33
% 3.06/1.00  conjectures:                            5
% 3.06/1.00  epr:                                    6
% 3.06/1.00  horn:                                   29
% 3.06/1.00  ground:                                 5
% 3.06/1.00  unary:                                  7
% 3.06/1.00  binary:                                 6
% 3.06/1.00  lits:                                   98
% 3.06/1.00  lits_eq:                                20
% 3.06/1.00  fd_pure:                                0
% 3.06/1.00  fd_pseudo:                              0
% 3.06/1.00  fd_cond:                                5
% 3.06/1.00  fd_pseudo_cond:                         2
% 3.06/1.00  ac_symbols:                             0
% 3.06/1.00  
% 3.06/1.00  ------ Propositional Solver
% 3.06/1.00  
% 3.06/1.00  prop_solver_calls:                      29
% 3.06/1.00  prop_fast_solver_calls:                 1431
% 3.06/1.00  smt_solver_calls:                       0
% 3.06/1.00  smt_fast_solver_calls:                  0
% 3.06/1.00  prop_num_of_clauses:                    3364
% 3.06/1.00  prop_preprocess_simplified:             9659
% 3.06/1.00  prop_fo_subsumed:                       67
% 3.06/1.00  prop_solver_time:                       0.
% 3.06/1.00  smt_solver_time:                        0.
% 3.06/1.00  smt_fast_solver_time:                   0.
% 3.06/1.00  prop_fast_solver_time:                  0.
% 3.06/1.00  prop_unsat_core_time:                   0.
% 3.06/1.00  
% 3.06/1.00  ------ QBF
% 3.06/1.00  
% 3.06/1.00  qbf_q_res:                              0
% 3.06/1.00  qbf_num_tautologies:                    0
% 3.06/1.00  qbf_prep_cycles:                        0
% 3.06/1.00  
% 3.06/1.00  ------ BMC1
% 3.06/1.00  
% 3.06/1.00  bmc1_current_bound:                     -1
% 3.06/1.00  bmc1_last_solved_bound:                 -1
% 3.06/1.00  bmc1_unsat_core_size:                   -1
% 3.06/1.00  bmc1_unsat_core_parents_size:           -1
% 3.06/1.00  bmc1_merge_next_fun:                    0
% 3.06/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.06/1.00  
% 3.06/1.00  ------ Instantiation
% 3.06/1.00  
% 3.06/1.00  inst_num_of_clauses:                    979
% 3.06/1.00  inst_num_in_passive:                    383
% 3.06/1.00  inst_num_in_active:                     438
% 3.06/1.00  inst_num_in_unprocessed:                161
% 3.06/1.00  inst_num_of_loops:                      580
% 3.06/1.00  inst_num_of_learning_restarts:          0
% 3.06/1.00  inst_num_moves_active_passive:          139
% 3.06/1.00  inst_lit_activity:                      0
% 3.06/1.00  inst_lit_activity_moves:                0
% 3.06/1.00  inst_num_tautologies:                   0
% 3.06/1.00  inst_num_prop_implied:                  0
% 3.06/1.00  inst_num_existing_simplified:           0
% 3.06/1.00  inst_num_eq_res_simplified:             0
% 3.06/1.00  inst_num_child_elim:                    0
% 3.06/1.00  inst_num_of_dismatching_blockings:      296
% 3.06/1.00  inst_num_of_non_proper_insts:           952
% 3.06/1.00  inst_num_of_duplicates:                 0
% 3.06/1.00  inst_inst_num_from_inst_to_res:         0
% 3.06/1.00  inst_dismatching_checking_time:         0.
% 3.06/1.00  
% 3.06/1.00  ------ Resolution
% 3.06/1.00  
% 3.06/1.00  res_num_of_clauses:                     0
% 3.06/1.00  res_num_in_passive:                     0
% 3.06/1.00  res_num_in_active:                      0
% 3.06/1.00  res_num_of_loops:                       171
% 3.06/1.00  res_forward_subset_subsumed:            44
% 3.06/1.00  res_backward_subset_subsumed:           10
% 3.06/1.00  res_forward_subsumed:                   0
% 3.06/1.00  res_backward_subsumed:                  0
% 3.06/1.00  res_forward_subsumption_resolution:     1
% 3.06/1.00  res_backward_subsumption_resolution:    0
% 3.06/1.00  res_clause_to_clause_subsumption:       420
% 3.06/1.00  res_orphan_elimination:                 0
% 3.06/1.00  res_tautology_del:                      51
% 3.06/1.00  res_num_eq_res_simplified:              0
% 3.06/1.00  res_num_sel_changes:                    0
% 3.06/1.00  res_moves_from_active_to_pass:          0
% 3.06/1.00  
% 3.06/1.00  ------ Superposition
% 3.06/1.00  
% 3.06/1.00  sup_time_total:                         0.
% 3.06/1.00  sup_time_generating:                    0.
% 3.06/1.00  sup_time_sim_full:                      0.
% 3.06/1.00  sup_time_sim_immed:                     0.
% 3.06/1.00  
% 3.06/1.00  sup_num_of_clauses:                     137
% 3.06/1.00  sup_num_in_active:                      62
% 3.06/1.00  sup_num_in_passive:                     75
% 3.06/1.00  sup_num_of_loops:                       114
% 3.06/1.00  sup_fw_superposition:                   116
% 3.06/1.00  sup_bw_superposition:                   78
% 3.06/1.00  sup_immediate_simplified:               26
% 3.06/1.00  sup_given_eliminated:                   0
% 3.06/1.00  comparisons_done:                       0
% 3.06/1.00  comparisons_avoided:                    0
% 3.06/1.00  
% 3.06/1.00  ------ Simplifications
% 3.06/1.00  
% 3.06/1.00  
% 3.06/1.00  sim_fw_subset_subsumed:                 6
% 3.06/1.00  sim_bw_subset_subsumed:                 4
% 3.06/1.00  sim_fw_subsumed:                        4
% 3.06/1.00  sim_bw_subsumed:                        0
% 3.06/1.00  sim_fw_subsumption_res:                 2
% 3.06/1.00  sim_bw_subsumption_res:                 0
% 3.06/1.00  sim_tautology_del:                      1
% 3.06/1.00  sim_eq_tautology_del:                   13
% 3.06/1.00  sim_eq_res_simp:                        2
% 3.06/1.00  sim_fw_demodulated:                     6
% 3.06/1.00  sim_bw_demodulated:                     76
% 3.06/1.00  sim_light_normalised:                   48
% 3.06/1.00  sim_joinable_taut:                      0
% 3.06/1.00  sim_joinable_simp:                      0
% 3.06/1.00  sim_ac_normalised:                      0
% 3.06/1.00  sim_smt_subsumption:                    0
% 3.06/1.00  
%------------------------------------------------------------------------------
