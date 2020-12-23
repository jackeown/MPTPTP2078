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
% DateTime   : Thu Dec  3 12:07:17 EST 2020

% Result     : Theorem 4.00s
% Output     : CNFRefutation 4.00s
% Verified   : 
% Statistics : Number of formulae       :  227 (3530 expanded)
%              Number of clauses        :  142 (1058 expanded)
%              Number of leaves         :   21 ( 689 expanded)
%              Depth                    :   27
%              Number of atoms          :  730 (16474 expanded)
%              Number of equality atoms :  352 (1903 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   13 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f22,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f51,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f52,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f51])).

fof(f58,plain,
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

fof(f59,plain,
    ( ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) )
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK1,sK0,sK0)
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f52,f58])).

fof(f101,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f59])).

fof(f14,axiom,(
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

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f56,plain,(
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
    inference(nnf_transformation,[],[f40])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f99,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f59])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_1(X1) = k2_funct_2(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f47])).

fof(f93,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f98,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f59])).

fof(f100,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f59])).

fof(f16,axiom,(
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

fof(f43,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f43])).

fof(f90,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f46,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f45])).

fof(f92,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f87,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k2_funct_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f30,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f68,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f20,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f94,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f20])).

fof(f104,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f68,f94])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f37])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f69,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f103,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f69,f94])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f41])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f102,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f59])).

fof(f17,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f91,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f35])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f55,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f67,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f53])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f106,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f64])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f107,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f63])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_38,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1599,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1610,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_6488,plain,
    ( k1_relset_1(sK0,sK0,sK1) = sK0
    | sK0 = k1_xboole_0
    | v1_funct_2(sK1,sK0,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1599,c_1610])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1618,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2704,plain,
    ( k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_1599,c_1618])).

cnf(c_6499,plain,
    ( k1_relat_1(sK1) = sK0
    | sK0 = k1_xboole_0
    | v1_funct_2(sK1,sK0,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6488,c_2704])).

cnf(c_40,negated_conjecture,
    ( v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_43,plain,
    ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_7219,plain,
    ( sK0 = k1_xboole_0
    | k1_relat_1(sK1) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6499,c_43])).

cnf(c_7220,plain,
    ( k1_relat_1(sK1) = sK0
    | sK0 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_7219])).

cnf(c_33,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1603,plain,
    ( k2_funct_2(X0,X1) = k2_funct_1(X1)
    | v1_funct_2(X1,X0,X0) != iProver_top
    | v3_funct_2(X1,X0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_4281,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1599,c_1603])).

cnf(c_41,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_39,negated_conjecture,
    ( v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_2025,plain,
    ( ~ v1_funct_2(sK1,X0,X0)
    | ~ v3_funct_2(sK1,X0,X0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ v1_funct_1(sK1)
    | k2_funct_2(X0,sK1) = k2_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_2181,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_2025])).

cnf(c_4743,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4281,c_41,c_40,c_39,c_38,c_2181])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1609,plain,
    ( v1_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(X0,X1,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_10127,plain,
    ( v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4743,c_1609])).

cnf(c_42,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_44,plain,
    ( v3_funct_2(sK1,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_45,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_10662,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10127,c_42,c_43,c_44,c_45])).

cnf(c_32,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1604,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_10680,plain,
    ( k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10662,c_1604])).

cnf(c_30,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_2(X1,X0)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1606,plain,
    ( v1_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(X0,X1,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_2(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_6354,plain,
    ( v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(k2_funct_2(sK0,sK1)) = iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1599,c_1606])).

cnf(c_6371,plain,
    ( v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(k2_funct_1(sK1)) = iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6354,c_4743])).

cnf(c_16559,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10680,c_42,c_43,c_44,c_6371])).

cnf(c_16560,plain,
    ( k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_16559])).

cnf(c_16571,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k5_relat_1(sK1,k2_funct_1(sK1))
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1599,c_16560])).

cnf(c_1596,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_9,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1621,plain,
    ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4665,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
    | v2_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1596,c_1621])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1937,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1958,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_17,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1975,plain,
    ( ~ v3_funct_2(sK1,X0,X1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK1)
    | v2_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2118,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | v2_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_1975])).

cnf(c_4739,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4665,c_41,c_39,c_38,c_1937,c_1958,c_2118])).

cnf(c_16599,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
    | v1_funct_1(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_16571,c_4739])).

cnf(c_16641,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_16599,c_42])).

cnf(c_4938,plain,
    ( k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1599,c_1604])).

cnf(c_5683,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4938,c_42])).

cnf(c_5684,plain,
    ( k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_5683])).

cnf(c_10137,plain,
    ( k1_partfun1(X0,X0,sK0,sK0,k2_funct_2(X0,X1),sK1) = k5_relat_1(k2_funct_2(X0,X1),sK1)
    | v1_funct_2(X1,X0,X0) != iProver_top
    | v3_funct_2(X1,X0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(k2_funct_2(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1609,c_5684])).

cnf(c_10879,plain,
    ( k1_partfun1(X0,X0,sK0,sK0,k2_funct_2(X0,X1),sK1) = k5_relat_1(k2_funct_2(X0,X1),sK1)
    | v1_funct_2(X1,X0,X0) != iProver_top
    | v3_funct_2(X1,X0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_10137,c_1606])).

cnf(c_10885,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1) = k5_relat_1(k2_funct_2(sK0,sK1),sK1)
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1599,c_10879])).

cnf(c_8,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1622,plain,
    ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_5261,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1))
    | v2_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1596,c_1622])).

cnf(c_16,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | v2_funct_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_12,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_26,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_418,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_12,c_26])).

cnf(c_430,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | k2_relat_1(X0) = X1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_418,c_11])).

cnf(c_461,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | X3 != X0
    | X5 != X2
    | k2_relat_1(X3) = X5 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_430])).

cnf(c_462,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ v1_funct_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(unflattening,[status(thm)],[c_461])).

cnf(c_1595,plain,
    ( k2_relat_1(X0) = X1
    | v3_funct_2(X0,X2,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_462])).

cnf(c_2513,plain,
    ( k2_relat_1(sK1) = sK0
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1599,c_1595])).

cnf(c_2010,plain,
    ( ~ v3_funct_2(sK1,X0,X1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(sK1)
    | k2_relat_1(sK1) = X1 ),
    inference(instantiation,[status(thm)],[c_462])).

cnf(c_2176,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | k2_relat_1(sK1) = sK0 ),
    inference(instantiation,[status(thm)],[c_2010])).

cnf(c_2356,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | k2_relat_1(sK1) = sK0 ),
    inference(instantiation,[status(thm)],[c_2176])).

cnf(c_2830,plain,
    ( k2_relat_1(sK1) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2513,c_41,c_39,c_38,c_2356])).

cnf(c_5262,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
    | v2_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5261,c_2830])).

cnf(c_1938,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1937])).

cnf(c_2119,plain,
    ( v3_funct_2(sK1,sK0,sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v2_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2118])).

cnf(c_6002,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5262,c_42,c_44,c_45,c_1938,c_2119])).

cnf(c_10911,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10885,c_4743,c_6002])).

cnf(c_10674,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k5_relat_1(k2_funct_1(sK1),sK1)
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10662,c_5684])).

cnf(c_10730,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10674,c_6002])).

cnf(c_10952,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10911,c_42,c_43,c_44,c_6371,c_10730])).

cnf(c_37,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1600,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) != iProver_top
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_4746,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) != iProver_top
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4743,c_1600])).

cnf(c_10955,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top
    | r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10952,c_4746])).

cnf(c_31,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_2597,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_2600,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2597])).

cnf(c_15,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1995,plain,
    ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_2628,plain,
    ( r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_1995])).

cnf(c_2629,plain,
    ( r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) = iProver_top
    | m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2628])).

cnf(c_10994,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10955,c_45,c_2600,c_2629])).

cnf(c_16644,plain,
    ( r2_relset_1(sK0,sK0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_16641,c_10994])).

cnf(c_17315,plain,
    ( sK0 = k1_xboole_0
    | r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7220,c_16644])).

cnf(c_17318,plain,
    ( sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_17315,c_45,c_2600,c_2629])).

cnf(c_17321,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_17318,c_16644])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_relat_1(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1624,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_relat_1(X0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2833,plain,
    ( k1_relat_1(sK1) = k1_xboole_0
    | sK0 != k1_xboole_0
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2830,c_1624])).

cnf(c_2834,plain,
    ( ~ v1_relat_1(sK1)
    | k1_relat_1(sK1) = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2833])).

cnf(c_2915,plain,
    ( sK0 != k1_xboole_0
    | k1_relat_1(sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2833,c_38,c_1937,c_2834])).

cnf(c_2916,plain,
    ( k1_relat_1(sK1) = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_2915])).

cnf(c_17382,plain,
    ( k1_relat_1(sK1) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_17318,c_2916])).

cnf(c_17399,plain,
    ( k1_relat_1(sK1) = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_17382])).

cnf(c_17602,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),k6_partfun1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_17321,c_17399])).

cnf(c_2,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f106])).

cnf(c_1605,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_2092,plain,
    ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_1605])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1625,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3176,plain,
    ( v1_xboole_0(k6_partfun1(k1_xboole_0)) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2092,c_1625])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_138,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2890,plain,
    ( ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(k6_partfun1(X0)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2891,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(X1)) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2890])).

cnf(c_2893,plain,
    ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_xboole_0(k6_partfun1(k1_xboole_0)) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2891])).

cnf(c_3993,plain,
    ( v1_xboole_0(k6_partfun1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3176,c_138,c_2092,c_2893])).

cnf(c_1627,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1626,plain,
    ( X0 = X1
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2390,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1627,c_1626])).

cnf(c_3998,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3993,c_2390])).

cnf(c_17604,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_17602,c_3998])).

cnf(c_1028,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | r2_relset_1(X4,X5,X6,X7)
    | X4 != X0
    | X5 != X1
    | X6 != X2
    | X7 != X3 ),
    theory(equality)).

cnf(c_3201,plain,
    ( r2_relset_1(X0,X1,X2,X3)
    | ~ r2_relset_1(X4,X4,k6_partfun1(X4),k6_partfun1(X4))
    | X0 != X4
    | X1 != X4
    | X2 != k6_partfun1(X4)
    | X3 != k6_partfun1(X4) ),
    inference(instantiation,[status(thm)],[c_1028])).

cnf(c_3202,plain,
    ( X0 != X1
    | X2 != X1
    | X3 != k6_partfun1(X1)
    | X4 != k6_partfun1(X1)
    | r2_relset_1(X0,X2,X3,X4) = iProver_top
    | r2_relset_1(X1,X1,k6_partfun1(X1),k6_partfun1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3201])).

cnf(c_3204,plain,
    ( k1_xboole_0 != k6_partfun1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0
    | r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),k6_partfun1(k1_xboole_0)) != iProver_top
    | r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3202])).

cnf(c_2892,plain,
    ( ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | v1_xboole_0(k6_partfun1(k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2890])).

cnf(c_2635,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(k6_partfun1(X1))
    | X0 = k6_partfun1(X1) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2637,plain,
    ( ~ v1_xboole_0(k6_partfun1(k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2635])).

cnf(c_2623,plain,
    ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0))
    | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(instantiation,[status(thm)],[c_1995])).

cnf(c_2624,plain,
    ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0)) = iProver_top
    | m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2623])).

cnf(c_2626,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),k6_partfun1(k1_xboole_0)) = iProver_top
    | m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2624])).

cnf(c_2094,plain,
    ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2092])).

cnf(c_3,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f107])).

cnf(c_134,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_4,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_133,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_60,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_62,plain,
    ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_60])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_17604,c_3204,c_2892,c_2637,c_2626,c_2094,c_0,c_134,c_133,c_62])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.11/0.33  % Computer   : n008.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 10:51:00 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running in FOF mode
% 4.00/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.00/0.98  
% 4.00/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.00/0.98  
% 4.00/0.98  ------  iProver source info
% 4.00/0.98  
% 4.00/0.98  git: date: 2020-06-30 10:37:57 +0100
% 4.00/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.00/0.98  git: non_committed_changes: false
% 4.00/0.98  git: last_make_outside_of_git: false
% 4.00/0.98  
% 4.00/0.98  ------ 
% 4.00/0.98  
% 4.00/0.98  ------ Input Options
% 4.00/0.98  
% 4.00/0.98  --out_options                           all
% 4.00/0.98  --tptp_safe_out                         true
% 4.00/0.98  --problem_path                          ""
% 4.00/0.98  --include_path                          ""
% 4.00/0.98  --clausifier                            res/vclausify_rel
% 4.00/0.98  --clausifier_options                    --mode clausify
% 4.00/0.98  --stdin                                 false
% 4.00/0.98  --stats_out                             all
% 4.00/0.98  
% 4.00/0.98  ------ General Options
% 4.00/0.98  
% 4.00/0.98  --fof                                   false
% 4.00/0.98  --time_out_real                         305.
% 4.00/0.98  --time_out_virtual                      -1.
% 4.00/0.98  --symbol_type_check                     false
% 4.00/0.98  --clausify_out                          false
% 4.00/0.98  --sig_cnt_out                           false
% 4.00/0.98  --trig_cnt_out                          false
% 4.00/0.98  --trig_cnt_out_tolerance                1.
% 4.00/0.98  --trig_cnt_out_sk_spl                   false
% 4.00/0.98  --abstr_cl_out                          false
% 4.00/0.98  
% 4.00/0.98  ------ Global Options
% 4.00/0.98  
% 4.00/0.98  --schedule                              default
% 4.00/0.98  --add_important_lit                     false
% 4.00/0.98  --prop_solver_per_cl                    1000
% 4.00/0.98  --min_unsat_core                        false
% 4.00/0.98  --soft_assumptions                      false
% 4.00/0.98  --soft_lemma_size                       3
% 4.00/0.98  --prop_impl_unit_size                   0
% 4.00/0.98  --prop_impl_unit                        []
% 4.00/0.98  --share_sel_clauses                     true
% 4.00/0.98  --reset_solvers                         false
% 4.00/0.98  --bc_imp_inh                            [conj_cone]
% 4.00/0.98  --conj_cone_tolerance                   3.
% 4.00/0.98  --extra_neg_conj                        none
% 4.00/0.98  --large_theory_mode                     true
% 4.00/0.98  --prolific_symb_bound                   200
% 4.00/0.98  --lt_threshold                          2000
% 4.00/0.98  --clause_weak_htbl                      true
% 4.00/0.98  --gc_record_bc_elim                     false
% 4.00/0.98  
% 4.00/0.98  ------ Preprocessing Options
% 4.00/0.98  
% 4.00/0.98  --preprocessing_flag                    true
% 4.00/0.98  --time_out_prep_mult                    0.1
% 4.00/0.98  --splitting_mode                        input
% 4.00/0.98  --splitting_grd                         true
% 4.00/0.98  --splitting_cvd                         false
% 4.00/0.98  --splitting_cvd_svl                     false
% 4.00/0.98  --splitting_nvd                         32
% 4.00/0.98  --sub_typing                            true
% 4.00/0.98  --prep_gs_sim                           true
% 4.00/0.98  --prep_unflatten                        true
% 4.00/0.98  --prep_res_sim                          true
% 4.00/0.98  --prep_upred                            true
% 4.00/0.98  --prep_sem_filter                       exhaustive
% 4.00/0.98  --prep_sem_filter_out                   false
% 4.00/0.98  --pred_elim                             true
% 4.00/0.98  --res_sim_input                         true
% 4.00/0.98  --eq_ax_congr_red                       true
% 4.00/0.98  --pure_diseq_elim                       true
% 4.00/0.98  --brand_transform                       false
% 4.00/0.98  --non_eq_to_eq                          false
% 4.00/0.98  --prep_def_merge                        true
% 4.00/0.98  --prep_def_merge_prop_impl              false
% 4.00/0.98  --prep_def_merge_mbd                    true
% 4.00/0.98  --prep_def_merge_tr_red                 false
% 4.00/0.98  --prep_def_merge_tr_cl                  false
% 4.00/0.98  --smt_preprocessing                     true
% 4.00/0.98  --smt_ac_axioms                         fast
% 4.00/0.98  --preprocessed_out                      false
% 4.00/0.98  --preprocessed_stats                    false
% 4.00/0.98  
% 4.00/0.98  ------ Abstraction refinement Options
% 4.00/0.98  
% 4.00/0.98  --abstr_ref                             []
% 4.00/0.98  --abstr_ref_prep                        false
% 4.00/0.98  --abstr_ref_until_sat                   false
% 4.00/0.98  --abstr_ref_sig_restrict                funpre
% 4.00/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 4.00/0.98  --abstr_ref_under                       []
% 4.00/0.98  
% 4.00/0.98  ------ SAT Options
% 4.00/0.98  
% 4.00/0.98  --sat_mode                              false
% 4.00/0.98  --sat_fm_restart_options                ""
% 4.00/0.98  --sat_gr_def                            false
% 4.00/0.98  --sat_epr_types                         true
% 4.00/0.98  --sat_non_cyclic_types                  false
% 4.00/0.98  --sat_finite_models                     false
% 4.00/0.98  --sat_fm_lemmas                         false
% 4.00/0.98  --sat_fm_prep                           false
% 4.00/0.98  --sat_fm_uc_incr                        true
% 4.00/0.98  --sat_out_model                         small
% 4.00/0.98  --sat_out_clauses                       false
% 4.00/0.98  
% 4.00/0.98  ------ QBF Options
% 4.00/0.98  
% 4.00/0.98  --qbf_mode                              false
% 4.00/0.98  --qbf_elim_univ                         false
% 4.00/0.98  --qbf_dom_inst                          none
% 4.00/0.98  --qbf_dom_pre_inst                      false
% 4.00/0.98  --qbf_sk_in                             false
% 4.00/0.98  --qbf_pred_elim                         true
% 4.00/0.98  --qbf_split                             512
% 4.00/0.98  
% 4.00/0.98  ------ BMC1 Options
% 4.00/0.98  
% 4.00/0.98  --bmc1_incremental                      false
% 4.00/0.98  --bmc1_axioms                           reachable_all
% 4.00/0.98  --bmc1_min_bound                        0
% 4.00/0.98  --bmc1_max_bound                        -1
% 4.00/0.98  --bmc1_max_bound_default                -1
% 4.00/0.98  --bmc1_symbol_reachability              true
% 4.00/0.98  --bmc1_property_lemmas                  false
% 4.00/0.98  --bmc1_k_induction                      false
% 4.00/0.98  --bmc1_non_equiv_states                 false
% 4.00/0.98  --bmc1_deadlock                         false
% 4.00/0.98  --bmc1_ucm                              false
% 4.00/0.98  --bmc1_add_unsat_core                   none
% 4.00/0.98  --bmc1_unsat_core_children              false
% 4.00/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 4.00/0.98  --bmc1_out_stat                         full
% 4.00/0.98  --bmc1_ground_init                      false
% 4.00/0.98  --bmc1_pre_inst_next_state              false
% 4.00/0.98  --bmc1_pre_inst_state                   false
% 4.00/0.98  --bmc1_pre_inst_reach_state             false
% 4.00/0.98  --bmc1_out_unsat_core                   false
% 4.00/0.98  --bmc1_aig_witness_out                  false
% 4.00/0.98  --bmc1_verbose                          false
% 4.00/0.98  --bmc1_dump_clauses_tptp                false
% 4.00/0.98  --bmc1_dump_unsat_core_tptp             false
% 4.00/0.98  --bmc1_dump_file                        -
% 4.00/0.98  --bmc1_ucm_expand_uc_limit              128
% 4.00/0.98  --bmc1_ucm_n_expand_iterations          6
% 4.00/0.98  --bmc1_ucm_extend_mode                  1
% 4.00/0.98  --bmc1_ucm_init_mode                    2
% 4.00/0.98  --bmc1_ucm_cone_mode                    none
% 4.00/0.98  --bmc1_ucm_reduced_relation_type        0
% 4.00/0.98  --bmc1_ucm_relax_model                  4
% 4.00/0.98  --bmc1_ucm_full_tr_after_sat            true
% 4.00/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 4.00/0.98  --bmc1_ucm_layered_model                none
% 4.00/0.98  --bmc1_ucm_max_lemma_size               10
% 4.00/0.98  
% 4.00/0.98  ------ AIG Options
% 4.00/0.98  
% 4.00/0.98  --aig_mode                              false
% 4.00/0.98  
% 4.00/0.98  ------ Instantiation Options
% 4.00/0.98  
% 4.00/0.98  --instantiation_flag                    true
% 4.00/0.98  --inst_sos_flag                         false
% 4.00/0.98  --inst_sos_phase                        true
% 4.00/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.00/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.00/0.98  --inst_lit_sel_side                     num_symb
% 4.00/0.98  --inst_solver_per_active                1400
% 4.00/0.98  --inst_solver_calls_frac                1.
% 4.00/0.98  --inst_passive_queue_type               priority_queues
% 4.00/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.00/0.98  --inst_passive_queues_freq              [25;2]
% 4.00/0.98  --inst_dismatching                      true
% 4.00/0.98  --inst_eager_unprocessed_to_passive     true
% 4.00/0.98  --inst_prop_sim_given                   true
% 4.00/0.98  --inst_prop_sim_new                     false
% 4.00/0.98  --inst_subs_new                         false
% 4.00/0.98  --inst_eq_res_simp                      false
% 4.00/0.98  --inst_subs_given                       false
% 4.00/0.98  --inst_orphan_elimination               true
% 4.00/0.98  --inst_learning_loop_flag               true
% 4.00/0.98  --inst_learning_start                   3000
% 4.00/0.98  --inst_learning_factor                  2
% 4.00/0.98  --inst_start_prop_sim_after_learn       3
% 4.00/0.98  --inst_sel_renew                        solver
% 4.00/0.98  --inst_lit_activity_flag                true
% 4.00/0.98  --inst_restr_to_given                   false
% 4.00/0.98  --inst_activity_threshold               500
% 4.00/0.98  --inst_out_proof                        true
% 4.00/0.98  
% 4.00/0.98  ------ Resolution Options
% 4.00/0.98  
% 4.00/0.98  --resolution_flag                       true
% 4.00/0.98  --res_lit_sel                           adaptive
% 4.00/0.98  --res_lit_sel_side                      none
% 4.00/0.98  --res_ordering                          kbo
% 4.00/0.98  --res_to_prop_solver                    active
% 4.00/0.98  --res_prop_simpl_new                    false
% 4.00/0.98  --res_prop_simpl_given                  true
% 4.00/0.98  --res_passive_queue_type                priority_queues
% 4.00/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.00/0.98  --res_passive_queues_freq               [15;5]
% 4.00/0.98  --res_forward_subs                      full
% 4.00/0.98  --res_backward_subs                     full
% 4.00/0.98  --res_forward_subs_resolution           true
% 4.00/0.98  --res_backward_subs_resolution          true
% 4.00/0.98  --res_orphan_elimination                true
% 4.00/0.98  --res_time_limit                        2.
% 4.00/0.98  --res_out_proof                         true
% 4.00/0.98  
% 4.00/0.98  ------ Superposition Options
% 4.00/0.98  
% 4.00/0.98  --superposition_flag                    true
% 4.00/0.98  --sup_passive_queue_type                priority_queues
% 4.00/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.00/0.98  --sup_passive_queues_freq               [8;1;4]
% 4.00/0.98  --demod_completeness_check              fast
% 4.00/0.98  --demod_use_ground                      true
% 4.00/0.98  --sup_to_prop_solver                    passive
% 4.00/0.98  --sup_prop_simpl_new                    true
% 4.00/0.98  --sup_prop_simpl_given                  true
% 4.00/0.98  --sup_fun_splitting                     false
% 4.00/0.98  --sup_smt_interval                      50000
% 4.00/0.98  
% 4.00/0.98  ------ Superposition Simplification Setup
% 4.00/0.98  
% 4.00/0.98  --sup_indices_passive                   []
% 4.00/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.00/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.00/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.00/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 4.00/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.00/0.98  --sup_full_bw                           [BwDemod]
% 4.00/0.98  --sup_immed_triv                        [TrivRules]
% 4.00/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.00/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.00/0.98  --sup_immed_bw_main                     []
% 4.00/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.00/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 4.00/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.00/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.00/0.98  
% 4.00/0.98  ------ Combination Options
% 4.00/0.98  
% 4.00/0.98  --comb_res_mult                         3
% 4.00/0.98  --comb_sup_mult                         2
% 4.00/0.98  --comb_inst_mult                        10
% 4.00/0.98  
% 4.00/0.98  ------ Debug Options
% 4.00/0.98  
% 4.00/0.98  --dbg_backtrace                         false
% 4.00/0.98  --dbg_dump_prop_clauses                 false
% 4.00/0.98  --dbg_dump_prop_clauses_file            -
% 4.00/0.98  --dbg_out_stat                          false
% 4.00/0.98  ------ Parsing...
% 4.00/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.00/0.98  
% 4.00/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 4.00/0.98  
% 4.00/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.00/0.98  
% 4.00/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.00/0.98  ------ Proving...
% 4.00/0.98  ------ Problem Properties 
% 4.00/0.98  
% 4.00/0.98  
% 4.00/0.98  clauses                                 37
% 4.00/0.98  conjectures                             5
% 4.00/0.98  EPR                                     5
% 4.00/0.98  Horn                                    32
% 4.00/0.98  unary                                   9
% 4.00/0.98  binary                                  3
% 4.00/0.98  lits                                    110
% 4.00/0.98  lits eq                                 26
% 4.00/0.98  fd_pure                                 0
% 4.00/0.98  fd_pseudo                               0
% 4.00/0.98  fd_cond                                 4
% 4.00/0.98  fd_pseudo_cond                          2
% 4.00/0.98  AC symbols                              0
% 4.00/0.98  
% 4.00/0.98  ------ Schedule dynamic 5 is on 
% 4.00/0.98  
% 4.00/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 4.00/0.98  
% 4.00/0.98  
% 4.00/0.98  ------ 
% 4.00/0.98  Current options:
% 4.00/0.98  ------ 
% 4.00/0.98  
% 4.00/0.98  ------ Input Options
% 4.00/0.98  
% 4.00/0.98  --out_options                           all
% 4.00/0.98  --tptp_safe_out                         true
% 4.00/0.98  --problem_path                          ""
% 4.00/0.98  --include_path                          ""
% 4.00/0.98  --clausifier                            res/vclausify_rel
% 4.00/0.98  --clausifier_options                    --mode clausify
% 4.00/0.98  --stdin                                 false
% 4.00/0.98  --stats_out                             all
% 4.00/0.98  
% 4.00/0.98  ------ General Options
% 4.00/0.98  
% 4.00/0.98  --fof                                   false
% 4.00/0.98  --time_out_real                         305.
% 4.00/0.98  --time_out_virtual                      -1.
% 4.00/0.98  --symbol_type_check                     false
% 4.00/0.98  --clausify_out                          false
% 4.00/0.98  --sig_cnt_out                           false
% 4.00/0.98  --trig_cnt_out                          false
% 4.00/0.98  --trig_cnt_out_tolerance                1.
% 4.00/0.98  --trig_cnt_out_sk_spl                   false
% 4.00/0.98  --abstr_cl_out                          false
% 4.00/0.98  
% 4.00/0.98  ------ Global Options
% 4.00/0.98  
% 4.00/0.98  --schedule                              default
% 4.00/0.98  --add_important_lit                     false
% 4.00/0.98  --prop_solver_per_cl                    1000
% 4.00/0.98  --min_unsat_core                        false
% 4.00/0.98  --soft_assumptions                      false
% 4.00/0.98  --soft_lemma_size                       3
% 4.00/0.98  --prop_impl_unit_size                   0
% 4.00/0.98  --prop_impl_unit                        []
% 4.00/0.98  --share_sel_clauses                     true
% 4.00/0.98  --reset_solvers                         false
% 4.00/0.98  --bc_imp_inh                            [conj_cone]
% 4.00/0.98  --conj_cone_tolerance                   3.
% 4.00/0.98  --extra_neg_conj                        none
% 4.00/0.98  --large_theory_mode                     true
% 4.00/0.98  --prolific_symb_bound                   200
% 4.00/0.98  --lt_threshold                          2000
% 4.00/0.98  --clause_weak_htbl                      true
% 4.00/0.98  --gc_record_bc_elim                     false
% 4.00/0.98  
% 4.00/0.98  ------ Preprocessing Options
% 4.00/0.98  
% 4.00/0.98  --preprocessing_flag                    true
% 4.00/0.98  --time_out_prep_mult                    0.1
% 4.00/0.98  --splitting_mode                        input
% 4.00/0.98  --splitting_grd                         true
% 4.00/0.98  --splitting_cvd                         false
% 4.00/0.98  --splitting_cvd_svl                     false
% 4.00/0.98  --splitting_nvd                         32
% 4.00/0.98  --sub_typing                            true
% 4.00/0.98  --prep_gs_sim                           true
% 4.00/0.98  --prep_unflatten                        true
% 4.00/0.98  --prep_res_sim                          true
% 4.00/0.98  --prep_upred                            true
% 4.00/0.98  --prep_sem_filter                       exhaustive
% 4.00/0.98  --prep_sem_filter_out                   false
% 4.00/0.98  --pred_elim                             true
% 4.00/0.98  --res_sim_input                         true
% 4.00/0.98  --eq_ax_congr_red                       true
% 4.00/0.98  --pure_diseq_elim                       true
% 4.00/0.98  --brand_transform                       false
% 4.00/0.98  --non_eq_to_eq                          false
% 4.00/0.98  --prep_def_merge                        true
% 4.00/0.98  --prep_def_merge_prop_impl              false
% 4.00/0.98  --prep_def_merge_mbd                    true
% 4.00/0.98  --prep_def_merge_tr_red                 false
% 4.00/0.98  --prep_def_merge_tr_cl                  false
% 4.00/0.98  --smt_preprocessing                     true
% 4.00/0.98  --smt_ac_axioms                         fast
% 4.00/0.98  --preprocessed_out                      false
% 4.00/0.98  --preprocessed_stats                    false
% 4.00/0.98  
% 4.00/0.98  ------ Abstraction refinement Options
% 4.00/0.98  
% 4.00/0.98  --abstr_ref                             []
% 4.00/0.98  --abstr_ref_prep                        false
% 4.00/0.98  --abstr_ref_until_sat                   false
% 4.00/0.98  --abstr_ref_sig_restrict                funpre
% 4.00/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 4.00/0.98  --abstr_ref_under                       []
% 4.00/0.98  
% 4.00/0.98  ------ SAT Options
% 4.00/0.98  
% 4.00/0.98  --sat_mode                              false
% 4.00/0.98  --sat_fm_restart_options                ""
% 4.00/0.98  --sat_gr_def                            false
% 4.00/0.98  --sat_epr_types                         true
% 4.00/0.98  --sat_non_cyclic_types                  false
% 4.00/0.98  --sat_finite_models                     false
% 4.00/0.98  --sat_fm_lemmas                         false
% 4.00/0.98  --sat_fm_prep                           false
% 4.00/0.98  --sat_fm_uc_incr                        true
% 4.00/0.98  --sat_out_model                         small
% 4.00/0.98  --sat_out_clauses                       false
% 4.00/0.98  
% 4.00/0.98  ------ QBF Options
% 4.00/0.98  
% 4.00/0.98  --qbf_mode                              false
% 4.00/0.98  --qbf_elim_univ                         false
% 4.00/0.98  --qbf_dom_inst                          none
% 4.00/0.98  --qbf_dom_pre_inst                      false
% 4.00/0.98  --qbf_sk_in                             false
% 4.00/0.98  --qbf_pred_elim                         true
% 4.00/0.98  --qbf_split                             512
% 4.00/0.98  
% 4.00/0.98  ------ BMC1 Options
% 4.00/0.98  
% 4.00/0.98  --bmc1_incremental                      false
% 4.00/0.98  --bmc1_axioms                           reachable_all
% 4.00/0.98  --bmc1_min_bound                        0
% 4.00/0.98  --bmc1_max_bound                        -1
% 4.00/0.98  --bmc1_max_bound_default                -1
% 4.00/0.98  --bmc1_symbol_reachability              true
% 4.00/0.98  --bmc1_property_lemmas                  false
% 4.00/0.98  --bmc1_k_induction                      false
% 4.00/0.98  --bmc1_non_equiv_states                 false
% 4.00/0.98  --bmc1_deadlock                         false
% 4.00/0.98  --bmc1_ucm                              false
% 4.00/0.98  --bmc1_add_unsat_core                   none
% 4.00/0.98  --bmc1_unsat_core_children              false
% 4.00/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 4.00/0.98  --bmc1_out_stat                         full
% 4.00/0.98  --bmc1_ground_init                      false
% 4.00/0.98  --bmc1_pre_inst_next_state              false
% 4.00/0.98  --bmc1_pre_inst_state                   false
% 4.00/0.98  --bmc1_pre_inst_reach_state             false
% 4.00/0.98  --bmc1_out_unsat_core                   false
% 4.00/0.98  --bmc1_aig_witness_out                  false
% 4.00/0.98  --bmc1_verbose                          false
% 4.00/0.98  --bmc1_dump_clauses_tptp                false
% 4.00/0.98  --bmc1_dump_unsat_core_tptp             false
% 4.00/0.98  --bmc1_dump_file                        -
% 4.00/0.98  --bmc1_ucm_expand_uc_limit              128
% 4.00/0.98  --bmc1_ucm_n_expand_iterations          6
% 4.00/0.98  --bmc1_ucm_extend_mode                  1
% 4.00/0.98  --bmc1_ucm_init_mode                    2
% 4.00/0.98  --bmc1_ucm_cone_mode                    none
% 4.00/0.98  --bmc1_ucm_reduced_relation_type        0
% 4.00/0.98  --bmc1_ucm_relax_model                  4
% 4.00/0.98  --bmc1_ucm_full_tr_after_sat            true
% 4.00/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 4.00/0.98  --bmc1_ucm_layered_model                none
% 4.00/0.98  --bmc1_ucm_max_lemma_size               10
% 4.00/0.98  
% 4.00/0.98  ------ AIG Options
% 4.00/0.98  
% 4.00/0.98  --aig_mode                              false
% 4.00/0.98  
% 4.00/0.98  ------ Instantiation Options
% 4.00/0.98  
% 4.00/0.98  --instantiation_flag                    true
% 4.00/0.98  --inst_sos_flag                         false
% 4.00/0.98  --inst_sos_phase                        true
% 4.00/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.00/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.00/0.98  --inst_lit_sel_side                     none
% 4.00/0.98  --inst_solver_per_active                1400
% 4.00/0.98  --inst_solver_calls_frac                1.
% 4.00/0.98  --inst_passive_queue_type               priority_queues
% 4.00/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.00/0.98  --inst_passive_queues_freq              [25;2]
% 4.00/0.98  --inst_dismatching                      true
% 4.00/0.98  --inst_eager_unprocessed_to_passive     true
% 4.00/0.98  --inst_prop_sim_given                   true
% 4.00/0.98  --inst_prop_sim_new                     false
% 4.00/0.98  --inst_subs_new                         false
% 4.00/0.98  --inst_eq_res_simp                      false
% 4.00/0.98  --inst_subs_given                       false
% 4.00/0.98  --inst_orphan_elimination               true
% 4.00/0.98  --inst_learning_loop_flag               true
% 4.00/0.98  --inst_learning_start                   3000
% 4.00/0.98  --inst_learning_factor                  2
% 4.00/0.98  --inst_start_prop_sim_after_learn       3
% 4.00/0.98  --inst_sel_renew                        solver
% 4.00/0.98  --inst_lit_activity_flag                true
% 4.00/0.98  --inst_restr_to_given                   false
% 4.00/0.98  --inst_activity_threshold               500
% 4.00/0.98  --inst_out_proof                        true
% 4.00/0.98  
% 4.00/0.98  ------ Resolution Options
% 4.00/0.98  
% 4.00/0.98  --resolution_flag                       false
% 4.00/0.98  --res_lit_sel                           adaptive
% 4.00/0.98  --res_lit_sel_side                      none
% 4.00/0.98  --res_ordering                          kbo
% 4.00/0.98  --res_to_prop_solver                    active
% 4.00/0.98  --res_prop_simpl_new                    false
% 4.00/0.98  --res_prop_simpl_given                  true
% 4.00/0.98  --res_passive_queue_type                priority_queues
% 4.00/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.00/0.98  --res_passive_queues_freq               [15;5]
% 4.00/0.98  --res_forward_subs                      full
% 4.00/0.98  --res_backward_subs                     full
% 4.00/0.98  --res_forward_subs_resolution           true
% 4.00/0.98  --res_backward_subs_resolution          true
% 4.00/0.98  --res_orphan_elimination                true
% 4.00/0.98  --res_time_limit                        2.
% 4.00/0.98  --res_out_proof                         true
% 4.00/0.98  
% 4.00/0.98  ------ Superposition Options
% 4.00/0.98  
% 4.00/0.98  --superposition_flag                    true
% 4.00/0.98  --sup_passive_queue_type                priority_queues
% 4.00/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.00/0.98  --sup_passive_queues_freq               [8;1;4]
% 4.00/0.98  --demod_completeness_check              fast
% 4.00/0.98  --demod_use_ground                      true
% 4.00/0.98  --sup_to_prop_solver                    passive
% 4.00/0.98  --sup_prop_simpl_new                    true
% 4.00/0.98  --sup_prop_simpl_given                  true
% 4.00/0.98  --sup_fun_splitting                     false
% 4.00/0.98  --sup_smt_interval                      50000
% 4.00/0.98  
% 4.00/0.98  ------ Superposition Simplification Setup
% 4.00/0.98  
% 4.00/0.98  --sup_indices_passive                   []
% 4.00/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.00/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.00/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.00/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 4.00/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.00/0.98  --sup_full_bw                           [BwDemod]
% 4.00/0.98  --sup_immed_triv                        [TrivRules]
% 4.00/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.00/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.00/0.98  --sup_immed_bw_main                     []
% 4.00/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.00/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 4.00/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.00/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.00/0.98  
% 4.00/0.98  ------ Combination Options
% 4.00/0.98  
% 4.00/0.98  --comb_res_mult                         3
% 4.00/0.98  --comb_sup_mult                         2
% 4.00/0.98  --comb_inst_mult                        10
% 4.00/0.98  
% 4.00/0.98  ------ Debug Options
% 4.00/0.98  
% 4.00/0.98  --dbg_backtrace                         false
% 4.00/0.98  --dbg_dump_prop_clauses                 false
% 4.00/0.98  --dbg_dump_prop_clauses_file            -
% 4.00/0.98  --dbg_out_stat                          false
% 4.00/0.98  
% 4.00/0.98  
% 4.00/0.98  
% 4.00/0.98  
% 4.00/0.98  ------ Proving...
% 4.00/0.98  
% 4.00/0.98  
% 4.00/0.98  % SZS status Theorem for theBenchmark.p
% 4.00/0.98  
% 4.00/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 4.00/0.98  
% 4.00/0.98  fof(f22,conjecture,(
% 4.00/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 4.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.98  
% 4.00/0.98  fof(f23,negated_conjecture,(
% 4.00/0.98    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 4.00/0.98    inference(negated_conjecture,[],[f22])).
% 4.00/0.98  
% 4.00/0.98  fof(f51,plain,(
% 4.00/0.98    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 4.00/0.98    inference(ennf_transformation,[],[f23])).
% 4.00/0.98  
% 4.00/0.98  fof(f52,plain,(
% 4.00/0.98    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 4.00/0.98    inference(flattening,[],[f51])).
% 4.00/0.98  
% 4.00/0.98  fof(f58,plain,(
% 4.00/0.98    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 4.00/0.98    introduced(choice_axiom,[])).
% 4.00/0.98  
% 4.00/0.98  fof(f59,plain,(
% 4.00/0.98    (~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 4.00/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f52,f58])).
% 4.00/0.98  
% 4.00/0.98  fof(f101,plain,(
% 4.00/0.98    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 4.00/0.98    inference(cnf_transformation,[],[f59])).
% 4.00/0.98  
% 4.00/0.98  fof(f14,axiom,(
% 4.00/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 4.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.98  
% 4.00/0.98  fof(f39,plain,(
% 4.00/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.00/0.98    inference(ennf_transformation,[],[f14])).
% 4.00/0.98  
% 4.00/0.98  fof(f40,plain,(
% 4.00/0.98    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.00/0.98    inference(flattening,[],[f39])).
% 4.00/0.98  
% 4.00/0.98  fof(f56,plain,(
% 4.00/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.00/0.98    inference(nnf_transformation,[],[f40])).
% 4.00/0.98  
% 4.00/0.98  fof(f79,plain,(
% 4.00/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.00/0.98    inference(cnf_transformation,[],[f56])).
% 4.00/0.98  
% 4.00/0.98  fof(f11,axiom,(
% 4.00/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 4.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.98  
% 4.00/0.98  fof(f34,plain,(
% 4.00/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.00/0.98    inference(ennf_transformation,[],[f11])).
% 4.00/0.98  
% 4.00/0.98  fof(f74,plain,(
% 4.00/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.00/0.98    inference(cnf_transformation,[],[f34])).
% 4.00/0.98  
% 4.00/0.98  fof(f99,plain,(
% 4.00/0.98    v1_funct_2(sK1,sK0,sK0)),
% 4.00/0.98    inference(cnf_transformation,[],[f59])).
% 4.00/0.98  
% 4.00/0.98  fof(f19,axiom,(
% 4.00/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_1(X1) = k2_funct_2(X0,X1))),
% 4.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.98  
% 4.00/0.98  fof(f47,plain,(
% 4.00/0.98    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 4.00/0.98    inference(ennf_transformation,[],[f19])).
% 4.00/0.98  
% 4.00/0.98  fof(f48,plain,(
% 4.00/0.98    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 4.00/0.98    inference(flattening,[],[f47])).
% 4.00/0.98  
% 4.00/0.98  fof(f93,plain,(
% 4.00/0.98    ( ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 4.00/0.98    inference(cnf_transformation,[],[f48])).
% 4.00/0.98  
% 4.00/0.98  fof(f98,plain,(
% 4.00/0.98    v1_funct_1(sK1)),
% 4.00/0.98    inference(cnf_transformation,[],[f59])).
% 4.00/0.98  
% 4.00/0.98  fof(f100,plain,(
% 4.00/0.98    v3_funct_2(sK1,sK0,sK0)),
% 4.00/0.98    inference(cnf_transformation,[],[f59])).
% 4.00/0.98  
% 4.00/0.98  fof(f16,axiom,(
% 4.00/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 4.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.98  
% 4.00/0.98  fof(f43,plain,(
% 4.00/0.98    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 4.00/0.98    inference(ennf_transformation,[],[f16])).
% 4.00/0.98  
% 4.00/0.98  fof(f44,plain,(
% 4.00/0.98    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 4.00/0.98    inference(flattening,[],[f43])).
% 4.00/0.98  
% 4.00/0.98  fof(f90,plain,(
% 4.00/0.98    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 4.00/0.98    inference(cnf_transformation,[],[f44])).
% 4.00/0.98  
% 4.00/0.98  fof(f18,axiom,(
% 4.00/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 4.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.98  
% 4.00/0.98  fof(f45,plain,(
% 4.00/0.98    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 4.00/0.98    inference(ennf_transformation,[],[f18])).
% 4.00/0.98  
% 4.00/0.98  fof(f46,plain,(
% 4.00/0.98    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 4.00/0.98    inference(flattening,[],[f45])).
% 4.00/0.98  
% 4.00/0.98  fof(f92,plain,(
% 4.00/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 4.00/0.98    inference(cnf_transformation,[],[f46])).
% 4.00/0.98  
% 4.00/0.98  fof(f87,plain,(
% 4.00/0.98    ( ! [X0,X1] : (v1_funct_1(k2_funct_2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 4.00/0.98    inference(cnf_transformation,[],[f44])).
% 4.00/0.98  
% 4.00/0.98  fof(f6,axiom,(
% 4.00/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 4.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.98  
% 4.00/0.98  fof(f29,plain,(
% 4.00/0.98    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 4.00/0.98    inference(ennf_transformation,[],[f6])).
% 4.00/0.98  
% 4.00/0.98  fof(f30,plain,(
% 4.00/0.98    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.00/0.98    inference(flattening,[],[f29])).
% 4.00/0.98  
% 4.00/0.98  fof(f68,plain,(
% 4.00/0.98    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.00/0.98    inference(cnf_transformation,[],[f30])).
% 4.00/0.98  
% 4.00/0.98  fof(f20,axiom,(
% 4.00/0.98    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 4.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.98  
% 4.00/0.98  fof(f94,plain,(
% 4.00/0.98    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 4.00/0.98    inference(cnf_transformation,[],[f20])).
% 4.00/0.98  
% 4.00/0.98  fof(f104,plain,(
% 4.00/0.98    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.00/0.98    inference(definition_unfolding,[],[f68,f94])).
% 4.00/0.98  
% 4.00/0.98  fof(f8,axiom,(
% 4.00/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 4.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.98  
% 4.00/0.98  fof(f31,plain,(
% 4.00/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.00/0.98    inference(ennf_transformation,[],[f8])).
% 4.00/0.98  
% 4.00/0.98  fof(f71,plain,(
% 4.00/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.00/0.98    inference(cnf_transformation,[],[f31])).
% 4.00/0.98  
% 4.00/0.98  fof(f13,axiom,(
% 4.00/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 4.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.98  
% 4.00/0.98  fof(f37,plain,(
% 4.00/0.98    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.00/0.98    inference(ennf_transformation,[],[f13])).
% 4.00/0.98  
% 4.00/0.98  fof(f38,plain,(
% 4.00/0.98    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.00/0.98    inference(flattening,[],[f37])).
% 4.00/0.98  
% 4.00/0.98  fof(f77,plain,(
% 4.00/0.98    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.00/0.98    inference(cnf_transformation,[],[f38])).
% 4.00/0.98  
% 4.00/0.98  fof(f69,plain,(
% 4.00/0.98    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.00/0.98    inference(cnf_transformation,[],[f30])).
% 4.00/0.98  
% 4.00/0.98  fof(f103,plain,(
% 4.00/0.98    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.00/0.98    inference(definition_unfolding,[],[f69,f94])).
% 4.00/0.98  
% 4.00/0.98  fof(f78,plain,(
% 4.00/0.98    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.00/0.98    inference(cnf_transformation,[],[f38])).
% 4.00/0.98  
% 4.00/0.98  fof(f9,axiom,(
% 4.00/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 4.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.98  
% 4.00/0.98  fof(f25,plain,(
% 4.00/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 4.00/0.98    inference(pure_predicate_removal,[],[f9])).
% 4.00/0.98  
% 4.00/0.98  fof(f32,plain,(
% 4.00/0.98    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.00/0.98    inference(ennf_transformation,[],[f25])).
% 4.00/0.98  
% 4.00/0.98  fof(f72,plain,(
% 4.00/0.98    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.00/0.98    inference(cnf_transformation,[],[f32])).
% 4.00/0.98  
% 4.00/0.98  fof(f15,axiom,(
% 4.00/0.98    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 4.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.98  
% 4.00/0.98  fof(f41,plain,(
% 4.00/0.98    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 4.00/0.98    inference(ennf_transformation,[],[f15])).
% 4.00/0.98  
% 4.00/0.98  fof(f42,plain,(
% 4.00/0.98    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 4.00/0.98    inference(flattening,[],[f41])).
% 4.00/0.98  
% 4.00/0.98  fof(f57,plain,(
% 4.00/0.98    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 4.00/0.98    inference(nnf_transformation,[],[f42])).
% 4.00/0.98  
% 4.00/0.98  fof(f85,plain,(
% 4.00/0.98    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 4.00/0.98    inference(cnf_transformation,[],[f57])).
% 4.00/0.98  
% 4.00/0.98  fof(f102,plain,(
% 4.00/0.98    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))),
% 4.00/0.98    inference(cnf_transformation,[],[f59])).
% 4.00/0.98  
% 4.00/0.98  fof(f17,axiom,(
% 4.00/0.98    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 4.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.98  
% 4.00/0.98  fof(f24,plain,(
% 4.00/0.98    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 4.00/0.98    inference(pure_predicate_removal,[],[f17])).
% 4.00/0.98  
% 4.00/0.98  fof(f91,plain,(
% 4.00/0.98    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 4.00/0.98    inference(cnf_transformation,[],[f24])).
% 4.00/0.98  
% 4.00/0.98  fof(f12,axiom,(
% 4.00/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 4.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.98  
% 4.00/0.98  fof(f35,plain,(
% 4.00/0.98    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 4.00/0.98    inference(ennf_transformation,[],[f12])).
% 4.00/0.98  
% 4.00/0.98  fof(f36,plain,(
% 4.00/0.98    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.00/0.98    inference(flattening,[],[f35])).
% 4.00/0.98  
% 4.00/0.98  fof(f75,plain,(
% 4.00/0.98    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.00/0.98    inference(cnf_transformation,[],[f36])).
% 4.00/0.98  
% 4.00/0.98  fof(f5,axiom,(
% 4.00/0.98    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 4.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.98  
% 4.00/0.98  fof(f28,plain,(
% 4.00/0.98    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 4.00/0.98    inference(ennf_transformation,[],[f5])).
% 4.00/0.98  
% 4.00/0.98  fof(f55,plain,(
% 4.00/0.98    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 4.00/0.98    inference(nnf_transformation,[],[f28])).
% 4.00/0.98  
% 4.00/0.98  fof(f67,plain,(
% 4.00/0.98    ( ! [X0] : (k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 4.00/0.98    inference(cnf_transformation,[],[f55])).
% 4.00/0.98  
% 4.00/0.98  fof(f3,axiom,(
% 4.00/0.98    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 4.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.98  
% 4.00/0.98  fof(f53,plain,(
% 4.00/0.98    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 4.00/0.98    inference(nnf_transformation,[],[f3])).
% 4.00/0.98  
% 4.00/0.98  fof(f54,plain,(
% 4.00/0.98    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 4.00/0.98    inference(flattening,[],[f53])).
% 4.00/0.98  
% 4.00/0.98  fof(f64,plain,(
% 4.00/0.98    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 4.00/0.98    inference(cnf_transformation,[],[f54])).
% 4.00/0.98  
% 4.00/0.98  fof(f106,plain,(
% 4.00/0.98    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 4.00/0.98    inference(equality_resolution,[],[f64])).
% 4.00/0.98  
% 4.00/0.98  fof(f4,axiom,(
% 4.00/0.98    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 4.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.98  
% 4.00/0.98  fof(f27,plain,(
% 4.00/0.98    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 4.00/0.98    inference(ennf_transformation,[],[f4])).
% 4.00/0.98  
% 4.00/0.98  fof(f65,plain,(
% 4.00/0.98    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 4.00/0.98    inference(cnf_transformation,[],[f27])).
% 4.00/0.98  
% 4.00/0.98  fof(f1,axiom,(
% 4.00/0.98    v1_xboole_0(k1_xboole_0)),
% 4.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.98  
% 4.00/0.98  fof(f60,plain,(
% 4.00/0.98    v1_xboole_0(k1_xboole_0)),
% 4.00/0.98    inference(cnf_transformation,[],[f1])).
% 4.00/0.98  
% 4.00/0.98  fof(f2,axiom,(
% 4.00/0.98    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 4.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.98  
% 4.00/0.98  fof(f26,plain,(
% 4.00/0.98    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 4.00/0.98    inference(ennf_transformation,[],[f2])).
% 4.00/0.98  
% 4.00/0.98  fof(f61,plain,(
% 4.00/0.98    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 4.00/0.98    inference(cnf_transformation,[],[f26])).
% 4.00/0.98  
% 4.00/0.98  fof(f63,plain,(
% 4.00/0.98    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 4.00/0.98    inference(cnf_transformation,[],[f54])).
% 4.00/0.98  
% 4.00/0.98  fof(f107,plain,(
% 4.00/0.98    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 4.00/0.98    inference(equality_resolution,[],[f63])).
% 4.00/0.98  
% 4.00/0.98  fof(f62,plain,(
% 4.00/0.98    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 4.00/0.98    inference(cnf_transformation,[],[f54])).
% 4.00/0.98  
% 4.00/0.98  cnf(c_38,negated_conjecture,
% 4.00/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 4.00/0.98      inference(cnf_transformation,[],[f101]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_1599,plain,
% 4.00/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 4.00/0.98      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_24,plain,
% 4.00/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 4.00/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.00/0.98      | k1_relset_1(X1,X2,X0) = X1
% 4.00/0.98      | k1_xboole_0 = X2 ),
% 4.00/0.98      inference(cnf_transformation,[],[f79]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_1610,plain,
% 4.00/0.98      ( k1_relset_1(X0,X1,X2) = X0
% 4.00/0.98      | k1_xboole_0 = X1
% 4.00/0.98      | v1_funct_2(X2,X0,X1) != iProver_top
% 4.00/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 4.00/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_6488,plain,
% 4.00/0.98      ( k1_relset_1(sK0,sK0,sK1) = sK0
% 4.00/0.98      | sK0 = k1_xboole_0
% 4.00/0.98      | v1_funct_2(sK1,sK0,sK0) != iProver_top ),
% 4.00/0.98      inference(superposition,[status(thm)],[c_1599,c_1610]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_14,plain,
% 4.00/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.00/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 4.00/0.98      inference(cnf_transformation,[],[f74]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_1618,plain,
% 4.00/0.98      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 4.00/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 4.00/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_2704,plain,
% 4.00/0.98      ( k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) ),
% 4.00/0.98      inference(superposition,[status(thm)],[c_1599,c_1618]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_6499,plain,
% 4.00/0.98      ( k1_relat_1(sK1) = sK0
% 4.00/0.98      | sK0 = k1_xboole_0
% 4.00/0.98      | v1_funct_2(sK1,sK0,sK0) != iProver_top ),
% 4.00/0.98      inference(demodulation,[status(thm)],[c_6488,c_2704]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_40,negated_conjecture,
% 4.00/0.98      ( v1_funct_2(sK1,sK0,sK0) ),
% 4.00/0.98      inference(cnf_transformation,[],[f99]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_43,plain,
% 4.00/0.98      ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
% 4.00/0.98      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_7219,plain,
% 4.00/0.98      ( sK0 = k1_xboole_0 | k1_relat_1(sK1) = sK0 ),
% 4.00/0.98      inference(global_propositional_subsumption,
% 4.00/0.98                [status(thm)],
% 4.00/0.98                [c_6499,c_43]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_7220,plain,
% 4.00/0.98      ( k1_relat_1(sK1) = sK0 | sK0 = k1_xboole_0 ),
% 4.00/0.98      inference(renaming,[status(thm)],[c_7219]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_33,plain,
% 4.00/0.98      ( ~ v1_funct_2(X0,X1,X1)
% 4.00/0.98      | ~ v3_funct_2(X0,X1,X1)
% 4.00/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 4.00/0.98      | ~ v1_funct_1(X0)
% 4.00/0.98      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 4.00/0.98      inference(cnf_transformation,[],[f93]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_1603,plain,
% 4.00/0.98      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
% 4.00/0.98      | v1_funct_2(X1,X0,X0) != iProver_top
% 4.00/0.98      | v3_funct_2(X1,X0,X0) != iProver_top
% 4.00/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 4.00/0.98      | v1_funct_1(X1) != iProver_top ),
% 4.00/0.98      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_4281,plain,
% 4.00/0.98      ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
% 4.00/0.98      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 4.00/0.98      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 4.00/0.98      | v1_funct_1(sK1) != iProver_top ),
% 4.00/0.98      inference(superposition,[status(thm)],[c_1599,c_1603]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_41,negated_conjecture,
% 4.00/0.98      ( v1_funct_1(sK1) ),
% 4.00/0.98      inference(cnf_transformation,[],[f98]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_39,negated_conjecture,
% 4.00/0.98      ( v3_funct_2(sK1,sK0,sK0) ),
% 4.00/0.98      inference(cnf_transformation,[],[f100]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_2025,plain,
% 4.00/0.98      ( ~ v1_funct_2(sK1,X0,X0)
% 4.00/0.98      | ~ v3_funct_2(sK1,X0,X0)
% 4.00/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 4.00/0.98      | ~ v1_funct_1(sK1)
% 4.00/0.98      | k2_funct_2(X0,sK1) = k2_funct_1(sK1) ),
% 4.00/0.98      inference(instantiation,[status(thm)],[c_33]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_2181,plain,
% 4.00/0.98      ( ~ v1_funct_2(sK1,sK0,sK0)
% 4.00/0.98      | ~ v3_funct_2(sK1,sK0,sK0)
% 4.00/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 4.00/0.98      | ~ v1_funct_1(sK1)
% 4.00/0.98      | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 4.00/0.98      inference(instantiation,[status(thm)],[c_2025]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_4743,plain,
% 4.00/0.98      ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 4.00/0.98      inference(global_propositional_subsumption,
% 4.00/0.98                [status(thm)],
% 4.00/0.98                [c_4281,c_41,c_40,c_39,c_38,c_2181]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_27,plain,
% 4.00/0.98      ( ~ v1_funct_2(X0,X1,X1)
% 4.00/0.98      | ~ v3_funct_2(X0,X1,X1)
% 4.00/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 4.00/0.98      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 4.00/0.98      | ~ v1_funct_1(X0) ),
% 4.00/0.98      inference(cnf_transformation,[],[f90]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_1609,plain,
% 4.00/0.98      ( v1_funct_2(X0,X1,X1) != iProver_top
% 4.00/0.98      | v3_funct_2(X0,X1,X1) != iProver_top
% 4.00/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 4.00/0.98      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) = iProver_top
% 4.00/0.98      | v1_funct_1(X0) != iProver_top ),
% 4.00/0.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_10127,plain,
% 4.00/0.98      ( v1_funct_2(sK1,sK0,sK0) != iProver_top
% 4.00/0.98      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 4.00/0.98      | m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 4.00/0.98      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 4.00/0.98      | v1_funct_1(sK1) != iProver_top ),
% 4.00/0.98      inference(superposition,[status(thm)],[c_4743,c_1609]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_42,plain,
% 4.00/0.98      ( v1_funct_1(sK1) = iProver_top ),
% 4.00/0.98      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_44,plain,
% 4.00/0.98      ( v3_funct_2(sK1,sK0,sK0) = iProver_top ),
% 4.00/0.98      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_45,plain,
% 4.00/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 4.00/0.98      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_10662,plain,
% 4.00/0.98      ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 4.00/0.98      inference(global_propositional_subsumption,
% 4.00/0.98                [status(thm)],
% 4.00/0.98                [c_10127,c_42,c_43,c_44,c_45]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_32,plain,
% 4.00/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.00/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 4.00/0.98      | ~ v1_funct_1(X0)
% 4.00/0.98      | ~ v1_funct_1(X3)
% 4.00/0.98      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 4.00/0.98      inference(cnf_transformation,[],[f92]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_1604,plain,
% 4.00/0.98      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 4.00/0.98      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 4.00/0.98      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 4.00/0.98      | v1_funct_1(X5) != iProver_top
% 4.00/0.98      | v1_funct_1(X4) != iProver_top ),
% 4.00/0.98      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_10680,plain,
% 4.00/0.98      ( k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1))
% 4.00/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 4.00/0.98      | v1_funct_1(X2) != iProver_top
% 4.00/0.98      | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
% 4.00/0.98      inference(superposition,[status(thm)],[c_10662,c_1604]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_30,plain,
% 4.00/0.98      ( ~ v1_funct_2(X0,X1,X1)
% 4.00/0.98      | ~ v3_funct_2(X0,X1,X1)
% 4.00/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 4.00/0.98      | ~ v1_funct_1(X0)
% 4.00/0.98      | v1_funct_1(k2_funct_2(X1,X0)) ),
% 4.00/0.98      inference(cnf_transformation,[],[f87]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_1606,plain,
% 4.00/0.98      ( v1_funct_2(X0,X1,X1) != iProver_top
% 4.00/0.98      | v3_funct_2(X0,X1,X1) != iProver_top
% 4.00/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 4.00/0.98      | v1_funct_1(X0) != iProver_top
% 4.00/0.98      | v1_funct_1(k2_funct_2(X1,X0)) = iProver_top ),
% 4.00/0.98      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_6354,plain,
% 4.00/0.98      ( v1_funct_2(sK1,sK0,sK0) != iProver_top
% 4.00/0.98      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 4.00/0.98      | v1_funct_1(k2_funct_2(sK0,sK1)) = iProver_top
% 4.00/0.98      | v1_funct_1(sK1) != iProver_top ),
% 4.00/0.98      inference(superposition,[status(thm)],[c_1599,c_1606]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_6371,plain,
% 4.00/0.98      ( v1_funct_2(sK1,sK0,sK0) != iProver_top
% 4.00/0.98      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 4.00/0.98      | v1_funct_1(k2_funct_1(sK1)) = iProver_top
% 4.00/0.98      | v1_funct_1(sK1) != iProver_top ),
% 4.00/0.98      inference(light_normalisation,[status(thm)],[c_6354,c_4743]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_16559,plain,
% 4.00/0.98      ( v1_funct_1(X2) != iProver_top
% 4.00/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 4.00/0.98      | k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1)) ),
% 4.00/0.98      inference(global_propositional_subsumption,
% 4.00/0.98                [status(thm)],
% 4.00/0.98                [c_10680,c_42,c_43,c_44,c_6371]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_16560,plain,
% 4.00/0.98      ( k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1))
% 4.00/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 4.00/0.98      | v1_funct_1(X2) != iProver_top ),
% 4.00/0.98      inference(renaming,[status(thm)],[c_16559]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_16571,plain,
% 4.00/0.98      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k5_relat_1(sK1,k2_funct_1(sK1))
% 4.00/0.98      | v1_funct_1(sK1) != iProver_top ),
% 4.00/0.98      inference(superposition,[status(thm)],[c_1599,c_16560]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_1596,plain,
% 4.00/0.98      ( v1_funct_1(sK1) = iProver_top ),
% 4.00/0.98      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_9,plain,
% 4.00/0.98      ( ~ v1_funct_1(X0)
% 4.00/0.98      | ~ v2_funct_1(X0)
% 4.00/0.98      | ~ v1_relat_1(X0)
% 4.00/0.98      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
% 4.00/0.98      inference(cnf_transformation,[],[f104]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_1621,plain,
% 4.00/0.98      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
% 4.00/0.98      | v1_funct_1(X0) != iProver_top
% 4.00/0.98      | v2_funct_1(X0) != iProver_top
% 4.00/0.98      | v1_relat_1(X0) != iProver_top ),
% 4.00/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_4665,plain,
% 4.00/0.98      ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
% 4.00/0.98      | v2_funct_1(sK1) != iProver_top
% 4.00/0.98      | v1_relat_1(sK1) != iProver_top ),
% 4.00/0.98      inference(superposition,[status(thm)],[c_1596,c_1621]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_11,plain,
% 4.00/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.00/0.98      | v1_relat_1(X0) ),
% 4.00/0.98      inference(cnf_transformation,[],[f71]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_1937,plain,
% 4.00/0.98      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 4.00/0.98      | v1_relat_1(sK1) ),
% 4.00/0.98      inference(instantiation,[status(thm)],[c_11]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_1958,plain,
% 4.00/0.98      ( ~ v1_funct_1(sK1)
% 4.00/0.98      | ~ v2_funct_1(sK1)
% 4.00/0.98      | ~ v1_relat_1(sK1)
% 4.00/0.98      | k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
% 4.00/0.98      inference(instantiation,[status(thm)],[c_9]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_17,plain,
% 4.00/0.98      ( ~ v3_funct_2(X0,X1,X2)
% 4.00/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.00/0.98      | ~ v1_funct_1(X0)
% 4.00/0.98      | v2_funct_1(X0) ),
% 4.00/0.98      inference(cnf_transformation,[],[f77]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_1975,plain,
% 4.00/0.98      ( ~ v3_funct_2(sK1,X0,X1)
% 4.00/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 4.00/0.98      | ~ v1_funct_1(sK1)
% 4.00/0.98      | v2_funct_1(sK1) ),
% 4.00/0.98      inference(instantiation,[status(thm)],[c_17]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_2118,plain,
% 4.00/0.98      ( ~ v3_funct_2(sK1,sK0,sK0)
% 4.00/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 4.00/0.98      | ~ v1_funct_1(sK1)
% 4.00/0.98      | v2_funct_1(sK1) ),
% 4.00/0.98      inference(instantiation,[status(thm)],[c_1975]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_4739,plain,
% 4.00/0.98      ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
% 4.00/0.98      inference(global_propositional_subsumption,
% 4.00/0.98                [status(thm)],
% 4.00/0.98                [c_4665,c_41,c_39,c_38,c_1937,c_1958,c_2118]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_16599,plain,
% 4.00/0.98      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
% 4.00/0.98      | v1_funct_1(sK1) != iProver_top ),
% 4.00/0.98      inference(light_normalisation,[status(thm)],[c_16571,c_4739]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_16641,plain,
% 4.00/0.98      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
% 4.00/0.98      inference(global_propositional_subsumption,
% 4.00/0.98                [status(thm)],
% 4.00/0.98                [c_16599,c_42]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_4938,plain,
% 4.00/0.98      ( k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1)
% 4.00/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 4.00/0.98      | v1_funct_1(X2) != iProver_top
% 4.00/0.98      | v1_funct_1(sK1) != iProver_top ),
% 4.00/0.98      inference(superposition,[status(thm)],[c_1599,c_1604]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_5683,plain,
% 4.00/0.98      ( v1_funct_1(X2) != iProver_top
% 4.00/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 4.00/0.98      | k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1) ),
% 4.00/0.98      inference(global_propositional_subsumption,
% 4.00/0.98                [status(thm)],
% 4.00/0.98                [c_4938,c_42]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_5684,plain,
% 4.00/0.98      ( k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1)
% 4.00/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 4.00/0.98      | v1_funct_1(X2) != iProver_top ),
% 4.00/0.98      inference(renaming,[status(thm)],[c_5683]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_10137,plain,
% 4.00/0.98      ( k1_partfun1(X0,X0,sK0,sK0,k2_funct_2(X0,X1),sK1) = k5_relat_1(k2_funct_2(X0,X1),sK1)
% 4.00/0.98      | v1_funct_2(X1,X0,X0) != iProver_top
% 4.00/0.98      | v3_funct_2(X1,X0,X0) != iProver_top
% 4.00/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 4.00/0.98      | v1_funct_1(X1) != iProver_top
% 4.00/0.98      | v1_funct_1(k2_funct_2(X0,X1)) != iProver_top ),
% 4.00/0.98      inference(superposition,[status(thm)],[c_1609,c_5684]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_10879,plain,
% 4.00/0.98      ( k1_partfun1(X0,X0,sK0,sK0,k2_funct_2(X0,X1),sK1) = k5_relat_1(k2_funct_2(X0,X1),sK1)
% 4.00/0.98      | v1_funct_2(X1,X0,X0) != iProver_top
% 4.00/0.98      | v3_funct_2(X1,X0,X0) != iProver_top
% 4.00/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 4.00/0.98      | v1_funct_1(X1) != iProver_top ),
% 4.00/0.98      inference(forward_subsumption_resolution,
% 4.00/0.98                [status(thm)],
% 4.00/0.98                [c_10137,c_1606]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_10885,plain,
% 4.00/0.98      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1) = k5_relat_1(k2_funct_2(sK0,sK1),sK1)
% 4.00/0.98      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 4.00/0.98      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 4.00/0.98      | v1_funct_1(sK1) != iProver_top ),
% 4.00/0.98      inference(superposition,[status(thm)],[c_1599,c_10879]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_8,plain,
% 4.00/0.98      ( ~ v1_funct_1(X0)
% 4.00/0.98      | ~ v2_funct_1(X0)
% 4.00/0.98      | ~ v1_relat_1(X0)
% 4.00/0.98      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
% 4.00/0.98      inference(cnf_transformation,[],[f103]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_1622,plain,
% 4.00/0.98      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
% 4.00/0.98      | v1_funct_1(X0) != iProver_top
% 4.00/0.98      | v2_funct_1(X0) != iProver_top
% 4.00/0.98      | v1_relat_1(X0) != iProver_top ),
% 4.00/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_5261,plain,
% 4.00/0.98      ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1))
% 4.00/0.98      | v2_funct_1(sK1) != iProver_top
% 4.00/0.98      | v1_relat_1(sK1) != iProver_top ),
% 4.00/0.98      inference(superposition,[status(thm)],[c_1596,c_1622]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_16,plain,
% 4.00/0.98      ( ~ v3_funct_2(X0,X1,X2)
% 4.00/0.98      | v2_funct_2(X0,X2)
% 4.00/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.00/0.98      | ~ v1_funct_1(X0) ),
% 4.00/0.98      inference(cnf_transformation,[],[f78]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_12,plain,
% 4.00/0.98      ( v5_relat_1(X0,X1)
% 4.00/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 4.00/0.98      inference(cnf_transformation,[],[f72]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_26,plain,
% 4.00/0.98      ( ~ v2_funct_2(X0,X1)
% 4.00/0.98      | ~ v5_relat_1(X0,X1)
% 4.00/0.98      | ~ v1_relat_1(X0)
% 4.00/0.98      | k2_relat_1(X0) = X1 ),
% 4.00/0.98      inference(cnf_transformation,[],[f85]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_418,plain,
% 4.00/0.98      ( ~ v2_funct_2(X0,X1)
% 4.00/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 4.00/0.98      | ~ v1_relat_1(X0)
% 4.00/0.98      | k2_relat_1(X0) = X1 ),
% 4.00/0.98      inference(resolution,[status(thm)],[c_12,c_26]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_430,plain,
% 4.00/0.98      ( ~ v2_funct_2(X0,X1)
% 4.00/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 4.00/0.98      | k2_relat_1(X0) = X1 ),
% 4.00/0.98      inference(forward_subsumption_resolution,
% 4.00/0.98                [status(thm)],
% 4.00/0.98                [c_418,c_11]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_461,plain,
% 4.00/0.98      ( ~ v3_funct_2(X0,X1,X2)
% 4.00/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.00/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 4.00/0.98      | ~ v1_funct_1(X0)
% 4.00/0.98      | X3 != X0
% 4.00/0.98      | X5 != X2
% 4.00/0.98      | k2_relat_1(X3) = X5 ),
% 4.00/0.98      inference(resolution_lifted,[status(thm)],[c_16,c_430]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_462,plain,
% 4.00/0.98      ( ~ v3_funct_2(X0,X1,X2)
% 4.00/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.00/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 4.00/0.98      | ~ v1_funct_1(X0)
% 4.00/0.98      | k2_relat_1(X0) = X2 ),
% 4.00/0.98      inference(unflattening,[status(thm)],[c_461]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_1595,plain,
% 4.00/0.98      ( k2_relat_1(X0) = X1
% 4.00/0.98      | v3_funct_2(X0,X2,X1) != iProver_top
% 4.00/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
% 4.00/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
% 4.00/0.98      | v1_funct_1(X0) != iProver_top ),
% 4.00/0.98      inference(predicate_to_equality,[status(thm)],[c_462]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_2513,plain,
% 4.00/0.98      ( k2_relat_1(sK1) = sK0
% 4.00/0.98      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 4.00/0.98      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 4.00/0.98      | v1_funct_1(sK1) != iProver_top ),
% 4.00/0.98      inference(superposition,[status(thm)],[c_1599,c_1595]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_2010,plain,
% 4.00/0.98      ( ~ v3_funct_2(sK1,X0,X1)
% 4.00/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 4.00/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 4.00/0.98      | ~ v1_funct_1(sK1)
% 4.00/0.98      | k2_relat_1(sK1) = X1 ),
% 4.00/0.98      inference(instantiation,[status(thm)],[c_462]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_2176,plain,
% 4.00/0.98      ( ~ v3_funct_2(sK1,sK0,sK0)
% 4.00/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
% 4.00/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 4.00/0.98      | ~ v1_funct_1(sK1)
% 4.00/0.98      | k2_relat_1(sK1) = sK0 ),
% 4.00/0.98      inference(instantiation,[status(thm)],[c_2010]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_2356,plain,
% 4.00/0.98      ( ~ v3_funct_2(sK1,sK0,sK0)
% 4.00/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 4.00/0.98      | ~ v1_funct_1(sK1)
% 4.00/0.98      | k2_relat_1(sK1) = sK0 ),
% 4.00/0.98      inference(instantiation,[status(thm)],[c_2176]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_2830,plain,
% 4.00/0.98      ( k2_relat_1(sK1) = sK0 ),
% 4.00/0.98      inference(global_propositional_subsumption,
% 4.00/0.98                [status(thm)],
% 4.00/0.98                [c_2513,c_41,c_39,c_38,c_2356]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_5262,plain,
% 4.00/0.98      ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
% 4.00/0.98      | v2_funct_1(sK1) != iProver_top
% 4.00/0.98      | v1_relat_1(sK1) != iProver_top ),
% 4.00/0.98      inference(light_normalisation,[status(thm)],[c_5261,c_2830]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_1938,plain,
% 4.00/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 4.00/0.98      | v1_relat_1(sK1) = iProver_top ),
% 4.00/0.98      inference(predicate_to_equality,[status(thm)],[c_1937]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_2119,plain,
% 4.00/0.98      ( v3_funct_2(sK1,sK0,sK0) != iProver_top
% 4.00/0.98      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 4.00/0.98      | v1_funct_1(sK1) != iProver_top
% 4.00/0.98      | v2_funct_1(sK1) = iProver_top ),
% 4.00/0.98      inference(predicate_to_equality,[status(thm)],[c_2118]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_6002,plain,
% 4.00/0.98      ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(sK0) ),
% 4.00/0.98      inference(global_propositional_subsumption,
% 4.00/0.98                [status(thm)],
% 4.00/0.98                [c_5262,c_42,c_44,c_45,c_1938,c_2119]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_10911,plain,
% 4.00/0.98      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
% 4.00/0.98      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 4.00/0.98      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 4.00/0.98      | v1_funct_1(sK1) != iProver_top ),
% 4.00/0.98      inference(light_normalisation,
% 4.00/0.98                [status(thm)],
% 4.00/0.98                [c_10885,c_4743,c_6002]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_10674,plain,
% 4.00/0.98      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k5_relat_1(k2_funct_1(sK1),sK1)
% 4.00/0.98      | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
% 4.00/0.98      inference(superposition,[status(thm)],[c_10662,c_5684]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_10730,plain,
% 4.00/0.98      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
% 4.00/0.98      | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
% 4.00/0.98      inference(light_normalisation,[status(thm)],[c_10674,c_6002]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_10952,plain,
% 4.00/0.98      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0) ),
% 4.00/0.98      inference(global_propositional_subsumption,
% 4.00/0.98                [status(thm)],
% 4.00/0.98                [c_10911,c_42,c_43,c_44,c_6371,c_10730]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_37,negated_conjecture,
% 4.00/0.98      ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
% 4.00/0.98      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
% 4.00/0.98      inference(cnf_transformation,[],[f102]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_1600,plain,
% 4.00/0.98      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) != iProver_top
% 4.00/0.98      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) != iProver_top ),
% 4.00/0.98      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_4746,plain,
% 4.00/0.98      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) != iProver_top
% 4.00/0.98      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
% 4.00/0.98      inference(demodulation,[status(thm)],[c_4743,c_1600]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_10955,plain,
% 4.00/0.98      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top
% 4.00/0.98      | r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
% 4.00/0.98      inference(demodulation,[status(thm)],[c_10952,c_4746]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_31,plain,
% 4.00/0.98      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 4.00/0.98      inference(cnf_transformation,[],[f91]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_2597,plain,
% 4.00/0.98      ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 4.00/0.98      inference(instantiation,[status(thm)],[c_31]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_2600,plain,
% 4.00/0.98      ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 4.00/0.98      inference(predicate_to_equality,[status(thm)],[c_2597]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_15,plain,
% 4.00/0.98      ( r2_relset_1(X0,X1,X2,X2)
% 4.00/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 4.00/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 4.00/0.98      inference(cnf_transformation,[],[f75]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_1995,plain,
% 4.00/0.98      ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0))
% 4.00/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 4.00/0.98      | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 4.00/0.98      inference(instantiation,[status(thm)],[c_15]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_2628,plain,
% 4.00/0.98      ( r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))
% 4.00/0.98      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 4.00/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 4.00/0.98      inference(instantiation,[status(thm)],[c_1995]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_2629,plain,
% 4.00/0.98      ( r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) = iProver_top
% 4.00/0.98      | m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 4.00/0.98      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 4.00/0.98      inference(predicate_to_equality,[status(thm)],[c_2628]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_10994,plain,
% 4.00/0.98      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
% 4.00/0.98      inference(global_propositional_subsumption,
% 4.00/0.98                [status(thm)],
% 4.00/0.98                [c_10955,c_45,c_2600,c_2629]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_16644,plain,
% 4.00/0.98      ( r2_relset_1(sK0,sK0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
% 4.00/0.98      inference(demodulation,[status(thm)],[c_16641,c_10994]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_17315,plain,
% 4.00/0.98      ( sK0 = k1_xboole_0
% 4.00/0.98      | r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
% 4.00/0.98      inference(superposition,[status(thm)],[c_7220,c_16644]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_17318,plain,
% 4.00/0.98      ( sK0 = k1_xboole_0 ),
% 4.00/0.98      inference(global_propositional_subsumption,
% 4.00/0.98                [status(thm)],
% 4.00/0.98                [c_17315,c_45,c_2600,c_2629]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_17321,plain,
% 4.00/0.98      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(k1_xboole_0)) != iProver_top ),
% 4.00/0.98      inference(demodulation,[status(thm)],[c_17318,c_16644]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_6,plain,
% 4.00/0.98      ( ~ v1_relat_1(X0)
% 4.00/0.98      | k2_relat_1(X0) != k1_xboole_0
% 4.00/0.98      | k1_relat_1(X0) = k1_xboole_0 ),
% 4.00/0.98      inference(cnf_transformation,[],[f67]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_1624,plain,
% 4.00/0.98      ( k2_relat_1(X0) != k1_xboole_0
% 4.00/0.98      | k1_relat_1(X0) = k1_xboole_0
% 4.00/0.98      | v1_relat_1(X0) != iProver_top ),
% 4.00/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_2833,plain,
% 4.00/0.98      ( k1_relat_1(sK1) = k1_xboole_0
% 4.00/0.98      | sK0 != k1_xboole_0
% 4.00/0.98      | v1_relat_1(sK1) != iProver_top ),
% 4.00/0.98      inference(superposition,[status(thm)],[c_2830,c_1624]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_2834,plain,
% 4.00/0.98      ( ~ v1_relat_1(sK1)
% 4.00/0.98      | k1_relat_1(sK1) = k1_xboole_0
% 4.00/0.98      | sK0 != k1_xboole_0 ),
% 4.00/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_2833]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_2915,plain,
% 4.00/0.98      ( sK0 != k1_xboole_0 | k1_relat_1(sK1) = k1_xboole_0 ),
% 4.00/0.98      inference(global_propositional_subsumption,
% 4.00/0.98                [status(thm)],
% 4.00/0.98                [c_2833,c_38,c_1937,c_2834]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_2916,plain,
% 4.00/0.98      ( k1_relat_1(sK1) = k1_xboole_0 | sK0 != k1_xboole_0 ),
% 4.00/0.98      inference(renaming,[status(thm)],[c_2915]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_17382,plain,
% 4.00/0.98      ( k1_relat_1(sK1) = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 4.00/0.98      inference(demodulation,[status(thm)],[c_17318,c_2916]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_17399,plain,
% 4.00/0.98      ( k1_relat_1(sK1) = k1_xboole_0 ),
% 4.00/0.98      inference(equality_resolution_simp,[status(thm)],[c_17382]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_17602,plain,
% 4.00/0.98      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),k6_partfun1(k1_xboole_0)) != iProver_top ),
% 4.00/0.98      inference(light_normalisation,[status(thm)],[c_17321,c_17399]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_2,plain,
% 4.00/0.98      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 4.00/0.98      inference(cnf_transformation,[],[f106]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_1605,plain,
% 4.00/0.98      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 4.00/0.98      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_2092,plain,
% 4.00/0.98      ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 4.00/0.98      inference(superposition,[status(thm)],[c_2,c_1605]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_5,plain,
% 4.00/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 4.00/0.98      | ~ v1_xboole_0(X1)
% 4.00/0.98      | v1_xboole_0(X0) ),
% 4.00/0.98      inference(cnf_transformation,[],[f65]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_1625,plain,
% 4.00/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 4.00/0.98      | v1_xboole_0(X1) != iProver_top
% 4.00/0.98      | v1_xboole_0(X0) = iProver_top ),
% 4.00/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_3176,plain,
% 4.00/0.98      ( v1_xboole_0(k6_partfun1(k1_xboole_0)) = iProver_top
% 4.00/0.98      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 4.00/0.98      inference(superposition,[status(thm)],[c_2092,c_1625]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_0,plain,
% 4.00/0.98      ( v1_xboole_0(k1_xboole_0) ),
% 4.00/0.98      inference(cnf_transformation,[],[f60]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_138,plain,
% 4.00/0.98      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 4.00/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_2890,plain,
% 4.00/0.98      ( ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(X1))
% 4.00/0.98      | ~ v1_xboole_0(X1)
% 4.00/0.98      | v1_xboole_0(k6_partfun1(X0)) ),
% 4.00/0.98      inference(instantiation,[status(thm)],[c_5]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_2891,plain,
% 4.00/0.98      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(X1)) != iProver_top
% 4.00/0.98      | v1_xboole_0(X1) != iProver_top
% 4.00/0.98      | v1_xboole_0(k6_partfun1(X0)) = iProver_top ),
% 4.00/0.98      inference(predicate_to_equality,[status(thm)],[c_2890]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_2893,plain,
% 4.00/0.98      ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 4.00/0.98      | v1_xboole_0(k6_partfun1(k1_xboole_0)) = iProver_top
% 4.00/0.98      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 4.00/0.98      inference(instantiation,[status(thm)],[c_2891]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_3993,plain,
% 4.00/0.98      ( v1_xboole_0(k6_partfun1(k1_xboole_0)) = iProver_top ),
% 4.00/0.98      inference(global_propositional_subsumption,
% 4.00/0.98                [status(thm)],
% 4.00/0.98                [c_3176,c_138,c_2092,c_2893]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_1627,plain,
% 4.00/0.98      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 4.00/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_1,plain,
% 4.00/0.98      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X1 = X0 ),
% 4.00/0.98      inference(cnf_transformation,[],[f61]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_1626,plain,
% 4.00/0.98      ( X0 = X1
% 4.00/0.98      | v1_xboole_0(X1) != iProver_top
% 4.00/0.98      | v1_xboole_0(X0) != iProver_top ),
% 4.00/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_2390,plain,
% 4.00/0.98      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 4.00/0.98      inference(superposition,[status(thm)],[c_1627,c_1626]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_3998,plain,
% 4.00/0.98      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 4.00/0.98      inference(superposition,[status(thm)],[c_3993,c_2390]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_17604,plain,
% 4.00/0.98      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 4.00/0.98      inference(light_normalisation,[status(thm)],[c_17602,c_3998]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_1028,plain,
% 4.00/0.98      ( ~ r2_relset_1(X0,X1,X2,X3)
% 4.00/0.98      | r2_relset_1(X4,X5,X6,X7)
% 4.00/0.98      | X4 != X0
% 4.00/0.98      | X5 != X1
% 4.00/0.98      | X6 != X2
% 4.00/0.98      | X7 != X3 ),
% 4.00/0.98      theory(equality) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_3201,plain,
% 4.00/0.98      ( r2_relset_1(X0,X1,X2,X3)
% 4.00/0.98      | ~ r2_relset_1(X4,X4,k6_partfun1(X4),k6_partfun1(X4))
% 4.00/0.98      | X0 != X4
% 4.00/0.98      | X1 != X4
% 4.00/0.98      | X2 != k6_partfun1(X4)
% 4.00/0.98      | X3 != k6_partfun1(X4) ),
% 4.00/0.98      inference(instantiation,[status(thm)],[c_1028]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_3202,plain,
% 4.00/0.98      ( X0 != X1
% 4.00/0.98      | X2 != X1
% 4.00/0.98      | X3 != k6_partfun1(X1)
% 4.00/0.98      | X4 != k6_partfun1(X1)
% 4.00/0.98      | r2_relset_1(X0,X2,X3,X4) = iProver_top
% 4.00/0.98      | r2_relset_1(X1,X1,k6_partfun1(X1),k6_partfun1(X1)) != iProver_top ),
% 4.00/0.98      inference(predicate_to_equality,[status(thm)],[c_3201]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_3204,plain,
% 4.00/0.98      ( k1_xboole_0 != k6_partfun1(k1_xboole_0)
% 4.00/0.98      | k1_xboole_0 != k1_xboole_0
% 4.00/0.98      | r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),k6_partfun1(k1_xboole_0)) != iProver_top
% 4.00/0.98      | r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top ),
% 4.00/0.98      inference(instantiation,[status(thm)],[c_3202]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_2892,plain,
% 4.00/0.98      ( ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
% 4.00/0.98      | v1_xboole_0(k6_partfun1(k1_xboole_0))
% 4.00/0.98      | ~ v1_xboole_0(k1_xboole_0) ),
% 4.00/0.98      inference(instantiation,[status(thm)],[c_2890]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_2635,plain,
% 4.00/0.98      ( ~ v1_xboole_0(X0)
% 4.00/0.98      | ~ v1_xboole_0(k6_partfun1(X1))
% 4.00/0.98      | X0 = k6_partfun1(X1) ),
% 4.00/0.98      inference(instantiation,[status(thm)],[c_1]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_2637,plain,
% 4.00/0.98      ( ~ v1_xboole_0(k6_partfun1(k1_xboole_0))
% 4.00/0.98      | ~ v1_xboole_0(k1_xboole_0)
% 4.00/0.98      | k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
% 4.00/0.98      inference(instantiation,[status(thm)],[c_2635]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_2623,plain,
% 4.00/0.98      ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0))
% 4.00/0.98      | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 4.00/0.98      inference(instantiation,[status(thm)],[c_1995]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_2624,plain,
% 4.00/0.98      ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0)) = iProver_top
% 4.00/0.98      | m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
% 4.00/0.98      inference(predicate_to_equality,[status(thm)],[c_2623]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_2626,plain,
% 4.00/0.98      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),k6_partfun1(k1_xboole_0)) = iProver_top
% 4.00/0.98      | m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 4.00/0.98      inference(instantiation,[status(thm)],[c_2624]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_2094,plain,
% 4.00/0.98      ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
% 4.00/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_2092]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_3,plain,
% 4.00/0.98      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 4.00/0.98      inference(cnf_transformation,[],[f107]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_134,plain,
% 4.00/0.98      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 4.00/0.98      inference(instantiation,[status(thm)],[c_3]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_4,plain,
% 4.00/0.98      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 4.00/0.98      | k1_xboole_0 = X1
% 4.00/0.98      | k1_xboole_0 = X0 ),
% 4.00/0.98      inference(cnf_transformation,[],[f62]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_133,plain,
% 4.00/0.98      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 4.00/0.98      | k1_xboole_0 = k1_xboole_0 ),
% 4.00/0.98      inference(instantiation,[status(thm)],[c_4]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_60,plain,
% 4.00/0.98      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 4.00/0.98      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_62,plain,
% 4.00/0.98      ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 4.00/0.98      inference(instantiation,[status(thm)],[c_60]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(contradiction,plain,
% 4.00/0.98      ( $false ),
% 4.00/0.98      inference(minisat,
% 4.00/0.98                [status(thm)],
% 4.00/0.98                [c_17604,c_3204,c_2892,c_2637,c_2626,c_2094,c_0,c_134,
% 4.00/0.98                 c_133,c_62]) ).
% 4.00/0.98  
% 4.00/0.98  
% 4.00/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 4.00/0.98  
% 4.00/0.98  ------                               Statistics
% 4.00/0.98  
% 4.00/0.98  ------ General
% 4.00/0.98  
% 4.00/0.98  abstr_ref_over_cycles:                  0
% 4.00/0.98  abstr_ref_under_cycles:                 0
% 4.00/0.98  gc_basic_clause_elim:                   0
% 4.00/0.98  forced_gc_time:                         0
% 4.00/0.98  parsing_time:                           0.013
% 4.00/0.98  unif_index_cands_time:                  0.
% 4.00/0.98  unif_index_add_time:                    0.
% 4.00/0.98  orderings_time:                         0.
% 4.00/0.98  out_proof_time:                         0.016
% 4.00/0.98  total_time:                             0.451
% 4.00/0.98  num_of_symbols:                         54
% 4.00/0.98  num_of_terms:                           13822
% 4.00/0.98  
% 4.00/0.98  ------ Preprocessing
% 4.00/0.98  
% 4.00/0.98  num_of_splits:                          0
% 4.00/0.98  num_of_split_atoms:                     0
% 4.00/0.98  num_of_reused_defs:                     0
% 4.00/0.98  num_eq_ax_congr_red:                    20
% 4.00/0.98  num_of_sem_filtered_clauses:            1
% 4.00/0.98  num_of_subtypes:                        0
% 4.00/0.98  monotx_restored_types:                  0
% 4.00/0.98  sat_num_of_epr_types:                   0
% 4.00/0.98  sat_num_of_non_cyclic_types:            0
% 4.00/0.98  sat_guarded_non_collapsed_types:        0
% 4.00/0.98  num_pure_diseq_elim:                    0
% 4.00/0.98  simp_replaced_by:                       0
% 4.00/0.98  res_preprocessed:                       184
% 4.00/0.98  prep_upred:                             0
% 4.00/0.98  prep_unflattend:                        6
% 4.00/0.98  smt_new_axioms:                         0
% 4.00/0.98  pred_elim_cands:                        8
% 4.00/0.98  pred_elim:                              2
% 4.00/0.98  pred_elim_cl:                           3
% 4.00/0.98  pred_elim_cycles:                       6
% 4.00/0.98  merged_defs:                            0
% 4.00/0.98  merged_defs_ncl:                        0
% 4.00/0.98  bin_hyper_res:                          0
% 4.00/0.98  prep_cycles:                            4
% 4.00/0.98  pred_elim_time:                         0.008
% 4.00/0.98  splitting_time:                         0.
% 4.00/0.98  sem_filter_time:                        0.
% 4.00/0.98  monotx_time:                            0.001
% 4.00/0.98  subtype_inf_time:                       0.
% 4.00/0.98  
% 4.00/0.98  ------ Problem properties
% 4.00/0.98  
% 4.00/0.98  clauses:                                37
% 4.00/0.98  conjectures:                            5
% 4.00/0.98  epr:                                    5
% 4.00/0.98  horn:                                   32
% 4.00/0.98  ground:                                 6
% 4.00/0.98  unary:                                  9
% 4.00/0.98  binary:                                 3
% 4.00/0.98  lits:                                   110
% 4.00/0.98  lits_eq:                                26
% 4.00/0.98  fd_pure:                                0
% 4.00/0.98  fd_pseudo:                              0
% 4.00/0.98  fd_cond:                                4
% 4.00/0.98  fd_pseudo_cond:                         2
% 4.00/0.98  ac_symbols:                             0
% 4.00/0.98  
% 4.00/0.98  ------ Propositional Solver
% 4.00/0.98  
% 4.00/0.98  prop_solver_calls:                      30
% 4.00/0.98  prop_fast_solver_calls:                 1774
% 4.00/0.98  smt_solver_calls:                       0
% 4.00/0.98  smt_fast_solver_calls:                  0
% 4.00/0.98  prop_num_of_clauses:                    6198
% 4.00/0.98  prop_preprocess_simplified:             15903
% 4.00/0.98  prop_fo_subsumed:                       80
% 4.00/0.98  prop_solver_time:                       0.
% 4.00/0.98  smt_solver_time:                        0.
% 4.00/0.98  smt_fast_solver_time:                   0.
% 4.00/0.98  prop_fast_solver_time:                  0.
% 4.00/0.98  prop_unsat_core_time:                   0.
% 4.00/0.98  
% 4.00/0.98  ------ QBF
% 4.00/0.98  
% 4.00/0.98  qbf_q_res:                              0
% 4.00/0.98  qbf_num_tautologies:                    0
% 4.00/0.98  qbf_prep_cycles:                        0
% 4.00/0.98  
% 4.00/0.98  ------ BMC1
% 4.00/0.98  
% 4.00/0.98  bmc1_current_bound:                     -1
% 4.00/0.98  bmc1_last_solved_bound:                 -1
% 4.00/0.98  bmc1_unsat_core_size:                   -1
% 4.00/0.98  bmc1_unsat_core_parents_size:           -1
% 4.00/0.98  bmc1_merge_next_fun:                    0
% 4.00/0.98  bmc1_unsat_core_clauses_time:           0.
% 4.00/0.98  
% 4.00/0.98  ------ Instantiation
% 4.00/0.98  
% 4.00/0.98  inst_num_of_clauses:                    2111
% 4.00/0.98  inst_num_in_passive:                    1017
% 4.00/0.98  inst_num_in_active:                     788
% 4.00/0.98  inst_num_in_unprocessed:                308
% 4.00/0.98  inst_num_of_loops:                      810
% 4.00/0.98  inst_num_of_learning_restarts:          0
% 4.00/0.98  inst_num_moves_active_passive:          20
% 4.00/0.98  inst_lit_activity:                      0
% 4.00/0.98  inst_lit_activity_moves:                0
% 4.00/0.98  inst_num_tautologies:                   0
% 4.00/0.98  inst_num_prop_implied:                  0
% 4.00/0.98  inst_num_existing_simplified:           0
% 4.00/0.98  inst_num_eq_res_simplified:             0
% 4.00/0.98  inst_num_child_elim:                    0
% 4.00/0.98  inst_num_of_dismatching_blockings:      318
% 4.00/0.98  inst_num_of_non_proper_insts:           1913
% 4.00/0.98  inst_num_of_duplicates:                 0
% 4.00/0.98  inst_inst_num_from_inst_to_res:         0
% 4.00/0.98  inst_dismatching_checking_time:         0.
% 4.00/0.98  
% 4.00/0.98  ------ Resolution
% 4.00/0.98  
% 4.00/0.98  res_num_of_clauses:                     0
% 4.00/0.98  res_num_in_passive:                     0
% 4.00/0.98  res_num_in_active:                      0
% 4.00/0.98  res_num_of_loops:                       188
% 4.00/0.98  res_forward_subset_subsumed:            52
% 4.00/0.98  res_backward_subset_subsumed:           12
% 4.00/0.98  res_forward_subsumed:                   0
% 4.00/0.98  res_backward_subsumed:                  0
% 4.00/0.98  res_forward_subsumption_resolution:     2
% 4.00/0.98  res_backward_subsumption_resolution:    0
% 4.00/0.98  res_clause_to_clause_subsumption:       916
% 4.00/0.98  res_orphan_elimination:                 0
% 4.00/0.98  res_tautology_del:                      68
% 4.00/0.98  res_num_eq_res_simplified:              0
% 4.00/0.98  res_num_sel_changes:                    0
% 4.00/0.98  res_moves_from_active_to_pass:          0
% 4.00/0.98  
% 4.00/0.98  ------ Superposition
% 4.00/0.98  
% 4.00/0.98  sup_time_total:                         0.
% 4.00/0.98  sup_time_generating:                    0.
% 4.00/0.98  sup_time_sim_full:                      0.
% 4.00/0.98  sup_time_sim_immed:                     0.
% 4.00/0.98  
% 4.00/0.98  sup_num_of_clauses:                     233
% 4.00/0.98  sup_num_in_active:                      75
% 4.00/0.98  sup_num_in_passive:                     158
% 4.00/0.98  sup_num_of_loops:                       161
% 4.00/0.98  sup_fw_superposition:                   199
% 4.00/0.98  sup_bw_superposition:                   106
% 4.00/0.98  sup_immediate_simplified:               95
% 4.00/0.98  sup_given_eliminated:                   3
% 4.00/0.98  comparisons_done:                       0
% 4.00/0.98  comparisons_avoided:                    0
% 4.00/0.98  
% 4.00/0.98  ------ Simplifications
% 4.00/0.98  
% 4.00/0.98  
% 4.00/0.98  sim_fw_subset_subsumed:                 17
% 4.00/0.98  sim_bw_subset_subsumed:                 16
% 4.00/0.98  sim_fw_subsumed:                        16
% 4.00/0.98  sim_bw_subsumed:                        4
% 4.00/0.98  sim_fw_subsumption_res:                 3
% 4.00/0.98  sim_bw_subsumption_res:                 0
% 4.00/0.98  sim_tautology_del:                      4
% 4.00/0.98  sim_eq_tautology_del:                   20
% 4.00/0.98  sim_eq_res_simp:                        1
% 4.00/0.98  sim_fw_demodulated:                     12
% 4.00/0.98  sim_bw_demodulated:                     78
% 4.00/0.98  sim_light_normalised:                   59
% 4.00/0.98  sim_joinable_taut:                      0
% 4.00/0.98  sim_joinable_simp:                      0
% 4.00/0.98  sim_ac_normalised:                      0
% 4.00/0.98  sim_smt_subsumption:                    0
% 4.00/0.98  
%------------------------------------------------------------------------------
