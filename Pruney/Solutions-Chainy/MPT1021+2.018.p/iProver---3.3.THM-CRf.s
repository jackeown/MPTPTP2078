%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:21 EST 2020

% Result     : Theorem 3.65s
% Output     : CNFRefutation 3.65s
% Verified   : 
% Statistics : Number of formulae       :  212 (14935 expanded)
%              Number of clauses        :  140 (4763 expanded)
%              Number of leaves         :   17 (2850 expanded)
%              Depth                    :   32
%              Number of atoms          :  657 (69276 expanded)
%              Number of equality atoms :  320 (7826 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f46,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f47,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f46])).

fof(f52,plain,
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

fof(f53,plain,
    ( ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) )
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK1,sK0,sK0)
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f47,f52])).

fof(f89,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f53])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f12])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f50,plain,(
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
    inference(nnf_transformation,[],[f37])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f87,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_1(X1) = k2_funct_2(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f44])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f86,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f88,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f53])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f14])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f40])).

fof(f81,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f42])).

fof(f83,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f78,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k2_funct_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f34])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f6,axiom,(
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
    inference(ennf_transformation,[],[f6])).

fof(f28,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f61,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f18,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f85,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f18])).

fof(f92,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f61,f85])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f62,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f91,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f62,f85])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f38])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f90,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f53])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f32])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f15,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f82,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f60,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v3_funct_2(k2_funct_2(X0,X1),X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f1,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f1])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1466,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1475,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3554,plain,
    ( k1_relset_1(sK0,sK0,sK1) = sK0
    | sK0 = k1_xboole_0
    | v1_funct_2(sK1,sK0,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1466,c_1475])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1483,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2077,plain,
    ( k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_1466,c_1483])).

cnf(c_3561,plain,
    ( k1_relat_1(sK1) = sK0
    | sK0 = k1_xboole_0
    | v1_funct_2(sK1,sK0,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3554,c_2077])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_37,plain,
    ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_4037,plain,
    ( sK0 = k1_xboole_0
    | k1_relat_1(sK1) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3561,c_37])).

cnf(c_4038,plain,
    ( k1_relat_1(sK1) = sK0
    | sK0 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_4037])).

cnf(c_30,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1468,plain,
    ( k2_funct_2(X0,X1) = k2_funct_1(X1)
    | v1_funct_2(X1,X0,X0) != iProver_top
    | v3_funct_2(X1,X0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_4485,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1466,c_1468])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_36,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_33,negated_conjecture,
    ( v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_38,plain,
    ( v3_funct_2(sK1,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_5051,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4485,c_36,c_37,c_38])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1474,plain,
    ( v1_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(X0,X1,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_5061,plain,
    ( v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5051,c_1474])).

cnf(c_39,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_7042,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5061,c_36,c_37,c_38,c_39])).

cnf(c_29,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1469,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_7058,plain,
    ( k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7042,c_1469])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_2(X1,X0)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1471,plain,
    ( v1_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(X0,X1,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_2(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3450,plain,
    ( v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(k2_funct_2(sK0,sK1)) = iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1466,c_1471])).

cnf(c_3279,plain,
    ( ~ v1_funct_2(sK1,X0,X0)
    | ~ v3_funct_2(sK1,X0,X0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | v1_funct_1(k2_funct_2(X0,sK1))
    | ~ v1_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_3425,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v1_funct_1(k2_funct_2(sK0,sK1))
    | ~ v1_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_3279])).

cnf(c_3426,plain,
    ( v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(k2_funct_2(sK0,sK1)) = iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3425])).

cnf(c_3748,plain,
    ( v1_funct_1(k2_funct_2(sK0,sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3450,c_36,c_37,c_38,c_39,c_3426])).

cnf(c_5055,plain,
    ( v1_funct_1(k2_funct_1(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5051,c_3748])).

cnf(c_8675,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7058,c_5055])).

cnf(c_8676,plain,
    ( k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_8675])).

cnf(c_8684,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k5_relat_1(sK1,k2_funct_1(sK1))
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1466,c_8676])).

cnf(c_14,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1481,plain,
    ( v3_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4462,plain,
    ( v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v2_funct_1(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1466,c_1481])).

cnf(c_5044,plain,
    ( v2_funct_1(sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4462,c_36,c_38])).

cnf(c_1463,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_8,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1485,plain,
    ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2888,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
    | v2_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1463,c_1485])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1484,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1830,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1466,c_1484])).

cnf(c_3027,plain,
    ( v2_funct_1(sK1) != iProver_top
    | k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2888,c_1830])).

cnf(c_3028,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
    | v2_funct_1(sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_3027])).

cnf(c_5049,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
    inference(superposition,[status(thm)],[c_5044,c_3028])).

cnf(c_8689,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
    | v1_funct_1(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8684,c_5049])).

cnf(c_8711,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8689,c_36])).

cnf(c_5999,plain,
    ( k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1466,c_1469])).

cnf(c_6182,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5999,c_36])).

cnf(c_6183,plain,
    ( k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_6182])).

cnf(c_6189,plain,
    ( k1_partfun1(X0,X0,sK0,sK0,k2_funct_2(X0,X1),sK1) = k5_relat_1(k2_funct_2(X0,X1),sK1)
    | v1_funct_2(X1,X0,X0) != iProver_top
    | v3_funct_2(X1,X0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(k2_funct_2(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1474,c_6183])).

cnf(c_7178,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1) = k5_relat_1(k2_funct_2(sK0,sK1),sK1)
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(k2_funct_2(sK0,sK1)) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1466,c_6189])).

cnf(c_7,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1486,plain,
    ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3471,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1))
    | v2_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1463,c_1486])).

cnf(c_13,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | v2_funct_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_23,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_473,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ v5_relat_1(X3,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X3)
    | X3 != X0
    | X4 != X2
    | k2_relat_1(X3) = X4 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_23])).

cnf(c_474,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ v5_relat_1(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(unflattening,[status(thm)],[c_473])).

cnf(c_478,plain,
    ( ~ v1_funct_1(X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v5_relat_1(X0,X2)
    | ~ v3_funct_2(X0,X1,X2)
    | k2_relat_1(X0) = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_474,c_9])).

cnf(c_479,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ v5_relat_1(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(renaming,[status(thm)],[c_478])).

cnf(c_10,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_494,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_479,c_10])).

cnf(c_1462,plain,
    ( k2_relat_1(X0) = X1
    | v3_funct_2(X0,X2,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_494])).

cnf(c_2700,plain,
    ( k2_relat_1(sK1) = sK0
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1466,c_1462])).

cnf(c_3020,plain,
    ( k2_relat_1(sK1) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2700,c_36,c_38])).

cnf(c_3472,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
    | v2_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3471,c_3020])).

cnf(c_3757,plain,
    ( v2_funct_1(sK1) != iProver_top
    | k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3472,c_1830])).

cnf(c_3758,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
    | v2_funct_1(sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_3757])).

cnf(c_5048,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(sK0) ),
    inference(superposition,[status(thm)],[c_5044,c_3758])).

cnf(c_7183,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7178,c_5048,c_5051])).

cnf(c_7046,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k5_relat_1(k2_funct_1(sK1),sK1)
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7042,c_6183])).

cnf(c_7060,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7046,c_5048])).

cnf(c_7205,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7183,c_5055,c_7060])).

cnf(c_31,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1467,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) != iProver_top
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_5056,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) != iProver_top
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5051,c_1467])).

cnf(c_7207,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top
    | r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7205,c_5056])).

cnf(c_12,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1546,plain,
    ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1589,plain,
    ( r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_1546])).

cnf(c_1590,plain,
    ( r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) = iProver_top
    | m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1589])).

cnf(c_28,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1667,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_1668,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1667])).

cnf(c_7247,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7207,c_39,c_1590,c_1668])).

cnf(c_8713,plain,
    ( r2_relset_1(sK0,sK0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8711,c_7247])).

cnf(c_8778,plain,
    ( sK0 = k1_xboole_0
    | r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4038,c_8713])).

cnf(c_8781,plain,
    ( sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8778,c_39,c_1590,c_1668])).

cnf(c_8783,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8781,c_8713])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1488,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3024,plain,
    ( sK1 = k1_xboole_0
    | sK0 != k1_xboole_0
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3020,c_1488])).

cnf(c_3126,plain,
    ( sK0 != k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3024,c_1830])).

cnf(c_3127,plain,
    ( sK1 = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_3126])).

cnf(c_8809,plain,
    ( sK1 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8781,c_3127])).

cnf(c_8816,plain,
    ( sK1 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_8809])).

cnf(c_8784,plain,
    ( k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
    inference(demodulation,[status(thm)],[c_8781,c_8711])).

cnf(c_7053,plain,
    ( k2_relat_1(k2_funct_1(sK1)) = sK0
    | v3_funct_2(k2_funct_1(sK1),sK0,sK0) != iProver_top
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7042,c_1462])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | v3_funct_2(k2_funct_2(X1,X0),X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1473,plain,
    ( v1_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(k2_funct_2(X1,X0),X1,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_4867,plain,
    ( v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0) = iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1466,c_1473])).

cnf(c_5267,plain,
    ( v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4867,c_36,c_37,c_38])).

cnf(c_5271,plain,
    ( v3_funct_2(k2_funct_1(sK1),sK0,sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5267,c_5051])).

cnf(c_7759,plain,
    ( k2_relat_1(k2_funct_1(sK1)) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7053,c_5055,c_5271])).

cnf(c_7763,plain,
    ( k2_funct_1(sK1) = k1_xboole_0
    | sK0 != k1_xboole_0
    | v1_relat_1(k2_funct_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7759,c_1488])).

cnf(c_7052,plain,
    ( v1_relat_1(k2_funct_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7042,c_1484])).

cnf(c_8080,plain,
    ( sK0 != k1_xboole_0
    | k2_funct_1(sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7763,c_7052])).

cnf(c_8081,plain,
    ( k2_funct_1(sK1) = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_8080])).

cnf(c_8787,plain,
    ( k2_funct_1(sK1) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8781,c_8081])).

cnf(c_8842,plain,
    ( k2_funct_1(sK1) = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_8787])).

cnf(c_8843,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8842,c_8816])).

cnf(c_8803,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_8781,c_5048])).

cnf(c_8826,plain,
    ( k5_relat_1(k2_funct_1(k1_xboole_0),k1_xboole_0) = k6_partfun1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_8803,c_8816])).

cnf(c_8851,plain,
    ( k5_relat_1(k1_xboole_0,k1_xboole_0) = k6_partfun1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_8843,c_8826])).

cnf(c_6191,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK1) = k5_relat_1(sK1,sK1)
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1466,c_6183])).

cnf(c_6316,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK1) = k5_relat_1(sK1,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6191,c_36])).

cnf(c_8801,plain,
    ( k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK1,sK1) = k5_relat_1(sK1,sK1) ),
    inference(demodulation,[status(thm)],[c_8781,c_6316])).

cnf(c_8828,plain,
    ( k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k5_relat_1(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_8801,c_8816])).

cnf(c_8856,plain,
    ( k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k6_partfun1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_8851,c_8828])).

cnf(c_8859,plain,
    ( k6_partfun1(k1_relat_1(k1_xboole_0)) = k6_partfun1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_8784,c_8816,c_8843,c_8856])).

cnf(c_8860,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),k6_partfun1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8783,c_8816,c_8859])).

cnf(c_0,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1583,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1584,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1583])).

cnf(c_1586,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1584])).

cnf(c_1547,plain,
    ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0)) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1546])).

cnf(c_1549,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),k6_partfun1(k1_xboole_0)) = iProver_top
    | m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1547])).

cnf(c_47,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_49,plain,
    ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_47])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8860,c_1586,c_1549,c_49])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:48:59 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.65/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.65/1.00  
% 3.65/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.65/1.00  
% 3.65/1.00  ------  iProver source info
% 3.65/1.00  
% 3.65/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.65/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.65/1.00  git: non_committed_changes: false
% 3.65/1.00  git: last_make_outside_of_git: false
% 3.65/1.00  
% 3.65/1.00  ------ 
% 3.65/1.00  
% 3.65/1.00  ------ Input Options
% 3.65/1.00  
% 3.65/1.00  --out_options                           all
% 3.65/1.00  --tptp_safe_out                         true
% 3.65/1.00  --problem_path                          ""
% 3.65/1.00  --include_path                          ""
% 3.65/1.00  --clausifier                            res/vclausify_rel
% 3.65/1.00  --clausifier_options                    ""
% 3.65/1.00  --stdin                                 false
% 3.65/1.00  --stats_out                             all
% 3.65/1.00  
% 3.65/1.00  ------ General Options
% 3.65/1.00  
% 3.65/1.00  --fof                                   false
% 3.65/1.00  --time_out_real                         305.
% 3.65/1.00  --time_out_virtual                      -1.
% 3.65/1.00  --symbol_type_check                     false
% 3.65/1.00  --clausify_out                          false
% 3.65/1.00  --sig_cnt_out                           false
% 3.65/1.00  --trig_cnt_out                          false
% 3.65/1.00  --trig_cnt_out_tolerance                1.
% 3.65/1.00  --trig_cnt_out_sk_spl                   false
% 3.65/1.00  --abstr_cl_out                          false
% 3.65/1.00  
% 3.65/1.00  ------ Global Options
% 3.65/1.00  
% 3.65/1.00  --schedule                              default
% 3.65/1.00  --add_important_lit                     false
% 3.65/1.00  --prop_solver_per_cl                    1000
% 3.65/1.00  --min_unsat_core                        false
% 3.65/1.00  --soft_assumptions                      false
% 3.65/1.00  --soft_lemma_size                       3
% 3.65/1.00  --prop_impl_unit_size                   0
% 3.65/1.00  --prop_impl_unit                        []
% 3.65/1.00  --share_sel_clauses                     true
% 3.65/1.00  --reset_solvers                         false
% 3.65/1.00  --bc_imp_inh                            [conj_cone]
% 3.65/1.00  --conj_cone_tolerance                   3.
% 3.65/1.00  --extra_neg_conj                        none
% 3.65/1.00  --large_theory_mode                     true
% 3.65/1.00  --prolific_symb_bound                   200
% 3.65/1.00  --lt_threshold                          2000
% 3.65/1.00  --clause_weak_htbl                      true
% 3.65/1.00  --gc_record_bc_elim                     false
% 3.65/1.00  
% 3.65/1.00  ------ Preprocessing Options
% 3.65/1.00  
% 3.65/1.00  --preprocessing_flag                    true
% 3.65/1.00  --time_out_prep_mult                    0.1
% 3.65/1.00  --splitting_mode                        input
% 3.65/1.00  --splitting_grd                         true
% 3.65/1.00  --splitting_cvd                         false
% 3.65/1.00  --splitting_cvd_svl                     false
% 3.65/1.00  --splitting_nvd                         32
% 3.65/1.00  --sub_typing                            true
% 3.65/1.00  --prep_gs_sim                           true
% 3.65/1.00  --prep_unflatten                        true
% 3.65/1.00  --prep_res_sim                          true
% 3.65/1.00  --prep_upred                            true
% 3.65/1.00  --prep_sem_filter                       exhaustive
% 3.65/1.00  --prep_sem_filter_out                   false
% 3.65/1.00  --pred_elim                             true
% 3.65/1.00  --res_sim_input                         true
% 3.65/1.00  --eq_ax_congr_red                       true
% 3.65/1.00  --pure_diseq_elim                       true
% 3.65/1.00  --brand_transform                       false
% 3.65/1.00  --non_eq_to_eq                          false
% 3.65/1.00  --prep_def_merge                        true
% 3.65/1.00  --prep_def_merge_prop_impl              false
% 3.65/1.00  --prep_def_merge_mbd                    true
% 3.65/1.00  --prep_def_merge_tr_red                 false
% 3.65/1.00  --prep_def_merge_tr_cl                  false
% 3.65/1.00  --smt_preprocessing                     true
% 3.65/1.00  --smt_ac_axioms                         fast
% 3.65/1.00  --preprocessed_out                      false
% 3.65/1.00  --preprocessed_stats                    false
% 3.65/1.00  
% 3.65/1.00  ------ Abstraction refinement Options
% 3.65/1.00  
% 3.65/1.00  --abstr_ref                             []
% 3.65/1.00  --abstr_ref_prep                        false
% 3.65/1.00  --abstr_ref_until_sat                   false
% 3.65/1.00  --abstr_ref_sig_restrict                funpre
% 3.65/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.65/1.00  --abstr_ref_under                       []
% 3.65/1.00  
% 3.65/1.00  ------ SAT Options
% 3.65/1.00  
% 3.65/1.00  --sat_mode                              false
% 3.65/1.00  --sat_fm_restart_options                ""
% 3.65/1.00  --sat_gr_def                            false
% 3.65/1.00  --sat_epr_types                         true
% 3.65/1.00  --sat_non_cyclic_types                  false
% 3.65/1.00  --sat_finite_models                     false
% 3.65/1.00  --sat_fm_lemmas                         false
% 3.65/1.00  --sat_fm_prep                           false
% 3.65/1.00  --sat_fm_uc_incr                        true
% 3.65/1.00  --sat_out_model                         small
% 3.65/1.00  --sat_out_clauses                       false
% 3.65/1.00  
% 3.65/1.00  ------ QBF Options
% 3.65/1.00  
% 3.65/1.00  --qbf_mode                              false
% 3.65/1.00  --qbf_elim_univ                         false
% 3.65/1.00  --qbf_dom_inst                          none
% 3.65/1.00  --qbf_dom_pre_inst                      false
% 3.65/1.00  --qbf_sk_in                             false
% 3.65/1.00  --qbf_pred_elim                         true
% 3.65/1.00  --qbf_split                             512
% 3.65/1.00  
% 3.65/1.00  ------ BMC1 Options
% 3.65/1.00  
% 3.65/1.00  --bmc1_incremental                      false
% 3.65/1.00  --bmc1_axioms                           reachable_all
% 3.65/1.00  --bmc1_min_bound                        0
% 3.65/1.00  --bmc1_max_bound                        -1
% 3.65/1.00  --bmc1_max_bound_default                -1
% 3.65/1.00  --bmc1_symbol_reachability              true
% 3.65/1.00  --bmc1_property_lemmas                  false
% 3.65/1.00  --bmc1_k_induction                      false
% 3.65/1.00  --bmc1_non_equiv_states                 false
% 3.65/1.00  --bmc1_deadlock                         false
% 3.65/1.00  --bmc1_ucm                              false
% 3.65/1.00  --bmc1_add_unsat_core                   none
% 3.65/1.00  --bmc1_unsat_core_children              false
% 3.65/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.65/1.00  --bmc1_out_stat                         full
% 3.65/1.00  --bmc1_ground_init                      false
% 3.65/1.00  --bmc1_pre_inst_next_state              false
% 3.65/1.00  --bmc1_pre_inst_state                   false
% 3.65/1.00  --bmc1_pre_inst_reach_state             false
% 3.65/1.00  --bmc1_out_unsat_core                   false
% 3.65/1.00  --bmc1_aig_witness_out                  false
% 3.65/1.00  --bmc1_verbose                          false
% 3.65/1.00  --bmc1_dump_clauses_tptp                false
% 3.65/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.65/1.00  --bmc1_dump_file                        -
% 3.65/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.65/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.65/1.00  --bmc1_ucm_extend_mode                  1
% 3.65/1.00  --bmc1_ucm_init_mode                    2
% 3.65/1.00  --bmc1_ucm_cone_mode                    none
% 3.65/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.65/1.00  --bmc1_ucm_relax_model                  4
% 3.65/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.65/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.65/1.00  --bmc1_ucm_layered_model                none
% 3.65/1.00  --bmc1_ucm_max_lemma_size               10
% 3.65/1.00  
% 3.65/1.00  ------ AIG Options
% 3.65/1.00  
% 3.65/1.00  --aig_mode                              false
% 3.65/1.00  
% 3.65/1.00  ------ Instantiation Options
% 3.65/1.00  
% 3.65/1.00  --instantiation_flag                    true
% 3.65/1.00  --inst_sos_flag                         true
% 3.65/1.00  --inst_sos_phase                        true
% 3.65/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.65/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.65/1.00  --inst_lit_sel_side                     num_symb
% 3.65/1.00  --inst_solver_per_active                1400
% 3.65/1.00  --inst_solver_calls_frac                1.
% 3.65/1.00  --inst_passive_queue_type               priority_queues
% 3.65/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.65/1.00  --inst_passive_queues_freq              [25;2]
% 3.65/1.00  --inst_dismatching                      true
% 3.65/1.00  --inst_eager_unprocessed_to_passive     true
% 3.65/1.00  --inst_prop_sim_given                   true
% 3.65/1.00  --inst_prop_sim_new                     false
% 3.65/1.00  --inst_subs_new                         false
% 3.65/1.00  --inst_eq_res_simp                      false
% 3.65/1.00  --inst_subs_given                       false
% 3.65/1.00  --inst_orphan_elimination               true
% 3.65/1.00  --inst_learning_loop_flag               true
% 3.65/1.00  --inst_learning_start                   3000
% 3.65/1.00  --inst_learning_factor                  2
% 3.65/1.00  --inst_start_prop_sim_after_learn       3
% 3.65/1.00  --inst_sel_renew                        solver
% 3.65/1.00  --inst_lit_activity_flag                true
% 3.65/1.00  --inst_restr_to_given                   false
% 3.65/1.00  --inst_activity_threshold               500
% 3.65/1.00  --inst_out_proof                        true
% 3.65/1.00  
% 3.65/1.00  ------ Resolution Options
% 3.65/1.00  
% 3.65/1.00  --resolution_flag                       true
% 3.65/1.00  --res_lit_sel                           adaptive
% 3.65/1.00  --res_lit_sel_side                      none
% 3.65/1.00  --res_ordering                          kbo
% 3.65/1.00  --res_to_prop_solver                    active
% 3.65/1.00  --res_prop_simpl_new                    false
% 3.65/1.00  --res_prop_simpl_given                  true
% 3.65/1.00  --res_passive_queue_type                priority_queues
% 3.65/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.65/1.00  --res_passive_queues_freq               [15;5]
% 3.65/1.00  --res_forward_subs                      full
% 3.65/1.00  --res_backward_subs                     full
% 3.65/1.00  --res_forward_subs_resolution           true
% 3.65/1.00  --res_backward_subs_resolution          true
% 3.65/1.00  --res_orphan_elimination                true
% 3.65/1.00  --res_time_limit                        2.
% 3.65/1.00  --res_out_proof                         true
% 3.65/1.00  
% 3.65/1.00  ------ Superposition Options
% 3.65/1.00  
% 3.65/1.00  --superposition_flag                    true
% 3.65/1.00  --sup_passive_queue_type                priority_queues
% 3.65/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.65/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.65/1.00  --demod_completeness_check              fast
% 3.65/1.00  --demod_use_ground                      true
% 3.65/1.00  --sup_to_prop_solver                    passive
% 3.65/1.00  --sup_prop_simpl_new                    true
% 3.65/1.00  --sup_prop_simpl_given                  true
% 3.65/1.00  --sup_fun_splitting                     true
% 3.65/1.00  --sup_smt_interval                      50000
% 3.65/1.00  
% 3.65/1.00  ------ Superposition Simplification Setup
% 3.65/1.00  
% 3.65/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.65/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.65/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.65/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.65/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.65/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.65/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.65/1.00  --sup_immed_triv                        [TrivRules]
% 3.65/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.65/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.65/1.00  --sup_immed_bw_main                     []
% 3.65/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.65/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.65/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.65/1.00  --sup_input_bw                          []
% 3.65/1.00  
% 3.65/1.00  ------ Combination Options
% 3.65/1.00  
% 3.65/1.00  --comb_res_mult                         3
% 3.65/1.00  --comb_sup_mult                         2
% 3.65/1.00  --comb_inst_mult                        10
% 3.65/1.00  
% 3.65/1.00  ------ Debug Options
% 3.65/1.00  
% 3.65/1.00  --dbg_backtrace                         false
% 3.65/1.00  --dbg_dump_prop_clauses                 false
% 3.65/1.00  --dbg_dump_prop_clauses_file            -
% 3.65/1.00  --dbg_out_stat                          false
% 3.65/1.00  ------ Parsing...
% 3.65/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.65/1.00  
% 3.65/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.65/1.00  
% 3.65/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.65/1.00  
% 3.65/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.65/1.00  ------ Proving...
% 3.65/1.00  ------ Problem Properties 
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  clauses                                 29
% 3.65/1.00  conjectures                             5
% 3.65/1.00  EPR                                     3
% 3.65/1.00  Horn                                    25
% 3.65/1.00  unary                                   6
% 3.65/1.00  binary                                  4
% 3.65/1.00  lits                                    90
% 3.65/1.00  lits eq                                 19
% 3.65/1.00  fd_pure                                 0
% 3.65/1.00  fd_pseudo                               0
% 3.65/1.00  fd_cond                                 5
% 3.65/1.00  fd_pseudo_cond                          1
% 3.65/1.00  AC symbols                              0
% 3.65/1.00  
% 3.65/1.00  ------ Schedule dynamic 5 is on 
% 3.65/1.00  
% 3.65/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  ------ 
% 3.65/1.00  Current options:
% 3.65/1.00  ------ 
% 3.65/1.00  
% 3.65/1.00  ------ Input Options
% 3.65/1.00  
% 3.65/1.00  --out_options                           all
% 3.65/1.00  --tptp_safe_out                         true
% 3.65/1.00  --problem_path                          ""
% 3.65/1.00  --include_path                          ""
% 3.65/1.00  --clausifier                            res/vclausify_rel
% 3.65/1.00  --clausifier_options                    ""
% 3.65/1.00  --stdin                                 false
% 3.65/1.00  --stats_out                             all
% 3.65/1.00  
% 3.65/1.00  ------ General Options
% 3.65/1.00  
% 3.65/1.00  --fof                                   false
% 3.65/1.00  --time_out_real                         305.
% 3.65/1.00  --time_out_virtual                      -1.
% 3.65/1.00  --symbol_type_check                     false
% 3.65/1.00  --clausify_out                          false
% 3.65/1.00  --sig_cnt_out                           false
% 3.65/1.00  --trig_cnt_out                          false
% 3.65/1.00  --trig_cnt_out_tolerance                1.
% 3.65/1.00  --trig_cnt_out_sk_spl                   false
% 3.65/1.00  --abstr_cl_out                          false
% 3.65/1.00  
% 3.65/1.00  ------ Global Options
% 3.65/1.00  
% 3.65/1.00  --schedule                              default
% 3.65/1.00  --add_important_lit                     false
% 3.65/1.00  --prop_solver_per_cl                    1000
% 3.65/1.00  --min_unsat_core                        false
% 3.65/1.00  --soft_assumptions                      false
% 3.65/1.00  --soft_lemma_size                       3
% 3.65/1.00  --prop_impl_unit_size                   0
% 3.65/1.00  --prop_impl_unit                        []
% 3.65/1.00  --share_sel_clauses                     true
% 3.65/1.00  --reset_solvers                         false
% 3.65/1.00  --bc_imp_inh                            [conj_cone]
% 3.65/1.00  --conj_cone_tolerance                   3.
% 3.65/1.00  --extra_neg_conj                        none
% 3.65/1.00  --large_theory_mode                     true
% 3.65/1.00  --prolific_symb_bound                   200
% 3.65/1.00  --lt_threshold                          2000
% 3.65/1.00  --clause_weak_htbl                      true
% 3.65/1.00  --gc_record_bc_elim                     false
% 3.65/1.00  
% 3.65/1.00  ------ Preprocessing Options
% 3.65/1.00  
% 3.65/1.00  --preprocessing_flag                    true
% 3.65/1.00  --time_out_prep_mult                    0.1
% 3.65/1.00  --splitting_mode                        input
% 3.65/1.00  --splitting_grd                         true
% 3.65/1.00  --splitting_cvd                         false
% 3.65/1.00  --splitting_cvd_svl                     false
% 3.65/1.00  --splitting_nvd                         32
% 3.65/1.00  --sub_typing                            true
% 3.65/1.00  --prep_gs_sim                           true
% 3.65/1.00  --prep_unflatten                        true
% 3.65/1.00  --prep_res_sim                          true
% 3.65/1.00  --prep_upred                            true
% 3.65/1.00  --prep_sem_filter                       exhaustive
% 3.65/1.00  --prep_sem_filter_out                   false
% 3.65/1.00  --pred_elim                             true
% 3.65/1.00  --res_sim_input                         true
% 3.65/1.00  --eq_ax_congr_red                       true
% 3.65/1.00  --pure_diseq_elim                       true
% 3.65/1.00  --brand_transform                       false
% 3.65/1.00  --non_eq_to_eq                          false
% 3.65/1.00  --prep_def_merge                        true
% 3.65/1.00  --prep_def_merge_prop_impl              false
% 3.65/1.00  --prep_def_merge_mbd                    true
% 3.65/1.00  --prep_def_merge_tr_red                 false
% 3.65/1.00  --prep_def_merge_tr_cl                  false
% 3.65/1.00  --smt_preprocessing                     true
% 3.65/1.00  --smt_ac_axioms                         fast
% 3.65/1.00  --preprocessed_out                      false
% 3.65/1.00  --preprocessed_stats                    false
% 3.65/1.00  
% 3.65/1.00  ------ Abstraction refinement Options
% 3.65/1.00  
% 3.65/1.00  --abstr_ref                             []
% 3.65/1.00  --abstr_ref_prep                        false
% 3.65/1.00  --abstr_ref_until_sat                   false
% 3.65/1.00  --abstr_ref_sig_restrict                funpre
% 3.65/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.65/1.00  --abstr_ref_under                       []
% 3.65/1.00  
% 3.65/1.00  ------ SAT Options
% 3.65/1.00  
% 3.65/1.00  --sat_mode                              false
% 3.65/1.00  --sat_fm_restart_options                ""
% 3.65/1.00  --sat_gr_def                            false
% 3.65/1.00  --sat_epr_types                         true
% 3.65/1.00  --sat_non_cyclic_types                  false
% 3.65/1.00  --sat_finite_models                     false
% 3.65/1.00  --sat_fm_lemmas                         false
% 3.65/1.00  --sat_fm_prep                           false
% 3.65/1.00  --sat_fm_uc_incr                        true
% 3.65/1.00  --sat_out_model                         small
% 3.65/1.00  --sat_out_clauses                       false
% 3.65/1.00  
% 3.65/1.00  ------ QBF Options
% 3.65/1.00  
% 3.65/1.00  --qbf_mode                              false
% 3.65/1.00  --qbf_elim_univ                         false
% 3.65/1.00  --qbf_dom_inst                          none
% 3.65/1.00  --qbf_dom_pre_inst                      false
% 3.65/1.00  --qbf_sk_in                             false
% 3.65/1.00  --qbf_pred_elim                         true
% 3.65/1.00  --qbf_split                             512
% 3.65/1.00  
% 3.65/1.00  ------ BMC1 Options
% 3.65/1.00  
% 3.65/1.00  --bmc1_incremental                      false
% 3.65/1.00  --bmc1_axioms                           reachable_all
% 3.65/1.00  --bmc1_min_bound                        0
% 3.65/1.00  --bmc1_max_bound                        -1
% 3.65/1.00  --bmc1_max_bound_default                -1
% 3.65/1.00  --bmc1_symbol_reachability              true
% 3.65/1.00  --bmc1_property_lemmas                  false
% 3.65/1.00  --bmc1_k_induction                      false
% 3.65/1.00  --bmc1_non_equiv_states                 false
% 3.65/1.00  --bmc1_deadlock                         false
% 3.65/1.00  --bmc1_ucm                              false
% 3.65/1.00  --bmc1_add_unsat_core                   none
% 3.65/1.00  --bmc1_unsat_core_children              false
% 3.65/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.65/1.00  --bmc1_out_stat                         full
% 3.65/1.00  --bmc1_ground_init                      false
% 3.65/1.00  --bmc1_pre_inst_next_state              false
% 3.65/1.00  --bmc1_pre_inst_state                   false
% 3.65/1.00  --bmc1_pre_inst_reach_state             false
% 3.65/1.00  --bmc1_out_unsat_core                   false
% 3.65/1.00  --bmc1_aig_witness_out                  false
% 3.65/1.00  --bmc1_verbose                          false
% 3.65/1.00  --bmc1_dump_clauses_tptp                false
% 3.65/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.65/1.00  --bmc1_dump_file                        -
% 3.65/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.65/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.65/1.00  --bmc1_ucm_extend_mode                  1
% 3.65/1.00  --bmc1_ucm_init_mode                    2
% 3.65/1.00  --bmc1_ucm_cone_mode                    none
% 3.65/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.65/1.00  --bmc1_ucm_relax_model                  4
% 3.65/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.65/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.65/1.00  --bmc1_ucm_layered_model                none
% 3.65/1.00  --bmc1_ucm_max_lemma_size               10
% 3.65/1.00  
% 3.65/1.00  ------ AIG Options
% 3.65/1.00  
% 3.65/1.00  --aig_mode                              false
% 3.65/1.00  
% 3.65/1.00  ------ Instantiation Options
% 3.65/1.00  
% 3.65/1.00  --instantiation_flag                    true
% 3.65/1.00  --inst_sos_flag                         true
% 3.65/1.00  --inst_sos_phase                        true
% 3.65/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.65/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.65/1.00  --inst_lit_sel_side                     none
% 3.65/1.00  --inst_solver_per_active                1400
% 3.65/1.00  --inst_solver_calls_frac                1.
% 3.65/1.00  --inst_passive_queue_type               priority_queues
% 3.65/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.65/1.00  --inst_passive_queues_freq              [25;2]
% 3.65/1.00  --inst_dismatching                      true
% 3.65/1.00  --inst_eager_unprocessed_to_passive     true
% 3.65/1.00  --inst_prop_sim_given                   true
% 3.65/1.00  --inst_prop_sim_new                     false
% 3.65/1.00  --inst_subs_new                         false
% 3.65/1.00  --inst_eq_res_simp                      false
% 3.65/1.00  --inst_subs_given                       false
% 3.65/1.00  --inst_orphan_elimination               true
% 3.65/1.00  --inst_learning_loop_flag               true
% 3.65/1.00  --inst_learning_start                   3000
% 3.65/1.00  --inst_learning_factor                  2
% 3.65/1.00  --inst_start_prop_sim_after_learn       3
% 3.65/1.00  --inst_sel_renew                        solver
% 3.65/1.00  --inst_lit_activity_flag                true
% 3.65/1.00  --inst_restr_to_given                   false
% 3.65/1.00  --inst_activity_threshold               500
% 3.65/1.00  --inst_out_proof                        true
% 3.65/1.00  
% 3.65/1.00  ------ Resolution Options
% 3.65/1.00  
% 3.65/1.00  --resolution_flag                       false
% 3.65/1.00  --res_lit_sel                           adaptive
% 3.65/1.00  --res_lit_sel_side                      none
% 3.65/1.00  --res_ordering                          kbo
% 3.65/1.00  --res_to_prop_solver                    active
% 3.65/1.00  --res_prop_simpl_new                    false
% 3.65/1.00  --res_prop_simpl_given                  true
% 3.65/1.00  --res_passive_queue_type                priority_queues
% 3.65/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.65/1.00  --res_passive_queues_freq               [15;5]
% 3.65/1.00  --res_forward_subs                      full
% 3.65/1.00  --res_backward_subs                     full
% 3.65/1.00  --res_forward_subs_resolution           true
% 3.65/1.00  --res_backward_subs_resolution          true
% 3.65/1.00  --res_orphan_elimination                true
% 3.65/1.00  --res_time_limit                        2.
% 3.65/1.00  --res_out_proof                         true
% 3.65/1.00  
% 3.65/1.00  ------ Superposition Options
% 3.65/1.00  
% 3.65/1.00  --superposition_flag                    true
% 3.65/1.00  --sup_passive_queue_type                priority_queues
% 3.65/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.65/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.65/1.00  --demod_completeness_check              fast
% 3.65/1.00  --demod_use_ground                      true
% 3.65/1.00  --sup_to_prop_solver                    passive
% 3.65/1.00  --sup_prop_simpl_new                    true
% 3.65/1.00  --sup_prop_simpl_given                  true
% 3.65/1.00  --sup_fun_splitting                     true
% 3.65/1.00  --sup_smt_interval                      50000
% 3.65/1.00  
% 3.65/1.00  ------ Superposition Simplification Setup
% 3.65/1.00  
% 3.65/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.65/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.65/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.65/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.65/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.65/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.65/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.65/1.00  --sup_immed_triv                        [TrivRules]
% 3.65/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.65/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.65/1.00  --sup_immed_bw_main                     []
% 3.65/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.65/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.65/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.65/1.00  --sup_input_bw                          []
% 3.65/1.00  
% 3.65/1.00  ------ Combination Options
% 3.65/1.00  
% 3.65/1.00  --comb_res_mult                         3
% 3.65/1.00  --comb_sup_mult                         2
% 3.65/1.00  --comb_inst_mult                        10
% 3.65/1.00  
% 3.65/1.00  ------ Debug Options
% 3.65/1.00  
% 3.65/1.00  --dbg_backtrace                         false
% 3.65/1.00  --dbg_dump_prop_clauses                 false
% 3.65/1.00  --dbg_dump_prop_clauses_file            -
% 3.65/1.00  --dbg_out_stat                          false
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  ------ Proving...
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  % SZS status Theorem for theBenchmark.p
% 3.65/1.00  
% 3.65/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.65/1.00  
% 3.65/1.00  fof(f19,conjecture,(
% 3.65/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 3.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/1.00  
% 3.65/1.00  fof(f20,negated_conjecture,(
% 3.65/1.00    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 3.65/1.00    inference(negated_conjecture,[],[f19])).
% 3.65/1.00  
% 3.65/1.00  fof(f46,plain,(
% 3.65/1.00    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 3.65/1.00    inference(ennf_transformation,[],[f20])).
% 3.65/1.00  
% 3.65/1.00  fof(f47,plain,(
% 3.65/1.00    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 3.65/1.00    inference(flattening,[],[f46])).
% 3.65/1.00  
% 3.65/1.00  fof(f52,plain,(
% 3.65/1.00    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 3.65/1.00    introduced(choice_axiom,[])).
% 3.65/1.00  
% 3.65/1.00  fof(f53,plain,(
% 3.65/1.00    (~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 3.65/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f47,f52])).
% 3.65/1.00  
% 3.65/1.00  fof(f89,plain,(
% 3.65/1.00    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.65/1.00    inference(cnf_transformation,[],[f53])).
% 3.65/1.00  
% 3.65/1.00  fof(f12,axiom,(
% 3.65/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/1.00  
% 3.65/1.00  fof(f36,plain,(
% 3.65/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.65/1.00    inference(ennf_transformation,[],[f12])).
% 3.65/1.00  
% 3.65/1.00  fof(f37,plain,(
% 3.65/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.65/1.00    inference(flattening,[],[f36])).
% 3.65/1.00  
% 3.65/1.00  fof(f50,plain,(
% 3.65/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.65/1.00    inference(nnf_transformation,[],[f37])).
% 3.65/1.00  
% 3.65/1.00  fof(f70,plain,(
% 3.65/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.65/1.00    inference(cnf_transformation,[],[f50])).
% 3.65/1.00  
% 3.65/1.00  fof(f9,axiom,(
% 3.65/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/1.00  
% 3.65/1.00  fof(f31,plain,(
% 3.65/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.65/1.00    inference(ennf_transformation,[],[f9])).
% 3.65/1.00  
% 3.65/1.00  fof(f65,plain,(
% 3.65/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.65/1.00    inference(cnf_transformation,[],[f31])).
% 3.65/1.00  
% 3.65/1.00  fof(f87,plain,(
% 3.65/1.00    v1_funct_2(sK1,sK0,sK0)),
% 3.65/1.00    inference(cnf_transformation,[],[f53])).
% 3.65/1.00  
% 3.65/1.00  fof(f17,axiom,(
% 3.65/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_1(X1) = k2_funct_2(X0,X1))),
% 3.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/1.00  
% 3.65/1.00  fof(f44,plain,(
% 3.65/1.00    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.65/1.00    inference(ennf_transformation,[],[f17])).
% 3.65/1.00  
% 3.65/1.00  fof(f45,plain,(
% 3.65/1.00    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.65/1.00    inference(flattening,[],[f44])).
% 3.65/1.00  
% 3.65/1.00  fof(f84,plain,(
% 3.65/1.00    ( ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.65/1.00    inference(cnf_transformation,[],[f45])).
% 3.65/1.00  
% 3.65/1.00  fof(f86,plain,(
% 3.65/1.00    v1_funct_1(sK1)),
% 3.65/1.00    inference(cnf_transformation,[],[f53])).
% 3.65/1.00  
% 3.65/1.00  fof(f88,plain,(
% 3.65/1.00    v3_funct_2(sK1,sK0,sK0)),
% 3.65/1.00    inference(cnf_transformation,[],[f53])).
% 3.65/1.00  
% 3.65/1.00  fof(f14,axiom,(
% 3.65/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 3.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/1.00  
% 3.65/1.00  fof(f40,plain,(
% 3.65/1.00    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.65/1.00    inference(ennf_transformation,[],[f14])).
% 3.65/1.00  
% 3.65/1.00  fof(f41,plain,(
% 3.65/1.00    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.65/1.00    inference(flattening,[],[f40])).
% 3.65/1.00  
% 3.65/1.00  fof(f81,plain,(
% 3.65/1.00    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.65/1.00    inference(cnf_transformation,[],[f41])).
% 3.65/1.00  
% 3.65/1.00  fof(f16,axiom,(
% 3.65/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/1.00  
% 3.65/1.00  fof(f42,plain,(
% 3.65/1.00    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.65/1.00    inference(ennf_transformation,[],[f16])).
% 3.65/1.00  
% 3.65/1.00  fof(f43,plain,(
% 3.65/1.00    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.65/1.00    inference(flattening,[],[f42])).
% 3.65/1.00  
% 3.65/1.00  fof(f83,plain,(
% 3.65/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.65/1.00    inference(cnf_transformation,[],[f43])).
% 3.65/1.00  
% 3.65/1.00  fof(f78,plain,(
% 3.65/1.00    ( ! [X0,X1] : (v1_funct_1(k2_funct_2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.65/1.00    inference(cnf_transformation,[],[f41])).
% 3.65/1.00  
% 3.65/1.00  fof(f11,axiom,(
% 3.65/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 3.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/1.00  
% 3.65/1.00  fof(f34,plain,(
% 3.65/1.00    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.65/1.00    inference(ennf_transformation,[],[f11])).
% 3.65/1.00  
% 3.65/1.00  fof(f35,plain,(
% 3.65/1.00    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.65/1.00    inference(flattening,[],[f34])).
% 3.65/1.00  
% 3.65/1.00  fof(f68,plain,(
% 3.65/1.00    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.65/1.00    inference(cnf_transformation,[],[f35])).
% 3.65/1.00  
% 3.65/1.00  fof(f6,axiom,(
% 3.65/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 3.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/1.00  
% 3.65/1.00  fof(f27,plain,(
% 3.65/1.00    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.65/1.00    inference(ennf_transformation,[],[f6])).
% 3.65/1.00  
% 3.65/1.00  fof(f28,plain,(
% 3.65/1.00    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.65/1.00    inference(flattening,[],[f27])).
% 3.65/1.00  
% 3.65/1.00  fof(f61,plain,(
% 3.65/1.00    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.65/1.00    inference(cnf_transformation,[],[f28])).
% 3.65/1.00  
% 3.65/1.00  fof(f18,axiom,(
% 3.65/1.00    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/1.00  
% 3.65/1.00  fof(f85,plain,(
% 3.65/1.00    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.65/1.00    inference(cnf_transformation,[],[f18])).
% 3.65/1.00  
% 3.65/1.00  fof(f92,plain,(
% 3.65/1.00    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.65/1.00    inference(definition_unfolding,[],[f61,f85])).
% 3.65/1.00  
% 3.65/1.00  fof(f7,axiom,(
% 3.65/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/1.00  
% 3.65/1.00  fof(f29,plain,(
% 3.65/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.65/1.00    inference(ennf_transformation,[],[f7])).
% 3.65/1.00  
% 3.65/1.00  fof(f63,plain,(
% 3.65/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.65/1.00    inference(cnf_transformation,[],[f29])).
% 3.65/1.00  
% 3.65/1.00  fof(f62,plain,(
% 3.65/1.00    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.65/1.00    inference(cnf_transformation,[],[f28])).
% 3.65/1.00  
% 3.65/1.00  fof(f91,plain,(
% 3.65/1.00    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.65/1.00    inference(definition_unfolding,[],[f62,f85])).
% 3.65/1.00  
% 3.65/1.00  fof(f69,plain,(
% 3.65/1.00    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.65/1.00    inference(cnf_transformation,[],[f35])).
% 3.65/1.00  
% 3.65/1.00  fof(f13,axiom,(
% 3.65/1.00    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 3.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/1.00  
% 3.65/1.00  fof(f38,plain,(
% 3.65/1.00    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.65/1.00    inference(ennf_transformation,[],[f13])).
% 3.65/1.00  
% 3.65/1.00  fof(f39,plain,(
% 3.65/1.00    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.65/1.00    inference(flattening,[],[f38])).
% 3.65/1.00  
% 3.65/1.00  fof(f51,plain,(
% 3.65/1.00    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.65/1.00    inference(nnf_transformation,[],[f39])).
% 3.65/1.00  
% 3.65/1.00  fof(f76,plain,(
% 3.65/1.00    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.65/1.00    inference(cnf_transformation,[],[f51])).
% 3.65/1.00  
% 3.65/1.00  fof(f8,axiom,(
% 3.65/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/1.00  
% 3.65/1.00  fof(f22,plain,(
% 3.65/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.65/1.00    inference(pure_predicate_removal,[],[f8])).
% 3.65/1.00  
% 3.65/1.00  fof(f30,plain,(
% 3.65/1.00    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.65/1.00    inference(ennf_transformation,[],[f22])).
% 3.65/1.00  
% 3.65/1.00  fof(f64,plain,(
% 3.65/1.00    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.65/1.00    inference(cnf_transformation,[],[f30])).
% 3.65/1.00  
% 3.65/1.00  fof(f90,plain,(
% 3.65/1.00    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))),
% 3.65/1.00    inference(cnf_transformation,[],[f53])).
% 3.65/1.00  
% 3.65/1.00  fof(f10,axiom,(
% 3.65/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 3.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/1.00  
% 3.65/1.00  fof(f32,plain,(
% 3.65/1.00    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.65/1.00    inference(ennf_transformation,[],[f10])).
% 3.65/1.00  
% 3.65/1.00  fof(f33,plain,(
% 3.65/1.00    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.65/1.00    inference(flattening,[],[f32])).
% 3.65/1.00  
% 3.65/1.00  fof(f66,plain,(
% 3.65/1.00    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.65/1.00    inference(cnf_transformation,[],[f33])).
% 3.65/1.00  
% 3.65/1.00  fof(f15,axiom,(
% 3.65/1.00    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 3.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/1.00  
% 3.65/1.00  fof(f21,plain,(
% 3.65/1.00    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.65/1.00    inference(pure_predicate_removal,[],[f15])).
% 3.65/1.00  
% 3.65/1.00  fof(f82,plain,(
% 3.65/1.00    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.65/1.00    inference(cnf_transformation,[],[f21])).
% 3.65/1.00  
% 3.65/1.00  fof(f5,axiom,(
% 3.65/1.00    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 3.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/1.00  
% 3.65/1.00  fof(f25,plain,(
% 3.65/1.00    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.65/1.00    inference(ennf_transformation,[],[f5])).
% 3.65/1.00  
% 3.65/1.00  fof(f26,plain,(
% 3.65/1.00    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.65/1.00    inference(flattening,[],[f25])).
% 3.65/1.00  
% 3.65/1.00  fof(f60,plain,(
% 3.65/1.00    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.65/1.00    inference(cnf_transformation,[],[f26])).
% 3.65/1.00  
% 3.65/1.00  fof(f80,plain,(
% 3.65/1.00    ( ! [X0,X1] : (v3_funct_2(k2_funct_2(X0,X1),X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.65/1.00    inference(cnf_transformation,[],[f41])).
% 3.65/1.00  
% 3.65/1.00  fof(f1,axiom,(
% 3.65/1.00    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/1.00  
% 3.65/1.00  fof(f54,plain,(
% 3.65/1.00    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.65/1.00    inference(cnf_transformation,[],[f1])).
% 3.65/1.00  
% 3.65/1.00  cnf(c_32,negated_conjecture,
% 3.65/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.65/1.00      inference(cnf_transformation,[],[f89]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_1466,plain,
% 3.65/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_21,plain,
% 3.65/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.65/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.65/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.65/1.00      | k1_xboole_0 = X2 ),
% 3.65/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_1475,plain,
% 3.65/1.00      ( k1_relset_1(X0,X1,X2) = X0
% 3.65/1.00      | k1_xboole_0 = X1
% 3.65/1.00      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.65/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_3554,plain,
% 3.65/1.00      ( k1_relset_1(sK0,sK0,sK1) = sK0
% 3.65/1.00      | sK0 = k1_xboole_0
% 3.65/1.00      | v1_funct_2(sK1,sK0,sK0) != iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_1466,c_1475]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_11,plain,
% 3.65/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.65/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.65/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_1483,plain,
% 3.65/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.65/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_2077,plain,
% 3.65/1.00      ( k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_1466,c_1483]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_3561,plain,
% 3.65/1.00      ( k1_relat_1(sK1) = sK0
% 3.65/1.00      | sK0 = k1_xboole_0
% 3.65/1.00      | v1_funct_2(sK1,sK0,sK0) != iProver_top ),
% 3.65/1.00      inference(demodulation,[status(thm)],[c_3554,c_2077]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_34,negated_conjecture,
% 3.65/1.00      ( v1_funct_2(sK1,sK0,sK0) ),
% 3.65/1.00      inference(cnf_transformation,[],[f87]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_37,plain,
% 3.65/1.00      ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_4037,plain,
% 3.65/1.00      ( sK0 = k1_xboole_0 | k1_relat_1(sK1) = sK0 ),
% 3.65/1.00      inference(global_propositional_subsumption,
% 3.65/1.00                [status(thm)],
% 3.65/1.00                [c_3561,c_37]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_4038,plain,
% 3.65/1.00      ( k1_relat_1(sK1) = sK0 | sK0 = k1_xboole_0 ),
% 3.65/1.00      inference(renaming,[status(thm)],[c_4037]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_30,plain,
% 3.65/1.00      ( ~ v1_funct_2(X0,X1,X1)
% 3.65/1.00      | ~ v3_funct_2(X0,X1,X1)
% 3.65/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.65/1.00      | ~ v1_funct_1(X0)
% 3.65/1.00      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 3.65/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_1468,plain,
% 3.65/1.00      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
% 3.65/1.00      | v1_funct_2(X1,X0,X0) != iProver_top
% 3.65/1.00      | v3_funct_2(X1,X0,X0) != iProver_top
% 3.65/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 3.65/1.00      | v1_funct_1(X1) != iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_4485,plain,
% 3.65/1.00      ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
% 3.65/1.00      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.65/1.00      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.65/1.00      | v1_funct_1(sK1) != iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_1466,c_1468]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_35,negated_conjecture,
% 3.65/1.00      ( v1_funct_1(sK1) ),
% 3.65/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_36,plain,
% 3.65/1.00      ( v1_funct_1(sK1) = iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_33,negated_conjecture,
% 3.65/1.00      ( v3_funct_2(sK1,sK0,sK0) ),
% 3.65/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_38,plain,
% 3.65/1.00      ( v3_funct_2(sK1,sK0,sK0) = iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_5051,plain,
% 3.65/1.00      ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 3.65/1.00      inference(global_propositional_subsumption,
% 3.65/1.00                [status(thm)],
% 3.65/1.00                [c_4485,c_36,c_37,c_38]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_24,plain,
% 3.65/1.00      ( ~ v1_funct_2(X0,X1,X1)
% 3.65/1.00      | ~ v3_funct_2(X0,X1,X1)
% 3.65/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.65/1.00      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.65/1.00      | ~ v1_funct_1(X0) ),
% 3.65/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_1474,plain,
% 3.65/1.00      ( v1_funct_2(X0,X1,X1) != iProver_top
% 3.65/1.00      | v3_funct_2(X0,X1,X1) != iProver_top
% 3.65/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 3.65/1.00      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) = iProver_top
% 3.65/1.00      | v1_funct_1(X0) != iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_5061,plain,
% 3.65/1.00      ( v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.65/1.00      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.65/1.00      | m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 3.65/1.00      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.65/1.00      | v1_funct_1(sK1) != iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_5051,c_1474]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_39,plain,
% 3.65/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_7042,plain,
% 3.65/1.00      ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.65/1.00      inference(global_propositional_subsumption,
% 3.65/1.00                [status(thm)],
% 3.65/1.00                [c_5061,c_36,c_37,c_38,c_39]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_29,plain,
% 3.65/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.65/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.65/1.00      | ~ v1_funct_1(X0)
% 3.65/1.00      | ~ v1_funct_1(X3)
% 3.65/1.00      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.65/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_1469,plain,
% 3.65/1.00      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 3.65/1.00      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 3.65/1.00      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.65/1.00      | v1_funct_1(X5) != iProver_top
% 3.65/1.00      | v1_funct_1(X4) != iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_7058,plain,
% 3.65/1.00      ( k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1))
% 3.65/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.65/1.00      | v1_funct_1(X2) != iProver_top
% 3.65/1.00      | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_7042,c_1469]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_27,plain,
% 3.65/1.00      ( ~ v1_funct_2(X0,X1,X1)
% 3.65/1.00      | ~ v3_funct_2(X0,X1,X1)
% 3.65/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.65/1.00      | ~ v1_funct_1(X0)
% 3.65/1.00      | v1_funct_1(k2_funct_2(X1,X0)) ),
% 3.65/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_1471,plain,
% 3.65/1.00      ( v1_funct_2(X0,X1,X1) != iProver_top
% 3.65/1.00      | v3_funct_2(X0,X1,X1) != iProver_top
% 3.65/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 3.65/1.00      | v1_funct_1(X0) != iProver_top
% 3.65/1.00      | v1_funct_1(k2_funct_2(X1,X0)) = iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_3450,plain,
% 3.65/1.00      ( v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.65/1.00      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.65/1.00      | v1_funct_1(k2_funct_2(sK0,sK1)) = iProver_top
% 3.65/1.00      | v1_funct_1(sK1) != iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_1466,c_1471]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_3279,plain,
% 3.65/1.00      ( ~ v1_funct_2(sK1,X0,X0)
% 3.65/1.00      | ~ v3_funct_2(sK1,X0,X0)
% 3.65/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 3.65/1.00      | v1_funct_1(k2_funct_2(X0,sK1))
% 3.65/1.00      | ~ v1_funct_1(sK1) ),
% 3.65/1.00      inference(instantiation,[status(thm)],[c_27]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_3425,plain,
% 3.65/1.00      ( ~ v1_funct_2(sK1,sK0,sK0)
% 3.65/1.00      | ~ v3_funct_2(sK1,sK0,sK0)
% 3.65/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.65/1.00      | v1_funct_1(k2_funct_2(sK0,sK1))
% 3.65/1.00      | ~ v1_funct_1(sK1) ),
% 3.65/1.00      inference(instantiation,[status(thm)],[c_3279]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_3426,plain,
% 3.65/1.00      ( v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.65/1.00      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.65/1.00      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.65/1.00      | v1_funct_1(k2_funct_2(sK0,sK1)) = iProver_top
% 3.65/1.00      | v1_funct_1(sK1) != iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_3425]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_3748,plain,
% 3.65/1.00      ( v1_funct_1(k2_funct_2(sK0,sK1)) = iProver_top ),
% 3.65/1.00      inference(global_propositional_subsumption,
% 3.65/1.00                [status(thm)],
% 3.65/1.00                [c_3450,c_36,c_37,c_38,c_39,c_3426]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_5055,plain,
% 3.65/1.00      ( v1_funct_1(k2_funct_1(sK1)) = iProver_top ),
% 3.65/1.00      inference(demodulation,[status(thm)],[c_5051,c_3748]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_8675,plain,
% 3.65/1.00      ( v1_funct_1(X2) != iProver_top
% 3.65/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.65/1.00      | k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1)) ),
% 3.65/1.00      inference(global_propositional_subsumption,
% 3.65/1.00                [status(thm)],
% 3.65/1.00                [c_7058,c_5055]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_8676,plain,
% 3.65/1.00      ( k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1))
% 3.65/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.65/1.00      | v1_funct_1(X2) != iProver_top ),
% 3.65/1.00      inference(renaming,[status(thm)],[c_8675]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_8684,plain,
% 3.65/1.00      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k5_relat_1(sK1,k2_funct_1(sK1))
% 3.65/1.00      | v1_funct_1(sK1) != iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_1466,c_8676]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_14,plain,
% 3.65/1.00      ( ~ v3_funct_2(X0,X1,X2)
% 3.65/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.65/1.00      | ~ v1_funct_1(X0)
% 3.65/1.00      | v2_funct_1(X0) ),
% 3.65/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_1481,plain,
% 3.65/1.00      ( v3_funct_2(X0,X1,X2) != iProver_top
% 3.65/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.65/1.00      | v1_funct_1(X0) != iProver_top
% 3.65/1.00      | v2_funct_1(X0) = iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_4462,plain,
% 3.65/1.00      ( v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.65/1.00      | v1_funct_1(sK1) != iProver_top
% 3.65/1.00      | v2_funct_1(sK1) = iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_1466,c_1481]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_5044,plain,
% 3.65/1.00      ( v2_funct_1(sK1) = iProver_top ),
% 3.65/1.00      inference(global_propositional_subsumption,
% 3.65/1.00                [status(thm)],
% 3.65/1.00                [c_4462,c_36,c_38]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_1463,plain,
% 3.65/1.00      ( v1_funct_1(sK1) = iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_8,plain,
% 3.65/1.00      ( ~ v1_funct_1(X0)
% 3.65/1.00      | ~ v2_funct_1(X0)
% 3.65/1.00      | ~ v1_relat_1(X0)
% 3.65/1.00      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
% 3.65/1.00      inference(cnf_transformation,[],[f92]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_1485,plain,
% 3.65/1.00      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
% 3.65/1.00      | v1_funct_1(X0) != iProver_top
% 3.65/1.00      | v2_funct_1(X0) != iProver_top
% 3.65/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_2888,plain,
% 3.65/1.00      ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
% 3.65/1.00      | v2_funct_1(sK1) != iProver_top
% 3.65/1.00      | v1_relat_1(sK1) != iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_1463,c_1485]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_9,plain,
% 3.65/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.65/1.00      | v1_relat_1(X0) ),
% 3.65/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_1484,plain,
% 3.65/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.65/1.00      | v1_relat_1(X0) = iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_1830,plain,
% 3.65/1.00      ( v1_relat_1(sK1) = iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_1466,c_1484]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_3027,plain,
% 3.65/1.00      ( v2_funct_1(sK1) != iProver_top
% 3.65/1.00      | k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
% 3.65/1.00      inference(global_propositional_subsumption,
% 3.65/1.00                [status(thm)],
% 3.65/1.00                [c_2888,c_1830]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_3028,plain,
% 3.65/1.00      ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
% 3.65/1.00      | v2_funct_1(sK1) != iProver_top ),
% 3.65/1.00      inference(renaming,[status(thm)],[c_3027]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_5049,plain,
% 3.65/1.00      ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_5044,c_3028]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_8689,plain,
% 3.65/1.00      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
% 3.65/1.00      | v1_funct_1(sK1) != iProver_top ),
% 3.65/1.00      inference(light_normalisation,[status(thm)],[c_8684,c_5049]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_8711,plain,
% 3.65/1.00      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
% 3.65/1.00      inference(global_propositional_subsumption,
% 3.65/1.00                [status(thm)],
% 3.65/1.00                [c_8689,c_36]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_5999,plain,
% 3.65/1.00      ( k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1)
% 3.65/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.65/1.00      | v1_funct_1(X2) != iProver_top
% 3.65/1.00      | v1_funct_1(sK1) != iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_1466,c_1469]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_6182,plain,
% 3.65/1.00      ( v1_funct_1(X2) != iProver_top
% 3.65/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.65/1.00      | k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1) ),
% 3.65/1.00      inference(global_propositional_subsumption,
% 3.65/1.00                [status(thm)],
% 3.65/1.00                [c_5999,c_36]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_6183,plain,
% 3.65/1.00      ( k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1)
% 3.65/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.65/1.00      | v1_funct_1(X2) != iProver_top ),
% 3.65/1.00      inference(renaming,[status(thm)],[c_6182]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_6189,plain,
% 3.65/1.00      ( k1_partfun1(X0,X0,sK0,sK0,k2_funct_2(X0,X1),sK1) = k5_relat_1(k2_funct_2(X0,X1),sK1)
% 3.65/1.00      | v1_funct_2(X1,X0,X0) != iProver_top
% 3.65/1.00      | v3_funct_2(X1,X0,X0) != iProver_top
% 3.65/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 3.65/1.00      | v1_funct_1(X1) != iProver_top
% 3.65/1.00      | v1_funct_1(k2_funct_2(X0,X1)) != iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_1474,c_6183]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_7178,plain,
% 3.65/1.00      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1) = k5_relat_1(k2_funct_2(sK0,sK1),sK1)
% 3.65/1.00      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.65/1.00      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.65/1.00      | v1_funct_1(k2_funct_2(sK0,sK1)) != iProver_top
% 3.65/1.00      | v1_funct_1(sK1) != iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_1466,c_6189]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_7,plain,
% 3.65/1.00      ( ~ v1_funct_1(X0)
% 3.65/1.00      | ~ v2_funct_1(X0)
% 3.65/1.00      | ~ v1_relat_1(X0)
% 3.65/1.00      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
% 3.65/1.00      inference(cnf_transformation,[],[f91]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_1486,plain,
% 3.65/1.00      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
% 3.65/1.00      | v1_funct_1(X0) != iProver_top
% 3.65/1.00      | v2_funct_1(X0) != iProver_top
% 3.65/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_3471,plain,
% 3.65/1.00      ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1))
% 3.65/1.00      | v2_funct_1(sK1) != iProver_top
% 3.65/1.00      | v1_relat_1(sK1) != iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_1463,c_1486]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_13,plain,
% 3.65/1.00      ( ~ v3_funct_2(X0,X1,X2)
% 3.65/1.00      | v2_funct_2(X0,X2)
% 3.65/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.65/1.00      | ~ v1_funct_1(X0) ),
% 3.65/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_23,plain,
% 3.65/1.00      ( ~ v2_funct_2(X0,X1)
% 3.65/1.00      | ~ v5_relat_1(X0,X1)
% 3.65/1.00      | ~ v1_relat_1(X0)
% 3.65/1.00      | k2_relat_1(X0) = X1 ),
% 3.65/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_473,plain,
% 3.65/1.00      ( ~ v3_funct_2(X0,X1,X2)
% 3.65/1.00      | ~ v5_relat_1(X3,X4)
% 3.65/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.65/1.00      | ~ v1_funct_1(X0)
% 3.65/1.00      | ~ v1_relat_1(X3)
% 3.65/1.00      | X3 != X0
% 3.65/1.00      | X4 != X2
% 3.65/1.00      | k2_relat_1(X3) = X4 ),
% 3.65/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_23]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_474,plain,
% 3.65/1.00      ( ~ v3_funct_2(X0,X1,X2)
% 3.65/1.00      | ~ v5_relat_1(X0,X2)
% 3.65/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.65/1.00      | ~ v1_funct_1(X0)
% 3.65/1.00      | ~ v1_relat_1(X0)
% 3.65/1.00      | k2_relat_1(X0) = X2 ),
% 3.65/1.00      inference(unflattening,[status(thm)],[c_473]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_478,plain,
% 3.65/1.00      ( ~ v1_funct_1(X0)
% 3.65/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.65/1.00      | ~ v5_relat_1(X0,X2)
% 3.65/1.00      | ~ v3_funct_2(X0,X1,X2)
% 3.65/1.00      | k2_relat_1(X0) = X2 ),
% 3.65/1.00      inference(global_propositional_subsumption,
% 3.65/1.00                [status(thm)],
% 3.65/1.00                [c_474,c_9]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_479,plain,
% 3.65/1.00      ( ~ v3_funct_2(X0,X1,X2)
% 3.65/1.00      | ~ v5_relat_1(X0,X2)
% 3.65/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.65/1.00      | ~ v1_funct_1(X0)
% 3.65/1.00      | k2_relat_1(X0) = X2 ),
% 3.65/1.00      inference(renaming,[status(thm)],[c_478]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_10,plain,
% 3.65/1.00      ( v5_relat_1(X0,X1)
% 3.65/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.65/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_494,plain,
% 3.65/1.00      ( ~ v3_funct_2(X0,X1,X2)
% 3.65/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.65/1.00      | ~ v1_funct_1(X0)
% 3.65/1.00      | k2_relat_1(X0) = X2 ),
% 3.65/1.00      inference(forward_subsumption_resolution,
% 3.65/1.00                [status(thm)],
% 3.65/1.00                [c_479,c_10]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_1462,plain,
% 3.65/1.00      ( k2_relat_1(X0) = X1
% 3.65/1.00      | v3_funct_2(X0,X2,X1) != iProver_top
% 3.65/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
% 3.65/1.00      | v1_funct_1(X0) != iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_494]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_2700,plain,
% 3.65/1.00      ( k2_relat_1(sK1) = sK0
% 3.65/1.00      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.65/1.00      | v1_funct_1(sK1) != iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_1466,c_1462]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_3020,plain,
% 3.65/1.00      ( k2_relat_1(sK1) = sK0 ),
% 3.65/1.00      inference(global_propositional_subsumption,
% 3.65/1.00                [status(thm)],
% 3.65/1.00                [c_2700,c_36,c_38]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_3472,plain,
% 3.65/1.00      ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
% 3.65/1.00      | v2_funct_1(sK1) != iProver_top
% 3.65/1.00      | v1_relat_1(sK1) != iProver_top ),
% 3.65/1.00      inference(light_normalisation,[status(thm)],[c_3471,c_3020]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_3757,plain,
% 3.65/1.00      ( v2_funct_1(sK1) != iProver_top
% 3.65/1.00      | k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(sK0) ),
% 3.65/1.00      inference(global_propositional_subsumption,
% 3.65/1.00                [status(thm)],
% 3.65/1.00                [c_3472,c_1830]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_3758,plain,
% 3.65/1.00      ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
% 3.65/1.00      | v2_funct_1(sK1) != iProver_top ),
% 3.65/1.00      inference(renaming,[status(thm)],[c_3757]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_5048,plain,
% 3.65/1.00      ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(sK0) ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_5044,c_3758]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_7183,plain,
% 3.65/1.00      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
% 3.65/1.00      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.65/1.00      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.65/1.00      | v1_funct_1(k2_funct_1(sK1)) != iProver_top
% 3.65/1.00      | v1_funct_1(sK1) != iProver_top ),
% 3.65/1.00      inference(light_normalisation,[status(thm)],[c_7178,c_5048,c_5051]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_7046,plain,
% 3.65/1.00      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k5_relat_1(k2_funct_1(sK1),sK1)
% 3.65/1.00      | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_7042,c_6183]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_7060,plain,
% 3.65/1.00      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
% 3.65/1.00      | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
% 3.65/1.00      inference(light_normalisation,[status(thm)],[c_7046,c_5048]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_7205,plain,
% 3.65/1.00      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0) ),
% 3.65/1.00      inference(global_propositional_subsumption,
% 3.65/1.00                [status(thm)],
% 3.65/1.00                [c_7183,c_5055,c_7060]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_31,negated_conjecture,
% 3.65/1.00      ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
% 3.65/1.00      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
% 3.65/1.00      inference(cnf_transformation,[],[f90]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_1467,plain,
% 3.65/1.00      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) != iProver_top
% 3.65/1.00      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) != iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_5056,plain,
% 3.65/1.00      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) != iProver_top
% 3.65/1.00      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
% 3.65/1.00      inference(demodulation,[status(thm)],[c_5051,c_1467]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_7207,plain,
% 3.65/1.00      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top
% 3.65/1.00      | r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
% 3.65/1.00      inference(demodulation,[status(thm)],[c_7205,c_5056]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_12,plain,
% 3.65/1.00      ( r2_relset_1(X0,X1,X2,X2)
% 3.65/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.65/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.65/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_1546,plain,
% 3.65/1.00      ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0))
% 3.65/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 3.65/1.00      | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.65/1.00      inference(instantiation,[status(thm)],[c_12]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_1589,plain,
% 3.65/1.00      ( r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))
% 3.65/1.00      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.65/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.65/1.00      inference(instantiation,[status(thm)],[c_1546]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_1590,plain,
% 3.65/1.00      ( r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) = iProver_top
% 3.65/1.00      | m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.65/1.00      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_1589]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_28,plain,
% 3.65/1.00      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.65/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_1667,plain,
% 3.65/1.00      ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.65/1.00      inference(instantiation,[status(thm)],[c_28]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_1668,plain,
% 3.65/1.00      ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_1667]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_7247,plain,
% 3.65/1.00      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
% 3.65/1.00      inference(global_propositional_subsumption,
% 3.65/1.00                [status(thm)],
% 3.65/1.00                [c_7207,c_39,c_1590,c_1668]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_8713,plain,
% 3.65/1.00      ( r2_relset_1(sK0,sK0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
% 3.65/1.00      inference(demodulation,[status(thm)],[c_8711,c_7247]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_8778,plain,
% 3.65/1.00      ( sK0 = k1_xboole_0
% 3.65/1.00      | r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_4038,c_8713]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_8781,plain,
% 3.65/1.00      ( sK0 = k1_xboole_0 ),
% 3.65/1.00      inference(global_propositional_subsumption,
% 3.65/1.00                [status(thm)],
% 3.65/1.00                [c_8778,c_39,c_1590,c_1668]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_8783,plain,
% 3.65/1.00      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(k1_xboole_0)) != iProver_top ),
% 3.65/1.00      inference(demodulation,[status(thm)],[c_8781,c_8713]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_5,plain,
% 3.65/1.00      ( ~ v1_relat_1(X0)
% 3.65/1.00      | k2_relat_1(X0) != k1_xboole_0
% 3.65/1.00      | k1_xboole_0 = X0 ),
% 3.65/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_1488,plain,
% 3.65/1.00      ( k2_relat_1(X0) != k1_xboole_0
% 3.65/1.00      | k1_xboole_0 = X0
% 3.65/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_3024,plain,
% 3.65/1.00      ( sK1 = k1_xboole_0
% 3.65/1.00      | sK0 != k1_xboole_0
% 3.65/1.00      | v1_relat_1(sK1) != iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_3020,c_1488]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_3126,plain,
% 3.65/1.00      ( sK0 != k1_xboole_0 | sK1 = k1_xboole_0 ),
% 3.65/1.00      inference(global_propositional_subsumption,
% 3.65/1.00                [status(thm)],
% 3.65/1.00                [c_3024,c_1830]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_3127,plain,
% 3.65/1.00      ( sK1 = k1_xboole_0 | sK0 != k1_xboole_0 ),
% 3.65/1.00      inference(renaming,[status(thm)],[c_3126]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_8809,plain,
% 3.65/1.00      ( sK1 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.65/1.00      inference(demodulation,[status(thm)],[c_8781,c_3127]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_8816,plain,
% 3.65/1.00      ( sK1 = k1_xboole_0 ),
% 3.65/1.00      inference(equality_resolution_simp,[status(thm)],[c_8809]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_8784,plain,
% 3.65/1.00      ( k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
% 3.65/1.00      inference(demodulation,[status(thm)],[c_8781,c_8711]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_7053,plain,
% 3.65/1.00      ( k2_relat_1(k2_funct_1(sK1)) = sK0
% 3.65/1.00      | v3_funct_2(k2_funct_1(sK1),sK0,sK0) != iProver_top
% 3.65/1.00      | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_7042,c_1462]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_25,plain,
% 3.65/1.00      ( ~ v1_funct_2(X0,X1,X1)
% 3.65/1.00      | ~ v3_funct_2(X0,X1,X1)
% 3.65/1.00      | v3_funct_2(k2_funct_2(X1,X0),X1,X1)
% 3.65/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.65/1.00      | ~ v1_funct_1(X0) ),
% 3.65/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_1473,plain,
% 3.65/1.00      ( v1_funct_2(X0,X1,X1) != iProver_top
% 3.65/1.00      | v3_funct_2(X0,X1,X1) != iProver_top
% 3.65/1.00      | v3_funct_2(k2_funct_2(X1,X0),X1,X1) = iProver_top
% 3.65/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 3.65/1.00      | v1_funct_1(X0) != iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_4867,plain,
% 3.65/1.00      ( v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.65/1.00      | v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0) = iProver_top
% 3.65/1.00      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.65/1.00      | v1_funct_1(sK1) != iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_1466,c_1473]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_5267,plain,
% 3.65/1.00      ( v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0) = iProver_top ),
% 3.65/1.00      inference(global_propositional_subsumption,
% 3.65/1.00                [status(thm)],
% 3.65/1.00                [c_4867,c_36,c_37,c_38]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_5271,plain,
% 3.65/1.00      ( v3_funct_2(k2_funct_1(sK1),sK0,sK0) = iProver_top ),
% 3.65/1.00      inference(light_normalisation,[status(thm)],[c_5267,c_5051]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_7759,plain,
% 3.65/1.00      ( k2_relat_1(k2_funct_1(sK1)) = sK0 ),
% 3.65/1.00      inference(global_propositional_subsumption,
% 3.65/1.00                [status(thm)],
% 3.65/1.00                [c_7053,c_5055,c_5271]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_7763,plain,
% 3.65/1.00      ( k2_funct_1(sK1) = k1_xboole_0
% 3.65/1.00      | sK0 != k1_xboole_0
% 3.65/1.00      | v1_relat_1(k2_funct_1(sK1)) != iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_7759,c_1488]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_7052,plain,
% 3.65/1.00      ( v1_relat_1(k2_funct_1(sK1)) = iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_7042,c_1484]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_8080,plain,
% 3.65/1.00      ( sK0 != k1_xboole_0 | k2_funct_1(sK1) = k1_xboole_0 ),
% 3.65/1.00      inference(global_propositional_subsumption,
% 3.65/1.00                [status(thm)],
% 3.65/1.00                [c_7763,c_7052]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_8081,plain,
% 3.65/1.00      ( k2_funct_1(sK1) = k1_xboole_0 | sK0 != k1_xboole_0 ),
% 3.65/1.00      inference(renaming,[status(thm)],[c_8080]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_8787,plain,
% 3.65/1.00      ( k2_funct_1(sK1) = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.65/1.00      inference(demodulation,[status(thm)],[c_8781,c_8081]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_8842,plain,
% 3.65/1.00      ( k2_funct_1(sK1) = k1_xboole_0 ),
% 3.65/1.00      inference(equality_resolution_simp,[status(thm)],[c_8787]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_8843,plain,
% 3.65/1.00      ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
% 3.65/1.00      inference(demodulation,[status(thm)],[c_8842,c_8816]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_8803,plain,
% 3.65/1.00      ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k1_xboole_0) ),
% 3.65/1.00      inference(demodulation,[status(thm)],[c_8781,c_5048]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_8826,plain,
% 3.65/1.00      ( k5_relat_1(k2_funct_1(k1_xboole_0),k1_xboole_0) = k6_partfun1(k1_xboole_0) ),
% 3.65/1.00      inference(demodulation,[status(thm)],[c_8803,c_8816]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_8851,plain,
% 3.65/1.00      ( k5_relat_1(k1_xboole_0,k1_xboole_0) = k6_partfun1(k1_xboole_0) ),
% 3.65/1.00      inference(demodulation,[status(thm)],[c_8843,c_8826]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_6191,plain,
% 3.65/1.00      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK1) = k5_relat_1(sK1,sK1)
% 3.65/1.00      | v1_funct_1(sK1) != iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_1466,c_6183]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_6316,plain,
% 3.65/1.00      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK1) = k5_relat_1(sK1,sK1) ),
% 3.65/1.00      inference(global_propositional_subsumption,
% 3.65/1.00                [status(thm)],
% 3.65/1.00                [c_6191,c_36]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_8801,plain,
% 3.65/1.00      ( k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK1,sK1) = k5_relat_1(sK1,sK1) ),
% 3.65/1.00      inference(demodulation,[status(thm)],[c_8781,c_6316]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_8828,plain,
% 3.65/1.00      ( k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k5_relat_1(k1_xboole_0,k1_xboole_0) ),
% 3.65/1.00      inference(demodulation,[status(thm)],[c_8801,c_8816]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_8856,plain,
% 3.65/1.00      ( k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k6_partfun1(k1_xboole_0) ),
% 3.65/1.00      inference(demodulation,[status(thm)],[c_8851,c_8828]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_8859,plain,
% 3.65/1.00      ( k6_partfun1(k1_relat_1(k1_xboole_0)) = k6_partfun1(k1_xboole_0) ),
% 3.65/1.00      inference(demodulation,[status(thm)],[c_8784,c_8816,c_8843,c_8856]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_8860,plain,
% 3.65/1.00      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),k6_partfun1(k1_xboole_0)) != iProver_top ),
% 3.65/1.00      inference(demodulation,[status(thm)],[c_8783,c_8816,c_8859]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_0,plain,
% 3.65/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.65/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_1583,plain,
% 3.65/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.65/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_1584,plain,
% 3.65/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_1583]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_1586,plain,
% 3.65/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 3.65/1.00      inference(instantiation,[status(thm)],[c_1584]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_1547,plain,
% 3.65/1.00      ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0)) = iProver_top
% 3.65/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 3.65/1.00      | m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_1546]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_1549,plain,
% 3.65/1.00      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),k6_partfun1(k1_xboole_0)) = iProver_top
% 3.65/1.00      | m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 3.65/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 3.65/1.00      inference(instantiation,[status(thm)],[c_1547]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_47,plain,
% 3.65/1.00      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_49,plain,
% 3.65/1.00      ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 3.65/1.00      inference(instantiation,[status(thm)],[c_47]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(contradiction,plain,
% 3.65/1.00      ( $false ),
% 3.65/1.00      inference(minisat,[status(thm)],[c_8860,c_1586,c_1549,c_49]) ).
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.65/1.00  
% 3.65/1.00  ------                               Statistics
% 3.65/1.00  
% 3.65/1.00  ------ General
% 3.65/1.00  
% 3.65/1.00  abstr_ref_over_cycles:                  0
% 3.65/1.00  abstr_ref_under_cycles:                 0
% 3.65/1.00  gc_basic_clause_elim:                   0
% 3.65/1.00  forced_gc_time:                         0
% 3.65/1.00  parsing_time:                           0.009
% 3.65/1.00  unif_index_cands_time:                  0.
% 3.65/1.00  unif_index_add_time:                    0.
% 3.65/1.00  orderings_time:                         0.
% 3.65/1.00  out_proof_time:                         0.014
% 3.65/1.00  total_time:                             0.344
% 3.65/1.00  num_of_symbols:                         54
% 3.65/1.00  num_of_terms:                           9711
% 3.65/1.00  
% 3.65/1.00  ------ Preprocessing
% 3.65/1.00  
% 3.65/1.00  num_of_splits:                          0
% 3.65/1.00  num_of_split_atoms:                     0
% 3.65/1.00  num_of_reused_defs:                     0
% 3.65/1.00  num_eq_ax_congr_red:                    24
% 3.65/1.00  num_of_sem_filtered_clauses:            1
% 3.65/1.00  num_of_subtypes:                        0
% 3.65/1.00  monotx_restored_types:                  0
% 3.65/1.00  sat_num_of_epr_types:                   0
% 3.65/1.00  sat_num_of_non_cyclic_types:            0
% 3.65/1.00  sat_guarded_non_collapsed_types:        0
% 3.65/1.00  num_pure_diseq_elim:                    0
% 3.65/1.00  simp_replaced_by:                       0
% 3.65/1.00  res_preprocessed:                       151
% 3.65/1.00  prep_upred:                             0
% 3.65/1.00  prep_unflattend:                        6
% 3.65/1.00  smt_new_axioms:                         0
% 3.65/1.00  pred_elim_cands:                        7
% 3.65/1.00  pred_elim:                              3
% 3.65/1.00  pred_elim_cl:                           6
% 3.65/1.00  pred_elim_cycles:                       7
% 3.65/1.00  merged_defs:                            2
% 3.65/1.00  merged_defs_ncl:                        0
% 3.65/1.00  bin_hyper_res:                          2
% 3.65/1.00  prep_cycles:                            4
% 3.65/1.00  pred_elim_time:                         0.007
% 3.65/1.00  splitting_time:                         0.
% 3.65/1.00  sem_filter_time:                        0.
% 3.65/1.00  monotx_time:                            0.001
% 3.65/1.00  subtype_inf_time:                       0.
% 3.65/1.00  
% 3.65/1.00  ------ Problem properties
% 3.65/1.00  
% 3.65/1.00  clauses:                                29
% 3.65/1.00  conjectures:                            5
% 3.65/1.00  epr:                                    3
% 3.65/1.00  horn:                                   25
% 3.65/1.00  ground:                                 5
% 3.65/1.00  unary:                                  6
% 3.65/1.00  binary:                                 4
% 3.65/1.00  lits:                                   90
% 3.65/1.00  lits_eq:                                19
% 3.65/1.00  fd_pure:                                0
% 3.65/1.00  fd_pseudo:                              0
% 3.65/1.00  fd_cond:                                5
% 3.65/1.00  fd_pseudo_cond:                         1
% 3.65/1.00  ac_symbols:                             0
% 3.65/1.00  
% 3.65/1.00  ------ Propositional Solver
% 3.65/1.00  
% 3.65/1.00  prop_solver_calls:                      30
% 3.65/1.00  prop_fast_solver_calls:                 1352
% 3.65/1.00  smt_solver_calls:                       0
% 3.65/1.00  smt_fast_solver_calls:                  0
% 3.65/1.00  prop_num_of_clauses:                    3558
% 3.65/1.00  prop_preprocess_simplified:             9496
% 3.65/1.00  prop_fo_subsumed:                       61
% 3.65/1.00  prop_solver_time:                       0.
% 3.65/1.00  smt_solver_time:                        0.
% 3.65/1.00  smt_fast_solver_time:                   0.
% 3.65/1.00  prop_fast_solver_time:                  0.
% 3.65/1.00  prop_unsat_core_time:                   0.
% 3.65/1.00  
% 3.65/1.00  ------ QBF
% 3.65/1.00  
% 3.65/1.00  qbf_q_res:                              0
% 3.65/1.00  qbf_num_tautologies:                    0
% 3.65/1.00  qbf_prep_cycles:                        0
% 3.65/1.00  
% 3.65/1.00  ------ BMC1
% 3.65/1.00  
% 3.65/1.00  bmc1_current_bound:                     -1
% 3.65/1.00  bmc1_last_solved_bound:                 -1
% 3.65/1.00  bmc1_unsat_core_size:                   -1
% 3.65/1.00  bmc1_unsat_core_parents_size:           -1
% 3.65/1.00  bmc1_merge_next_fun:                    0
% 3.65/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.65/1.00  
% 3.65/1.00  ------ Instantiation
% 3.65/1.00  
% 3.65/1.00  inst_num_of_clauses:                    960
% 3.65/1.00  inst_num_in_passive:                    132
% 3.65/1.00  inst_num_in_active:                     449
% 3.65/1.00  inst_num_in_unprocessed:                383
% 3.65/1.00  inst_num_of_loops:                      540
% 3.65/1.00  inst_num_of_learning_restarts:          0
% 3.65/1.00  inst_num_moves_active_passive:          86
% 3.65/1.00  inst_lit_activity:                      0
% 3.65/1.00  inst_lit_activity_moves:                0
% 3.65/1.00  inst_num_tautologies:                   0
% 3.65/1.00  inst_num_prop_implied:                  0
% 3.65/1.00  inst_num_existing_simplified:           0
% 3.65/1.00  inst_num_eq_res_simplified:             0
% 3.65/1.00  inst_num_child_elim:                    0
% 3.65/1.00  inst_num_of_dismatching_blockings:      929
% 3.65/1.00  inst_num_of_non_proper_insts:           1174
% 3.65/1.00  inst_num_of_duplicates:                 0
% 3.65/1.00  inst_inst_num_from_inst_to_res:         0
% 3.65/1.00  inst_dismatching_checking_time:         0.
% 3.65/1.00  
% 3.65/1.00  ------ Resolution
% 3.65/1.00  
% 3.65/1.00  res_num_of_clauses:                     0
% 3.65/1.00  res_num_in_passive:                     0
% 3.65/1.00  res_num_in_active:                      0
% 3.65/1.00  res_num_of_loops:                       155
% 3.65/1.00  res_forward_subset_subsumed:            91
% 3.65/1.00  res_backward_subset_subsumed:           16
% 3.65/1.00  res_forward_subsumed:                   0
% 3.65/1.00  res_backward_subsumed:                  0
% 3.65/1.00  res_forward_subsumption_resolution:     2
% 3.65/1.00  res_backward_subsumption_resolution:    0
% 3.65/1.00  res_clause_to_clause_subsumption:       365
% 3.65/1.00  res_orphan_elimination:                 0
% 3.65/1.00  res_tautology_del:                      62
% 3.65/1.00  res_num_eq_res_simplified:              0
% 3.65/1.00  res_num_sel_changes:                    0
% 3.65/1.00  res_moves_from_active_to_pass:          0
% 3.65/1.00  
% 3.65/1.00  ------ Superposition
% 3.65/1.00  
% 3.65/1.00  sup_time_total:                         0.
% 3.65/1.00  sup_time_generating:                    0.
% 3.65/1.00  sup_time_sim_full:                      0.
% 3.65/1.00  sup_time_sim_immed:                     0.
% 3.65/1.00  
% 3.65/1.00  sup_num_of_clauses:                     159
% 3.65/1.00  sup_num_in_active:                      55
% 3.65/1.00  sup_num_in_passive:                     104
% 3.65/1.00  sup_num_of_loops:                       107
% 3.65/1.00  sup_fw_superposition:                   121
% 3.65/1.00  sup_bw_superposition:                   65
% 3.65/1.00  sup_immediate_simplified:               78
% 3.65/1.00  sup_given_eliminated:                   0
% 3.65/1.00  comparisons_done:                       0
% 3.65/1.00  comparisons_avoided:                    0
% 3.65/1.00  
% 3.65/1.00  ------ Simplifications
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  sim_fw_subset_subsumed:                 3
% 3.65/1.00  sim_bw_subset_subsumed:                 14
% 3.65/1.00  sim_fw_subsumed:                        10
% 3.65/1.00  sim_bw_subsumed:                        2
% 3.65/1.00  sim_fw_subsumption_res:                 0
% 3.65/1.00  sim_bw_subsumption_res:                 0
% 3.65/1.00  sim_tautology_del:                      0
% 3.65/1.00  sim_eq_tautology_del:                   4
% 3.65/1.00  sim_eq_res_simp:                        2
% 3.65/1.00  sim_fw_demodulated:                     35
% 3.65/1.00  sim_bw_demodulated:                     63
% 3.65/1.00  sim_light_normalised:                   8
% 3.65/1.00  sim_joinable_taut:                      0
% 3.65/1.00  sim_joinable_simp:                      0
% 3.65/1.00  sim_ac_normalised:                      0
% 3.65/1.00  sim_smt_subsumption:                    0
% 3.65/1.00  
%------------------------------------------------------------------------------
