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
% DateTime   : Thu Dec  3 12:07:20 EST 2020

% Result     : Theorem 7.80s
% Output     : CNFRefutation 7.80s
% Verified   : 
% Statistics : Number of formulae       :  215 (3127 expanded)
%              Number of clauses        :  129 ( 964 expanded)
%              Number of leaves         :   23 ( 622 expanded)
%              Depth                    :   28
%              Number of atoms          :  686 (14558 expanded)
%              Number of equality atoms :  319 (1713 expanded)
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

fof(f42,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f43,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f42])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f43,f52])).

fof(f94,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
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

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

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
    inference(nnf_transformation,[],[f33])).

fof(f75,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f92,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_1(X1) = k2_funct_2(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f40])).

fof(f89,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f91,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f93,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
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

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f86,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f38])).

fof(f88,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f83,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k2_funct_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f65,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f18,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f90,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f18])).

fof(f97,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f65,f90])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f30])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f66,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f96,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f66,f90])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

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

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f95,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f53])).

fof(f15,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f87,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f10,axiom,(
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
    inference(ennf_transformation,[],[f10])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f28])).

fof(f49,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f102,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f71])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f46])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f100,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f60])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f44])).

fof(f56,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f5,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f101,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f59])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_37,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1781,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1790,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_6747,plain,
    ( k1_relset_1(sK0,sK0,sK1) = sK0
    | sK0 = k1_xboole_0
    | v1_funct_2(sK1,sK0,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1781,c_1790])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1799,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3546,plain,
    ( k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_1781,c_1799])).

cnf(c_6757,plain,
    ( k1_relat_1(sK1) = sK0
    | sK0 = k1_xboole_0
    | v1_funct_2(sK1,sK0,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6747,c_3546])).

cnf(c_39,negated_conjecture,
    ( v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_42,plain,
    ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_6872,plain,
    ( sK0 = k1_xboole_0
    | k1_relat_1(sK1) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6757,c_42])).

cnf(c_6873,plain,
    ( k1_relat_1(sK1) = sK0
    | sK0 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_6872])).

cnf(c_35,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1783,plain,
    ( k2_funct_2(X0,X1) = k2_funct_1(X1)
    | v1_funct_2(X1,X0,X0) != iProver_top
    | v3_funct_2(X1,X0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_10669,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1781,c_1783])).

cnf(c_40,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_38,negated_conjecture,
    ( v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_2168,plain,
    ( ~ v1_funct_2(sK1,X0,X0)
    | ~ v3_funct_2(sK1,X0,X0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ v1_funct_1(sK1)
    | k2_funct_2(X0,sK1) = k2_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_35])).

cnf(c_2305,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_2168])).

cnf(c_11125,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10669,c_40,c_39,c_38,c_37,c_2305])).

cnf(c_29,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1789,plain,
    ( v1_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(X0,X1,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_11146,plain,
    ( v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_11125,c_1789])).

cnf(c_41,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_43,plain,
    ( v3_funct_2(sK1,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_44,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_11652,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11146,c_41,c_42,c_43,c_44])).

cnf(c_34,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1784,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_12237,plain,
    ( k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11652,c_1784])).

cnf(c_32,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_2(X1,X0)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2153,plain,
    ( ~ v1_funct_2(sK1,X0,X0)
    | ~ v3_funct_2(sK1,X0,X0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | v1_funct_1(k2_funct_2(X0,sK1))
    | ~ v1_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_2302,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v1_funct_1(k2_funct_2(sK0,sK1))
    | ~ v1_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_2153])).

cnf(c_2303,plain,
    ( v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(k2_funct_2(sK0,sK1)) = iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2302])).

cnf(c_1009,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2979,plain,
    ( X0 != X1
    | X0 = k2_funct_2(sK0,sK1)
    | k2_funct_2(sK0,sK1) != X1 ),
    inference(instantiation,[status(thm)],[c_1009])).

cnf(c_3835,plain,
    ( X0 = k2_funct_2(sK0,sK1)
    | X0 != k2_funct_1(sK1)
    | k2_funct_2(sK0,sK1) != k2_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_2979])).

cnf(c_4980,plain,
    ( k2_funct_2(sK0,sK1) != k2_funct_1(sK1)
    | k2_funct_1(sK1) = k2_funct_2(sK0,sK1)
    | k2_funct_1(sK1) != k2_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_3835])).

cnf(c_1008,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_4981,plain,
    ( k2_funct_1(sK1) = k2_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_1008])).

cnf(c_1018,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2414,plain,
    ( v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_2(sK0,sK1))
    | X0 != k2_funct_2(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_1018])).

cnf(c_9601,plain,
    ( ~ v1_funct_1(k2_funct_2(sK0,sK1))
    | v1_funct_1(k2_funct_1(sK1))
    | k2_funct_1(sK1) != k2_funct_2(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_2414])).

cnf(c_9602,plain,
    ( k2_funct_1(sK1) != k2_funct_2(sK0,sK1)
    | v1_funct_1(k2_funct_2(sK0,sK1)) != iProver_top
    | v1_funct_1(k2_funct_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9601])).

cnf(c_19171,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12237,c_40,c_41,c_39,c_42,c_38,c_43,c_37,c_44,c_2303,c_2305,c_4980,c_4981,c_9602])).

cnf(c_19172,plain,
    ( k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_19171])).

cnf(c_19183,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k5_relat_1(sK1,k2_funct_1(sK1))
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1781,c_19172])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1800,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2788,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1781,c_1800])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1801,plain,
    ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_5612,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
    | v1_funct_1(sK1) != iProver_top
    | v2_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2788,c_1801])).

cnf(c_2100,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2206,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_19,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2137,plain,
    ( ~ v3_funct_2(sK1,X0,X1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK1)
    | v2_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_2249,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | v2_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_2137])).

cnf(c_5917,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5612,c_40,c_38,c_37,c_2100,c_2206,c_2249])).

cnf(c_19205,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
    | v1_funct_1(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_19183,c_5917])).

cnf(c_20207,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19205,c_41])).

cnf(c_12236,plain,
    ( k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1781,c_1784])).

cnf(c_12717,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12236,c_41])).

cnf(c_12718,plain,
    ( k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_12717])).

cnf(c_12727,plain,
    ( k1_partfun1(X0,X0,sK0,sK0,k2_funct_2(X0,X1),sK1) = k5_relat_1(k2_funct_2(X0,X1),sK1)
    | v1_funct_2(X1,X0,X0) != iProver_top
    | v3_funct_2(X1,X0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(k2_funct_2(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1789,c_12718])).

cnf(c_1786,plain,
    ( v1_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(X0,X1,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_2(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_14751,plain,
    ( k1_partfun1(X0,X0,sK0,sK0,k2_funct_2(X0,X1),sK1) = k5_relat_1(k2_funct_2(X0,X1),sK1)
    | v1_funct_2(X1,X0,X0) != iProver_top
    | v3_funct_2(X1,X0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_12727,c_1786])).

cnf(c_14758,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1) = k5_relat_1(k2_funct_2(sK0,sK1),sK1)
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1781,c_14751])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1802,plain,
    ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_5728,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1))
    | v1_funct_1(sK1) != iProver_top
    | v2_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2788,c_1802])).

cnf(c_18,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | v2_funct_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_14,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_28,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_481,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_14,c_28])).

cnf(c_491,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | k2_relat_1(X0) = X1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_481,c_13])).

cnf(c_562,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | X3 != X0
    | X5 != X2
    | k2_relat_1(X3) = X5 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_491])).

cnf(c_563,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ v1_funct_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(unflattening,[status(thm)],[c_562])).

cnf(c_1777,plain,
    ( k2_relat_1(X0) = X1
    | v3_funct_2(X0,X2,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_563])).

cnf(c_2668,plain,
    ( k2_relat_1(sK1) = sK0
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1781,c_1777])).

cnf(c_3145,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | k2_relat_1(sK1) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2668,c_41,c_43])).

cnf(c_3146,plain,
    ( k2_relat_1(sK1) = sK0
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3145])).

cnf(c_3154,plain,
    ( k2_relat_1(sK1) = sK0 ),
    inference(superposition,[status(thm)],[c_1781,c_3146])).

cnf(c_5739,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
    | v1_funct_1(sK1) != iProver_top
    | v2_funct_1(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5728,c_3154])).

cnf(c_2250,plain,
    ( v3_funct_2(sK1,sK0,sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v2_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2249])).

cnf(c_5913,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5739,c_41,c_43,c_44,c_2250])).

cnf(c_14784,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_14758,c_5913,c_11125])).

cnf(c_12730,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k5_relat_1(k2_funct_1(sK1),sK1)
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11652,c_12718])).

cnf(c_12747,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12730,c_5913])).

cnf(c_14838,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14784,c_40,c_41,c_39,c_42,c_38,c_43,c_37,c_44,c_2303,c_2305,c_4980,c_4981,c_9602,c_12747])).

cnf(c_36,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1782,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) != iProver_top
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_11131,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) != iProver_top
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11125,c_1782])).

cnf(c_14841,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top
    | r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_14838,c_11131])).

cnf(c_33,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1785,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_16,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1798,plain,
    ( r2_relset_1(X0,X1,X2,X2) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2889,plain,
    ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1785,c_1798])).

cnf(c_15590,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_14841,c_2889])).

cnf(c_20210,plain,
    ( r2_relset_1(sK0,sK0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_20207,c_15590])).

cnf(c_20451,plain,
    ( sK0 = k1_xboole_0
    | r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6873,c_20210])).

cnf(c_20456,plain,
    ( sK0 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_20451,c_2889])).

cnf(c_20457,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_20456,c_20210])).

cnf(c_4,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_2343,plain,
    ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_1785])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1803,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2473,plain,
    ( r1_tarski(k6_partfun1(k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2343,c_1803])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1805,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1807,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4806,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1805,c_1807])).

cnf(c_5055,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2473,c_4806])).

cnf(c_20871,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_relat_1(sK1)),k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_20457,c_5055])).

cnf(c_10,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2472,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(sK0,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1781,c_1803])).

cnf(c_20519,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_20456,c_2472])).

cnf(c_5,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_20531,plain,
    ( r1_tarski(sK1,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_20519,c_5])).

cnf(c_22147,plain,
    ( sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_20531,c_4806])).

cnf(c_40671,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_20871,c_10,c_5055,c_22147])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1804,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2888,plain,
    ( r2_relset_1(X0,X1,X2,X2) = iProver_top
    | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1804,c_1798])).

cnf(c_6935,plain,
    ( r2_relset_1(X0,X1,k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1805,c_2888])).

cnf(c_40673,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_40671,c_6935])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : iproveropt_run.sh %d %s
% 0.11/0.31  % Computer   : n005.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % WCLimit    : 600
% 0.11/0.31  % DateTime   : Tue Dec  1 10:41:32 EST 2020
% 0.11/0.31  % CPUTime    : 
% 0.16/0.31  % Running in FOF mode
% 7.80/1.45  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.80/1.45  
% 7.80/1.45  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.80/1.45  
% 7.80/1.45  ------  iProver source info
% 7.80/1.45  
% 7.80/1.45  git: date: 2020-06-30 10:37:57 +0100
% 7.80/1.45  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.80/1.45  git: non_committed_changes: false
% 7.80/1.45  git: last_make_outside_of_git: false
% 7.80/1.45  
% 7.80/1.45  ------ 
% 7.80/1.45  
% 7.80/1.45  ------ Input Options
% 7.80/1.45  
% 7.80/1.45  --out_options                           all
% 7.80/1.45  --tptp_safe_out                         true
% 7.80/1.45  --problem_path                          ""
% 7.80/1.45  --include_path                          ""
% 7.80/1.45  --clausifier                            res/vclausify_rel
% 7.80/1.45  --clausifier_options                    --mode clausify
% 7.80/1.45  --stdin                                 false
% 7.80/1.45  --stats_out                             all
% 7.80/1.45  
% 7.80/1.45  ------ General Options
% 7.80/1.45  
% 7.80/1.45  --fof                                   false
% 7.80/1.45  --time_out_real                         305.
% 7.80/1.45  --time_out_virtual                      -1.
% 7.80/1.45  --symbol_type_check                     false
% 7.80/1.45  --clausify_out                          false
% 7.80/1.45  --sig_cnt_out                           false
% 7.80/1.45  --trig_cnt_out                          false
% 7.80/1.45  --trig_cnt_out_tolerance                1.
% 7.80/1.45  --trig_cnt_out_sk_spl                   false
% 7.80/1.45  --abstr_cl_out                          false
% 7.80/1.45  
% 7.80/1.45  ------ Global Options
% 7.80/1.45  
% 7.80/1.45  --schedule                              default
% 7.80/1.45  --add_important_lit                     false
% 7.80/1.45  --prop_solver_per_cl                    1000
% 7.80/1.45  --min_unsat_core                        false
% 7.80/1.45  --soft_assumptions                      false
% 7.80/1.45  --soft_lemma_size                       3
% 7.80/1.45  --prop_impl_unit_size                   0
% 7.80/1.45  --prop_impl_unit                        []
% 7.80/1.45  --share_sel_clauses                     true
% 7.80/1.45  --reset_solvers                         false
% 7.80/1.45  --bc_imp_inh                            [conj_cone]
% 7.80/1.45  --conj_cone_tolerance                   3.
% 7.80/1.45  --extra_neg_conj                        none
% 7.80/1.45  --large_theory_mode                     true
% 7.80/1.45  --prolific_symb_bound                   200
% 7.80/1.45  --lt_threshold                          2000
% 7.80/1.45  --clause_weak_htbl                      true
% 7.80/1.45  --gc_record_bc_elim                     false
% 7.80/1.45  
% 7.80/1.45  ------ Preprocessing Options
% 7.80/1.45  
% 7.80/1.45  --preprocessing_flag                    true
% 7.80/1.45  --time_out_prep_mult                    0.1
% 7.80/1.45  --splitting_mode                        input
% 7.80/1.45  --splitting_grd                         true
% 7.80/1.45  --splitting_cvd                         false
% 7.80/1.45  --splitting_cvd_svl                     false
% 7.80/1.45  --splitting_nvd                         32
% 7.80/1.45  --sub_typing                            true
% 7.80/1.45  --prep_gs_sim                           true
% 7.80/1.45  --prep_unflatten                        true
% 7.80/1.45  --prep_res_sim                          true
% 7.80/1.45  --prep_upred                            true
% 7.80/1.45  --prep_sem_filter                       exhaustive
% 7.80/1.45  --prep_sem_filter_out                   false
% 7.80/1.45  --pred_elim                             true
% 7.80/1.45  --res_sim_input                         true
% 7.80/1.45  --eq_ax_congr_red                       true
% 7.80/1.45  --pure_diseq_elim                       true
% 7.80/1.45  --brand_transform                       false
% 7.80/1.45  --non_eq_to_eq                          false
% 7.80/1.45  --prep_def_merge                        true
% 7.80/1.45  --prep_def_merge_prop_impl              false
% 7.80/1.45  --prep_def_merge_mbd                    true
% 7.80/1.45  --prep_def_merge_tr_red                 false
% 7.80/1.45  --prep_def_merge_tr_cl                  false
% 7.80/1.45  --smt_preprocessing                     true
% 7.80/1.45  --smt_ac_axioms                         fast
% 7.80/1.45  --preprocessed_out                      false
% 7.80/1.45  --preprocessed_stats                    false
% 7.80/1.45  
% 7.80/1.45  ------ Abstraction refinement Options
% 7.80/1.45  
% 7.80/1.45  --abstr_ref                             []
% 7.80/1.45  --abstr_ref_prep                        false
% 7.80/1.45  --abstr_ref_until_sat                   false
% 7.80/1.45  --abstr_ref_sig_restrict                funpre
% 7.80/1.45  --abstr_ref_af_restrict_to_split_sk     false
% 7.80/1.45  --abstr_ref_under                       []
% 7.80/1.45  
% 7.80/1.45  ------ SAT Options
% 7.80/1.45  
% 7.80/1.45  --sat_mode                              false
% 7.80/1.45  --sat_fm_restart_options                ""
% 7.80/1.45  --sat_gr_def                            false
% 7.80/1.45  --sat_epr_types                         true
% 7.80/1.45  --sat_non_cyclic_types                  false
% 7.80/1.45  --sat_finite_models                     false
% 7.80/1.45  --sat_fm_lemmas                         false
% 7.80/1.45  --sat_fm_prep                           false
% 7.80/1.45  --sat_fm_uc_incr                        true
% 7.80/1.45  --sat_out_model                         small
% 7.80/1.45  --sat_out_clauses                       false
% 7.80/1.45  
% 7.80/1.45  ------ QBF Options
% 7.80/1.45  
% 7.80/1.45  --qbf_mode                              false
% 7.80/1.45  --qbf_elim_univ                         false
% 7.80/1.45  --qbf_dom_inst                          none
% 7.80/1.45  --qbf_dom_pre_inst                      false
% 7.80/1.45  --qbf_sk_in                             false
% 7.80/1.45  --qbf_pred_elim                         true
% 7.80/1.45  --qbf_split                             512
% 7.80/1.45  
% 7.80/1.45  ------ BMC1 Options
% 7.80/1.45  
% 7.80/1.45  --bmc1_incremental                      false
% 7.80/1.45  --bmc1_axioms                           reachable_all
% 7.80/1.45  --bmc1_min_bound                        0
% 7.80/1.45  --bmc1_max_bound                        -1
% 7.80/1.45  --bmc1_max_bound_default                -1
% 7.80/1.45  --bmc1_symbol_reachability              true
% 7.80/1.45  --bmc1_property_lemmas                  false
% 7.80/1.45  --bmc1_k_induction                      false
% 7.80/1.45  --bmc1_non_equiv_states                 false
% 7.80/1.45  --bmc1_deadlock                         false
% 7.80/1.45  --bmc1_ucm                              false
% 7.80/1.45  --bmc1_add_unsat_core                   none
% 7.80/1.45  --bmc1_unsat_core_children              false
% 7.80/1.45  --bmc1_unsat_core_extrapolate_axioms    false
% 7.80/1.45  --bmc1_out_stat                         full
% 7.80/1.45  --bmc1_ground_init                      false
% 7.80/1.45  --bmc1_pre_inst_next_state              false
% 7.80/1.45  --bmc1_pre_inst_state                   false
% 7.80/1.45  --bmc1_pre_inst_reach_state             false
% 7.80/1.45  --bmc1_out_unsat_core                   false
% 7.80/1.45  --bmc1_aig_witness_out                  false
% 7.80/1.45  --bmc1_verbose                          false
% 7.80/1.45  --bmc1_dump_clauses_tptp                false
% 7.80/1.45  --bmc1_dump_unsat_core_tptp             false
% 7.80/1.45  --bmc1_dump_file                        -
% 7.80/1.45  --bmc1_ucm_expand_uc_limit              128
% 7.80/1.45  --bmc1_ucm_n_expand_iterations          6
% 7.80/1.45  --bmc1_ucm_extend_mode                  1
% 7.80/1.45  --bmc1_ucm_init_mode                    2
% 7.80/1.45  --bmc1_ucm_cone_mode                    none
% 7.80/1.45  --bmc1_ucm_reduced_relation_type        0
% 7.80/1.45  --bmc1_ucm_relax_model                  4
% 7.80/1.45  --bmc1_ucm_full_tr_after_sat            true
% 7.80/1.45  --bmc1_ucm_expand_neg_assumptions       false
% 7.80/1.45  --bmc1_ucm_layered_model                none
% 7.80/1.45  --bmc1_ucm_max_lemma_size               10
% 7.80/1.45  
% 7.80/1.45  ------ AIG Options
% 7.80/1.45  
% 7.80/1.45  --aig_mode                              false
% 7.80/1.45  
% 7.80/1.45  ------ Instantiation Options
% 7.80/1.45  
% 7.80/1.45  --instantiation_flag                    true
% 7.80/1.45  --inst_sos_flag                         false
% 7.80/1.45  --inst_sos_phase                        true
% 7.80/1.45  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.80/1.45  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.80/1.45  --inst_lit_sel_side                     num_symb
% 7.80/1.45  --inst_solver_per_active                1400
% 7.80/1.45  --inst_solver_calls_frac                1.
% 7.80/1.45  --inst_passive_queue_type               priority_queues
% 7.80/1.45  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.80/1.45  --inst_passive_queues_freq              [25;2]
% 7.80/1.45  --inst_dismatching                      true
% 7.80/1.45  --inst_eager_unprocessed_to_passive     true
% 7.80/1.45  --inst_prop_sim_given                   true
% 7.80/1.45  --inst_prop_sim_new                     false
% 7.80/1.45  --inst_subs_new                         false
% 7.80/1.45  --inst_eq_res_simp                      false
% 7.80/1.45  --inst_subs_given                       false
% 7.80/1.45  --inst_orphan_elimination               true
% 7.80/1.45  --inst_learning_loop_flag               true
% 7.80/1.45  --inst_learning_start                   3000
% 7.80/1.45  --inst_learning_factor                  2
% 7.80/1.45  --inst_start_prop_sim_after_learn       3
% 7.80/1.45  --inst_sel_renew                        solver
% 7.80/1.45  --inst_lit_activity_flag                true
% 7.80/1.45  --inst_restr_to_given                   false
% 7.80/1.45  --inst_activity_threshold               500
% 7.80/1.45  --inst_out_proof                        true
% 7.80/1.45  
% 7.80/1.45  ------ Resolution Options
% 7.80/1.45  
% 7.80/1.45  --resolution_flag                       true
% 7.80/1.45  --res_lit_sel                           adaptive
% 7.80/1.45  --res_lit_sel_side                      none
% 7.80/1.45  --res_ordering                          kbo
% 7.80/1.45  --res_to_prop_solver                    active
% 7.80/1.45  --res_prop_simpl_new                    false
% 7.80/1.45  --res_prop_simpl_given                  true
% 7.80/1.45  --res_passive_queue_type                priority_queues
% 7.80/1.45  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.80/1.45  --res_passive_queues_freq               [15;5]
% 7.80/1.45  --res_forward_subs                      full
% 7.80/1.45  --res_backward_subs                     full
% 7.80/1.45  --res_forward_subs_resolution           true
% 7.80/1.45  --res_backward_subs_resolution          true
% 7.80/1.45  --res_orphan_elimination                true
% 7.80/1.45  --res_time_limit                        2.
% 7.80/1.45  --res_out_proof                         true
% 7.80/1.45  
% 7.80/1.45  ------ Superposition Options
% 7.80/1.45  
% 7.80/1.45  --superposition_flag                    true
% 7.80/1.45  --sup_passive_queue_type                priority_queues
% 7.80/1.45  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.80/1.45  --sup_passive_queues_freq               [8;1;4]
% 7.80/1.45  --demod_completeness_check              fast
% 7.80/1.45  --demod_use_ground                      true
% 7.80/1.45  --sup_to_prop_solver                    passive
% 7.80/1.45  --sup_prop_simpl_new                    true
% 7.80/1.45  --sup_prop_simpl_given                  true
% 7.80/1.45  --sup_fun_splitting                     false
% 7.80/1.45  --sup_smt_interval                      50000
% 7.80/1.45  
% 7.80/1.45  ------ Superposition Simplification Setup
% 7.80/1.45  
% 7.80/1.45  --sup_indices_passive                   []
% 7.80/1.45  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.80/1.45  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.80/1.45  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.80/1.45  --sup_full_triv                         [TrivRules;PropSubs]
% 7.80/1.45  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.80/1.45  --sup_full_bw                           [BwDemod]
% 7.80/1.45  --sup_immed_triv                        [TrivRules]
% 7.80/1.45  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.80/1.45  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.80/1.45  --sup_immed_bw_main                     []
% 7.80/1.45  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.80/1.45  --sup_input_triv                        [Unflattening;TrivRules]
% 7.80/1.45  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.80/1.45  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.80/1.45  
% 7.80/1.45  ------ Combination Options
% 7.80/1.45  
% 7.80/1.45  --comb_res_mult                         3
% 7.80/1.45  --comb_sup_mult                         2
% 7.80/1.45  --comb_inst_mult                        10
% 7.80/1.45  
% 7.80/1.45  ------ Debug Options
% 7.80/1.45  
% 7.80/1.45  --dbg_backtrace                         false
% 7.80/1.45  --dbg_dump_prop_clauses                 false
% 7.80/1.45  --dbg_dump_prop_clauses_file            -
% 7.80/1.45  --dbg_out_stat                          false
% 7.80/1.45  ------ Parsing...
% 7.80/1.45  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.80/1.45  
% 7.80/1.45  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 7.80/1.45  
% 7.80/1.45  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.80/1.45  
% 7.80/1.45  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.80/1.45  ------ Proving...
% 7.80/1.45  ------ Problem Properties 
% 7.80/1.45  
% 7.80/1.45  
% 7.80/1.45  clauses                                 36
% 7.80/1.45  conjectures                             5
% 7.80/1.45  EPR                                     6
% 7.80/1.45  Horn                                    31
% 7.80/1.45  unary                                   11
% 7.80/1.45  binary                                  6
% 7.80/1.45  lits                                    101
% 7.80/1.45  lits eq                                 24
% 7.80/1.45  fd_pure                                 0
% 7.80/1.45  fd_pseudo                               0
% 7.80/1.45  fd_cond                                 4
% 7.80/1.45  fd_pseudo_cond                          3
% 7.80/1.45  AC symbols                              0
% 7.80/1.45  
% 7.80/1.45  ------ Schedule dynamic 5 is on 
% 7.80/1.45  
% 7.80/1.45  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.80/1.45  
% 7.80/1.45  
% 7.80/1.45  ------ 
% 7.80/1.45  Current options:
% 7.80/1.45  ------ 
% 7.80/1.45  
% 7.80/1.45  ------ Input Options
% 7.80/1.45  
% 7.80/1.45  --out_options                           all
% 7.80/1.45  --tptp_safe_out                         true
% 7.80/1.45  --problem_path                          ""
% 7.80/1.45  --include_path                          ""
% 7.80/1.45  --clausifier                            res/vclausify_rel
% 7.80/1.45  --clausifier_options                    --mode clausify
% 7.80/1.45  --stdin                                 false
% 7.80/1.45  --stats_out                             all
% 7.80/1.45  
% 7.80/1.45  ------ General Options
% 7.80/1.45  
% 7.80/1.45  --fof                                   false
% 7.80/1.45  --time_out_real                         305.
% 7.80/1.45  --time_out_virtual                      -1.
% 7.80/1.45  --symbol_type_check                     false
% 7.80/1.45  --clausify_out                          false
% 7.80/1.45  --sig_cnt_out                           false
% 7.80/1.45  --trig_cnt_out                          false
% 7.80/1.45  --trig_cnt_out_tolerance                1.
% 7.80/1.45  --trig_cnt_out_sk_spl                   false
% 7.80/1.45  --abstr_cl_out                          false
% 7.80/1.45  
% 7.80/1.45  ------ Global Options
% 7.80/1.45  
% 7.80/1.45  --schedule                              default
% 7.80/1.45  --add_important_lit                     false
% 7.80/1.45  --prop_solver_per_cl                    1000
% 7.80/1.45  --min_unsat_core                        false
% 7.80/1.45  --soft_assumptions                      false
% 7.80/1.45  --soft_lemma_size                       3
% 7.80/1.45  --prop_impl_unit_size                   0
% 7.80/1.45  --prop_impl_unit                        []
% 7.80/1.45  --share_sel_clauses                     true
% 7.80/1.45  --reset_solvers                         false
% 7.80/1.45  --bc_imp_inh                            [conj_cone]
% 7.80/1.45  --conj_cone_tolerance                   3.
% 7.80/1.45  --extra_neg_conj                        none
% 7.80/1.45  --large_theory_mode                     true
% 7.80/1.45  --prolific_symb_bound                   200
% 7.80/1.45  --lt_threshold                          2000
% 7.80/1.45  --clause_weak_htbl                      true
% 7.80/1.45  --gc_record_bc_elim                     false
% 7.80/1.45  
% 7.80/1.45  ------ Preprocessing Options
% 7.80/1.45  
% 7.80/1.45  --preprocessing_flag                    true
% 7.80/1.45  --time_out_prep_mult                    0.1
% 7.80/1.45  --splitting_mode                        input
% 7.80/1.45  --splitting_grd                         true
% 7.80/1.45  --splitting_cvd                         false
% 7.80/1.45  --splitting_cvd_svl                     false
% 7.80/1.45  --splitting_nvd                         32
% 7.80/1.45  --sub_typing                            true
% 7.80/1.45  --prep_gs_sim                           true
% 7.80/1.45  --prep_unflatten                        true
% 7.80/1.45  --prep_res_sim                          true
% 7.80/1.45  --prep_upred                            true
% 7.80/1.45  --prep_sem_filter                       exhaustive
% 7.80/1.45  --prep_sem_filter_out                   false
% 7.80/1.45  --pred_elim                             true
% 7.80/1.45  --res_sim_input                         true
% 7.80/1.45  --eq_ax_congr_red                       true
% 7.80/1.45  --pure_diseq_elim                       true
% 7.80/1.45  --brand_transform                       false
% 7.80/1.45  --non_eq_to_eq                          false
% 7.80/1.45  --prep_def_merge                        true
% 7.80/1.45  --prep_def_merge_prop_impl              false
% 7.80/1.45  --prep_def_merge_mbd                    true
% 7.80/1.45  --prep_def_merge_tr_red                 false
% 7.80/1.45  --prep_def_merge_tr_cl                  false
% 7.80/1.45  --smt_preprocessing                     true
% 7.80/1.45  --smt_ac_axioms                         fast
% 7.80/1.45  --preprocessed_out                      false
% 7.80/1.45  --preprocessed_stats                    false
% 7.80/1.45  
% 7.80/1.45  ------ Abstraction refinement Options
% 7.80/1.45  
% 7.80/1.45  --abstr_ref                             []
% 7.80/1.45  --abstr_ref_prep                        false
% 7.80/1.45  --abstr_ref_until_sat                   false
% 7.80/1.45  --abstr_ref_sig_restrict                funpre
% 7.80/1.45  --abstr_ref_af_restrict_to_split_sk     false
% 7.80/1.45  --abstr_ref_under                       []
% 7.80/1.45  
% 7.80/1.45  ------ SAT Options
% 7.80/1.45  
% 7.80/1.45  --sat_mode                              false
% 7.80/1.45  --sat_fm_restart_options                ""
% 7.80/1.45  --sat_gr_def                            false
% 7.80/1.45  --sat_epr_types                         true
% 7.80/1.45  --sat_non_cyclic_types                  false
% 7.80/1.45  --sat_finite_models                     false
% 7.80/1.45  --sat_fm_lemmas                         false
% 7.80/1.45  --sat_fm_prep                           false
% 7.80/1.45  --sat_fm_uc_incr                        true
% 7.80/1.45  --sat_out_model                         small
% 7.80/1.45  --sat_out_clauses                       false
% 7.80/1.45  
% 7.80/1.45  ------ QBF Options
% 7.80/1.45  
% 7.80/1.45  --qbf_mode                              false
% 7.80/1.45  --qbf_elim_univ                         false
% 7.80/1.45  --qbf_dom_inst                          none
% 7.80/1.45  --qbf_dom_pre_inst                      false
% 7.80/1.45  --qbf_sk_in                             false
% 7.80/1.45  --qbf_pred_elim                         true
% 7.80/1.45  --qbf_split                             512
% 7.80/1.45  
% 7.80/1.45  ------ BMC1 Options
% 7.80/1.45  
% 7.80/1.45  --bmc1_incremental                      false
% 7.80/1.45  --bmc1_axioms                           reachable_all
% 7.80/1.45  --bmc1_min_bound                        0
% 7.80/1.45  --bmc1_max_bound                        -1
% 7.80/1.45  --bmc1_max_bound_default                -1
% 7.80/1.45  --bmc1_symbol_reachability              true
% 7.80/1.45  --bmc1_property_lemmas                  false
% 7.80/1.45  --bmc1_k_induction                      false
% 7.80/1.45  --bmc1_non_equiv_states                 false
% 7.80/1.45  --bmc1_deadlock                         false
% 7.80/1.45  --bmc1_ucm                              false
% 7.80/1.45  --bmc1_add_unsat_core                   none
% 7.80/1.45  --bmc1_unsat_core_children              false
% 7.80/1.45  --bmc1_unsat_core_extrapolate_axioms    false
% 7.80/1.45  --bmc1_out_stat                         full
% 7.80/1.45  --bmc1_ground_init                      false
% 7.80/1.45  --bmc1_pre_inst_next_state              false
% 7.80/1.45  --bmc1_pre_inst_state                   false
% 7.80/1.45  --bmc1_pre_inst_reach_state             false
% 7.80/1.45  --bmc1_out_unsat_core                   false
% 7.80/1.45  --bmc1_aig_witness_out                  false
% 7.80/1.45  --bmc1_verbose                          false
% 7.80/1.45  --bmc1_dump_clauses_tptp                false
% 7.80/1.45  --bmc1_dump_unsat_core_tptp             false
% 7.80/1.45  --bmc1_dump_file                        -
% 7.80/1.45  --bmc1_ucm_expand_uc_limit              128
% 7.80/1.45  --bmc1_ucm_n_expand_iterations          6
% 7.80/1.45  --bmc1_ucm_extend_mode                  1
% 7.80/1.45  --bmc1_ucm_init_mode                    2
% 7.80/1.45  --bmc1_ucm_cone_mode                    none
% 7.80/1.45  --bmc1_ucm_reduced_relation_type        0
% 7.80/1.45  --bmc1_ucm_relax_model                  4
% 7.80/1.45  --bmc1_ucm_full_tr_after_sat            true
% 7.80/1.45  --bmc1_ucm_expand_neg_assumptions       false
% 7.80/1.45  --bmc1_ucm_layered_model                none
% 7.80/1.45  --bmc1_ucm_max_lemma_size               10
% 7.80/1.45  
% 7.80/1.45  ------ AIG Options
% 7.80/1.45  
% 7.80/1.45  --aig_mode                              false
% 7.80/1.45  
% 7.80/1.45  ------ Instantiation Options
% 7.80/1.45  
% 7.80/1.45  --instantiation_flag                    true
% 7.80/1.45  --inst_sos_flag                         false
% 7.80/1.45  --inst_sos_phase                        true
% 7.80/1.45  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.80/1.45  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.80/1.45  --inst_lit_sel_side                     none
% 7.80/1.45  --inst_solver_per_active                1400
% 7.80/1.45  --inst_solver_calls_frac                1.
% 7.80/1.45  --inst_passive_queue_type               priority_queues
% 7.80/1.45  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.80/1.45  --inst_passive_queues_freq              [25;2]
% 7.80/1.45  --inst_dismatching                      true
% 7.80/1.45  --inst_eager_unprocessed_to_passive     true
% 7.80/1.45  --inst_prop_sim_given                   true
% 7.80/1.45  --inst_prop_sim_new                     false
% 7.80/1.45  --inst_subs_new                         false
% 7.80/1.45  --inst_eq_res_simp                      false
% 7.80/1.45  --inst_subs_given                       false
% 7.80/1.45  --inst_orphan_elimination               true
% 7.80/1.45  --inst_learning_loop_flag               true
% 7.80/1.45  --inst_learning_start                   3000
% 7.80/1.45  --inst_learning_factor                  2
% 7.80/1.45  --inst_start_prop_sim_after_learn       3
% 7.80/1.45  --inst_sel_renew                        solver
% 7.80/1.45  --inst_lit_activity_flag                true
% 7.80/1.45  --inst_restr_to_given                   false
% 7.80/1.45  --inst_activity_threshold               500
% 7.80/1.45  --inst_out_proof                        true
% 7.80/1.45  
% 7.80/1.45  ------ Resolution Options
% 7.80/1.45  
% 7.80/1.45  --resolution_flag                       false
% 7.80/1.45  --res_lit_sel                           adaptive
% 7.80/1.45  --res_lit_sel_side                      none
% 7.80/1.45  --res_ordering                          kbo
% 7.80/1.45  --res_to_prop_solver                    active
% 7.80/1.45  --res_prop_simpl_new                    false
% 7.80/1.45  --res_prop_simpl_given                  true
% 7.80/1.45  --res_passive_queue_type                priority_queues
% 7.80/1.45  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.80/1.45  --res_passive_queues_freq               [15;5]
% 7.80/1.45  --res_forward_subs                      full
% 7.80/1.45  --res_backward_subs                     full
% 7.80/1.45  --res_forward_subs_resolution           true
% 7.80/1.45  --res_backward_subs_resolution          true
% 7.80/1.45  --res_orphan_elimination                true
% 7.80/1.45  --res_time_limit                        2.
% 7.80/1.45  --res_out_proof                         true
% 7.80/1.45  
% 7.80/1.45  ------ Superposition Options
% 7.80/1.45  
% 7.80/1.45  --superposition_flag                    true
% 7.80/1.45  --sup_passive_queue_type                priority_queues
% 7.80/1.45  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.80/1.45  --sup_passive_queues_freq               [8;1;4]
% 7.80/1.45  --demod_completeness_check              fast
% 7.80/1.45  --demod_use_ground                      true
% 7.80/1.45  --sup_to_prop_solver                    passive
% 7.80/1.45  --sup_prop_simpl_new                    true
% 7.80/1.45  --sup_prop_simpl_given                  true
% 7.80/1.45  --sup_fun_splitting                     false
% 7.80/1.45  --sup_smt_interval                      50000
% 7.80/1.45  
% 7.80/1.45  ------ Superposition Simplification Setup
% 7.80/1.45  
% 7.80/1.45  --sup_indices_passive                   []
% 7.80/1.45  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.80/1.45  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.80/1.45  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.80/1.45  --sup_full_triv                         [TrivRules;PropSubs]
% 7.80/1.45  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.80/1.45  --sup_full_bw                           [BwDemod]
% 7.80/1.45  --sup_immed_triv                        [TrivRules]
% 7.80/1.45  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.80/1.45  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.80/1.45  --sup_immed_bw_main                     []
% 7.80/1.45  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.80/1.45  --sup_input_triv                        [Unflattening;TrivRules]
% 7.80/1.45  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.80/1.45  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.80/1.45  
% 7.80/1.45  ------ Combination Options
% 7.80/1.45  
% 7.80/1.45  --comb_res_mult                         3
% 7.80/1.45  --comb_sup_mult                         2
% 7.80/1.45  --comb_inst_mult                        10
% 7.80/1.45  
% 7.80/1.45  ------ Debug Options
% 7.80/1.45  
% 7.80/1.45  --dbg_backtrace                         false
% 7.80/1.45  --dbg_dump_prop_clauses                 false
% 7.80/1.45  --dbg_dump_prop_clauses_file            -
% 7.80/1.45  --dbg_out_stat                          false
% 7.80/1.45  
% 7.80/1.45  
% 7.80/1.45  
% 7.80/1.45  
% 7.80/1.45  ------ Proving...
% 7.80/1.45  
% 7.80/1.45  
% 7.80/1.45  % SZS status Theorem for theBenchmark.p
% 7.80/1.45  
% 7.80/1.45   Resolution empty clause
% 7.80/1.45  
% 7.80/1.45  % SZS output start CNFRefutation for theBenchmark.p
% 7.80/1.45  
% 7.80/1.45  fof(f19,conjecture,(
% 7.80/1.45    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 7.80/1.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.80/1.45  
% 7.80/1.45  fof(f20,negated_conjecture,(
% 7.80/1.45    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 7.80/1.45    inference(negated_conjecture,[],[f19])).
% 7.80/1.45  
% 7.80/1.45  fof(f42,plain,(
% 7.80/1.45    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 7.80/1.45    inference(ennf_transformation,[],[f20])).
% 7.80/1.45  
% 7.80/1.45  fof(f43,plain,(
% 7.80/1.45    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 7.80/1.45    inference(flattening,[],[f42])).
% 7.80/1.45  
% 7.80/1.45  fof(f52,plain,(
% 7.80/1.45    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 7.80/1.45    introduced(choice_axiom,[])).
% 7.80/1.45  
% 7.80/1.45  fof(f53,plain,(
% 7.80/1.45    (~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 7.80/1.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f43,f52])).
% 7.80/1.45  
% 7.80/1.45  fof(f94,plain,(
% 7.80/1.45    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 7.80/1.45    inference(cnf_transformation,[],[f53])).
% 7.80/1.45  
% 7.80/1.45  fof(f12,axiom,(
% 7.80/1.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 7.80/1.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.80/1.45  
% 7.80/1.45  fof(f32,plain,(
% 7.80/1.45    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.80/1.45    inference(ennf_transformation,[],[f12])).
% 7.80/1.45  
% 7.80/1.45  fof(f33,plain,(
% 7.80/1.45    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.80/1.45    inference(flattening,[],[f32])).
% 7.80/1.45  
% 7.80/1.45  fof(f50,plain,(
% 7.80/1.45    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.80/1.45    inference(nnf_transformation,[],[f33])).
% 7.80/1.45  
% 7.80/1.45  fof(f75,plain,(
% 7.80/1.45    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.80/1.45    inference(cnf_transformation,[],[f50])).
% 7.80/1.45  
% 7.80/1.45  fof(f9,axiom,(
% 7.80/1.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 7.80/1.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.80/1.45  
% 7.80/1.45  fof(f27,plain,(
% 7.80/1.45    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.80/1.45    inference(ennf_transformation,[],[f9])).
% 7.80/1.45  
% 7.80/1.45  fof(f69,plain,(
% 7.80/1.45    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.80/1.45    inference(cnf_transformation,[],[f27])).
% 7.80/1.45  
% 7.80/1.45  fof(f92,plain,(
% 7.80/1.45    v1_funct_2(sK1,sK0,sK0)),
% 7.80/1.45    inference(cnf_transformation,[],[f53])).
% 7.80/1.45  
% 7.80/1.45  fof(f17,axiom,(
% 7.80/1.45    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_1(X1) = k2_funct_2(X0,X1))),
% 7.80/1.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.80/1.45  
% 7.80/1.45  fof(f40,plain,(
% 7.80/1.45    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 7.80/1.45    inference(ennf_transformation,[],[f17])).
% 7.80/1.45  
% 7.80/1.45  fof(f41,plain,(
% 7.80/1.45    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 7.80/1.45    inference(flattening,[],[f40])).
% 7.80/1.45  
% 7.80/1.45  fof(f89,plain,(
% 7.80/1.45    ( ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 7.80/1.45    inference(cnf_transformation,[],[f41])).
% 7.80/1.45  
% 7.80/1.45  fof(f91,plain,(
% 7.80/1.45    v1_funct_1(sK1)),
% 7.80/1.45    inference(cnf_transformation,[],[f53])).
% 7.80/1.45  
% 7.80/1.45  fof(f93,plain,(
% 7.80/1.45    v3_funct_2(sK1,sK0,sK0)),
% 7.80/1.45    inference(cnf_transformation,[],[f53])).
% 7.80/1.45  
% 7.80/1.45  fof(f14,axiom,(
% 7.80/1.45    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 7.80/1.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.80/1.45  
% 7.80/1.45  fof(f36,plain,(
% 7.80/1.45    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 7.80/1.45    inference(ennf_transformation,[],[f14])).
% 7.80/1.45  
% 7.80/1.45  fof(f37,plain,(
% 7.80/1.45    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 7.80/1.45    inference(flattening,[],[f36])).
% 7.80/1.45  
% 7.80/1.45  fof(f86,plain,(
% 7.80/1.45    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 7.80/1.45    inference(cnf_transformation,[],[f37])).
% 7.80/1.45  
% 7.80/1.45  fof(f16,axiom,(
% 7.80/1.45    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 7.80/1.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.80/1.45  
% 7.80/1.45  fof(f38,plain,(
% 7.80/1.45    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 7.80/1.45    inference(ennf_transformation,[],[f16])).
% 7.80/1.45  
% 7.80/1.45  fof(f39,plain,(
% 7.80/1.45    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 7.80/1.45    inference(flattening,[],[f38])).
% 7.80/1.45  
% 7.80/1.45  fof(f88,plain,(
% 7.80/1.45    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 7.80/1.45    inference(cnf_transformation,[],[f39])).
% 7.80/1.45  
% 7.80/1.45  fof(f83,plain,(
% 7.80/1.45    ( ! [X0,X1] : (v1_funct_1(k2_funct_2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 7.80/1.45    inference(cnf_transformation,[],[f37])).
% 7.80/1.45  
% 7.80/1.45  fof(f7,axiom,(
% 7.80/1.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.80/1.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.80/1.45  
% 7.80/1.45  fof(f25,plain,(
% 7.80/1.45    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.80/1.45    inference(ennf_transformation,[],[f7])).
% 7.80/1.45  
% 7.80/1.45  fof(f67,plain,(
% 7.80/1.45    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.80/1.45    inference(cnf_transformation,[],[f25])).
% 7.80/1.45  
% 7.80/1.45  fof(f6,axiom,(
% 7.80/1.45    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 7.80/1.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.80/1.45  
% 7.80/1.45  fof(f23,plain,(
% 7.80/1.45    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.80/1.45    inference(ennf_transformation,[],[f6])).
% 7.80/1.45  
% 7.80/1.45  fof(f24,plain,(
% 7.80/1.45    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.80/1.45    inference(flattening,[],[f23])).
% 7.80/1.45  
% 7.80/1.45  fof(f65,plain,(
% 7.80/1.45    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.80/1.45    inference(cnf_transformation,[],[f24])).
% 7.80/1.45  
% 7.80/1.45  fof(f18,axiom,(
% 7.80/1.45    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 7.80/1.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.80/1.45  
% 7.80/1.45  fof(f90,plain,(
% 7.80/1.45    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 7.80/1.45    inference(cnf_transformation,[],[f18])).
% 7.80/1.45  
% 7.80/1.45  fof(f97,plain,(
% 7.80/1.45    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.80/1.45    inference(definition_unfolding,[],[f65,f90])).
% 7.80/1.45  
% 7.80/1.45  fof(f11,axiom,(
% 7.80/1.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 7.80/1.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.80/1.45  
% 7.80/1.45  fof(f30,plain,(
% 7.80/1.45    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.80/1.45    inference(ennf_transformation,[],[f11])).
% 7.80/1.45  
% 7.80/1.45  fof(f31,plain,(
% 7.80/1.45    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.80/1.45    inference(flattening,[],[f30])).
% 7.80/1.45  
% 7.80/1.45  fof(f73,plain,(
% 7.80/1.45    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.80/1.45    inference(cnf_transformation,[],[f31])).
% 7.80/1.45  
% 7.80/1.45  fof(f66,plain,(
% 7.80/1.45    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.80/1.45    inference(cnf_transformation,[],[f24])).
% 7.80/1.45  
% 7.80/1.45  fof(f96,plain,(
% 7.80/1.45    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.80/1.45    inference(definition_unfolding,[],[f66,f90])).
% 7.80/1.45  
% 7.80/1.45  fof(f74,plain,(
% 7.80/1.45    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.80/1.45    inference(cnf_transformation,[],[f31])).
% 7.80/1.45  
% 7.80/1.45  fof(f8,axiom,(
% 7.80/1.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.80/1.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.80/1.45  
% 7.80/1.45  fof(f22,plain,(
% 7.80/1.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 7.80/1.45    inference(pure_predicate_removal,[],[f8])).
% 7.80/1.45  
% 7.80/1.45  fof(f26,plain,(
% 7.80/1.45    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.80/1.45    inference(ennf_transformation,[],[f22])).
% 7.80/1.45  
% 7.80/1.45  fof(f68,plain,(
% 7.80/1.45    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.80/1.45    inference(cnf_transformation,[],[f26])).
% 7.80/1.45  
% 7.80/1.45  fof(f13,axiom,(
% 7.80/1.45    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 7.80/1.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.80/1.45  
% 7.80/1.45  fof(f34,plain,(
% 7.80/1.45    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 7.80/1.45    inference(ennf_transformation,[],[f13])).
% 7.80/1.45  
% 7.80/1.45  fof(f35,plain,(
% 7.80/1.45    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.80/1.45    inference(flattening,[],[f34])).
% 7.80/1.45  
% 7.80/1.45  fof(f51,plain,(
% 7.80/1.45    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.80/1.45    inference(nnf_transformation,[],[f35])).
% 7.80/1.45  
% 7.80/1.45  fof(f81,plain,(
% 7.80/1.45    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.80/1.45    inference(cnf_transformation,[],[f51])).
% 7.80/1.45  
% 7.80/1.45  fof(f95,plain,(
% 7.80/1.45    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))),
% 7.80/1.45    inference(cnf_transformation,[],[f53])).
% 7.80/1.45  
% 7.80/1.45  fof(f15,axiom,(
% 7.80/1.45    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 7.80/1.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.80/1.45  
% 7.80/1.45  fof(f21,plain,(
% 7.80/1.45    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 7.80/1.45    inference(pure_predicate_removal,[],[f15])).
% 7.80/1.45  
% 7.80/1.45  fof(f87,plain,(
% 7.80/1.45    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 7.80/1.45    inference(cnf_transformation,[],[f21])).
% 7.80/1.45  
% 7.80/1.45  fof(f10,axiom,(
% 7.80/1.45    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 7.80/1.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.80/1.45  
% 7.80/1.45  fof(f28,plain,(
% 7.80/1.45    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 7.80/1.45    inference(ennf_transformation,[],[f10])).
% 7.80/1.45  
% 7.80/1.45  fof(f29,plain,(
% 7.80/1.45    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.80/1.45    inference(flattening,[],[f28])).
% 7.80/1.45  
% 7.80/1.45  fof(f49,plain,(
% 7.80/1.45    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.80/1.45    inference(nnf_transformation,[],[f29])).
% 7.80/1.45  
% 7.80/1.45  fof(f71,plain,(
% 7.80/1.45    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.80/1.45    inference(cnf_transformation,[],[f49])).
% 7.80/1.45  
% 7.80/1.45  fof(f102,plain,(
% 7.80/1.45    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.80/1.45    inference(equality_resolution,[],[f71])).
% 7.80/1.45  
% 7.80/1.45  fof(f3,axiom,(
% 7.80/1.45    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.80/1.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.80/1.45  
% 7.80/1.45  fof(f46,plain,(
% 7.80/1.45    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.80/1.45    inference(nnf_transformation,[],[f3])).
% 7.80/1.45  
% 7.80/1.45  fof(f47,plain,(
% 7.80/1.45    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.80/1.46    inference(flattening,[],[f46])).
% 7.80/1.46  
% 7.80/1.46  fof(f60,plain,(
% 7.80/1.46    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 7.80/1.46    inference(cnf_transformation,[],[f47])).
% 7.80/1.46  
% 7.80/1.46  fof(f100,plain,(
% 7.80/1.46    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 7.80/1.46    inference(equality_resolution,[],[f60])).
% 7.80/1.46  
% 7.80/1.46  fof(f4,axiom,(
% 7.80/1.46    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.80/1.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.80/1.46  
% 7.80/1.46  fof(f48,plain,(
% 7.80/1.46    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.80/1.46    inference(nnf_transformation,[],[f4])).
% 7.80/1.46  
% 7.80/1.46  fof(f61,plain,(
% 7.80/1.46    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.80/1.46    inference(cnf_transformation,[],[f48])).
% 7.80/1.46  
% 7.80/1.46  fof(f2,axiom,(
% 7.80/1.46    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 7.80/1.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.80/1.46  
% 7.80/1.46  fof(f57,plain,(
% 7.80/1.46    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 7.80/1.46    inference(cnf_transformation,[],[f2])).
% 7.80/1.46  
% 7.80/1.46  fof(f1,axiom,(
% 7.80/1.46    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.80/1.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.80/1.46  
% 7.80/1.46  fof(f44,plain,(
% 7.80/1.46    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.80/1.46    inference(nnf_transformation,[],[f1])).
% 7.80/1.46  
% 7.80/1.46  fof(f45,plain,(
% 7.80/1.46    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.80/1.46    inference(flattening,[],[f44])).
% 7.80/1.46  
% 7.80/1.46  fof(f56,plain,(
% 7.80/1.46    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.80/1.46    inference(cnf_transformation,[],[f45])).
% 7.80/1.46  
% 7.80/1.46  fof(f5,axiom,(
% 7.80/1.46    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 7.80/1.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.80/1.46  
% 7.80/1.46  fof(f63,plain,(
% 7.80/1.46    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 7.80/1.46    inference(cnf_transformation,[],[f5])).
% 7.80/1.46  
% 7.80/1.46  fof(f59,plain,(
% 7.80/1.46    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 7.80/1.46    inference(cnf_transformation,[],[f47])).
% 7.80/1.46  
% 7.80/1.46  fof(f101,plain,(
% 7.80/1.46    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 7.80/1.46    inference(equality_resolution,[],[f59])).
% 7.80/1.46  
% 7.80/1.46  fof(f62,plain,(
% 7.80/1.46    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.80/1.46    inference(cnf_transformation,[],[f48])).
% 7.80/1.46  
% 7.80/1.46  cnf(c_37,negated_conjecture,
% 7.80/1.46      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 7.80/1.46      inference(cnf_transformation,[],[f94]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_1781,plain,
% 7.80/1.46      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 7.80/1.46      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_26,plain,
% 7.80/1.46      ( ~ v1_funct_2(X0,X1,X2)
% 7.80/1.46      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.80/1.46      | k1_relset_1(X1,X2,X0) = X1
% 7.80/1.46      | k1_xboole_0 = X2 ),
% 7.80/1.46      inference(cnf_transformation,[],[f75]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_1790,plain,
% 7.80/1.46      ( k1_relset_1(X0,X1,X2) = X0
% 7.80/1.46      | k1_xboole_0 = X1
% 7.80/1.46      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.80/1.46      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.80/1.46      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_6747,plain,
% 7.80/1.46      ( k1_relset_1(sK0,sK0,sK1) = sK0
% 7.80/1.46      | sK0 = k1_xboole_0
% 7.80/1.46      | v1_funct_2(sK1,sK0,sK0) != iProver_top ),
% 7.80/1.46      inference(superposition,[status(thm)],[c_1781,c_1790]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_15,plain,
% 7.80/1.46      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.80/1.46      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.80/1.46      inference(cnf_transformation,[],[f69]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_1799,plain,
% 7.80/1.46      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.80/1.46      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.80/1.46      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_3546,plain,
% 7.80/1.46      ( k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) ),
% 7.80/1.46      inference(superposition,[status(thm)],[c_1781,c_1799]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_6757,plain,
% 7.80/1.46      ( k1_relat_1(sK1) = sK0
% 7.80/1.46      | sK0 = k1_xboole_0
% 7.80/1.46      | v1_funct_2(sK1,sK0,sK0) != iProver_top ),
% 7.80/1.46      inference(demodulation,[status(thm)],[c_6747,c_3546]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_39,negated_conjecture,
% 7.80/1.46      ( v1_funct_2(sK1,sK0,sK0) ),
% 7.80/1.46      inference(cnf_transformation,[],[f92]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_42,plain,
% 7.80/1.46      ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
% 7.80/1.46      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_6872,plain,
% 7.80/1.46      ( sK0 = k1_xboole_0 | k1_relat_1(sK1) = sK0 ),
% 7.80/1.46      inference(global_propositional_subsumption,[status(thm)],[c_6757,c_42]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_6873,plain,
% 7.80/1.46      ( k1_relat_1(sK1) = sK0 | sK0 = k1_xboole_0 ),
% 7.80/1.46      inference(renaming,[status(thm)],[c_6872]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_35,plain,
% 7.80/1.46      ( ~ v1_funct_2(X0,X1,X1)
% 7.80/1.46      | ~ v3_funct_2(X0,X1,X1)
% 7.80/1.46      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 7.80/1.46      | ~ v1_funct_1(X0)
% 7.80/1.46      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 7.80/1.46      inference(cnf_transformation,[],[f89]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_1783,plain,
% 7.80/1.46      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
% 7.80/1.46      | v1_funct_2(X1,X0,X0) != iProver_top
% 7.80/1.46      | v3_funct_2(X1,X0,X0) != iProver_top
% 7.80/1.46      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 7.80/1.46      | v1_funct_1(X1) != iProver_top ),
% 7.80/1.46      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_10669,plain,
% 7.80/1.46      ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
% 7.80/1.46      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 7.80/1.46      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 7.80/1.46      | v1_funct_1(sK1) != iProver_top ),
% 7.80/1.46      inference(superposition,[status(thm)],[c_1781,c_1783]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_40,negated_conjecture,
% 7.80/1.46      ( v1_funct_1(sK1) ),
% 7.80/1.46      inference(cnf_transformation,[],[f91]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_38,negated_conjecture,
% 7.80/1.46      ( v3_funct_2(sK1,sK0,sK0) ),
% 7.80/1.46      inference(cnf_transformation,[],[f93]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_2168,plain,
% 7.80/1.46      ( ~ v1_funct_2(sK1,X0,X0)
% 7.80/1.46      | ~ v3_funct_2(sK1,X0,X0)
% 7.80/1.46      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 7.80/1.46      | ~ v1_funct_1(sK1)
% 7.80/1.46      | k2_funct_2(X0,sK1) = k2_funct_1(sK1) ),
% 7.80/1.46      inference(instantiation,[status(thm)],[c_35]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_2305,plain,
% 7.80/1.46      ( ~ v1_funct_2(sK1,sK0,sK0)
% 7.80/1.46      | ~ v3_funct_2(sK1,sK0,sK0)
% 7.80/1.46      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.80/1.46      | ~ v1_funct_1(sK1)
% 7.80/1.46      | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 7.80/1.46      inference(instantiation,[status(thm)],[c_2168]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_11125,plain,
% 7.80/1.46      ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 7.80/1.46      inference(global_propositional_subsumption,
% 7.80/1.46                [status(thm)],
% 7.80/1.46                [c_10669,c_40,c_39,c_38,c_37,c_2305]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_29,plain,
% 7.80/1.46      ( ~ v1_funct_2(X0,X1,X1)
% 7.80/1.46      | ~ v3_funct_2(X0,X1,X1)
% 7.80/1.46      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 7.80/1.46      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 7.80/1.46      | ~ v1_funct_1(X0) ),
% 7.80/1.46      inference(cnf_transformation,[],[f86]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_1789,plain,
% 7.80/1.46      ( v1_funct_2(X0,X1,X1) != iProver_top
% 7.80/1.46      | v3_funct_2(X0,X1,X1) != iProver_top
% 7.80/1.46      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 7.80/1.46      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) = iProver_top
% 7.80/1.46      | v1_funct_1(X0) != iProver_top ),
% 7.80/1.46      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_11146,plain,
% 7.80/1.46      ( v1_funct_2(sK1,sK0,sK0) != iProver_top
% 7.80/1.46      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 7.80/1.46      | m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 7.80/1.46      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 7.80/1.46      | v1_funct_1(sK1) != iProver_top ),
% 7.80/1.46      inference(superposition,[status(thm)],[c_11125,c_1789]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_41,plain,
% 7.80/1.46      ( v1_funct_1(sK1) = iProver_top ),
% 7.80/1.46      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_43,plain,
% 7.80/1.46      ( v3_funct_2(sK1,sK0,sK0) = iProver_top ),
% 7.80/1.46      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_44,plain,
% 7.80/1.46      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 7.80/1.46      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_11652,plain,
% 7.80/1.46      ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 7.80/1.46      inference(global_propositional_subsumption,
% 7.80/1.46                [status(thm)],
% 7.80/1.46                [c_11146,c_41,c_42,c_43,c_44]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_34,plain,
% 7.80/1.46      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.80/1.46      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.80/1.46      | ~ v1_funct_1(X0)
% 7.80/1.46      | ~ v1_funct_1(X3)
% 7.80/1.46      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 7.80/1.46      inference(cnf_transformation,[],[f88]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_1784,plain,
% 7.80/1.46      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 7.80/1.46      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 7.80/1.46      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.80/1.46      | v1_funct_1(X5) != iProver_top
% 7.80/1.46      | v1_funct_1(X4) != iProver_top ),
% 7.80/1.46      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_12237,plain,
% 7.80/1.46      ( k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1))
% 7.80/1.46      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.80/1.46      | v1_funct_1(X2) != iProver_top
% 7.80/1.46      | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
% 7.80/1.46      inference(superposition,[status(thm)],[c_11652,c_1784]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_32,plain,
% 7.80/1.46      ( ~ v1_funct_2(X0,X1,X1)
% 7.80/1.46      | ~ v3_funct_2(X0,X1,X1)
% 7.80/1.46      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 7.80/1.46      | ~ v1_funct_1(X0)
% 7.80/1.46      | v1_funct_1(k2_funct_2(X1,X0)) ),
% 7.80/1.46      inference(cnf_transformation,[],[f83]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_2153,plain,
% 7.80/1.46      ( ~ v1_funct_2(sK1,X0,X0)
% 7.80/1.46      | ~ v3_funct_2(sK1,X0,X0)
% 7.80/1.46      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 7.80/1.46      | v1_funct_1(k2_funct_2(X0,sK1))
% 7.80/1.46      | ~ v1_funct_1(sK1) ),
% 7.80/1.46      inference(instantiation,[status(thm)],[c_32]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_2302,plain,
% 7.80/1.46      ( ~ v1_funct_2(sK1,sK0,sK0)
% 7.80/1.46      | ~ v3_funct_2(sK1,sK0,sK0)
% 7.80/1.46      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.80/1.46      | v1_funct_1(k2_funct_2(sK0,sK1))
% 7.80/1.46      | ~ v1_funct_1(sK1) ),
% 7.80/1.46      inference(instantiation,[status(thm)],[c_2153]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_2303,plain,
% 7.80/1.46      ( v1_funct_2(sK1,sK0,sK0) != iProver_top
% 7.80/1.46      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 7.80/1.46      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 7.80/1.46      | v1_funct_1(k2_funct_2(sK0,sK1)) = iProver_top
% 7.80/1.46      | v1_funct_1(sK1) != iProver_top ),
% 7.80/1.46      inference(predicate_to_equality,[status(thm)],[c_2302]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_1009,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_2979,plain,
% 7.80/1.46      ( X0 != X1 | X0 = k2_funct_2(sK0,sK1) | k2_funct_2(sK0,sK1) != X1 ),
% 7.80/1.46      inference(instantiation,[status(thm)],[c_1009]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_3835,plain,
% 7.80/1.46      ( X0 = k2_funct_2(sK0,sK1)
% 7.80/1.46      | X0 != k2_funct_1(sK1)
% 7.80/1.46      | k2_funct_2(sK0,sK1) != k2_funct_1(sK1) ),
% 7.80/1.46      inference(instantiation,[status(thm)],[c_2979]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_4980,plain,
% 7.80/1.46      ( k2_funct_2(sK0,sK1) != k2_funct_1(sK1)
% 7.80/1.46      | k2_funct_1(sK1) = k2_funct_2(sK0,sK1)
% 7.80/1.46      | k2_funct_1(sK1) != k2_funct_1(sK1) ),
% 7.80/1.46      inference(instantiation,[status(thm)],[c_3835]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_1008,plain,( X0 = X0 ),theory(equality) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_4981,plain,
% 7.80/1.46      ( k2_funct_1(sK1) = k2_funct_1(sK1) ),
% 7.80/1.46      inference(instantiation,[status(thm)],[c_1008]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_1018,plain,
% 7.80/1.46      ( ~ v1_funct_1(X0) | v1_funct_1(X1) | X1 != X0 ),
% 7.80/1.46      theory(equality) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_2414,plain,
% 7.80/1.46      ( v1_funct_1(X0)
% 7.80/1.46      | ~ v1_funct_1(k2_funct_2(sK0,sK1))
% 7.80/1.46      | X0 != k2_funct_2(sK0,sK1) ),
% 7.80/1.46      inference(instantiation,[status(thm)],[c_1018]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_9601,plain,
% 7.80/1.46      ( ~ v1_funct_1(k2_funct_2(sK0,sK1))
% 7.80/1.46      | v1_funct_1(k2_funct_1(sK1))
% 7.80/1.46      | k2_funct_1(sK1) != k2_funct_2(sK0,sK1) ),
% 7.80/1.46      inference(instantiation,[status(thm)],[c_2414]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_9602,plain,
% 7.80/1.46      ( k2_funct_1(sK1) != k2_funct_2(sK0,sK1)
% 7.80/1.46      | v1_funct_1(k2_funct_2(sK0,sK1)) != iProver_top
% 7.80/1.46      | v1_funct_1(k2_funct_1(sK1)) = iProver_top ),
% 7.80/1.46      inference(predicate_to_equality,[status(thm)],[c_9601]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_19171,plain,
% 7.80/1.46      ( v1_funct_1(X2) != iProver_top
% 7.80/1.46      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.80/1.46      | k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1)) ),
% 7.80/1.46      inference(global_propositional_subsumption,
% 7.80/1.46                [status(thm)],
% 7.80/1.46                [c_12237,c_40,c_41,c_39,c_42,c_38,c_43,c_37,c_44,c_2303,
% 7.80/1.46                 c_2305,c_4980,c_4981,c_9602]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_19172,plain,
% 7.80/1.46      ( k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1))
% 7.80/1.46      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.80/1.46      | v1_funct_1(X2) != iProver_top ),
% 7.80/1.46      inference(renaming,[status(thm)],[c_19171]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_19183,plain,
% 7.80/1.46      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k5_relat_1(sK1,k2_funct_1(sK1))
% 7.80/1.46      | v1_funct_1(sK1) != iProver_top ),
% 7.80/1.46      inference(superposition,[status(thm)],[c_1781,c_19172]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_13,plain,
% 7.80/1.46      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 7.80/1.46      inference(cnf_transformation,[],[f67]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_1800,plain,
% 7.80/1.46      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.80/1.46      | v1_relat_1(X0) = iProver_top ),
% 7.80/1.46      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_2788,plain,
% 7.80/1.46      ( v1_relat_1(sK1) = iProver_top ),
% 7.80/1.46      inference(superposition,[status(thm)],[c_1781,c_1800]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_12,plain,
% 7.80/1.46      ( ~ v1_relat_1(X0)
% 7.80/1.46      | ~ v1_funct_1(X0)
% 7.80/1.46      | ~ v2_funct_1(X0)
% 7.80/1.46      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
% 7.80/1.46      inference(cnf_transformation,[],[f97]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_1801,plain,
% 7.80/1.46      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
% 7.80/1.46      | v1_relat_1(X0) != iProver_top
% 7.80/1.46      | v1_funct_1(X0) != iProver_top
% 7.80/1.46      | v2_funct_1(X0) != iProver_top ),
% 7.80/1.46      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_5612,plain,
% 7.80/1.46      ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
% 7.80/1.46      | v1_funct_1(sK1) != iProver_top
% 7.80/1.46      | v2_funct_1(sK1) != iProver_top ),
% 7.80/1.46      inference(superposition,[status(thm)],[c_2788,c_1801]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_2100,plain,
% 7.80/1.46      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.80/1.46      | v1_relat_1(sK1) ),
% 7.80/1.46      inference(instantiation,[status(thm)],[c_13]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_2206,plain,
% 7.80/1.46      ( ~ v1_relat_1(sK1)
% 7.80/1.46      | ~ v1_funct_1(sK1)
% 7.80/1.46      | ~ v2_funct_1(sK1)
% 7.80/1.46      | k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
% 7.80/1.46      inference(instantiation,[status(thm)],[c_12]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_19,plain,
% 7.80/1.46      ( ~ v3_funct_2(X0,X1,X2)
% 7.80/1.46      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.80/1.46      | ~ v1_funct_1(X0)
% 7.80/1.46      | v2_funct_1(X0) ),
% 7.80/1.46      inference(cnf_transformation,[],[f73]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_2137,plain,
% 7.80/1.46      ( ~ v3_funct_2(sK1,X0,X1)
% 7.80/1.46      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.80/1.46      | ~ v1_funct_1(sK1)
% 7.80/1.46      | v2_funct_1(sK1) ),
% 7.80/1.46      inference(instantiation,[status(thm)],[c_19]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_2249,plain,
% 7.80/1.46      ( ~ v3_funct_2(sK1,sK0,sK0)
% 7.80/1.46      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.80/1.46      | ~ v1_funct_1(sK1)
% 7.80/1.46      | v2_funct_1(sK1) ),
% 7.80/1.46      inference(instantiation,[status(thm)],[c_2137]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_5917,plain,
% 7.80/1.46      ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
% 7.80/1.46      inference(global_propositional_subsumption,
% 7.80/1.46                [status(thm)],
% 7.80/1.46                [c_5612,c_40,c_38,c_37,c_2100,c_2206,c_2249]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_19205,plain,
% 7.80/1.46      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
% 7.80/1.46      | v1_funct_1(sK1) != iProver_top ),
% 7.80/1.46      inference(light_normalisation,[status(thm)],[c_19183,c_5917]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_20207,plain,
% 7.80/1.46      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
% 7.80/1.46      inference(global_propositional_subsumption,[status(thm)],[c_19205,c_41]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_12236,plain,
% 7.80/1.46      ( k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1)
% 7.80/1.46      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.80/1.46      | v1_funct_1(X2) != iProver_top
% 7.80/1.46      | v1_funct_1(sK1) != iProver_top ),
% 7.80/1.46      inference(superposition,[status(thm)],[c_1781,c_1784]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_12717,plain,
% 7.80/1.46      ( v1_funct_1(X2) != iProver_top
% 7.80/1.46      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.80/1.46      | k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1) ),
% 7.80/1.46      inference(global_propositional_subsumption,[status(thm)],[c_12236,c_41]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_12718,plain,
% 7.80/1.46      ( k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1)
% 7.80/1.46      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.80/1.46      | v1_funct_1(X2) != iProver_top ),
% 7.80/1.46      inference(renaming,[status(thm)],[c_12717]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_12727,plain,
% 7.80/1.46      ( k1_partfun1(X0,X0,sK0,sK0,k2_funct_2(X0,X1),sK1) = k5_relat_1(k2_funct_2(X0,X1),sK1)
% 7.80/1.46      | v1_funct_2(X1,X0,X0) != iProver_top
% 7.80/1.46      | v3_funct_2(X1,X0,X0) != iProver_top
% 7.80/1.46      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 7.80/1.46      | v1_funct_1(X1) != iProver_top
% 7.80/1.46      | v1_funct_1(k2_funct_2(X0,X1)) != iProver_top ),
% 7.80/1.46      inference(superposition,[status(thm)],[c_1789,c_12718]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_1786,plain,
% 7.80/1.46      ( v1_funct_2(X0,X1,X1) != iProver_top
% 7.80/1.46      | v3_funct_2(X0,X1,X1) != iProver_top
% 7.80/1.46      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 7.80/1.46      | v1_funct_1(X0) != iProver_top
% 7.80/1.46      | v1_funct_1(k2_funct_2(X1,X0)) = iProver_top ),
% 7.80/1.46      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_14751,plain,
% 7.80/1.46      ( k1_partfun1(X0,X0,sK0,sK0,k2_funct_2(X0,X1),sK1) = k5_relat_1(k2_funct_2(X0,X1),sK1)
% 7.80/1.46      | v1_funct_2(X1,X0,X0) != iProver_top
% 7.80/1.46      | v3_funct_2(X1,X0,X0) != iProver_top
% 7.80/1.46      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 7.80/1.46      | v1_funct_1(X1) != iProver_top ),
% 7.80/1.46      inference(forward_subsumption_resolution,[status(thm)],[c_12727,c_1786]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_14758,plain,
% 7.80/1.46      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1) = k5_relat_1(k2_funct_2(sK0,sK1),sK1)
% 7.80/1.46      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 7.80/1.46      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 7.80/1.46      | v1_funct_1(sK1) != iProver_top ),
% 7.80/1.46      inference(superposition,[status(thm)],[c_1781,c_14751]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_11,plain,
% 7.80/1.46      ( ~ v1_relat_1(X0)
% 7.80/1.46      | ~ v1_funct_1(X0)
% 7.80/1.46      | ~ v2_funct_1(X0)
% 7.80/1.46      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
% 7.80/1.46      inference(cnf_transformation,[],[f96]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_1802,plain,
% 7.80/1.46      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
% 7.80/1.46      | v1_relat_1(X0) != iProver_top
% 7.80/1.46      | v1_funct_1(X0) != iProver_top
% 7.80/1.46      | v2_funct_1(X0) != iProver_top ),
% 7.80/1.46      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_5728,plain,
% 7.80/1.46      ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1))
% 7.80/1.46      | v1_funct_1(sK1) != iProver_top
% 7.80/1.46      | v2_funct_1(sK1) != iProver_top ),
% 7.80/1.46      inference(superposition,[status(thm)],[c_2788,c_1802]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_18,plain,
% 7.80/1.46      ( ~ v3_funct_2(X0,X1,X2)
% 7.80/1.46      | v2_funct_2(X0,X2)
% 7.80/1.46      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.80/1.46      | ~ v1_funct_1(X0) ),
% 7.80/1.46      inference(cnf_transformation,[],[f74]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_14,plain,
% 7.80/1.46      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 7.80/1.46      inference(cnf_transformation,[],[f68]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_28,plain,
% 7.80/1.46      ( ~ v2_funct_2(X0,X1)
% 7.80/1.46      | ~ v5_relat_1(X0,X1)
% 7.80/1.46      | ~ v1_relat_1(X0)
% 7.80/1.46      | k2_relat_1(X0) = X1 ),
% 7.80/1.46      inference(cnf_transformation,[],[f81]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_481,plain,
% 7.80/1.46      ( ~ v2_funct_2(X0,X1)
% 7.80/1.46      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 7.80/1.46      | ~ v1_relat_1(X0)
% 7.80/1.46      | k2_relat_1(X0) = X1 ),
% 7.80/1.46      inference(resolution,[status(thm)],[c_14,c_28]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_491,plain,
% 7.80/1.46      ( ~ v2_funct_2(X0,X1)
% 7.80/1.46      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 7.80/1.46      | k2_relat_1(X0) = X1 ),
% 7.80/1.46      inference(forward_subsumption_resolution,[status(thm)],[c_481,c_13]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_562,plain,
% 7.80/1.46      ( ~ v3_funct_2(X0,X1,X2)
% 7.80/1.46      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.80/1.46      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.80/1.46      | ~ v1_funct_1(X0)
% 7.80/1.46      | X3 != X0
% 7.80/1.46      | X5 != X2
% 7.80/1.46      | k2_relat_1(X3) = X5 ),
% 7.80/1.46      inference(resolution_lifted,[status(thm)],[c_18,c_491]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_563,plain,
% 7.80/1.46      ( ~ v3_funct_2(X0,X1,X2)
% 7.80/1.46      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.80/1.46      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 7.80/1.46      | ~ v1_funct_1(X0)
% 7.80/1.46      | k2_relat_1(X0) = X2 ),
% 7.80/1.46      inference(unflattening,[status(thm)],[c_562]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_1777,plain,
% 7.80/1.46      ( k2_relat_1(X0) = X1
% 7.80/1.46      | v3_funct_2(X0,X2,X1) != iProver_top
% 7.80/1.46      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
% 7.80/1.46      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
% 7.80/1.46      | v1_funct_1(X0) != iProver_top ),
% 7.80/1.46      inference(predicate_to_equality,[status(thm)],[c_563]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_2668,plain,
% 7.80/1.46      ( k2_relat_1(sK1) = sK0
% 7.80/1.46      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 7.80/1.46      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 7.80/1.46      | v1_funct_1(sK1) != iProver_top ),
% 7.80/1.46      inference(superposition,[status(thm)],[c_1781,c_1777]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_3145,plain,
% 7.80/1.46      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 7.80/1.46      | k2_relat_1(sK1) = sK0 ),
% 7.80/1.46      inference(global_propositional_subsumption,
% 7.80/1.46                [status(thm)],
% 7.80/1.46                [c_2668,c_41,c_43]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_3146,plain,
% 7.80/1.46      ( k2_relat_1(sK1) = sK0
% 7.80/1.46      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top ),
% 7.80/1.46      inference(renaming,[status(thm)],[c_3145]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_3154,plain,
% 7.80/1.46      ( k2_relat_1(sK1) = sK0 ),
% 7.80/1.46      inference(superposition,[status(thm)],[c_1781,c_3146]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_5739,plain,
% 7.80/1.46      ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
% 7.80/1.46      | v1_funct_1(sK1) != iProver_top
% 7.80/1.46      | v2_funct_1(sK1) != iProver_top ),
% 7.80/1.46      inference(light_normalisation,[status(thm)],[c_5728,c_3154]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_2250,plain,
% 7.80/1.46      ( v3_funct_2(sK1,sK0,sK0) != iProver_top
% 7.80/1.46      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 7.80/1.46      | v1_funct_1(sK1) != iProver_top
% 7.80/1.46      | v2_funct_1(sK1) = iProver_top ),
% 7.80/1.46      inference(predicate_to_equality,[status(thm)],[c_2249]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_5913,plain,
% 7.80/1.46      ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(sK0) ),
% 7.80/1.46      inference(global_propositional_subsumption,
% 7.80/1.46                [status(thm)],
% 7.80/1.46                [c_5739,c_41,c_43,c_44,c_2250]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_14784,plain,
% 7.80/1.46      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
% 7.80/1.46      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 7.80/1.46      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 7.80/1.46      | v1_funct_1(sK1) != iProver_top ),
% 7.80/1.46      inference(light_normalisation,[status(thm)],[c_14758,c_5913,c_11125]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_12730,plain,
% 7.80/1.46      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k5_relat_1(k2_funct_1(sK1),sK1)
% 7.80/1.46      | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
% 7.80/1.46      inference(superposition,[status(thm)],[c_11652,c_12718]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_12747,plain,
% 7.80/1.46      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
% 7.80/1.46      | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
% 7.80/1.46      inference(light_normalisation,[status(thm)],[c_12730,c_5913]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_14838,plain,
% 7.80/1.46      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0) ),
% 7.80/1.46      inference(global_propositional_subsumption,
% 7.80/1.46                [status(thm)],
% 7.80/1.46                [c_14784,c_40,c_41,c_39,c_42,c_38,c_43,c_37,c_44,c_2303,
% 7.80/1.46                 c_2305,c_4980,c_4981,c_9602,c_12747]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_36,negated_conjecture,
% 7.80/1.46      ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
% 7.80/1.46      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
% 7.80/1.46      inference(cnf_transformation,[],[f95]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_1782,plain,
% 7.80/1.46      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) != iProver_top
% 7.80/1.46      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) != iProver_top ),
% 7.80/1.46      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_11131,plain,
% 7.80/1.46      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) != iProver_top
% 7.80/1.46      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
% 7.80/1.46      inference(demodulation,[status(thm)],[c_11125,c_1782]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_14841,plain,
% 7.80/1.46      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top
% 7.80/1.46      | r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
% 7.80/1.46      inference(demodulation,[status(thm)],[c_14838,c_11131]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_33,plain,
% 7.80/1.46      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 7.80/1.46      inference(cnf_transformation,[],[f87]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_1785,plain,
% 7.80/1.46      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 7.80/1.46      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_16,plain,
% 7.80/1.46      ( r2_relset_1(X0,X1,X2,X2)
% 7.80/1.46      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 7.80/1.46      inference(cnf_transformation,[],[f102]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_1798,plain,
% 7.80/1.46      ( r2_relset_1(X0,X1,X2,X2) = iProver_top
% 7.80/1.46      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.80/1.46      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_2889,plain,
% 7.80/1.46      ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0)) = iProver_top ),
% 7.80/1.46      inference(superposition,[status(thm)],[c_1785,c_1798]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_15590,plain,
% 7.80/1.46      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
% 7.80/1.46      inference(forward_subsumption_resolution,[status(thm)],[c_14841,c_2889]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_20210,plain,
% 7.80/1.46      ( r2_relset_1(sK0,sK0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
% 7.80/1.46      inference(demodulation,[status(thm)],[c_20207,c_15590]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_20451,plain,
% 7.80/1.46      ( sK0 = k1_xboole_0
% 7.80/1.46      | r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
% 7.80/1.46      inference(superposition,[status(thm)],[c_6873,c_20210]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_20456,plain,
% 7.80/1.46      ( sK0 = k1_xboole_0 ),
% 7.80/1.46      inference(forward_subsumption_resolution,[status(thm)],[c_20451,c_2889]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_20457,plain,
% 7.80/1.46      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(k1_xboole_0)) != iProver_top ),
% 7.80/1.46      inference(demodulation,[status(thm)],[c_20456,c_20210]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_4,plain,
% 7.80/1.46      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 7.80/1.46      inference(cnf_transformation,[],[f100]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_2343,plain,
% 7.80/1.46      ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 7.80/1.46      inference(superposition,[status(thm)],[c_4,c_1785]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_8,plain,
% 7.80/1.46      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.80/1.46      inference(cnf_transformation,[],[f61]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_1803,plain,
% 7.80/1.46      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.80/1.46      | r1_tarski(X0,X1) = iProver_top ),
% 7.80/1.46      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_2473,plain,
% 7.80/1.46      ( r1_tarski(k6_partfun1(k1_xboole_0),k1_xboole_0) = iProver_top ),
% 7.80/1.46      inference(superposition,[status(thm)],[c_2343,c_1803]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_3,plain,
% 7.80/1.46      ( r1_tarski(k1_xboole_0,X0) ),
% 7.80/1.46      inference(cnf_transformation,[],[f57]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_1805,plain,
% 7.80/1.46      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.80/1.46      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_0,plain,
% 7.80/1.46      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.80/1.46      inference(cnf_transformation,[],[f56]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_1807,plain,
% 7.80/1.46      ( X0 = X1
% 7.80/1.46      | r1_tarski(X0,X1) != iProver_top
% 7.80/1.46      | r1_tarski(X1,X0) != iProver_top ),
% 7.80/1.46      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_4806,plain,
% 7.80/1.46      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 7.80/1.46      inference(superposition,[status(thm)],[c_1805,c_1807]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_5055,plain,
% 7.80/1.46      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 7.80/1.46      inference(superposition,[status(thm)],[c_2473,c_4806]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_20871,plain,
% 7.80/1.46      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_relat_1(sK1)),k1_xboole_0) != iProver_top ),
% 7.80/1.46      inference(light_normalisation,[status(thm)],[c_20457,c_5055]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_10,plain,
% 7.80/1.46      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.80/1.46      inference(cnf_transformation,[],[f63]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_2472,plain,
% 7.80/1.46      ( r1_tarski(sK1,k2_zfmisc_1(sK0,sK0)) = iProver_top ),
% 7.80/1.46      inference(superposition,[status(thm)],[c_1781,c_1803]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_20519,plain,
% 7.80/1.46      ( r1_tarski(sK1,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 7.80/1.46      inference(demodulation,[status(thm)],[c_20456,c_2472]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_5,plain,
% 7.80/1.46      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.80/1.46      inference(cnf_transformation,[],[f101]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_20531,plain,
% 7.80/1.46      ( r1_tarski(sK1,k1_xboole_0) = iProver_top ),
% 7.80/1.46      inference(demodulation,[status(thm)],[c_20519,c_5]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_22147,plain,
% 7.80/1.46      ( sK1 = k1_xboole_0 ),
% 7.80/1.46      inference(superposition,[status(thm)],[c_20531,c_4806]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_40671,plain,
% 7.80/1.46      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 7.80/1.46      inference(light_normalisation,
% 7.80/1.46                [status(thm)],
% 7.80/1.46                [c_20871,c_10,c_5055,c_22147]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_7,plain,
% 7.80/1.46      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.80/1.46      inference(cnf_transformation,[],[f62]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_1804,plain,
% 7.80/1.46      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 7.80/1.46      | r1_tarski(X0,X1) != iProver_top ),
% 7.80/1.46      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_2888,plain,
% 7.80/1.46      ( r2_relset_1(X0,X1,X2,X2) = iProver_top
% 7.80/1.46      | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 7.80/1.46      inference(superposition,[status(thm)],[c_1804,c_1798]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_6935,plain,
% 7.80/1.46      ( r2_relset_1(X0,X1,k1_xboole_0,k1_xboole_0) = iProver_top ),
% 7.80/1.46      inference(superposition,[status(thm)],[c_1805,c_2888]) ).
% 7.80/1.46  
% 7.80/1.46  cnf(c_40673,plain,
% 7.80/1.46      ( $false ),
% 7.80/1.46      inference(forward_subsumption_resolution,[status(thm)],[c_40671,c_6935]) ).
% 7.80/1.46  
% 7.80/1.46  
% 7.80/1.46  % SZS output end CNFRefutation for theBenchmark.p
% 7.80/1.46  
% 7.80/1.46  ------                               Statistics
% 7.80/1.46  
% 7.80/1.46  ------ General
% 7.80/1.46  
% 7.80/1.46  abstr_ref_over_cycles:                  0
% 7.80/1.46  abstr_ref_under_cycles:                 0
% 7.80/1.46  gc_basic_clause_elim:                   0
% 7.80/1.46  forced_gc_time:                         0
% 7.80/1.46  parsing_time:                           0.01
% 7.80/1.46  unif_index_cands_time:                  0.
% 7.80/1.46  unif_index_add_time:                    0.
% 7.80/1.46  orderings_time:                         0.
% 7.80/1.46  out_proof_time:                         0.018
% 7.80/1.46  total_time:                             0.997
% 7.80/1.46  num_of_symbols:                         54
% 7.80/1.46  num_of_terms:                           28948
% 7.80/1.46  
% 7.80/1.46  ------ Preprocessing
% 7.80/1.46  
% 7.80/1.46  num_of_splits:                          0
% 7.80/1.46  num_of_split_atoms:                     0
% 7.80/1.46  num_of_reused_defs:                     0
% 7.80/1.46  num_eq_ax_congr_red:                    20
% 7.80/1.46  num_of_sem_filtered_clauses:            1
% 7.80/1.46  num_of_subtypes:                        0
% 7.80/1.46  monotx_restored_types:                  0
% 7.80/1.46  sat_num_of_epr_types:                   0
% 7.80/1.46  sat_num_of_non_cyclic_types:            0
% 7.80/1.46  sat_guarded_non_collapsed_types:        0
% 7.80/1.46  num_pure_diseq_elim:                    0
% 7.80/1.46  simp_replaced_by:                       0
% 7.80/1.46  res_preprocessed:                       182
% 7.80/1.46  prep_upred:                             0
% 7.80/1.46  prep_unflattend:                        6
% 7.80/1.46  smt_new_axioms:                         0
% 7.80/1.46  pred_elim_cands:                        8
% 7.80/1.46  pred_elim:                              2
% 7.80/1.46  pred_elim_cl:                           3
% 7.80/1.46  pred_elim_cycles:                       6
% 7.80/1.46  merged_defs:                            8
% 7.80/1.46  merged_defs_ncl:                        0
% 7.80/1.46  bin_hyper_res:                          8
% 7.80/1.46  prep_cycles:                            4
% 7.80/1.46  pred_elim_time:                         0.005
% 7.80/1.46  splitting_time:                         0.
% 7.80/1.46  sem_filter_time:                        0.
% 7.80/1.46  monotx_time:                            0.001
% 7.80/1.46  subtype_inf_time:                       0.
% 7.80/1.46  
% 7.80/1.46  ------ Problem properties
% 7.80/1.46  
% 7.80/1.46  clauses:                                36
% 7.80/1.46  conjectures:                            5
% 7.80/1.46  epr:                                    6
% 7.80/1.46  horn:                                   31
% 7.80/1.46  ground:                                 7
% 7.80/1.46  unary:                                  11
% 7.80/1.46  binary:                                 6
% 7.80/1.46  lits:                                   101
% 7.80/1.46  lits_eq:                                24
% 7.80/1.46  fd_pure:                                0
% 7.80/1.46  fd_pseudo:                              0
% 7.80/1.46  fd_cond:                                4
% 7.80/1.46  fd_pseudo_cond:                         3
% 7.80/1.46  ac_symbols:                             0
% 7.80/1.46  
% 7.80/1.46  ------ Propositional Solver
% 7.80/1.46  
% 7.80/1.46  prop_solver_calls:                      32
% 7.80/1.46  prop_fast_solver_calls:                 2771
% 7.80/1.46  smt_solver_calls:                       0
% 7.80/1.46  smt_fast_solver_calls:                  0
% 7.80/1.46  prop_num_of_clauses:                    12944
% 7.80/1.46  prop_preprocess_simplified:             30111
% 7.80/1.46  prop_fo_subsumed:                       240
% 7.80/1.46  prop_solver_time:                       0.
% 7.80/1.46  smt_solver_time:                        0.
% 7.80/1.46  smt_fast_solver_time:                   0.
% 7.80/1.46  prop_fast_solver_time:                  0.
% 7.80/1.46  prop_unsat_core_time:                   0.
% 7.80/1.46  
% 7.80/1.46  ------ QBF
% 7.80/1.46  
% 7.80/1.46  qbf_q_res:                              0
% 7.80/1.46  qbf_num_tautologies:                    0
% 7.80/1.46  qbf_prep_cycles:                        0
% 7.80/1.46  
% 7.80/1.46  ------ BMC1
% 7.80/1.46  
% 7.80/1.46  bmc1_current_bound:                     -1
% 7.80/1.46  bmc1_last_solved_bound:                 -1
% 7.80/1.46  bmc1_unsat_core_size:                   -1
% 7.80/1.46  bmc1_unsat_core_parents_size:           -1
% 7.80/1.46  bmc1_merge_next_fun:                    0
% 7.80/1.46  bmc1_unsat_core_clauses_time:           0.
% 7.80/1.46  
% 7.80/1.46  ------ Instantiation
% 7.80/1.46  
% 7.80/1.46  inst_num_of_clauses:                    3723
% 7.80/1.46  inst_num_in_passive:                    2659
% 7.80/1.46  inst_num_in_active:                     1038
% 7.80/1.46  inst_num_in_unprocessed:                26
% 7.80/1.46  inst_num_of_loops:                      1760
% 7.80/1.46  inst_num_of_learning_restarts:          0
% 7.80/1.46  inst_num_moves_active_passive:          719
% 7.80/1.46  inst_lit_activity:                      0
% 7.80/1.46  inst_lit_activity_moves:                1
% 7.80/1.46  inst_num_tautologies:                   0
% 7.80/1.46  inst_num_prop_implied:                  0
% 7.80/1.46  inst_num_existing_simplified:           0
% 7.80/1.46  inst_num_eq_res_simplified:             0
% 7.80/1.46  inst_num_child_elim:                    0
% 7.80/1.46  inst_num_of_dismatching_blockings:      1522
% 7.80/1.46  inst_num_of_non_proper_insts:           5292
% 7.80/1.46  inst_num_of_duplicates:                 0
% 7.80/1.46  inst_inst_num_from_inst_to_res:         0
% 7.80/1.46  inst_dismatching_checking_time:         0.
% 7.80/1.46  
% 7.80/1.46  ------ Resolution
% 7.80/1.46  
% 7.80/1.46  res_num_of_clauses:                     0
% 7.80/1.46  res_num_in_passive:                     0
% 7.80/1.46  res_num_in_active:                      0
% 7.80/1.46  res_num_of_loops:                       186
% 7.80/1.46  res_forward_subset_subsumed:            171
% 7.80/1.46  res_backward_subset_subsumed:           8
% 7.80/1.46  res_forward_subsumed:                   0
% 7.80/1.46  res_backward_subsumed:                  0
% 7.80/1.46  res_forward_subsumption_resolution:     2
% 7.80/1.46  res_backward_subsumption_resolution:    0
% 7.80/1.46  res_clause_to_clause_subsumption:       4891
% 7.80/1.46  res_orphan_elimination:                 0
% 7.80/1.46  res_tautology_del:                      302
% 7.80/1.46  res_num_eq_res_simplified:              0
% 7.80/1.46  res_num_sel_changes:                    0
% 7.80/1.46  res_moves_from_active_to_pass:          0
% 7.80/1.46  
% 7.80/1.46  ------ Superposition
% 7.80/1.46  
% 7.80/1.46  sup_time_total:                         0.
% 7.80/1.46  sup_time_generating:                    0.
% 7.80/1.46  sup_time_sim_full:                      0.
% 7.80/1.46  sup_time_sim_immed:                     0.
% 7.80/1.46  
% 7.80/1.46  sup_num_of_clauses:                     502
% 7.80/1.46  sup_num_in_active:                      218
% 7.80/1.46  sup_num_in_passive:                     284
% 7.80/1.46  sup_num_of_loops:                       350
% 7.80/1.46  sup_fw_superposition:                   666
% 7.80/1.46  sup_bw_superposition:                   368
% 7.80/1.46  sup_immediate_simplified:               333
% 7.80/1.46  sup_given_eliminated:                   11
% 7.80/1.46  comparisons_done:                       0
% 7.80/1.46  comparisons_avoided:                    1
% 7.80/1.46  
% 7.80/1.46  ------ Simplifications
% 7.80/1.46  
% 7.80/1.46  
% 7.80/1.46  sim_fw_subset_subsumed:                 86
% 7.80/1.46  sim_bw_subset_subsumed:                 43
% 7.80/1.46  sim_fw_subsumed:                        44
% 7.80/1.46  sim_bw_subsumed:                        22
% 7.80/1.46  sim_fw_subsumption_res:                 10
% 7.80/1.46  sim_bw_subsumption_res:                 0
% 7.80/1.46  sim_tautology_del:                      1
% 7.80/1.46  sim_eq_tautology_del:                   153
% 7.80/1.46  sim_eq_res_simp:                        2
% 7.80/1.46  sim_fw_demodulated:                     99
% 7.80/1.46  sim_bw_demodulated:                     138
% 7.80/1.46  sim_light_normalised:                   233
% 7.80/1.46  sim_joinable_taut:                      0
% 7.80/1.46  sim_joinable_simp:                      0
% 7.80/1.46  sim_ac_normalised:                      0
% 7.80/1.46  sim_smt_subsumption:                    0
% 7.80/1.46  
%------------------------------------------------------------------------------
