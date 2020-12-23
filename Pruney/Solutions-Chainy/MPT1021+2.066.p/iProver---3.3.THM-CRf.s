%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:31 EST 2020

% Result     : Theorem 3.19s
% Output     : CNFRefutation 3.19s
% Verified   : 
% Statistics : Number of formulae       :  203 (3406 expanded)
%              Number of clauses        :  124 (1049 expanded)
%              Number of leaves         :   20 ( 669 expanded)
%              Depth                    :   25
%              Number of atoms          :  657 (15715 expanded)
%              Number of equality atoms :  306 (1840 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   13 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f43,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f44,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f43])).

fof(f48,plain,
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

fof(f49,plain,
    ( ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) )
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK1,sK0,sK0)
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f44,f48])).

fof(f86,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f49])).

fof(f11,axiom,(
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
    inference(ennf_transformation,[],[f11])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

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
    inference(nnf_transformation,[],[f34])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f84,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_1(X1) = k2_funct_2(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f41])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f83,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f85,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f13,axiom,(
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
    inference(ennf_transformation,[],[f13])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f78,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

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

fof(f80,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f75,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k2_funct_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f58,plain,(
    ! [X0] :
      ( k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f17,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f82,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f17])).

fof(f91,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f58,f82])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f31])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f59,plain,(
    ! [X0] :
      ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f90,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f59,f82])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f87,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f49])).

fof(f14,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f79,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f29])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f92,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f63])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f55,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f5,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f89,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f56,f82])).

fof(f54,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1261,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1270,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3715,plain,
    ( k1_relset_1(sK0,sK0,sK1) = sK0
    | sK0 = k1_xboole_0
    | v1_funct_2(sK1,sK0,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1261,c_1270])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1279,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2564,plain,
    ( k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_1261,c_1279])).

cnf(c_3720,plain,
    ( k1_relat_1(sK1) = sK0
    | sK0 = k1_xboole_0
    | v1_funct_2(sK1,sK0,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3715,c_2564])).

cnf(c_35,negated_conjecture,
    ( v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_38,plain,
    ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_4062,plain,
    ( sK0 = k1_xboole_0
    | k1_relat_1(sK1) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3720,c_38])).

cnf(c_4063,plain,
    ( k1_relat_1(sK1) = sK0
    | sK0 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_4062])).

cnf(c_31,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1263,plain,
    ( k2_funct_2(X0,X1) = k2_funct_1(X1)
    | v1_funct_2(X1,X0,X0) != iProver_top
    | v3_funct_2(X1,X0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_3490,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1261,c_1263])).

cnf(c_36,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_34,negated_conjecture,
    ( v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1624,plain,
    ( ~ v1_funct_2(sK1,X0,X0)
    | ~ v3_funct_2(sK1,X0,X0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ v1_funct_1(sK1)
    | k2_funct_2(X0,sK1) = k2_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_1802,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_1624])).

cnf(c_3998,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3490,c_36,c_35,c_34,c_33,c_1802])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1269,plain,
    ( v1_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(X0,X1,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_5999,plain,
    ( v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3998,c_1269])).

cnf(c_37,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_39,plain,
    ( v3_funct_2(sK1,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_40,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_6494,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5999,c_37,c_38,c_39,c_40])).

cnf(c_30,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1264,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_6509,plain,
    ( k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6494,c_1264])).

cnf(c_28,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_2(X1,X0)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1266,plain,
    ( v1_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(X0,X1,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_2(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_4766,plain,
    ( v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(k2_funct_2(sK0,sK1)) = iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1261,c_1266])).

cnf(c_4780,plain,
    ( v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(k2_funct_1(sK1)) = iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4766,c_3998])).

cnf(c_8934,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6509,c_37,c_38,c_39,c_4780])).

cnf(c_8935,plain,
    ( k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_8934])).

cnf(c_8945,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k5_relat_1(sK1,k2_funct_1(sK1))
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1261,c_8935])).

cnf(c_1258,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_9,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1280,plain,
    ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3558,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
    | v2_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1258,c_1280])).

cnf(c_1561,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_15,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1590,plain,
    ( ~ v3_funct_2(sK1,X0,X1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK1)
    | v2_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1702,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | v2_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_1590])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1548,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1830,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_1548])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1947,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3726,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3558,c_36,c_34,c_33,c_1561,c_1702,c_1830,c_1947])).

cnf(c_8958,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
    | v1_funct_1(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8945,c_3726])).

cnf(c_9018,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8958,c_37])).

cnf(c_4449,plain,
    ( k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1261,c_1264])).

cnf(c_4925,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4449,c_37])).

cnf(c_4926,plain,
    ( k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_4925])).

cnf(c_6003,plain,
    ( k1_partfun1(X0,X0,sK0,sK0,k2_funct_2(X0,X1),sK1) = k5_relat_1(k2_funct_2(X0,X1),sK1)
    | v1_funct_2(X1,X0,X0) != iProver_top
    | v3_funct_2(X1,X0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(k2_funct_2(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1269,c_4926])).

cnf(c_7144,plain,
    ( k1_partfun1(X0,X0,sK0,sK0,k2_funct_2(X0,X1),sK1) = k5_relat_1(k2_funct_2(X0,X1),sK1)
    | v1_funct_2(X1,X0,X0) != iProver_top
    | v3_funct_2(X1,X0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6003,c_1266])).

cnf(c_7150,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1) = k5_relat_1(k2_funct_2(sK0,sK1),sK1)
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1261,c_7144])).

cnf(c_8,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1281,plain,
    ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3565,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1))
    | v2_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1258,c_1281])).

cnf(c_14,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | v2_funct_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_24,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_411,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ v5_relat_1(X3,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X3)
    | X3 != X0
    | X4 != X2
    | k2_relat_1(X3) = X4 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_24])).

cnf(c_412,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ v5_relat_1(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(unflattening,[status(thm)],[c_411])).

cnf(c_10,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_426,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_412,c_10])).

cnf(c_1257,plain,
    ( k2_relat_1(X0) = X1
    | v3_funct_2(X0,X2,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_426])).

cnf(c_2582,plain,
    ( k2_relat_1(sK1) = sK0
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1261,c_1257])).

cnf(c_1831,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
    | v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1830])).

cnf(c_1948,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1947])).

cnf(c_3054,plain,
    ( k2_relat_1(sK1) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2582,c_37,c_39,c_40,c_1831,c_1948])).

cnf(c_3566,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
    | v2_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3565,c_3054])).

cnf(c_1703,plain,
    ( v3_funct_2(sK1,sK0,sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v2_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1702])).

cnf(c_4058,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3566,c_37,c_39,c_40,c_1703,c_1831,c_1948])).

cnf(c_7173,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7150,c_3998,c_4058])).

cnf(c_6502,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k5_relat_1(k2_funct_1(sK1),sK1)
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6494,c_4926])).

cnf(c_6576,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6502,c_4058])).

cnf(c_7212,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7173,c_37,c_38,c_39,c_4780,c_6576])).

cnf(c_32,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1262,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) != iProver_top
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_4001,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) != iProver_top
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3998,c_1262])).

cnf(c_7215,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top
    | r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7212,c_4001])).

cnf(c_29,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1265,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_12,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1278,plain,
    ( r2_relset_1(X0,X1,X2,X2) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2185,plain,
    ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1265,c_1278])).

cnf(c_7712,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7215,c_2185])).

cnf(c_9021,plain,
    ( r2_relset_1(sK0,sK0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9018,c_7712])).

cnf(c_9025,plain,
    ( sK0 = k1_xboole_0
    | r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4063,c_9021])).

cnf(c_9174,plain,
    ( sK0 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_9025,c_2185])).

cnf(c_9175,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9174,c_9021])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1283,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3057,plain,
    ( sK1 = k1_xboole_0
    | sK0 != k1_xboole_0
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3054,c_1283])).

cnf(c_3058,plain,
    ( ~ v1_relat_1(sK1)
    | sK1 = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3057])).

cnf(c_3060,plain,
    ( sK0 != k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3057,c_33,c_1830,c_1947,c_3058])).

cnf(c_3061,plain,
    ( sK1 = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_3060])).

cnf(c_9206,plain,
    ( sK1 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_9174,c_3061])).

cnf(c_9225,plain,
    ( sK1 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_9206])).

cnf(c_9368,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_relat_1(k1_xboole_0)),k6_partfun1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9175,c_9225])).

cnf(c_3,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_7,plain,
    ( k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1282,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1770,plain,
    ( k6_partfun1(X0) = k1_xboole_0
    | k1_xboole_0 != X0
    | v1_relat_1(k6_partfun1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_1282])).

cnf(c_1870,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0
    | v1_relat_1(k6_partfun1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1770])).

cnf(c_49,plain,
    ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_121,plain,
    ( v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_733,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_766,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_733])).

cnf(c_1777,plain,
    ( ~ v1_relat_1(k6_partfun1(X0))
    | k6_partfun1(X0) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1770])).

cnf(c_1779,plain,
    ( ~ v1_relat_1(k6_partfun1(k1_xboole_0))
    | k6_partfun1(k1_xboole_0) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1777])).

cnf(c_1825,plain,
    ( ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ v1_relat_1(k2_zfmisc_1(X0,X0))
    | v1_relat_1(k6_partfun1(X0)) ),
    inference(instantiation,[status(thm)],[c_1548])).

cnf(c_1827,plain,
    ( ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | v1_relat_1(k6_partfun1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_1825])).

cnf(c_2031,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1870,c_49,c_121,c_766,c_1779,c_1827])).

cnf(c_9370,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9368,c_3,c_2031])).

cnf(c_2034,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2031,c_1265])).

cnf(c_97,plain,
    ( r2_relset_1(X0,X1,X2,X2) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_99,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_97])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9370,c_2034,c_99])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:40:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.19/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.19/0.98  
% 3.19/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.19/0.98  
% 3.19/0.98  ------  iProver source info
% 3.19/0.98  
% 3.19/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.19/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.19/0.98  git: non_committed_changes: false
% 3.19/0.98  git: last_make_outside_of_git: false
% 3.19/0.98  
% 3.19/0.98  ------ 
% 3.19/0.98  
% 3.19/0.98  ------ Input Options
% 3.19/0.98  
% 3.19/0.98  --out_options                           all
% 3.19/0.98  --tptp_safe_out                         true
% 3.19/0.98  --problem_path                          ""
% 3.19/0.98  --include_path                          ""
% 3.19/0.98  --clausifier                            res/vclausify_rel
% 3.19/0.98  --clausifier_options                    --mode clausify
% 3.19/0.98  --stdin                                 false
% 3.19/0.98  --stats_out                             all
% 3.19/0.98  
% 3.19/0.98  ------ General Options
% 3.19/0.98  
% 3.19/0.98  --fof                                   false
% 3.19/0.98  --time_out_real                         305.
% 3.19/0.98  --time_out_virtual                      -1.
% 3.19/0.98  --symbol_type_check                     false
% 3.19/0.98  --clausify_out                          false
% 3.19/0.98  --sig_cnt_out                           false
% 3.19/0.98  --trig_cnt_out                          false
% 3.19/0.98  --trig_cnt_out_tolerance                1.
% 3.19/0.98  --trig_cnt_out_sk_spl                   false
% 3.19/0.98  --abstr_cl_out                          false
% 3.19/0.98  
% 3.19/0.98  ------ Global Options
% 3.19/0.98  
% 3.19/0.98  --schedule                              default
% 3.19/0.98  --add_important_lit                     false
% 3.19/0.98  --prop_solver_per_cl                    1000
% 3.19/0.98  --min_unsat_core                        false
% 3.19/0.98  --soft_assumptions                      false
% 3.19/0.98  --soft_lemma_size                       3
% 3.19/0.98  --prop_impl_unit_size                   0
% 3.19/0.98  --prop_impl_unit                        []
% 3.19/0.98  --share_sel_clauses                     true
% 3.19/0.98  --reset_solvers                         false
% 3.19/0.98  --bc_imp_inh                            [conj_cone]
% 3.19/0.98  --conj_cone_tolerance                   3.
% 3.19/0.98  --extra_neg_conj                        none
% 3.19/0.98  --large_theory_mode                     true
% 3.19/0.98  --prolific_symb_bound                   200
% 3.19/0.98  --lt_threshold                          2000
% 3.19/0.98  --clause_weak_htbl                      true
% 3.19/0.98  --gc_record_bc_elim                     false
% 3.19/0.98  
% 3.19/0.98  ------ Preprocessing Options
% 3.19/0.98  
% 3.19/0.98  --preprocessing_flag                    true
% 3.19/0.98  --time_out_prep_mult                    0.1
% 3.19/0.98  --splitting_mode                        input
% 3.19/0.98  --splitting_grd                         true
% 3.19/0.98  --splitting_cvd                         false
% 3.19/0.98  --splitting_cvd_svl                     false
% 3.19/0.98  --splitting_nvd                         32
% 3.19/0.98  --sub_typing                            true
% 3.19/0.98  --prep_gs_sim                           true
% 3.19/0.98  --prep_unflatten                        true
% 3.19/0.98  --prep_res_sim                          true
% 3.19/0.98  --prep_upred                            true
% 3.19/0.98  --prep_sem_filter                       exhaustive
% 3.19/0.98  --prep_sem_filter_out                   false
% 3.19/0.98  --pred_elim                             true
% 3.19/0.98  --res_sim_input                         true
% 3.19/0.98  --eq_ax_congr_red                       true
% 3.19/0.98  --pure_diseq_elim                       true
% 3.19/0.98  --brand_transform                       false
% 3.19/0.98  --non_eq_to_eq                          false
% 3.19/0.98  --prep_def_merge                        true
% 3.19/0.98  --prep_def_merge_prop_impl              false
% 3.19/0.98  --prep_def_merge_mbd                    true
% 3.19/0.98  --prep_def_merge_tr_red                 false
% 3.19/0.98  --prep_def_merge_tr_cl                  false
% 3.19/0.98  --smt_preprocessing                     true
% 3.19/0.98  --smt_ac_axioms                         fast
% 3.19/0.98  --preprocessed_out                      false
% 3.19/0.98  --preprocessed_stats                    false
% 3.19/0.98  
% 3.19/0.98  ------ Abstraction refinement Options
% 3.19/0.98  
% 3.19/0.98  --abstr_ref                             []
% 3.19/0.98  --abstr_ref_prep                        false
% 3.19/0.98  --abstr_ref_until_sat                   false
% 3.19/0.98  --abstr_ref_sig_restrict                funpre
% 3.19/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.19/0.98  --abstr_ref_under                       []
% 3.19/0.98  
% 3.19/0.98  ------ SAT Options
% 3.19/0.98  
% 3.19/0.98  --sat_mode                              false
% 3.19/0.98  --sat_fm_restart_options                ""
% 3.19/0.98  --sat_gr_def                            false
% 3.19/0.98  --sat_epr_types                         true
% 3.19/0.98  --sat_non_cyclic_types                  false
% 3.19/0.98  --sat_finite_models                     false
% 3.19/0.98  --sat_fm_lemmas                         false
% 3.19/0.98  --sat_fm_prep                           false
% 3.19/0.98  --sat_fm_uc_incr                        true
% 3.19/0.98  --sat_out_model                         small
% 3.19/0.98  --sat_out_clauses                       false
% 3.19/0.98  
% 3.19/0.98  ------ QBF Options
% 3.19/0.98  
% 3.19/0.98  --qbf_mode                              false
% 3.19/0.98  --qbf_elim_univ                         false
% 3.19/0.98  --qbf_dom_inst                          none
% 3.19/0.98  --qbf_dom_pre_inst                      false
% 3.19/0.98  --qbf_sk_in                             false
% 3.19/0.98  --qbf_pred_elim                         true
% 3.19/0.98  --qbf_split                             512
% 3.19/0.98  
% 3.19/0.98  ------ BMC1 Options
% 3.19/0.98  
% 3.19/0.98  --bmc1_incremental                      false
% 3.19/0.98  --bmc1_axioms                           reachable_all
% 3.19/0.98  --bmc1_min_bound                        0
% 3.19/0.98  --bmc1_max_bound                        -1
% 3.19/0.98  --bmc1_max_bound_default                -1
% 3.19/0.98  --bmc1_symbol_reachability              true
% 3.19/0.98  --bmc1_property_lemmas                  false
% 3.19/0.98  --bmc1_k_induction                      false
% 3.19/0.98  --bmc1_non_equiv_states                 false
% 3.19/0.98  --bmc1_deadlock                         false
% 3.19/0.98  --bmc1_ucm                              false
% 3.19/0.98  --bmc1_add_unsat_core                   none
% 3.19/0.98  --bmc1_unsat_core_children              false
% 3.19/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.19/0.98  --bmc1_out_stat                         full
% 3.19/0.98  --bmc1_ground_init                      false
% 3.19/0.98  --bmc1_pre_inst_next_state              false
% 3.19/0.98  --bmc1_pre_inst_state                   false
% 3.19/0.98  --bmc1_pre_inst_reach_state             false
% 3.19/0.98  --bmc1_out_unsat_core                   false
% 3.19/0.98  --bmc1_aig_witness_out                  false
% 3.19/0.98  --bmc1_verbose                          false
% 3.19/0.98  --bmc1_dump_clauses_tptp                false
% 3.19/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.19/0.98  --bmc1_dump_file                        -
% 3.19/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.19/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.19/0.98  --bmc1_ucm_extend_mode                  1
% 3.19/0.98  --bmc1_ucm_init_mode                    2
% 3.19/0.98  --bmc1_ucm_cone_mode                    none
% 3.19/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.19/0.98  --bmc1_ucm_relax_model                  4
% 3.19/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.19/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.19/0.98  --bmc1_ucm_layered_model                none
% 3.19/0.98  --bmc1_ucm_max_lemma_size               10
% 3.19/0.98  
% 3.19/0.98  ------ AIG Options
% 3.19/0.98  
% 3.19/0.98  --aig_mode                              false
% 3.19/0.98  
% 3.19/0.98  ------ Instantiation Options
% 3.19/0.98  
% 3.19/0.98  --instantiation_flag                    true
% 3.19/0.98  --inst_sos_flag                         false
% 3.19/0.98  --inst_sos_phase                        true
% 3.19/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.19/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.19/0.98  --inst_lit_sel_side                     num_symb
% 3.19/0.98  --inst_solver_per_active                1400
% 3.19/0.98  --inst_solver_calls_frac                1.
% 3.19/0.98  --inst_passive_queue_type               priority_queues
% 3.19/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.19/0.98  --inst_passive_queues_freq              [25;2]
% 3.19/0.98  --inst_dismatching                      true
% 3.19/0.98  --inst_eager_unprocessed_to_passive     true
% 3.19/0.98  --inst_prop_sim_given                   true
% 3.19/0.98  --inst_prop_sim_new                     false
% 3.19/0.98  --inst_subs_new                         false
% 3.19/0.98  --inst_eq_res_simp                      false
% 3.19/0.98  --inst_subs_given                       false
% 3.19/0.98  --inst_orphan_elimination               true
% 3.19/0.98  --inst_learning_loop_flag               true
% 3.19/0.98  --inst_learning_start                   3000
% 3.19/0.98  --inst_learning_factor                  2
% 3.19/0.98  --inst_start_prop_sim_after_learn       3
% 3.19/0.98  --inst_sel_renew                        solver
% 3.19/0.98  --inst_lit_activity_flag                true
% 3.19/0.98  --inst_restr_to_given                   false
% 3.19/0.98  --inst_activity_threshold               500
% 3.19/0.98  --inst_out_proof                        true
% 3.19/0.98  
% 3.19/0.98  ------ Resolution Options
% 3.19/0.98  
% 3.19/0.98  --resolution_flag                       true
% 3.19/0.98  --res_lit_sel                           adaptive
% 3.19/0.98  --res_lit_sel_side                      none
% 3.19/0.98  --res_ordering                          kbo
% 3.19/0.98  --res_to_prop_solver                    active
% 3.19/0.98  --res_prop_simpl_new                    false
% 3.19/0.98  --res_prop_simpl_given                  true
% 3.19/0.98  --res_passive_queue_type                priority_queues
% 3.19/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.19/0.98  --res_passive_queues_freq               [15;5]
% 3.19/0.98  --res_forward_subs                      full
% 3.19/0.98  --res_backward_subs                     full
% 3.19/0.98  --res_forward_subs_resolution           true
% 3.19/0.98  --res_backward_subs_resolution          true
% 3.19/0.98  --res_orphan_elimination                true
% 3.19/0.98  --res_time_limit                        2.
% 3.19/0.98  --res_out_proof                         true
% 3.19/0.98  
% 3.19/0.98  ------ Superposition Options
% 3.19/0.98  
% 3.19/0.98  --superposition_flag                    true
% 3.19/0.98  --sup_passive_queue_type                priority_queues
% 3.19/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.19/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.19/0.98  --demod_completeness_check              fast
% 3.19/0.98  --demod_use_ground                      true
% 3.19/0.98  --sup_to_prop_solver                    passive
% 3.19/0.98  --sup_prop_simpl_new                    true
% 3.19/0.98  --sup_prop_simpl_given                  true
% 3.19/0.98  --sup_fun_splitting                     false
% 3.19/0.98  --sup_smt_interval                      50000
% 3.19/0.98  
% 3.19/0.98  ------ Superposition Simplification Setup
% 3.19/0.98  
% 3.19/0.98  --sup_indices_passive                   []
% 3.19/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.19/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.19/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.19/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.19/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.19/0.98  --sup_full_bw                           [BwDemod]
% 3.19/0.98  --sup_immed_triv                        [TrivRules]
% 3.19/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.19/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.19/0.98  --sup_immed_bw_main                     []
% 3.19/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.19/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.19/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.19/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.19/0.98  
% 3.19/0.98  ------ Combination Options
% 3.19/0.98  
% 3.19/0.98  --comb_res_mult                         3
% 3.19/0.98  --comb_sup_mult                         2
% 3.19/0.98  --comb_inst_mult                        10
% 3.19/0.98  
% 3.19/0.98  ------ Debug Options
% 3.19/0.98  
% 3.19/0.98  --dbg_backtrace                         false
% 3.19/0.98  --dbg_dump_prop_clauses                 false
% 3.19/0.98  --dbg_dump_prop_clauses_file            -
% 3.19/0.98  --dbg_out_stat                          false
% 3.19/0.98  ------ Parsing...
% 3.19/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.19/0.98  
% 3.19/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.19/0.98  
% 3.19/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.19/0.98  
% 3.19/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.19/0.98  ------ Proving...
% 3.19/0.98  ------ Problem Properties 
% 3.19/0.98  
% 3.19/0.98  
% 3.19/0.98  clauses                                 33
% 3.19/0.98  conjectures                             5
% 3.19/0.98  EPR                                     3
% 3.19/0.98  Horn                                    29
% 3.19/0.98  unary                                   10
% 3.19/0.98  binary                                  3
% 3.19/0.98  lits                                    97
% 3.19/0.98  lits eq                                 24
% 3.19/0.98  fd_pure                                 0
% 3.19/0.98  fd_pseudo                               0
% 3.19/0.98  fd_cond                                 5
% 3.19/0.98  fd_pseudo_cond                          2
% 3.19/0.98  AC symbols                              0
% 3.19/0.98  
% 3.19/0.98  ------ Schedule dynamic 5 is on 
% 3.19/0.98  
% 3.19/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.19/0.98  
% 3.19/0.98  
% 3.19/0.98  ------ 
% 3.19/0.98  Current options:
% 3.19/0.98  ------ 
% 3.19/0.98  
% 3.19/0.98  ------ Input Options
% 3.19/0.98  
% 3.19/0.98  --out_options                           all
% 3.19/0.98  --tptp_safe_out                         true
% 3.19/0.98  --problem_path                          ""
% 3.19/0.98  --include_path                          ""
% 3.19/0.98  --clausifier                            res/vclausify_rel
% 3.19/0.98  --clausifier_options                    --mode clausify
% 3.19/0.98  --stdin                                 false
% 3.19/0.98  --stats_out                             all
% 3.19/0.98  
% 3.19/0.98  ------ General Options
% 3.19/0.98  
% 3.19/0.98  --fof                                   false
% 3.19/0.98  --time_out_real                         305.
% 3.19/0.98  --time_out_virtual                      -1.
% 3.19/0.98  --symbol_type_check                     false
% 3.19/0.98  --clausify_out                          false
% 3.19/0.98  --sig_cnt_out                           false
% 3.19/0.98  --trig_cnt_out                          false
% 3.19/0.98  --trig_cnt_out_tolerance                1.
% 3.19/0.98  --trig_cnt_out_sk_spl                   false
% 3.19/0.98  --abstr_cl_out                          false
% 3.19/0.98  
% 3.19/0.98  ------ Global Options
% 3.19/0.98  
% 3.19/0.98  --schedule                              default
% 3.19/0.98  --add_important_lit                     false
% 3.19/0.98  --prop_solver_per_cl                    1000
% 3.19/0.98  --min_unsat_core                        false
% 3.19/0.98  --soft_assumptions                      false
% 3.19/0.98  --soft_lemma_size                       3
% 3.19/0.98  --prop_impl_unit_size                   0
% 3.19/0.98  --prop_impl_unit                        []
% 3.19/0.98  --share_sel_clauses                     true
% 3.19/0.98  --reset_solvers                         false
% 3.19/0.98  --bc_imp_inh                            [conj_cone]
% 3.19/0.98  --conj_cone_tolerance                   3.
% 3.19/0.98  --extra_neg_conj                        none
% 3.19/0.98  --large_theory_mode                     true
% 3.19/0.98  --prolific_symb_bound                   200
% 3.19/0.98  --lt_threshold                          2000
% 3.19/0.98  --clause_weak_htbl                      true
% 3.19/0.98  --gc_record_bc_elim                     false
% 3.19/0.98  
% 3.19/0.98  ------ Preprocessing Options
% 3.19/0.98  
% 3.19/0.98  --preprocessing_flag                    true
% 3.19/0.98  --time_out_prep_mult                    0.1
% 3.19/0.98  --splitting_mode                        input
% 3.19/0.98  --splitting_grd                         true
% 3.19/0.98  --splitting_cvd                         false
% 3.19/0.98  --splitting_cvd_svl                     false
% 3.19/0.98  --splitting_nvd                         32
% 3.19/0.98  --sub_typing                            true
% 3.19/0.98  --prep_gs_sim                           true
% 3.19/0.98  --prep_unflatten                        true
% 3.19/0.98  --prep_res_sim                          true
% 3.19/0.98  --prep_upred                            true
% 3.19/0.98  --prep_sem_filter                       exhaustive
% 3.19/0.98  --prep_sem_filter_out                   false
% 3.19/0.98  --pred_elim                             true
% 3.19/0.98  --res_sim_input                         true
% 3.19/0.98  --eq_ax_congr_red                       true
% 3.19/0.98  --pure_diseq_elim                       true
% 3.19/0.98  --brand_transform                       false
% 3.19/0.98  --non_eq_to_eq                          false
% 3.19/0.98  --prep_def_merge                        true
% 3.19/0.98  --prep_def_merge_prop_impl              false
% 3.19/0.98  --prep_def_merge_mbd                    true
% 3.19/0.98  --prep_def_merge_tr_red                 false
% 3.19/0.98  --prep_def_merge_tr_cl                  false
% 3.19/0.98  --smt_preprocessing                     true
% 3.19/0.98  --smt_ac_axioms                         fast
% 3.19/0.98  --preprocessed_out                      false
% 3.19/0.98  --preprocessed_stats                    false
% 3.19/0.98  
% 3.19/0.98  ------ Abstraction refinement Options
% 3.19/0.98  
% 3.19/0.98  --abstr_ref                             []
% 3.19/0.98  --abstr_ref_prep                        false
% 3.19/0.98  --abstr_ref_until_sat                   false
% 3.19/0.98  --abstr_ref_sig_restrict                funpre
% 3.19/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.19/0.98  --abstr_ref_under                       []
% 3.19/0.98  
% 3.19/0.98  ------ SAT Options
% 3.19/0.98  
% 3.19/0.98  --sat_mode                              false
% 3.19/0.98  --sat_fm_restart_options                ""
% 3.19/0.98  --sat_gr_def                            false
% 3.19/0.98  --sat_epr_types                         true
% 3.19/0.98  --sat_non_cyclic_types                  false
% 3.19/0.98  --sat_finite_models                     false
% 3.19/0.98  --sat_fm_lemmas                         false
% 3.19/0.98  --sat_fm_prep                           false
% 3.19/0.98  --sat_fm_uc_incr                        true
% 3.19/0.98  --sat_out_model                         small
% 3.19/0.98  --sat_out_clauses                       false
% 3.19/0.98  
% 3.19/0.98  ------ QBF Options
% 3.19/0.98  
% 3.19/0.98  --qbf_mode                              false
% 3.19/0.98  --qbf_elim_univ                         false
% 3.19/0.98  --qbf_dom_inst                          none
% 3.19/0.98  --qbf_dom_pre_inst                      false
% 3.19/0.98  --qbf_sk_in                             false
% 3.19/0.98  --qbf_pred_elim                         true
% 3.19/0.98  --qbf_split                             512
% 3.19/0.98  
% 3.19/0.98  ------ BMC1 Options
% 3.19/0.98  
% 3.19/0.98  --bmc1_incremental                      false
% 3.19/0.98  --bmc1_axioms                           reachable_all
% 3.19/0.98  --bmc1_min_bound                        0
% 3.19/0.98  --bmc1_max_bound                        -1
% 3.19/0.98  --bmc1_max_bound_default                -1
% 3.19/0.98  --bmc1_symbol_reachability              true
% 3.19/0.98  --bmc1_property_lemmas                  false
% 3.19/0.98  --bmc1_k_induction                      false
% 3.19/0.98  --bmc1_non_equiv_states                 false
% 3.19/0.98  --bmc1_deadlock                         false
% 3.19/0.98  --bmc1_ucm                              false
% 3.19/0.98  --bmc1_add_unsat_core                   none
% 3.19/0.98  --bmc1_unsat_core_children              false
% 3.19/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.19/0.98  --bmc1_out_stat                         full
% 3.19/0.98  --bmc1_ground_init                      false
% 3.19/0.98  --bmc1_pre_inst_next_state              false
% 3.19/0.98  --bmc1_pre_inst_state                   false
% 3.19/0.98  --bmc1_pre_inst_reach_state             false
% 3.19/0.98  --bmc1_out_unsat_core                   false
% 3.19/0.98  --bmc1_aig_witness_out                  false
% 3.19/0.98  --bmc1_verbose                          false
% 3.19/0.98  --bmc1_dump_clauses_tptp                false
% 3.19/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.19/0.98  --bmc1_dump_file                        -
% 3.19/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.19/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.19/0.98  --bmc1_ucm_extend_mode                  1
% 3.19/0.98  --bmc1_ucm_init_mode                    2
% 3.19/0.98  --bmc1_ucm_cone_mode                    none
% 3.19/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.19/0.98  --bmc1_ucm_relax_model                  4
% 3.19/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.19/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.19/0.98  --bmc1_ucm_layered_model                none
% 3.19/0.98  --bmc1_ucm_max_lemma_size               10
% 3.19/0.98  
% 3.19/0.98  ------ AIG Options
% 3.19/0.98  
% 3.19/0.98  --aig_mode                              false
% 3.19/0.98  
% 3.19/0.98  ------ Instantiation Options
% 3.19/0.98  
% 3.19/0.98  --instantiation_flag                    true
% 3.19/0.98  --inst_sos_flag                         false
% 3.19/0.98  --inst_sos_phase                        true
% 3.19/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.19/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.19/0.98  --inst_lit_sel_side                     none
% 3.19/0.98  --inst_solver_per_active                1400
% 3.19/0.98  --inst_solver_calls_frac                1.
% 3.19/0.98  --inst_passive_queue_type               priority_queues
% 3.19/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.19/0.98  --inst_passive_queues_freq              [25;2]
% 3.19/0.98  --inst_dismatching                      true
% 3.19/0.98  --inst_eager_unprocessed_to_passive     true
% 3.19/0.98  --inst_prop_sim_given                   true
% 3.19/0.98  --inst_prop_sim_new                     false
% 3.19/0.98  --inst_subs_new                         false
% 3.19/0.98  --inst_eq_res_simp                      false
% 3.19/0.98  --inst_subs_given                       false
% 3.19/0.98  --inst_orphan_elimination               true
% 3.19/0.98  --inst_learning_loop_flag               true
% 3.19/0.98  --inst_learning_start                   3000
% 3.19/0.98  --inst_learning_factor                  2
% 3.19/0.98  --inst_start_prop_sim_after_learn       3
% 3.19/0.98  --inst_sel_renew                        solver
% 3.19/0.98  --inst_lit_activity_flag                true
% 3.19/0.98  --inst_restr_to_given                   false
% 3.19/0.98  --inst_activity_threshold               500
% 3.19/0.98  --inst_out_proof                        true
% 3.19/0.98  
% 3.19/0.98  ------ Resolution Options
% 3.19/0.98  
% 3.19/0.98  --resolution_flag                       false
% 3.19/0.98  --res_lit_sel                           adaptive
% 3.19/0.98  --res_lit_sel_side                      none
% 3.19/0.98  --res_ordering                          kbo
% 3.19/0.98  --res_to_prop_solver                    active
% 3.19/0.98  --res_prop_simpl_new                    false
% 3.19/0.98  --res_prop_simpl_given                  true
% 3.19/0.98  --res_passive_queue_type                priority_queues
% 3.19/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.19/0.98  --res_passive_queues_freq               [15;5]
% 3.19/0.98  --res_forward_subs                      full
% 3.19/0.98  --res_backward_subs                     full
% 3.19/0.98  --res_forward_subs_resolution           true
% 3.19/0.98  --res_backward_subs_resolution          true
% 3.19/0.98  --res_orphan_elimination                true
% 3.19/0.98  --res_time_limit                        2.
% 3.19/0.98  --res_out_proof                         true
% 3.19/0.98  
% 3.19/0.98  ------ Superposition Options
% 3.19/0.98  
% 3.19/0.98  --superposition_flag                    true
% 3.19/0.98  --sup_passive_queue_type                priority_queues
% 3.19/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.19/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.19/0.98  --demod_completeness_check              fast
% 3.19/0.98  --demod_use_ground                      true
% 3.19/0.98  --sup_to_prop_solver                    passive
% 3.19/0.98  --sup_prop_simpl_new                    true
% 3.19/0.98  --sup_prop_simpl_given                  true
% 3.19/0.98  --sup_fun_splitting                     false
% 3.19/0.98  --sup_smt_interval                      50000
% 3.19/0.98  
% 3.19/0.98  ------ Superposition Simplification Setup
% 3.19/0.98  
% 3.19/0.98  --sup_indices_passive                   []
% 3.19/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.19/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.19/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.19/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.19/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.19/0.98  --sup_full_bw                           [BwDemod]
% 3.19/0.98  --sup_immed_triv                        [TrivRules]
% 3.19/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.19/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.19/0.98  --sup_immed_bw_main                     []
% 3.19/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.19/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.19/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.19/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.19/0.98  
% 3.19/0.98  ------ Combination Options
% 3.19/0.98  
% 3.19/0.98  --comb_res_mult                         3
% 3.19/0.98  --comb_sup_mult                         2
% 3.19/0.98  --comb_inst_mult                        10
% 3.19/0.98  
% 3.19/0.98  ------ Debug Options
% 3.19/0.98  
% 3.19/0.98  --dbg_backtrace                         false
% 3.19/0.98  --dbg_dump_prop_clauses                 false
% 3.19/0.98  --dbg_dump_prop_clauses_file            -
% 3.19/0.98  --dbg_out_stat                          false
% 3.19/0.98  
% 3.19/0.98  
% 3.19/0.98  
% 3.19/0.98  
% 3.19/0.98  ------ Proving...
% 3.19/0.98  
% 3.19/0.98  
% 3.19/0.98  % SZS status Theorem for theBenchmark.p
% 3.19/0.98  
% 3.19/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.19/0.98  
% 3.19/0.98  fof(f18,conjecture,(
% 3.19/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 3.19/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/0.98  
% 3.19/0.98  fof(f19,negated_conjecture,(
% 3.19/0.98    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 3.19/0.98    inference(negated_conjecture,[],[f18])).
% 3.19/0.98  
% 3.19/0.98  fof(f43,plain,(
% 3.19/0.98    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 3.19/0.98    inference(ennf_transformation,[],[f19])).
% 3.19/0.98  
% 3.19/0.98  fof(f44,plain,(
% 3.19/0.98    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 3.19/0.98    inference(flattening,[],[f43])).
% 3.19/0.98  
% 3.19/0.98  fof(f48,plain,(
% 3.19/0.98    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 3.19/0.98    introduced(choice_axiom,[])).
% 3.19/0.98  
% 3.19/0.98  fof(f49,plain,(
% 3.19/0.98    (~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 3.19/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f44,f48])).
% 3.19/0.98  
% 3.19/0.98  fof(f86,plain,(
% 3.19/0.98    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.19/0.98    inference(cnf_transformation,[],[f49])).
% 3.19/0.98  
% 3.19/0.98  fof(f11,axiom,(
% 3.19/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.19/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/0.98  
% 3.19/0.98  fof(f33,plain,(
% 3.19/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.19/0.98    inference(ennf_transformation,[],[f11])).
% 3.19/0.98  
% 3.19/0.98  fof(f34,plain,(
% 3.19/0.98    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.19/0.98    inference(flattening,[],[f33])).
% 3.19/0.98  
% 3.19/0.98  fof(f46,plain,(
% 3.19/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.19/0.98    inference(nnf_transformation,[],[f34])).
% 3.19/0.98  
% 3.19/0.98  fof(f67,plain,(
% 3.19/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.19/0.98    inference(cnf_transformation,[],[f46])).
% 3.19/0.98  
% 3.19/0.98  fof(f8,axiom,(
% 3.19/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.19/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/0.98  
% 3.19/0.98  fof(f28,plain,(
% 3.19/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.19/0.98    inference(ennf_transformation,[],[f8])).
% 3.19/0.98  
% 3.19/0.98  fof(f61,plain,(
% 3.19/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.19/0.98    inference(cnf_transformation,[],[f28])).
% 3.19/0.98  
% 3.19/0.98  fof(f84,plain,(
% 3.19/0.98    v1_funct_2(sK1,sK0,sK0)),
% 3.19/0.98    inference(cnf_transformation,[],[f49])).
% 3.19/0.98  
% 3.19/0.98  fof(f16,axiom,(
% 3.19/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_1(X1) = k2_funct_2(X0,X1))),
% 3.19/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/0.98  
% 3.19/0.98  fof(f41,plain,(
% 3.19/0.98    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.19/0.98    inference(ennf_transformation,[],[f16])).
% 3.19/0.98  
% 3.19/0.98  fof(f42,plain,(
% 3.19/0.98    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.19/0.98    inference(flattening,[],[f41])).
% 3.19/0.98  
% 3.19/0.98  fof(f81,plain,(
% 3.19/0.98    ( ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.19/0.98    inference(cnf_transformation,[],[f42])).
% 3.19/0.98  
% 3.19/0.98  fof(f83,plain,(
% 3.19/0.98    v1_funct_1(sK1)),
% 3.19/0.98    inference(cnf_transformation,[],[f49])).
% 3.19/0.98  
% 3.19/0.98  fof(f85,plain,(
% 3.19/0.98    v3_funct_2(sK1,sK0,sK0)),
% 3.19/0.98    inference(cnf_transformation,[],[f49])).
% 3.19/0.98  
% 3.19/0.98  fof(f13,axiom,(
% 3.19/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 3.19/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/0.98  
% 3.19/0.98  fof(f37,plain,(
% 3.19/0.98    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.19/0.98    inference(ennf_transformation,[],[f13])).
% 3.19/0.98  
% 3.19/0.98  fof(f38,plain,(
% 3.19/0.98    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.19/0.98    inference(flattening,[],[f37])).
% 3.19/0.98  
% 3.19/0.98  fof(f78,plain,(
% 3.19/0.98    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.19/0.98    inference(cnf_transformation,[],[f38])).
% 3.19/0.98  
% 3.19/0.98  fof(f15,axiom,(
% 3.19/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.19/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/0.98  
% 3.19/0.98  fof(f39,plain,(
% 3.19/0.98    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.19/0.98    inference(ennf_transformation,[],[f15])).
% 3.19/0.98  
% 3.19/0.98  fof(f40,plain,(
% 3.19/0.98    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.19/0.98    inference(flattening,[],[f39])).
% 3.19/0.98  
% 3.19/0.98  fof(f80,plain,(
% 3.19/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.19/0.98    inference(cnf_transformation,[],[f40])).
% 3.19/0.98  
% 3.19/0.98  fof(f75,plain,(
% 3.19/0.98    ( ! [X0,X1] : (v1_funct_1(k2_funct_2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.19/0.98    inference(cnf_transformation,[],[f38])).
% 3.19/0.98  
% 3.19/0.98  fof(f6,axiom,(
% 3.19/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)))))),
% 3.19/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/0.98  
% 3.19/0.98  fof(f25,plain,(
% 3.19/0.98    ! [X0] : (((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.19/0.98    inference(ennf_transformation,[],[f6])).
% 3.19/0.98  
% 3.19/0.98  fof(f26,plain,(
% 3.19/0.98    ! [X0] : ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.19/0.98    inference(flattening,[],[f25])).
% 3.19/0.98  
% 3.19/0.98  fof(f58,plain,(
% 3.19/0.98    ( ! [X0] : (k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.19/0.98    inference(cnf_transformation,[],[f26])).
% 3.19/0.98  
% 3.19/0.98  fof(f17,axiom,(
% 3.19/0.98    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.19/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/0.98  
% 3.19/0.98  fof(f82,plain,(
% 3.19/0.98    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.19/0.98    inference(cnf_transformation,[],[f17])).
% 3.19/0.98  
% 3.19/0.98  fof(f91,plain,(
% 3.19/0.98    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.19/0.98    inference(definition_unfolding,[],[f58,f82])).
% 3.19/0.98  
% 3.19/0.98  fof(f10,axiom,(
% 3.19/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 3.19/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/0.98  
% 3.19/0.98  fof(f31,plain,(
% 3.19/0.98    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.19/0.98    inference(ennf_transformation,[],[f10])).
% 3.19/0.98  
% 3.19/0.98  fof(f32,plain,(
% 3.19/0.98    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.19/0.98    inference(flattening,[],[f31])).
% 3.19/0.98  
% 3.19/0.98  fof(f65,plain,(
% 3.19/0.98    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.19/0.98    inference(cnf_transformation,[],[f32])).
% 3.19/0.98  
% 3.19/0.98  fof(f1,axiom,(
% 3.19/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.19/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/0.98  
% 3.19/0.98  fof(f22,plain,(
% 3.19/0.98    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.19/0.98    inference(ennf_transformation,[],[f1])).
% 3.19/0.98  
% 3.19/0.98  fof(f50,plain,(
% 3.19/0.98    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.19/0.98    inference(cnf_transformation,[],[f22])).
% 3.19/0.98  
% 3.19/0.98  fof(f2,axiom,(
% 3.19/0.98    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.19/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/0.98  
% 3.19/0.98  fof(f51,plain,(
% 3.19/0.98    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.19/0.98    inference(cnf_transformation,[],[f2])).
% 3.19/0.98  
% 3.19/0.98  fof(f59,plain,(
% 3.19/0.98    ( ! [X0] : (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.19/0.98    inference(cnf_transformation,[],[f26])).
% 3.19/0.98  
% 3.19/0.98  fof(f90,plain,(
% 3.19/0.98    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.19/0.98    inference(definition_unfolding,[],[f59,f82])).
% 3.19/0.98  
% 3.19/0.98  fof(f66,plain,(
% 3.19/0.98    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.19/0.98    inference(cnf_transformation,[],[f32])).
% 3.19/0.98  
% 3.19/0.98  fof(f12,axiom,(
% 3.19/0.98    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 3.19/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/0.98  
% 3.19/0.98  fof(f35,plain,(
% 3.19/0.98    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.19/0.98    inference(ennf_transformation,[],[f12])).
% 3.19/0.98  
% 3.19/0.98  fof(f36,plain,(
% 3.19/0.98    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.19/0.98    inference(flattening,[],[f35])).
% 3.19/0.98  
% 3.19/0.98  fof(f47,plain,(
% 3.19/0.98    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.19/0.98    inference(nnf_transformation,[],[f36])).
% 3.19/0.98  
% 3.19/0.98  fof(f73,plain,(
% 3.19/0.98    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.19/0.98    inference(cnf_transformation,[],[f47])).
% 3.19/0.98  
% 3.19/0.98  fof(f7,axiom,(
% 3.19/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.19/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/0.98  
% 3.19/0.98  fof(f21,plain,(
% 3.19/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.19/0.98    inference(pure_predicate_removal,[],[f7])).
% 3.19/0.98  
% 3.19/0.98  fof(f27,plain,(
% 3.19/0.98    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.19/0.98    inference(ennf_transformation,[],[f21])).
% 3.19/0.98  
% 3.19/0.98  fof(f60,plain,(
% 3.19/0.98    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.19/0.98    inference(cnf_transformation,[],[f27])).
% 3.19/0.98  
% 3.19/0.98  fof(f87,plain,(
% 3.19/0.98    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))),
% 3.19/0.98    inference(cnf_transformation,[],[f49])).
% 3.19/0.98  
% 3.19/0.98  fof(f14,axiom,(
% 3.19/0.98    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 3.19/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/0.98  
% 3.19/0.98  fof(f20,plain,(
% 3.19/0.98    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.19/0.98    inference(pure_predicate_removal,[],[f14])).
% 3.19/0.98  
% 3.19/0.98  fof(f79,plain,(
% 3.19/0.98    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.19/0.98    inference(cnf_transformation,[],[f20])).
% 3.19/0.98  
% 3.19/0.98  fof(f9,axiom,(
% 3.19/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.19/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/0.98  
% 3.19/0.98  fof(f29,plain,(
% 3.19/0.98    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.19/0.98    inference(ennf_transformation,[],[f9])).
% 3.19/0.98  
% 3.19/0.98  fof(f30,plain,(
% 3.19/0.98    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.19/0.98    inference(flattening,[],[f29])).
% 3.19/0.98  
% 3.19/0.98  fof(f45,plain,(
% 3.19/0.98    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.19/0.98    inference(nnf_transformation,[],[f30])).
% 3.19/0.98  
% 3.19/0.98  fof(f63,plain,(
% 3.19/0.98    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.19/0.98    inference(cnf_transformation,[],[f45])).
% 3.19/0.98  
% 3.19/0.98  fof(f92,plain,(
% 3.19/0.98    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.19/0.98    inference(equality_resolution,[],[f63])).
% 3.19/0.98  
% 3.19/0.98  fof(f4,axiom,(
% 3.19/0.98    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 3.19/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/0.98  
% 3.19/0.98  fof(f23,plain,(
% 3.19/0.98    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.19/0.98    inference(ennf_transformation,[],[f4])).
% 3.19/0.98  
% 3.19/0.98  fof(f24,plain,(
% 3.19/0.98    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.19/0.98    inference(flattening,[],[f23])).
% 3.19/0.98  
% 3.19/0.98  fof(f55,plain,(
% 3.19/0.98    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.19/0.98    inference(cnf_transformation,[],[f24])).
% 3.19/0.98  
% 3.19/0.98  fof(f3,axiom,(
% 3.19/0.98    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.19/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/0.98  
% 3.19/0.98  fof(f52,plain,(
% 3.19/0.98    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.19/0.98    inference(cnf_transformation,[],[f3])).
% 3.19/0.98  
% 3.19/0.98  fof(f5,axiom,(
% 3.19/0.98    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.19/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.19/0.98  
% 3.19/0.98  fof(f56,plain,(
% 3.19/0.98    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 3.19/0.98    inference(cnf_transformation,[],[f5])).
% 3.19/0.98  
% 3.19/0.98  fof(f89,plain,(
% 3.19/0.98    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 3.19/0.98    inference(definition_unfolding,[],[f56,f82])).
% 3.19/0.98  
% 3.19/0.98  fof(f54,plain,(
% 3.19/0.99    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.19/0.99    inference(cnf_transformation,[],[f24])).
% 3.19/0.99  
% 3.19/0.99  cnf(c_33,negated_conjecture,
% 3.19/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.19/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1261,plain,
% 3.19/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.19/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_22,plain,
% 3.19/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.19/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.19/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.19/0.99      | k1_xboole_0 = X2 ),
% 3.19/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1270,plain,
% 3.19/0.99      ( k1_relset_1(X0,X1,X2) = X0
% 3.19/0.99      | k1_xboole_0 = X1
% 3.19/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.19/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.19/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_3715,plain,
% 3.19/0.99      ( k1_relset_1(sK0,sK0,sK1) = sK0
% 3.19/0.99      | sK0 = k1_xboole_0
% 3.19/0.99      | v1_funct_2(sK1,sK0,sK0) != iProver_top ),
% 3.19/0.99      inference(superposition,[status(thm)],[c_1261,c_1270]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_11,plain,
% 3.19/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.19/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.19/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1279,plain,
% 3.19/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.19/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.19/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_2564,plain,
% 3.19/0.99      ( k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) ),
% 3.19/0.99      inference(superposition,[status(thm)],[c_1261,c_1279]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_3720,plain,
% 3.19/0.99      ( k1_relat_1(sK1) = sK0
% 3.19/0.99      | sK0 = k1_xboole_0
% 3.19/0.99      | v1_funct_2(sK1,sK0,sK0) != iProver_top ),
% 3.19/0.99      inference(demodulation,[status(thm)],[c_3715,c_2564]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_35,negated_conjecture,
% 3.19/0.99      ( v1_funct_2(sK1,sK0,sK0) ),
% 3.19/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_38,plain,
% 3.19/0.99      ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
% 3.19/0.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_4062,plain,
% 3.19/0.99      ( sK0 = k1_xboole_0 | k1_relat_1(sK1) = sK0 ),
% 3.19/0.99      inference(global_propositional_subsumption,
% 3.19/0.99                [status(thm)],
% 3.19/0.99                [c_3720,c_38]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_4063,plain,
% 3.19/0.99      ( k1_relat_1(sK1) = sK0 | sK0 = k1_xboole_0 ),
% 3.19/0.99      inference(renaming,[status(thm)],[c_4062]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_31,plain,
% 3.19/0.99      ( ~ v1_funct_2(X0,X1,X1)
% 3.19/0.99      | ~ v3_funct_2(X0,X1,X1)
% 3.19/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.19/0.99      | ~ v1_funct_1(X0)
% 3.19/0.99      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 3.19/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1263,plain,
% 3.19/0.99      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
% 3.19/0.99      | v1_funct_2(X1,X0,X0) != iProver_top
% 3.19/0.99      | v3_funct_2(X1,X0,X0) != iProver_top
% 3.19/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 3.19/0.99      | v1_funct_1(X1) != iProver_top ),
% 3.19/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_3490,plain,
% 3.19/0.99      ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
% 3.19/0.99      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.19/0.99      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.19/0.99      | v1_funct_1(sK1) != iProver_top ),
% 3.19/0.99      inference(superposition,[status(thm)],[c_1261,c_1263]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_36,negated_conjecture,
% 3.19/0.99      ( v1_funct_1(sK1) ),
% 3.19/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_34,negated_conjecture,
% 3.19/0.99      ( v3_funct_2(sK1,sK0,sK0) ),
% 3.19/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1624,plain,
% 3.19/0.99      ( ~ v1_funct_2(sK1,X0,X0)
% 3.19/0.99      | ~ v3_funct_2(sK1,X0,X0)
% 3.19/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 3.19/0.99      | ~ v1_funct_1(sK1)
% 3.19/0.99      | k2_funct_2(X0,sK1) = k2_funct_1(sK1) ),
% 3.19/0.99      inference(instantiation,[status(thm)],[c_31]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1802,plain,
% 3.19/0.99      ( ~ v1_funct_2(sK1,sK0,sK0)
% 3.19/0.99      | ~ v3_funct_2(sK1,sK0,sK0)
% 3.19/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.19/0.99      | ~ v1_funct_1(sK1)
% 3.19/0.99      | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 3.19/0.99      inference(instantiation,[status(thm)],[c_1624]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_3998,plain,
% 3.19/0.99      ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 3.19/0.99      inference(global_propositional_subsumption,
% 3.19/0.99                [status(thm)],
% 3.19/0.99                [c_3490,c_36,c_35,c_34,c_33,c_1802]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_25,plain,
% 3.19/0.99      ( ~ v1_funct_2(X0,X1,X1)
% 3.19/0.99      | ~ v3_funct_2(X0,X1,X1)
% 3.19/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.19/0.99      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.19/0.99      | ~ v1_funct_1(X0) ),
% 3.19/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1269,plain,
% 3.19/0.99      ( v1_funct_2(X0,X1,X1) != iProver_top
% 3.19/0.99      | v3_funct_2(X0,X1,X1) != iProver_top
% 3.19/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 3.19/0.99      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) = iProver_top
% 3.19/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.19/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_5999,plain,
% 3.19/0.99      ( v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.19/0.99      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.19/0.99      | m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 3.19/0.99      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.19/0.99      | v1_funct_1(sK1) != iProver_top ),
% 3.19/0.99      inference(superposition,[status(thm)],[c_3998,c_1269]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_37,plain,
% 3.19/0.99      ( v1_funct_1(sK1) = iProver_top ),
% 3.19/0.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_39,plain,
% 3.19/0.99      ( v3_funct_2(sK1,sK0,sK0) = iProver_top ),
% 3.19/0.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_40,plain,
% 3.19/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.19/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_6494,plain,
% 3.19/0.99      ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.19/0.99      inference(global_propositional_subsumption,
% 3.19/0.99                [status(thm)],
% 3.19/0.99                [c_5999,c_37,c_38,c_39,c_40]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_30,plain,
% 3.19/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.19/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.19/0.99      | ~ v1_funct_1(X0)
% 3.19/0.99      | ~ v1_funct_1(X3)
% 3.19/0.99      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.19/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1264,plain,
% 3.19/0.99      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 3.19/0.99      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 3.19/0.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.19/0.99      | v1_funct_1(X5) != iProver_top
% 3.19/0.99      | v1_funct_1(X4) != iProver_top ),
% 3.19/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_6509,plain,
% 3.19/0.99      ( k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1))
% 3.19/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.19/0.99      | v1_funct_1(X2) != iProver_top
% 3.19/0.99      | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
% 3.19/0.99      inference(superposition,[status(thm)],[c_6494,c_1264]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_28,plain,
% 3.19/0.99      ( ~ v1_funct_2(X0,X1,X1)
% 3.19/0.99      | ~ v3_funct_2(X0,X1,X1)
% 3.19/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.19/0.99      | ~ v1_funct_1(X0)
% 3.19/0.99      | v1_funct_1(k2_funct_2(X1,X0)) ),
% 3.19/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1266,plain,
% 3.19/0.99      ( v1_funct_2(X0,X1,X1) != iProver_top
% 3.19/0.99      | v3_funct_2(X0,X1,X1) != iProver_top
% 3.19/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 3.19/0.99      | v1_funct_1(X0) != iProver_top
% 3.19/0.99      | v1_funct_1(k2_funct_2(X1,X0)) = iProver_top ),
% 3.19/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_4766,plain,
% 3.19/0.99      ( v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.19/0.99      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.19/0.99      | v1_funct_1(k2_funct_2(sK0,sK1)) = iProver_top
% 3.19/0.99      | v1_funct_1(sK1) != iProver_top ),
% 3.19/0.99      inference(superposition,[status(thm)],[c_1261,c_1266]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_4780,plain,
% 3.19/0.99      ( v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.19/0.99      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.19/0.99      | v1_funct_1(k2_funct_1(sK1)) = iProver_top
% 3.19/0.99      | v1_funct_1(sK1) != iProver_top ),
% 3.19/0.99      inference(light_normalisation,[status(thm)],[c_4766,c_3998]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_8934,plain,
% 3.19/0.99      ( v1_funct_1(X2) != iProver_top
% 3.19/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.19/0.99      | k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1)) ),
% 3.19/0.99      inference(global_propositional_subsumption,
% 3.19/0.99                [status(thm)],
% 3.19/0.99                [c_6509,c_37,c_38,c_39,c_4780]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_8935,plain,
% 3.19/0.99      ( k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1))
% 3.19/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.19/0.99      | v1_funct_1(X2) != iProver_top ),
% 3.19/0.99      inference(renaming,[status(thm)],[c_8934]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_8945,plain,
% 3.19/0.99      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k5_relat_1(sK1,k2_funct_1(sK1))
% 3.19/0.99      | v1_funct_1(sK1) != iProver_top ),
% 3.19/0.99      inference(superposition,[status(thm)],[c_1261,c_8935]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1258,plain,
% 3.19/0.99      ( v1_funct_1(sK1) = iProver_top ),
% 3.19/0.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_9,plain,
% 3.19/0.99      ( ~ v1_funct_1(X0)
% 3.19/0.99      | ~ v2_funct_1(X0)
% 3.19/0.99      | ~ v1_relat_1(X0)
% 3.19/0.99      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
% 3.19/0.99      inference(cnf_transformation,[],[f91]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1280,plain,
% 3.19/0.99      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
% 3.19/0.99      | v1_funct_1(X0) != iProver_top
% 3.19/0.99      | v2_funct_1(X0) != iProver_top
% 3.19/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.19/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_3558,plain,
% 3.19/0.99      ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
% 3.19/0.99      | v2_funct_1(sK1) != iProver_top
% 3.19/0.99      | v1_relat_1(sK1) != iProver_top ),
% 3.19/0.99      inference(superposition,[status(thm)],[c_1258,c_1280]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1561,plain,
% 3.19/0.99      ( ~ v1_funct_1(sK1)
% 3.19/0.99      | ~ v2_funct_1(sK1)
% 3.19/0.99      | ~ v1_relat_1(sK1)
% 3.19/0.99      | k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
% 3.19/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_15,plain,
% 3.19/0.99      ( ~ v3_funct_2(X0,X1,X2)
% 3.19/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.19/0.99      | ~ v1_funct_1(X0)
% 3.19/0.99      | v2_funct_1(X0) ),
% 3.19/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1590,plain,
% 3.19/0.99      ( ~ v3_funct_2(sK1,X0,X1)
% 3.19/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.19/0.99      | ~ v1_funct_1(sK1)
% 3.19/0.99      | v2_funct_1(sK1) ),
% 3.19/0.99      inference(instantiation,[status(thm)],[c_15]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1702,plain,
% 3.19/0.99      ( ~ v3_funct_2(sK1,sK0,sK0)
% 3.19/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.19/0.99      | ~ v1_funct_1(sK1)
% 3.19/0.99      | v2_funct_1(sK1) ),
% 3.19/0.99      inference(instantiation,[status(thm)],[c_1590]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_0,plain,
% 3.19/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.19/0.99      | ~ v1_relat_1(X1)
% 3.19/0.99      | v1_relat_1(X0) ),
% 3.19/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1548,plain,
% 3.19/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.19/0.99      | v1_relat_1(X0)
% 3.19/0.99      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 3.19/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1830,plain,
% 3.19/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.19/0.99      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
% 3.19/0.99      | v1_relat_1(sK1) ),
% 3.19/0.99      inference(instantiation,[status(thm)],[c_1548]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1,plain,
% 3.19/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.19/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1947,plain,
% 3.19/0.99      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
% 3.19/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_3726,plain,
% 3.19/0.99      ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
% 3.19/0.99      inference(global_propositional_subsumption,
% 3.19/0.99                [status(thm)],
% 3.19/0.99                [c_3558,c_36,c_34,c_33,c_1561,c_1702,c_1830,c_1947]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_8958,plain,
% 3.19/0.99      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
% 3.19/0.99      | v1_funct_1(sK1) != iProver_top ),
% 3.19/0.99      inference(light_normalisation,[status(thm)],[c_8945,c_3726]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_9018,plain,
% 3.19/0.99      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
% 3.19/0.99      inference(global_propositional_subsumption,
% 3.19/0.99                [status(thm)],
% 3.19/0.99                [c_8958,c_37]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_4449,plain,
% 3.19/0.99      ( k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1)
% 3.19/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.19/0.99      | v1_funct_1(X2) != iProver_top
% 3.19/0.99      | v1_funct_1(sK1) != iProver_top ),
% 3.19/0.99      inference(superposition,[status(thm)],[c_1261,c_1264]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_4925,plain,
% 3.19/0.99      ( v1_funct_1(X2) != iProver_top
% 3.19/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.19/0.99      | k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1) ),
% 3.19/0.99      inference(global_propositional_subsumption,
% 3.19/0.99                [status(thm)],
% 3.19/0.99                [c_4449,c_37]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_4926,plain,
% 3.19/0.99      ( k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1)
% 3.19/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.19/0.99      | v1_funct_1(X2) != iProver_top ),
% 3.19/0.99      inference(renaming,[status(thm)],[c_4925]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_6003,plain,
% 3.19/0.99      ( k1_partfun1(X0,X0,sK0,sK0,k2_funct_2(X0,X1),sK1) = k5_relat_1(k2_funct_2(X0,X1),sK1)
% 3.19/0.99      | v1_funct_2(X1,X0,X0) != iProver_top
% 3.19/0.99      | v3_funct_2(X1,X0,X0) != iProver_top
% 3.19/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 3.19/0.99      | v1_funct_1(X1) != iProver_top
% 3.19/0.99      | v1_funct_1(k2_funct_2(X0,X1)) != iProver_top ),
% 3.19/0.99      inference(superposition,[status(thm)],[c_1269,c_4926]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_7144,plain,
% 3.19/0.99      ( k1_partfun1(X0,X0,sK0,sK0,k2_funct_2(X0,X1),sK1) = k5_relat_1(k2_funct_2(X0,X1),sK1)
% 3.19/0.99      | v1_funct_2(X1,X0,X0) != iProver_top
% 3.19/0.99      | v3_funct_2(X1,X0,X0) != iProver_top
% 3.19/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 3.19/0.99      | v1_funct_1(X1) != iProver_top ),
% 3.19/0.99      inference(forward_subsumption_resolution,
% 3.19/0.99                [status(thm)],
% 3.19/0.99                [c_6003,c_1266]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_7150,plain,
% 3.19/0.99      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1) = k5_relat_1(k2_funct_2(sK0,sK1),sK1)
% 3.19/0.99      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.19/0.99      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.19/0.99      | v1_funct_1(sK1) != iProver_top ),
% 3.19/0.99      inference(superposition,[status(thm)],[c_1261,c_7144]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_8,plain,
% 3.19/0.99      ( ~ v1_funct_1(X0)
% 3.19/0.99      | ~ v2_funct_1(X0)
% 3.19/0.99      | ~ v1_relat_1(X0)
% 3.19/0.99      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
% 3.19/0.99      inference(cnf_transformation,[],[f90]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1281,plain,
% 3.19/0.99      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
% 3.19/0.99      | v1_funct_1(X0) != iProver_top
% 3.19/0.99      | v2_funct_1(X0) != iProver_top
% 3.19/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.19/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_3565,plain,
% 3.19/0.99      ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1))
% 3.19/0.99      | v2_funct_1(sK1) != iProver_top
% 3.19/0.99      | v1_relat_1(sK1) != iProver_top ),
% 3.19/0.99      inference(superposition,[status(thm)],[c_1258,c_1281]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_14,plain,
% 3.19/0.99      ( ~ v3_funct_2(X0,X1,X2)
% 3.19/0.99      | v2_funct_2(X0,X2)
% 3.19/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.19/0.99      | ~ v1_funct_1(X0) ),
% 3.19/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_24,plain,
% 3.19/0.99      ( ~ v2_funct_2(X0,X1)
% 3.19/0.99      | ~ v5_relat_1(X0,X1)
% 3.19/0.99      | ~ v1_relat_1(X0)
% 3.19/0.99      | k2_relat_1(X0) = X1 ),
% 3.19/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_411,plain,
% 3.19/0.99      ( ~ v3_funct_2(X0,X1,X2)
% 3.19/0.99      | ~ v5_relat_1(X3,X4)
% 3.19/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.19/0.99      | ~ v1_funct_1(X0)
% 3.19/0.99      | ~ v1_relat_1(X3)
% 3.19/0.99      | X3 != X0
% 3.19/0.99      | X4 != X2
% 3.19/0.99      | k2_relat_1(X3) = X4 ),
% 3.19/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_24]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_412,plain,
% 3.19/0.99      ( ~ v3_funct_2(X0,X1,X2)
% 3.19/0.99      | ~ v5_relat_1(X0,X2)
% 3.19/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.19/0.99      | ~ v1_funct_1(X0)
% 3.19/0.99      | ~ v1_relat_1(X0)
% 3.19/0.99      | k2_relat_1(X0) = X2 ),
% 3.19/0.99      inference(unflattening,[status(thm)],[c_411]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_10,plain,
% 3.19/0.99      ( v5_relat_1(X0,X1)
% 3.19/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.19/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_426,plain,
% 3.19/0.99      ( ~ v3_funct_2(X0,X1,X2)
% 3.19/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.19/0.99      | ~ v1_funct_1(X0)
% 3.19/0.99      | ~ v1_relat_1(X0)
% 3.19/0.99      | k2_relat_1(X0) = X2 ),
% 3.19/0.99      inference(forward_subsumption_resolution,
% 3.19/0.99                [status(thm)],
% 3.19/0.99                [c_412,c_10]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1257,plain,
% 3.19/0.99      ( k2_relat_1(X0) = X1
% 3.19/0.99      | v3_funct_2(X0,X2,X1) != iProver_top
% 3.19/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
% 3.19/0.99      | v1_funct_1(X0) != iProver_top
% 3.19/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.19/0.99      inference(predicate_to_equality,[status(thm)],[c_426]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_2582,plain,
% 3.19/0.99      ( k2_relat_1(sK1) = sK0
% 3.19/0.99      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.19/0.99      | v1_funct_1(sK1) != iProver_top
% 3.19/0.99      | v1_relat_1(sK1) != iProver_top ),
% 3.19/0.99      inference(superposition,[status(thm)],[c_1261,c_1257]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1831,plain,
% 3.19/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.19/0.99      | v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
% 3.19/0.99      | v1_relat_1(sK1) = iProver_top ),
% 3.19/0.99      inference(predicate_to_equality,[status(thm)],[c_1830]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1948,plain,
% 3.19/0.99      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) = iProver_top ),
% 3.19/0.99      inference(predicate_to_equality,[status(thm)],[c_1947]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_3054,plain,
% 3.19/0.99      ( k2_relat_1(sK1) = sK0 ),
% 3.19/0.99      inference(global_propositional_subsumption,
% 3.19/0.99                [status(thm)],
% 3.19/0.99                [c_2582,c_37,c_39,c_40,c_1831,c_1948]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_3566,plain,
% 3.19/0.99      ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
% 3.19/0.99      | v2_funct_1(sK1) != iProver_top
% 3.19/0.99      | v1_relat_1(sK1) != iProver_top ),
% 3.19/0.99      inference(light_normalisation,[status(thm)],[c_3565,c_3054]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1703,plain,
% 3.19/0.99      ( v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.19/0.99      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.19/0.99      | v1_funct_1(sK1) != iProver_top
% 3.19/0.99      | v2_funct_1(sK1) = iProver_top ),
% 3.19/0.99      inference(predicate_to_equality,[status(thm)],[c_1702]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_4058,plain,
% 3.19/0.99      ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(sK0) ),
% 3.19/0.99      inference(global_propositional_subsumption,
% 3.19/0.99                [status(thm)],
% 3.19/0.99                [c_3566,c_37,c_39,c_40,c_1703,c_1831,c_1948]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_7173,plain,
% 3.19/0.99      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
% 3.19/0.99      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.19/0.99      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.19/0.99      | v1_funct_1(sK1) != iProver_top ),
% 3.19/0.99      inference(light_normalisation,[status(thm)],[c_7150,c_3998,c_4058]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_6502,plain,
% 3.19/0.99      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k5_relat_1(k2_funct_1(sK1),sK1)
% 3.19/0.99      | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
% 3.19/0.99      inference(superposition,[status(thm)],[c_6494,c_4926]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_6576,plain,
% 3.19/0.99      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
% 3.19/0.99      | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
% 3.19/0.99      inference(light_normalisation,[status(thm)],[c_6502,c_4058]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_7212,plain,
% 3.19/0.99      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0) ),
% 3.19/0.99      inference(global_propositional_subsumption,
% 3.19/0.99                [status(thm)],
% 3.19/0.99                [c_7173,c_37,c_38,c_39,c_4780,c_6576]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_32,negated_conjecture,
% 3.19/0.99      ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
% 3.19/0.99      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
% 3.19/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1262,plain,
% 3.19/0.99      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) != iProver_top
% 3.19/0.99      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) != iProver_top ),
% 3.19/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_4001,plain,
% 3.19/0.99      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) != iProver_top
% 3.19/0.99      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
% 3.19/0.99      inference(demodulation,[status(thm)],[c_3998,c_1262]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_7215,plain,
% 3.19/0.99      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top
% 3.19/0.99      | r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
% 3.19/0.99      inference(demodulation,[status(thm)],[c_7212,c_4001]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_29,plain,
% 3.19/0.99      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.19/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1265,plain,
% 3.19/0.99      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 3.19/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_12,plain,
% 3.19/0.99      ( r2_relset_1(X0,X1,X2,X2)
% 3.19/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.19/0.99      inference(cnf_transformation,[],[f92]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1278,plain,
% 3.19/0.99      ( r2_relset_1(X0,X1,X2,X2) = iProver_top
% 3.19/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.19/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_2185,plain,
% 3.19/0.99      ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0)) = iProver_top ),
% 3.19/0.99      inference(superposition,[status(thm)],[c_1265,c_1278]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_7712,plain,
% 3.19/0.99      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
% 3.19/0.99      inference(forward_subsumption_resolution,
% 3.19/0.99                [status(thm)],
% 3.19/0.99                [c_7215,c_2185]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_9021,plain,
% 3.19/0.99      ( r2_relset_1(sK0,sK0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
% 3.19/0.99      inference(demodulation,[status(thm)],[c_9018,c_7712]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_9025,plain,
% 3.19/0.99      ( sK0 = k1_xboole_0
% 3.19/0.99      | r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
% 3.19/0.99      inference(superposition,[status(thm)],[c_4063,c_9021]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_9174,plain,
% 3.19/0.99      ( sK0 = k1_xboole_0 ),
% 3.19/0.99      inference(forward_subsumption_resolution,
% 3.19/0.99                [status(thm)],
% 3.19/0.99                [c_9025,c_2185]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_9175,plain,
% 3.19/0.99      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(k1_xboole_0)) != iProver_top ),
% 3.19/0.99      inference(demodulation,[status(thm)],[c_9174,c_9021]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_4,plain,
% 3.19/0.99      ( ~ v1_relat_1(X0)
% 3.19/0.99      | k2_relat_1(X0) != k1_xboole_0
% 3.19/0.99      | k1_xboole_0 = X0 ),
% 3.19/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1283,plain,
% 3.19/0.99      ( k2_relat_1(X0) != k1_xboole_0
% 3.19/0.99      | k1_xboole_0 = X0
% 3.19/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.19/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_3057,plain,
% 3.19/0.99      ( sK1 = k1_xboole_0
% 3.19/0.99      | sK0 != k1_xboole_0
% 3.19/0.99      | v1_relat_1(sK1) != iProver_top ),
% 3.19/0.99      inference(superposition,[status(thm)],[c_3054,c_1283]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_3058,plain,
% 3.19/0.99      ( ~ v1_relat_1(sK1) | sK1 = k1_xboole_0 | sK0 != k1_xboole_0 ),
% 3.19/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_3057]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_3060,plain,
% 3.19/0.99      ( sK0 != k1_xboole_0 | sK1 = k1_xboole_0 ),
% 3.19/0.99      inference(global_propositional_subsumption,
% 3.19/0.99                [status(thm)],
% 3.19/0.99                [c_3057,c_33,c_1830,c_1947,c_3058]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_3061,plain,
% 3.19/0.99      ( sK1 = k1_xboole_0 | sK0 != k1_xboole_0 ),
% 3.19/0.99      inference(renaming,[status(thm)],[c_3060]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_9206,plain,
% 3.19/0.99      ( sK1 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.19/0.99      inference(demodulation,[status(thm)],[c_9174,c_3061]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_9225,plain,
% 3.19/0.99      ( sK1 = k1_xboole_0 ),
% 3.19/0.99      inference(equality_resolution_simp,[status(thm)],[c_9206]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_9368,plain,
% 3.19/0.99      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_relat_1(k1_xboole_0)),k6_partfun1(k1_xboole_0)) != iProver_top ),
% 3.19/0.99      inference(light_normalisation,[status(thm)],[c_9175,c_9225]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_3,plain,
% 3.19/0.99      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.19/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_7,plain,
% 3.19/0.99      ( k1_relat_1(k6_partfun1(X0)) = X0 ),
% 3.19/0.99      inference(cnf_transformation,[],[f89]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_5,plain,
% 3.19/0.99      ( ~ v1_relat_1(X0)
% 3.19/0.99      | k1_relat_1(X0) != k1_xboole_0
% 3.19/0.99      | k1_xboole_0 = X0 ),
% 3.19/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1282,plain,
% 3.19/0.99      ( k1_relat_1(X0) != k1_xboole_0
% 3.19/0.99      | k1_xboole_0 = X0
% 3.19/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.19/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1770,plain,
% 3.19/0.99      ( k6_partfun1(X0) = k1_xboole_0
% 3.19/0.99      | k1_xboole_0 != X0
% 3.19/0.99      | v1_relat_1(k6_partfun1(X0)) != iProver_top ),
% 3.19/0.99      inference(superposition,[status(thm)],[c_7,c_1282]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1870,plain,
% 3.19/0.99      ( k6_partfun1(k1_xboole_0) = k1_xboole_0
% 3.19/0.99      | v1_relat_1(k6_partfun1(k1_xboole_0)) != iProver_top ),
% 3.19/0.99      inference(equality_resolution,[status(thm)],[c_1770]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_49,plain,
% 3.19/0.99      ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
% 3.19/0.99      inference(instantiation,[status(thm)],[c_29]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_121,plain,
% 3.19/0.99      ( v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) ),
% 3.19/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_733,plain,( X0 = X0 ),theory(equality) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_766,plain,
% 3.19/0.99      ( k1_xboole_0 = k1_xboole_0 ),
% 3.19/0.99      inference(instantiation,[status(thm)],[c_733]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1777,plain,
% 3.19/0.99      ( ~ v1_relat_1(k6_partfun1(X0))
% 3.19/0.99      | k6_partfun1(X0) = k1_xboole_0
% 3.19/0.99      | k1_xboole_0 != X0 ),
% 3.19/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_1770]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1779,plain,
% 3.19/0.99      ( ~ v1_relat_1(k6_partfun1(k1_xboole_0))
% 3.19/0.99      | k6_partfun1(k1_xboole_0) = k1_xboole_0
% 3.19/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.19/0.99      inference(instantiation,[status(thm)],[c_1777]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1825,plain,
% 3.19/0.99      ( ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 3.19/0.99      | ~ v1_relat_1(k2_zfmisc_1(X0,X0))
% 3.19/0.99      | v1_relat_1(k6_partfun1(X0)) ),
% 3.19/0.99      inference(instantiation,[status(thm)],[c_1548]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1827,plain,
% 3.19/0.99      ( ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
% 3.19/0.99      | ~ v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
% 3.19/0.99      | v1_relat_1(k6_partfun1(k1_xboole_0)) ),
% 3.19/0.99      inference(instantiation,[status(thm)],[c_1825]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_2031,plain,
% 3.19/0.99      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 3.19/0.99      inference(global_propositional_subsumption,
% 3.19/0.99                [status(thm)],
% 3.19/0.99                [c_1870,c_49,c_121,c_766,c_1779,c_1827]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_9370,plain,
% 3.19/0.99      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.19/0.99      inference(light_normalisation,[status(thm)],[c_9368,c_3,c_2031]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_2034,plain,
% 3.19/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 3.19/0.99      inference(superposition,[status(thm)],[c_2031,c_1265]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_97,plain,
% 3.19/0.99      ( r2_relset_1(X0,X1,X2,X2) = iProver_top
% 3.19/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.19/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_99,plain,
% 3.19/0.99      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top
% 3.19/0.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 3.19/0.99      inference(instantiation,[status(thm)],[c_97]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(contradiction,plain,
% 3.19/0.99      ( $false ),
% 3.19/0.99      inference(minisat,[status(thm)],[c_9370,c_2034,c_99]) ).
% 3.19/0.99  
% 3.19/0.99  
% 3.19/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.19/0.99  
% 3.19/0.99  ------                               Statistics
% 3.19/0.99  
% 3.19/0.99  ------ General
% 3.19/0.99  
% 3.19/0.99  abstr_ref_over_cycles:                  0
% 3.19/0.99  abstr_ref_under_cycles:                 0
% 3.19/0.99  gc_basic_clause_elim:                   0
% 3.19/0.99  forced_gc_time:                         0
% 3.19/0.99  parsing_time:                           0.016
% 3.19/0.99  unif_index_cands_time:                  0.
% 3.19/0.99  unif_index_add_time:                    0.
% 3.19/0.99  orderings_time:                         0.
% 3.19/0.99  out_proof_time:                         0.015
% 3.19/0.99  total_time:                             0.296
% 3.19/0.99  num_of_symbols:                         53
% 3.19/0.99  num_of_terms:                           10004
% 3.19/0.99  
% 3.19/0.99  ------ Preprocessing
% 3.19/0.99  
% 3.19/0.99  num_of_splits:                          0
% 3.19/0.99  num_of_split_atoms:                     0
% 3.19/0.99  num_of_reused_defs:                     0
% 3.19/0.99  num_eq_ax_congr_red:                    14
% 3.19/0.99  num_of_sem_filtered_clauses:            1
% 3.19/0.99  num_of_subtypes:                        0
% 3.19/0.99  monotx_restored_types:                  0
% 3.19/0.99  sat_num_of_epr_types:                   0
% 3.19/0.99  sat_num_of_non_cyclic_types:            0
% 3.19/0.99  sat_guarded_non_collapsed_types:        0
% 3.19/0.99  num_pure_diseq_elim:                    0
% 3.19/0.99  simp_replaced_by:                       0
% 3.19/0.99  res_preprocessed:                       170
% 3.19/0.99  prep_upred:                             0
% 3.19/0.99  prep_unflattend:                        6
% 3.19/0.99  smt_new_axioms:                         0
% 3.19/0.99  pred_elim_cands:                        7
% 3.19/0.99  pred_elim:                              2
% 3.19/0.99  pred_elim_cl:                           3
% 3.19/0.99  pred_elim_cycles:                       5
% 3.19/0.99  merged_defs:                            0
% 3.19/0.99  merged_defs_ncl:                        0
% 3.19/0.99  bin_hyper_res:                          0
% 3.19/0.99  prep_cycles:                            4
% 3.19/0.99  pred_elim_time:                         0.004
% 3.19/0.99  splitting_time:                         0.
% 3.19/0.99  sem_filter_time:                        0.
% 3.19/0.99  monotx_time:                            0.001
% 3.19/0.99  subtype_inf_time:                       0.
% 3.19/0.99  
% 3.19/0.99  ------ Problem properties
% 3.19/0.99  
% 3.19/0.99  clauses:                                33
% 3.19/0.99  conjectures:                            5
% 3.19/0.99  epr:                                    3
% 3.19/0.99  horn:                                   29
% 3.19/0.99  ground:                                 7
% 3.19/0.99  unary:                                  10
% 3.19/0.99  binary:                                 3
% 3.19/0.99  lits:                                   97
% 3.19/0.99  lits_eq:                                24
% 3.19/0.99  fd_pure:                                0
% 3.19/0.99  fd_pseudo:                              0
% 3.19/0.99  fd_cond:                                5
% 3.19/0.99  fd_pseudo_cond:                         2
% 3.19/0.99  ac_symbols:                             0
% 3.19/0.99  
% 3.19/0.99  ------ Propositional Solver
% 3.19/0.99  
% 3.19/0.99  prop_solver_calls:                      27
% 3.19/0.99  prop_fast_solver_calls:                 1376
% 3.19/0.99  smt_solver_calls:                       0
% 3.19/0.99  smt_fast_solver_calls:                  0
% 3.19/0.99  prop_num_of_clauses:                    3564
% 3.19/0.99  prop_preprocess_simplified:             10405
% 3.19/0.99  prop_fo_subsumed:                       63
% 3.19/0.99  prop_solver_time:                       0.
% 3.19/0.99  smt_solver_time:                        0.
% 3.19/0.99  smt_fast_solver_time:                   0.
% 3.19/0.99  prop_fast_solver_time:                  0.
% 3.19/0.99  prop_unsat_core_time:                   0.
% 3.19/0.99  
% 3.19/0.99  ------ QBF
% 3.19/0.99  
% 3.19/0.99  qbf_q_res:                              0
% 3.19/0.99  qbf_num_tautologies:                    0
% 3.19/0.99  qbf_prep_cycles:                        0
% 3.19/0.99  
% 3.19/0.99  ------ BMC1
% 3.19/0.99  
% 3.19/0.99  bmc1_current_bound:                     -1
% 3.19/0.99  bmc1_last_solved_bound:                 -1
% 3.19/0.99  bmc1_unsat_core_size:                   -1
% 3.19/0.99  bmc1_unsat_core_parents_size:           -1
% 3.19/0.99  bmc1_merge_next_fun:                    0
% 3.19/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.19/0.99  
% 3.19/0.99  ------ Instantiation
% 3.19/0.99  
% 3.19/0.99  inst_num_of_clauses:                    1074
% 3.19/0.99  inst_num_in_passive:                    448
% 3.19/0.99  inst_num_in_active:                     415
% 3.19/0.99  inst_num_in_unprocessed:                211
% 3.19/0.99  inst_num_of_loops:                      490
% 3.19/0.99  inst_num_of_learning_restarts:          0
% 3.19/0.99  inst_num_moves_active_passive:          74
% 3.19/0.99  inst_lit_activity:                      0
% 3.19/0.99  inst_lit_activity_moves:                0
% 3.19/0.99  inst_num_tautologies:                   0
% 3.19/0.99  inst_num_prop_implied:                  0
% 3.19/0.99  inst_num_existing_simplified:           0
% 3.19/0.99  inst_num_eq_res_simplified:             0
% 3.19/0.99  inst_num_child_elim:                    0
% 3.19/0.99  inst_num_of_dismatching_blockings:      127
% 3.19/0.99  inst_num_of_non_proper_insts:           775
% 3.19/0.99  inst_num_of_duplicates:                 0
% 3.19/0.99  inst_inst_num_from_inst_to_res:         0
% 3.19/0.99  inst_dismatching_checking_time:         0.
% 3.19/0.99  
% 3.19/0.99  ------ Resolution
% 3.19/0.99  
% 3.19/0.99  res_num_of_clauses:                     0
% 3.19/0.99  res_num_in_passive:                     0
% 3.19/0.99  res_num_in_active:                      0
% 3.19/0.99  res_num_of_loops:                       174
% 3.19/0.99  res_forward_subset_subsumed:            27
% 3.19/0.99  res_backward_subset_subsumed:           0
% 3.19/0.99  res_forward_subsumed:                   0
% 3.19/0.99  res_backward_subsumed:                  0
% 3.19/0.99  res_forward_subsumption_resolution:     1
% 3.19/0.99  res_backward_subsumption_resolution:    0
% 3.19/0.99  res_clause_to_clause_subsumption:       260
% 3.19/0.99  res_orphan_elimination:                 0
% 3.19/0.99  res_tautology_del:                      29
% 3.19/0.99  res_num_eq_res_simplified:              0
% 3.19/0.99  res_num_sel_changes:                    0
% 3.19/0.99  res_moves_from_active_to_pass:          0
% 3.19/0.99  
% 3.19/0.99  ------ Superposition
% 3.19/0.99  
% 3.19/0.99  sup_time_total:                         0.
% 3.19/0.99  sup_time_generating:                    0.
% 3.19/0.99  sup_time_sim_full:                      0.
% 3.19/0.99  sup_time_sim_immed:                     0.
% 3.19/0.99  
% 3.19/0.99  sup_num_of_clauses:                     104
% 3.19/0.99  sup_num_in_active:                      53
% 3.19/0.99  sup_num_in_passive:                     51
% 3.19/0.99  sup_num_of_loops:                       96
% 3.19/0.99  sup_fw_superposition:                   90
% 3.19/0.99  sup_bw_superposition:                   44
% 3.19/0.99  sup_immediate_simplified:               86
% 3.19/0.99  sup_given_eliminated:                   0
% 3.19/0.99  comparisons_done:                       0
% 3.19/0.99  comparisons_avoided:                    0
% 3.19/0.99  
% 3.19/0.99  ------ Simplifications
% 3.19/0.99  
% 3.19/0.99  
% 3.19/0.99  sim_fw_subset_subsumed:                 9
% 3.19/0.99  sim_bw_subset_subsumed:                 4
% 3.19/0.99  sim_fw_subsumed:                        3
% 3.19/0.99  sim_bw_subsumed:                        0
% 3.19/0.99  sim_fw_subsumption_res:                 4
% 3.19/0.99  sim_bw_subsumption_res:                 0
% 3.19/0.99  sim_tautology_del:                      0
% 3.19/0.99  sim_eq_tautology_del:                   18
% 3.19/0.99  sim_eq_res_simp:                        2
% 3.19/0.99  sim_fw_demodulated:                     7
% 3.19/0.99  sim_bw_demodulated:                     61
% 3.19/0.99  sim_light_normalised:                   53
% 3.19/0.99  sim_joinable_taut:                      0
% 3.19/0.99  sim_joinable_simp:                      0
% 3.19/0.99  sim_ac_normalised:                      0
% 3.19/0.99  sim_smt_subsumption:                    0
% 3.19/0.99  
%------------------------------------------------------------------------------
