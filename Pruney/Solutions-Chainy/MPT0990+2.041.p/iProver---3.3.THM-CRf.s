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
% DateTime   : Thu Dec  3 12:03:05 EST 2020

% Result     : Theorem 39.86s
% Output     : CNFRefutation 39.86s
% Verified   : 
% Statistics : Number of formulae       :  271 (3109 expanded)
%              Number of clauses        :  199 ( 917 expanded)
%              Number of leaves         :   19 ( 788 expanded)
%              Depth                    :   26
%              Number of atoms          : 1005 (27028 expanded)
%              Number of equality atoms :  632 (10275 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    inference(ennf_transformation,[],[f16])).

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

fof(f42,plain,(
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

fof(f41,plain,
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

fof(f43,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f38,f42,f41])).

fof(f72,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f43])).

fof(f9,axiom,(
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

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f71,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f76,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f43])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f21,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f47,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f13,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f81,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f47,f65])).

fof(f70,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f69,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f43])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f73,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f43])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => ( v2_funct_1(X0)
              & v2_funct_1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X0)
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f31])).

fof(f62,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f67,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f27])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f74,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f43])).

fof(f11,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f63,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f33])).

fof(f64,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f2,axiom,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f79,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f46,f65])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
              & k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f49,f65])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
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

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f68,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f77,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f43])).

fof(f78,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f43])).

fof(f75,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_153045,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_153048,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_154018,plain,
    ( k1_relset_1(sK1,sK0,sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_153045,c_153048])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_153055,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_153698,plain,
    ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_153045,c_153055])).

cnf(c_154030,plain,
    ( k1_relat_1(sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_154018,c_153698])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_38,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_24,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_638,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_665,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_638])).

cnf(c_639,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_7559,plain,
    ( sK0 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_639])).

cnf(c_7560,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7559])).

cnf(c_25678,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_25679,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_25731,plain,
    ( k1_relset_1(sK1,sK0,sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_25678,c_25679])).

cnf(c_25680,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_25722,plain,
    ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_25678,c_25680])).

cnf(c_25732,plain,
    ( k1_relat_1(sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_25731,c_25722])).

cnf(c_159902,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_154030,c_38,c_24,c_665,c_7560,c_25732])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_153056,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_153516,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_153045,c_153056])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_153058,plain,
    ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_153935,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_153516,c_153058])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_37,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_42339,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_42345,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_42476,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_42339,c_42345])).

cnf(c_42347,plain,
    ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_42535,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_42476,c_42347])).

cnf(c_154993,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
    | v2_funct_1(sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_153935,c_37,c_42535])).

cnf(c_159905,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | v2_funct_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_159902,c_154993])).

cnf(c_42342,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_42560,plain,
    ( k1_relset_1(sK1,sK0,sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_42339,c_42342])).

cnf(c_42344,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_42517,plain,
    ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_42339,c_42344])).

cnf(c_42564,plain,
    ( k1_relat_1(sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_42560,c_42517])).

cnf(c_42630,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_42564,c_38,c_24,c_665,c_7560,c_25732])).

cnf(c_42612,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
    | v2_funct_1(sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_42535,c_37])).

cnf(c_42633,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | v2_funct_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_42630,c_42612])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_153042,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_153054,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_153646,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_153042,c_153054])).

cnf(c_27,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_153648,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_153646,c_27])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | v2_funct_1(X1)
    | ~ v2_funct_1(k5_relat_1(X0,X1))
    | k1_relat_1(X1) != k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_153062,plain,
    ( k1_relat_1(X0) != k2_relat_1(X1)
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) = iProver_top
    | v2_funct_1(k5_relat_1(X1,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_159914,plain,
    ( k2_relat_1(X0) != sK1
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_159902,c_153062])).

cnf(c_86233,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_85913,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(arAF1_k2_zfmisc_1_0_1(sK1)))
    | ~ iProver_ARSWP_232 ),
    inference(arg_filter_abstr,[status(unp)],[c_28])).

cnf(c_86212,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(arAF1_k2_zfmisc_1_0_1(sK1))) = iProver_top
    | iProver_ARSWP_232 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_85913])).

cnf(c_85908,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(arAF1_k2_zfmisc_1_0_1(X1)))
    | ~ iProver_ARSWP_227
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(arg_filter_abstr,[status(unp)],[c_16])).

cnf(c_86217,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(arAF1_k2_zfmisc_1_0_1(X0))) != iProver_top
    | iProver_ARSWP_227 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_85908])).

cnf(c_87766,plain,
    ( k1_relset_1(sK1,X0,sK3) = sK1
    | k1_xboole_0 = X0
    | v1_funct_2(sK3,sK1,X0) != iProver_top
    | iProver_ARSWP_232 != iProver_top
    | iProver_ARSWP_227 != iProver_top ),
    inference(superposition,[status(thm)],[c_86212,c_86217])).

cnf(c_89469,plain,
    ( k1_relset_1(sK1,sK0,sK3) = sK1
    | sK0 = k1_xboole_0
    | iProver_ARSWP_232 != iProver_top
    | iProver_ARSWP_227 != iProver_top ),
    inference(superposition,[status(thm)],[c_86233,c_87766])).

cnf(c_25711,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k1_relset_1(sK1,sK0,sK3) = sK1
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_89472,plain,
    ( k1_relset_1(sK1,sK0,sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_89469,c_29,c_28,c_24,c_25711])).

cnf(c_85901,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(arAF1_k2_zfmisc_1_0_1(X1)))
    | ~ iProver_ARSWP_220
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(arg_filter_abstr,[status(unp)],[c_7])).

cnf(c_86224,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(arAF1_k2_zfmisc_1_0_1(X0))) != iProver_top
    | iProver_ARSWP_220 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_85901])).

cnf(c_87329,plain,
    ( k1_relset_1(sK1,X0,sK3) = k1_relat_1(sK3)
    | iProver_ARSWP_232 != iProver_top
    | iProver_ARSWP_220 != iProver_top ),
    inference(superposition,[status(thm)],[c_86212,c_86224])).

cnf(c_89477,plain,
    ( k1_relat_1(sK3) = sK1
    | iProver_ARSWP_232 != iProver_top
    | iProver_ARSWP_220 != iProver_top ),
    inference(superposition,[status(thm)],[c_89472,c_87329])).

cnf(c_89538,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_89477,c_38,c_24,c_665,c_7560,c_25732])).

cnf(c_86240,plain,
    ( k1_relat_1(X0) != k2_relat_1(X1)
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) = iProver_top
    | v2_funct_1(k5_relat_1(X1,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_89571,plain,
    ( k2_relat_1(X0) != sK1
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_89538,c_86240])).

cnf(c_39,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_42451,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_42452,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42451])).

cnf(c_89925,plain,
    ( v1_funct_1(X0) != iProver_top
    | k2_relat_1(X0) != sK1
    | v1_relat_1(X0) != iProver_top
    | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_89571,c_37,c_39,c_42452])).

cnf(c_89926,plain,
    ( k2_relat_1(X0) != sK1
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_89925])).

cnf(c_192895,plain,
    ( v1_funct_1(X0) != iProver_top
    | k2_relat_1(X0) != sK1
    | v1_relat_1(X0) != iProver_top
    | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_159914,c_37,c_39,c_42452,c_89571])).

cnf(c_192896,plain,
    ( k2_relat_1(X0) != sK1
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_192895])).

cnf(c_192905,plain,
    ( v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_153648,c_192896])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_152760,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(arAF1_k1_partfun1_0_1_2(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | ~ iProver_ARSWP_239 ),
    inference(arg_filter_abstr,[status(unp)],[c_17])).

cnf(c_153035,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(arAF1_k1_partfun1_0_1_2(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | iProver_ARSWP_239 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_152760])).

cnf(c_154889,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(arAF1_k1_partfun1_0_1_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,sK0))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | iProver_ARSWP_239 != iProver_top ),
    inference(superposition,[status(thm)],[c_153045,c_153035])).

cnf(c_155033,plain,
    ( v1_funct_1(X0) != iProver_top
    | m1_subset_1(arAF1_k1_partfun1_0_1_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,sK0))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | iProver_ARSWP_239 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_154889,c_37])).

cnf(c_155034,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(arAF1_k1_partfun1_0_1_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,sK0))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | iProver_ARSWP_239 != iProver_top ),
    inference(renaming,[status(thm)],[c_155033])).

cnf(c_155045,plain,
    ( m1_subset_1(arAF1_k1_partfun1_0_1_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | iProver_ARSWP_239 != iProver_top ),
    inference(superposition,[status(thm)],[c_153042,c_155034])).

cnf(c_33,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_34,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_155240,plain,
    ( m1_subset_1(arAF1_k1_partfun1_0_1_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | iProver_ARSWP_239 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_155045,c_34])).

cnf(c_10,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_26,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_373,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_26])).

cnf(c_374,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_373])).

cnf(c_19,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_382,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_374,c_19])).

cnf(c_152764,plain,
    ( ~ m1_subset_1(arAF1_k1_partfun1_0_1_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ iProver_ARSWP_243
    | k6_partfun1(sK0) = arAF1_k1_partfun1_0_1_2(sK0,sK1) ),
    inference(arg_filter_abstr,[status(unp)],[c_382])).

cnf(c_153031,plain,
    ( k6_partfun1(sK0) = arAF1_k1_partfun1_0_1_2(sK0,sK1)
    | m1_subset_1(arAF1_k1_partfun1_0_1_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | iProver_ARSWP_243 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_152764])).

cnf(c_155259,plain,
    ( arAF1_k1_partfun1_0_1_2(sK0,sK1) = k6_partfun1(sK0)
    | iProver_ARSWP_243 != iProver_top
    | iProver_ARSWP_239 != iProver_top ),
    inference(superposition,[status(thm)],[c_155240,c_153031])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_152762,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | ~ iProver_ARSWP_241
    | arAF1_k1_partfun1_0_1_2(X4,X5) = k5_relat_1(X3,X0) ),
    inference(arg_filter_abstr,[status(unp)],[c_20])).

cnf(c_153033,plain,
    ( arAF1_k1_partfun1_0_1_2(X0,X1) = k5_relat_1(X2,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | iProver_ARSWP_241 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_152762])).

cnf(c_153877,plain,
    ( k5_relat_1(sK2,X0) = arAF1_k1_partfun1_0_1_2(sK0,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | iProver_ARSWP_241 != iProver_top ),
    inference(superposition,[status(thm)],[c_153042,c_153033])).

cnf(c_154214,plain,
    ( v1_funct_1(X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | k5_relat_1(sK2,X0) = arAF1_k1_partfun1_0_1_2(sK0,sK1)
    | iProver_ARSWP_241 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_153877,c_34])).

cnf(c_154215,plain,
    ( k5_relat_1(sK2,X0) = arAF1_k1_partfun1_0_1_2(sK0,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | iProver_ARSWP_241 != iProver_top ),
    inference(renaming,[status(thm)],[c_154214])).

cnf(c_154225,plain,
    ( arAF1_k1_partfun1_0_1_2(sK0,sK1) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK3) != iProver_top
    | iProver_ARSWP_241 != iProver_top ),
    inference(superposition,[status(thm)],[c_153045,c_154215])).

cnf(c_154260,plain,
    ( arAF1_k1_partfun1_0_1_2(sK0,sK1) = k5_relat_1(sK2,sK3)
    | iProver_ARSWP_241 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_154225,c_37])).

cnf(c_156074,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | iProver_ARSWP_243 != iProver_top
    | iProver_ARSWP_241 != iProver_top
    | iProver_ARSWP_239 != iProver_top ),
    inference(superposition,[status(thm)],[c_155259,c_154260])).

cnf(c_36,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_119896,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_119899,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_119901,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_120312,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_119899,c_119901])).

cnf(c_85442,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_85444,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_85715,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_85442,c_85444])).

cnf(c_120351,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_120312,c_37,c_85715])).

cnf(c_120352,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_120351])).

cnf(c_120360,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_119896,c_120352])).

cnf(c_85545,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(X1,X2,sK1,sK0,X0,sK3) = k5_relat_1(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_85614,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_85545])).

cnf(c_120386,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_120360,c_33,c_31,c_30,c_28,c_85614])).

cnf(c_119893,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_382])).

cnf(c_120389,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_120386,c_119893])).

cnf(c_119904,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_120513,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_120386,c_119904])).

cnf(c_159685,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_156074,c_34,c_36,c_37,c_39,c_120389,c_120513])).

cnf(c_192955,plain,
    ( v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_192905,c_159685])).

cnf(c_85572,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_85573,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_85572])).

cnf(c_192980,plain,
    ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_192955,c_34,c_36,c_85573])).

cnf(c_2,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_153060,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_192986,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_192980,c_153060])).

cnf(c_195818,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_159905,c_42633,c_192986])).

cnf(c_154226,plain,
    ( arAF1_k1_partfun1_0_1_2(sK0,sK1) = k5_relat_1(sK2,sK2)
    | v1_funct_1(sK2) != iProver_top
    | iProver_ARSWP_241 != iProver_top ),
    inference(superposition,[status(thm)],[c_153042,c_154215])).

cnf(c_154337,plain,
    ( arAF1_k1_partfun1_0_1_2(sK0,sK1) = k5_relat_1(sK2,sK2)
    | iProver_ARSWP_241 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_154226,c_34])).

cnf(c_154343,plain,
    ( k5_relat_1(sK2,sK2) = k5_relat_1(sK2,sK3)
    | iProver_ARSWP_241 != iProver_top ),
    inference(superposition,[status(thm)],[c_154260,c_154337])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k1_relat_1(X1) != k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_153057,plain,
    ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k1_relat_1(X1) != k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v2_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_154795,plain,
    ( k2_funct_1(sK3) = sK2
    | k6_partfun1(k2_relat_1(sK3)) != k5_relat_1(sK2,sK2)
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | iProver_ARSWP_241 != iProver_top ),
    inference(superposition,[status(thm)],[c_154343,c_153057])).

cnf(c_153645,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_153045,c_153054])).

cnf(c_21,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X3,X1,X0)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_386,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k1_partfun1(X1,X2,X2,X1,X0,X3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X2,X1,X3) = X1
    | k6_partfun1(X1) != k6_partfun1(sK0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_26])).

cnf(c_387,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X0)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0
    | k6_partfun1(sK0) != k6_partfun1(sK0) ),
    inference(unflattening,[status(thm)],[c_386])).

cnf(c_470,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_387])).

cnf(c_152765,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | ~ iProver_ARSWP_244
    | k2_relset_1(X1,sK0,X0) = sK0
    | arAF1_k1_partfun1_0_1_2(sK0,X1) != arAF1_k1_partfun1_0_1_2(sK0,sK1) ),
    inference(arg_filter_abstr,[status(unp)],[c_470])).

cnf(c_153030,plain,
    ( k2_relset_1(X0,sK0,X1) = sK0
    | arAF1_k1_partfun1_0_1_2(sK0,X0) != arAF1_k1_partfun1_0_1_2(sK0,sK1)
    | v1_funct_2(X1,X0,sK0) != iProver_top
    | v1_funct_2(X2,sK0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | iProver_ARSWP_244 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_152765])).

cnf(c_153404,plain,
    ( k2_relset_1(sK1,sK0,X0) = sK0
    | v1_funct_2(X1,sK0,sK1) != iProver_top
    | v1_funct_2(X0,sK1,sK0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | iProver_ARSWP_244 != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_153030])).

cnf(c_153462,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | v1_funct_2(X0,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | iProver_ARSWP_244 != iProver_top ),
    inference(superposition,[status(thm)],[c_153045,c_153404])).

cnf(c_32,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_35,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_119892,plain,
    ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X0,sK0,X2) = sK0
    | v1_funct_2(X2,X0,sK0) != iProver_top
    | v1_funct_2(X1,sK0,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_470])).

cnf(c_120097,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_119892])).

cnf(c_153487,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_153462,c_34,c_35,c_36,c_37,c_38,c_39,c_120097])).

cnf(c_153651,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_153645,c_153487])).

cnf(c_154796,plain,
    ( k5_relat_1(sK2,sK2) != k6_partfun1(sK0)
    | k2_funct_1(sK3) = sK2
    | k1_relat_1(sK3) != sK1
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | iProver_ARSWP_241 != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_154795,c_153648,c_153651])).

cnf(c_120743,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_120389,c_34,c_36,c_37,c_39,c_120513])).

cnf(c_119910,plain,
    ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k1_relat_1(X1) != k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v2_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_120747,plain,
    ( k2_funct_1(sK3) = sK2
    | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_120743,c_119910])).

cnf(c_119907,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_120208,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_119896,c_119907])).

cnf(c_120210,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_120208,c_27])).

cnf(c_120207,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_119899,c_119907])).

cnf(c_120142,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_120097,c_34,c_35,c_36,c_37,c_38,c_39])).

cnf(c_120213,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_120207,c_120142])).

cnf(c_119905,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_120255,plain,
    ( k1_relset_1(sK1,sK0,sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_119899,c_119905])).

cnf(c_120727,plain,
    ( k1_relset_1(sK1,sK0,sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_120255,c_29,c_28,c_24,c_25711])).

cnf(c_119908,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_120230,plain,
    ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_119899,c_119908])).

cnf(c_120730,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(demodulation,[status(thm)],[c_120727,c_120230])).

cnf(c_120748,plain,
    ( k2_funct_1(sK3) = sK2
    | k6_partfun1(sK0) != k6_partfun1(sK0)
    | sK1 != sK1
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_120747,c_120210,c_120213,c_120730])).

cnf(c_120749,plain,
    ( k2_funct_1(sK3) = sK2
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_120748])).

cnf(c_154799,plain,
    ( v2_funct_1(sK3) != iProver_top
    | k2_funct_1(sK3) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_154796,c_34,c_36,c_37,c_39,c_42452,c_85573,c_120749])).

cnf(c_154800,plain,
    ( k2_funct_1(sK3) = sK2
    | v2_funct_1(sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_154799])).

cnf(c_192989,plain,
    ( k2_funct_1(sK3) = sK2 ),
    inference(superposition,[status(thm)],[c_192986,c_154800])).

cnf(c_195820,plain,
    ( k5_relat_1(sK3,sK2) = k6_partfun1(sK1) ),
    inference(light_normalisation,[status(thm)],[c_195818,c_192989])).

cnf(c_196460,plain,
    ( k2_funct_1(sK2) = sK3
    | k6_partfun1(k2_relat_1(sK2)) != k6_partfun1(sK1)
    | k1_relat_1(sK2) != k2_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_195820,c_153057])).

cnf(c_154019,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_153042,c_153048])).

cnf(c_153699,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_153042,c_153055])).

cnf(c_154023,plain,
    ( k1_relat_1(sK2) = sK0
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_154019,c_153699])).

cnf(c_23,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_7557,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_639])).

cnf(c_7558,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7557])).

cnf(c_85439,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_85445,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_85692,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_85439,c_85445])).

cnf(c_85447,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_85621,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_85439,c_85447])).

cnf(c_85696,plain,
    ( k1_relat_1(sK2) = sK0
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_85692,c_85621])).

cnf(c_159277,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_154023,c_35,c_23,c_665,c_7558,c_85696])).

cnf(c_196461,plain,
    ( k2_funct_1(sK2) = sK3
    | k6_partfun1(sK1) != k6_partfun1(sK1)
    | sK0 != sK0
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_196460,c_153648,c_153651,c_159277])).

cnf(c_196462,plain,
    ( k2_funct_1(sK2) = sK3
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_196461])).

cnf(c_22,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_25,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_41,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_196462,c_85573,c_42452,c_22,c_41,c_39,c_37,c_36,c_34])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 09:28:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 39.86/5.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 39.86/5.50  
% 39.86/5.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 39.86/5.50  
% 39.86/5.50  ------  iProver source info
% 39.86/5.50  
% 39.86/5.50  git: date: 2020-06-30 10:37:57 +0100
% 39.86/5.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 39.86/5.50  git: non_committed_changes: false
% 39.86/5.50  git: last_make_outside_of_git: false
% 39.86/5.50  
% 39.86/5.50  ------ 
% 39.86/5.50  ------ Parsing...
% 39.86/5.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 39.86/5.50  
% 39.86/5.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 39.86/5.50  
% 39.86/5.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 39.86/5.50  
% 39.86/5.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.86/5.50  ------ Proving...
% 39.86/5.50  ------ Problem Properties 
% 39.86/5.50  
% 39.86/5.50  
% 39.86/5.50  clauses                                 33
% 39.86/5.50  conjectures                             11
% 39.86/5.50  EPR                                     7
% 39.86/5.50  Horn                                    29
% 39.86/5.50  unary                                   13
% 39.86/5.50  binary                                  4
% 39.86/5.50  lits                                    103
% 39.86/5.50  lits eq                                 28
% 39.86/5.50  fd_pure                                 0
% 39.86/5.50  fd_pseudo                               0
% 39.86/5.50  fd_cond                                 3
% 39.86/5.50  fd_pseudo_cond                          1
% 39.86/5.50  AC symbols                              0
% 39.86/5.50  
% 39.86/5.50  ------ Input Options Time Limit: Unbounded
% 39.86/5.50  
% 39.86/5.50  
% 39.86/5.50  
% 39.86/5.50  
% 39.86/5.50  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 39.86/5.50  Current options:
% 39.86/5.50  ------ 
% 39.86/5.50  
% 39.86/5.50  
% 39.86/5.50  
% 39.86/5.50  
% 39.86/5.50  ------ Proving...
% 39.86/5.50  
% 39.86/5.50  
% 39.86/5.50  ------ Preprocessing... sf_s  rm: 7 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.86/5.50  
% 39.86/5.50  ------ Proving...
% 39.86/5.50  
% 39.86/5.50  
% 39.86/5.50  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.86/5.50  
% 39.86/5.50  ------ Proving...
% 39.86/5.50  
% 39.86/5.50  
% 39.86/5.50  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.86/5.50  
% 39.86/5.50  ------ Proving...
% 39.86/5.50  
% 39.86/5.50  
% 39.86/5.50  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.86/5.50  
% 39.86/5.50  ------ Proving...
% 39.86/5.50  
% 39.86/5.50  
% 39.86/5.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.86/5.50  
% 39.86/5.50  ------ Proving...
% 39.86/5.50  
% 39.86/5.50  
% 39.86/5.50  ------ Preprocessing... sf_s  rm: 8 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.86/5.50  
% 39.86/5.50  ------ Proving...
% 39.86/5.50  
% 39.86/5.50  
% 39.86/5.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.86/5.50  
% 39.86/5.50  ------ Proving...
% 39.86/5.50  
% 39.86/5.50  
% 39.86/5.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.86/5.50  
% 39.86/5.50  ------ Proving...
% 39.86/5.50  
% 39.86/5.50  
% 39.86/5.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.86/5.50  
% 39.86/5.50  ------ Proving...
% 39.86/5.50  
% 39.86/5.50  
% 39.86/5.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.86/5.50  
% 39.86/5.50  ------ Proving...
% 39.86/5.50  
% 39.86/5.50  
% 39.86/5.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 39.86/5.50  
% 39.86/5.50  ------ Proving...
% 39.86/5.50  
% 39.86/5.50  
% 39.86/5.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 39.86/5.50  
% 39.86/5.50  ------ Proving...
% 39.86/5.50  
% 39.86/5.50  
% 39.86/5.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 39.86/5.50  
% 39.86/5.50  ------ Proving...
% 39.86/5.50  
% 39.86/5.50  
% 39.86/5.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 39.86/5.50  
% 39.86/5.50  ------ Proving...
% 39.86/5.50  
% 39.86/5.50  
% 39.86/5.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 39.86/5.50  
% 39.86/5.50  ------ Proving...
% 39.86/5.50  
% 39.86/5.50  
% 39.86/5.50  % SZS status Theorem for theBenchmark.p
% 39.86/5.50  
% 39.86/5.50  % SZS output start CNFRefutation for theBenchmark.p
% 39.86/5.50  
% 39.86/5.50  fof(f15,conjecture,(
% 39.86/5.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 39.86/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.86/5.50  
% 39.86/5.50  fof(f16,negated_conjecture,(
% 39.86/5.50    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 39.86/5.50    inference(negated_conjecture,[],[f15])).
% 39.86/5.50  
% 39.86/5.50  fof(f37,plain,(
% 39.86/5.50    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 39.86/5.50    inference(ennf_transformation,[],[f16])).
% 39.86/5.50  
% 39.86/5.50  fof(f38,plain,(
% 39.86/5.50    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 39.86/5.50    inference(flattening,[],[f37])).
% 39.86/5.50  
% 39.86/5.50  fof(f42,plain,(
% 39.86/5.50    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 39.86/5.50    introduced(choice_axiom,[])).
% 39.86/5.50  
% 39.86/5.50  fof(f41,plain,(
% 39.86/5.50    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 39.86/5.50    introduced(choice_axiom,[])).
% 39.86/5.50  
% 39.86/5.50  fof(f43,plain,(
% 39.86/5.50    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 39.86/5.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f38,f42,f41])).
% 39.86/5.50  
% 39.86/5.50  fof(f72,plain,(
% 39.86/5.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 39.86/5.50    inference(cnf_transformation,[],[f43])).
% 39.86/5.50  
% 39.86/5.50  fof(f9,axiom,(
% 39.86/5.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 39.86/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.86/5.50  
% 39.86/5.50  fof(f29,plain,(
% 39.86/5.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 39.86/5.50    inference(ennf_transformation,[],[f9])).
% 39.86/5.50  
% 39.86/5.50  fof(f30,plain,(
% 39.86/5.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 39.86/5.50    inference(flattening,[],[f29])).
% 39.86/5.50  
% 39.86/5.50  fof(f40,plain,(
% 39.86/5.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 39.86/5.50    inference(nnf_transformation,[],[f30])).
% 39.86/5.50  
% 39.86/5.50  fof(f55,plain,(
% 39.86/5.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 39.86/5.50    inference(cnf_transformation,[],[f40])).
% 39.86/5.50  
% 39.86/5.50  fof(f6,axiom,(
% 39.86/5.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 39.86/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.86/5.50  
% 39.86/5.50  fof(f25,plain,(
% 39.86/5.50    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 39.86/5.50    inference(ennf_transformation,[],[f6])).
% 39.86/5.50  
% 39.86/5.50  fof(f51,plain,(
% 39.86/5.50    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 39.86/5.50    inference(cnf_transformation,[],[f25])).
% 39.86/5.50  
% 39.86/5.50  fof(f71,plain,(
% 39.86/5.50    v1_funct_2(sK3,sK1,sK0)),
% 39.86/5.50    inference(cnf_transformation,[],[f43])).
% 39.86/5.50  
% 39.86/5.50  fof(f76,plain,(
% 39.86/5.50    k1_xboole_0 != sK0),
% 39.86/5.50    inference(cnf_transformation,[],[f43])).
% 39.86/5.50  
% 39.86/5.50  fof(f5,axiom,(
% 39.86/5.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 39.86/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.86/5.50  
% 39.86/5.50  fof(f24,plain,(
% 39.86/5.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 39.86/5.50    inference(ennf_transformation,[],[f5])).
% 39.86/5.50  
% 39.86/5.50  fof(f50,plain,(
% 39.86/5.50    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 39.86/5.50    inference(cnf_transformation,[],[f24])).
% 39.86/5.50  
% 39.86/5.50  fof(f3,axiom,(
% 39.86/5.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 39.86/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.86/5.50  
% 39.86/5.50  fof(f20,plain,(
% 39.86/5.50    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 39.86/5.50    inference(ennf_transformation,[],[f3])).
% 39.86/5.50  
% 39.86/5.50  fof(f21,plain,(
% 39.86/5.50    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 39.86/5.50    inference(flattening,[],[f20])).
% 39.86/5.50  
% 39.86/5.50  fof(f47,plain,(
% 39.86/5.50    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 39.86/5.50    inference(cnf_transformation,[],[f21])).
% 39.86/5.50  
% 39.86/5.50  fof(f13,axiom,(
% 39.86/5.50    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 39.86/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.86/5.50  
% 39.86/5.50  fof(f65,plain,(
% 39.86/5.50    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 39.86/5.50    inference(cnf_transformation,[],[f13])).
% 39.86/5.50  
% 39.86/5.50  fof(f81,plain,(
% 39.86/5.50    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 39.86/5.50    inference(definition_unfolding,[],[f47,f65])).
% 39.86/5.50  
% 39.86/5.50  fof(f70,plain,(
% 39.86/5.50    v1_funct_1(sK3)),
% 39.86/5.50    inference(cnf_transformation,[],[f43])).
% 39.86/5.50  
% 39.86/5.50  fof(f69,plain,(
% 39.86/5.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 39.86/5.50    inference(cnf_transformation,[],[f43])).
% 39.86/5.50  
% 39.86/5.50  fof(f7,axiom,(
% 39.86/5.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 39.86/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.86/5.50  
% 39.86/5.50  fof(f26,plain,(
% 39.86/5.50    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 39.86/5.50    inference(ennf_transformation,[],[f7])).
% 39.86/5.50  
% 39.86/5.50  fof(f52,plain,(
% 39.86/5.50    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 39.86/5.50    inference(cnf_transformation,[],[f26])).
% 39.86/5.50  
% 39.86/5.50  fof(f73,plain,(
% 39.86/5.50    k2_relset_1(sK0,sK1,sK2) = sK1),
% 39.86/5.50    inference(cnf_transformation,[],[f43])).
% 39.86/5.50  
% 39.86/5.50  fof(f1,axiom,(
% 39.86/5.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 39.86/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.86/5.50  
% 39.86/5.50  fof(f18,plain,(
% 39.86/5.50    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 39.86/5.50    inference(ennf_transformation,[],[f1])).
% 39.86/5.50  
% 39.86/5.50  fof(f19,plain,(
% 39.86/5.50    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 39.86/5.50    inference(flattening,[],[f18])).
% 39.86/5.50  
% 39.86/5.50  fof(f45,plain,(
% 39.86/5.50    ( ! [X0,X1] : (v2_funct_1(X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 39.86/5.50    inference(cnf_transformation,[],[f19])).
% 39.86/5.50  
% 39.86/5.50  fof(f10,axiom,(
% 39.86/5.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 39.86/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.86/5.50  
% 39.86/5.50  fof(f31,plain,(
% 39.86/5.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 39.86/5.50    inference(ennf_transformation,[],[f10])).
% 39.86/5.50  
% 39.86/5.50  fof(f32,plain,(
% 39.86/5.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 39.86/5.50    inference(flattening,[],[f31])).
% 39.86/5.50  
% 39.86/5.50  fof(f62,plain,(
% 39.86/5.50    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 39.86/5.50    inference(cnf_transformation,[],[f32])).
% 39.86/5.50  
% 39.86/5.50  fof(f67,plain,(
% 39.86/5.50    v1_funct_1(sK2)),
% 39.86/5.50    inference(cnf_transformation,[],[f43])).
% 39.86/5.50  
% 39.86/5.50  fof(f8,axiom,(
% 39.86/5.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 39.86/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.86/5.50  
% 39.86/5.50  fof(f27,plain,(
% 39.86/5.50    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 39.86/5.50    inference(ennf_transformation,[],[f8])).
% 39.86/5.50  
% 39.86/5.50  fof(f28,plain,(
% 39.86/5.50    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 39.86/5.50    inference(flattening,[],[f27])).
% 39.86/5.50  
% 39.86/5.50  fof(f39,plain,(
% 39.86/5.50    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 39.86/5.50    inference(nnf_transformation,[],[f28])).
% 39.86/5.50  
% 39.86/5.50  fof(f53,plain,(
% 39.86/5.50    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 39.86/5.50    inference(cnf_transformation,[],[f39])).
% 39.86/5.50  
% 39.86/5.50  fof(f74,plain,(
% 39.86/5.50    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 39.86/5.50    inference(cnf_transformation,[],[f43])).
% 39.86/5.50  
% 39.86/5.50  fof(f11,axiom,(
% 39.86/5.50    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 39.86/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.86/5.50  
% 39.86/5.50  fof(f17,plain,(
% 39.86/5.50    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 39.86/5.50    inference(pure_predicate_removal,[],[f11])).
% 39.86/5.50  
% 39.86/5.50  fof(f63,plain,(
% 39.86/5.50    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 39.86/5.50    inference(cnf_transformation,[],[f17])).
% 39.86/5.50  
% 39.86/5.50  fof(f12,axiom,(
% 39.86/5.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 39.86/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.86/5.50  
% 39.86/5.50  fof(f33,plain,(
% 39.86/5.50    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 39.86/5.50    inference(ennf_transformation,[],[f12])).
% 39.86/5.50  
% 39.86/5.50  fof(f34,plain,(
% 39.86/5.50    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 39.86/5.50    inference(flattening,[],[f33])).
% 39.86/5.50  
% 39.86/5.50  fof(f64,plain,(
% 39.86/5.50    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 39.86/5.50    inference(cnf_transformation,[],[f34])).
% 39.86/5.50  
% 39.86/5.50  fof(f2,axiom,(
% 39.86/5.50    ! [X0] : v2_funct_1(k6_relat_1(X0))),
% 39.86/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.86/5.50  
% 39.86/5.50  fof(f46,plain,(
% 39.86/5.50    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 39.86/5.50    inference(cnf_transformation,[],[f2])).
% 39.86/5.50  
% 39.86/5.50  fof(f79,plain,(
% 39.86/5.50    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 39.86/5.50    inference(definition_unfolding,[],[f46,f65])).
% 39.86/5.50  
% 39.86/5.50  fof(f4,axiom,(
% 39.86/5.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 39.86/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.86/5.50  
% 39.86/5.50  fof(f22,plain,(
% 39.86/5.50    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 39.86/5.50    inference(ennf_transformation,[],[f4])).
% 39.86/5.50  
% 39.86/5.50  fof(f23,plain,(
% 39.86/5.50    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 39.86/5.50    inference(flattening,[],[f22])).
% 39.86/5.50  
% 39.86/5.50  fof(f49,plain,(
% 39.86/5.50    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 39.86/5.50    inference(cnf_transformation,[],[f23])).
% 39.86/5.50  
% 39.86/5.50  fof(f82,plain,(
% 39.86/5.50    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 39.86/5.50    inference(definition_unfolding,[],[f49,f65])).
% 39.86/5.50  
% 39.86/5.50  fof(f14,axiom,(
% 39.86/5.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 39.86/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.86/5.50  
% 39.86/5.50  fof(f35,plain,(
% 39.86/5.50    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 39.86/5.50    inference(ennf_transformation,[],[f14])).
% 39.86/5.50  
% 39.86/5.50  fof(f36,plain,(
% 39.86/5.50    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 39.86/5.50    inference(flattening,[],[f35])).
% 39.86/5.50  
% 39.86/5.50  fof(f66,plain,(
% 39.86/5.50    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 39.86/5.50    inference(cnf_transformation,[],[f36])).
% 39.86/5.50  
% 39.86/5.50  fof(f68,plain,(
% 39.86/5.50    v1_funct_2(sK2,sK0,sK1)),
% 39.86/5.50    inference(cnf_transformation,[],[f43])).
% 39.86/5.50  
% 39.86/5.50  fof(f77,plain,(
% 39.86/5.50    k1_xboole_0 != sK1),
% 39.86/5.50    inference(cnf_transformation,[],[f43])).
% 39.86/5.50  
% 39.86/5.50  fof(f78,plain,(
% 39.86/5.50    k2_funct_1(sK2) != sK3),
% 39.86/5.50    inference(cnf_transformation,[],[f43])).
% 39.86/5.50  
% 39.86/5.50  fof(f75,plain,(
% 39.86/5.50    v2_funct_1(sK2)),
% 39.86/5.50    inference(cnf_transformation,[],[f43])).
% 39.86/5.50  
% 39.86/5.50  cnf(c_28,negated_conjecture,
% 39.86/5.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 39.86/5.50      inference(cnf_transformation,[],[f72]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_153045,plain,
% 39.86/5.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 39.86/5.50      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_16,plain,
% 39.86/5.50      ( ~ v1_funct_2(X0,X1,X2)
% 39.86/5.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 39.86/5.50      | k1_relset_1(X1,X2,X0) = X1
% 39.86/5.50      | k1_xboole_0 = X2 ),
% 39.86/5.50      inference(cnf_transformation,[],[f55]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_153048,plain,
% 39.86/5.50      ( k1_relset_1(X0,X1,X2) = X0
% 39.86/5.50      | k1_xboole_0 = X1
% 39.86/5.50      | v1_funct_2(X2,X0,X1) != iProver_top
% 39.86/5.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 39.86/5.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_154018,plain,
% 39.86/5.50      ( k1_relset_1(sK1,sK0,sK3) = sK1
% 39.86/5.50      | sK0 = k1_xboole_0
% 39.86/5.50      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 39.86/5.50      inference(superposition,[status(thm)],[c_153045,c_153048]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_7,plain,
% 39.86/5.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 39.86/5.50      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 39.86/5.50      inference(cnf_transformation,[],[f51]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_153055,plain,
% 39.86/5.50      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 39.86/5.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 39.86/5.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_153698,plain,
% 39.86/5.50      ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
% 39.86/5.50      inference(superposition,[status(thm)],[c_153045,c_153055]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_154030,plain,
% 39.86/5.50      ( k1_relat_1(sK3) = sK1
% 39.86/5.50      | sK0 = k1_xboole_0
% 39.86/5.50      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 39.86/5.50      inference(demodulation,[status(thm)],[c_154018,c_153698]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_29,negated_conjecture,
% 39.86/5.50      ( v1_funct_2(sK3,sK1,sK0) ),
% 39.86/5.50      inference(cnf_transformation,[],[f71]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_38,plain,
% 39.86/5.50      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 39.86/5.50      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_24,negated_conjecture,
% 39.86/5.50      ( k1_xboole_0 != sK0 ),
% 39.86/5.50      inference(cnf_transformation,[],[f76]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_638,plain,( X0 = X0 ),theory(equality) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_665,plain,
% 39.86/5.50      ( k1_xboole_0 = k1_xboole_0 ),
% 39.86/5.50      inference(instantiation,[status(thm)],[c_638]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_639,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_7559,plain,
% 39.86/5.50      ( sK0 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK0 ),
% 39.86/5.50      inference(instantiation,[status(thm)],[c_639]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_7560,plain,
% 39.86/5.50      ( sK0 != k1_xboole_0
% 39.86/5.50      | k1_xboole_0 = sK0
% 39.86/5.50      | k1_xboole_0 != k1_xboole_0 ),
% 39.86/5.50      inference(instantiation,[status(thm)],[c_7559]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_25678,plain,
% 39.86/5.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 39.86/5.50      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_25679,plain,
% 39.86/5.50      ( k1_relset_1(X0,X1,X2) = X0
% 39.86/5.50      | k1_xboole_0 = X1
% 39.86/5.50      | v1_funct_2(X2,X0,X1) != iProver_top
% 39.86/5.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 39.86/5.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_25731,plain,
% 39.86/5.50      ( k1_relset_1(sK1,sK0,sK3) = sK1
% 39.86/5.50      | sK0 = k1_xboole_0
% 39.86/5.50      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 39.86/5.50      inference(superposition,[status(thm)],[c_25678,c_25679]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_25680,plain,
% 39.86/5.50      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 39.86/5.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 39.86/5.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_25722,plain,
% 39.86/5.50      ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
% 39.86/5.50      inference(superposition,[status(thm)],[c_25678,c_25680]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_25732,plain,
% 39.86/5.50      ( k1_relat_1(sK3) = sK1
% 39.86/5.50      | sK0 = k1_xboole_0
% 39.86/5.50      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 39.86/5.50      inference(demodulation,[status(thm)],[c_25731,c_25722]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_159902,plain,
% 39.86/5.50      ( k1_relat_1(sK3) = sK1 ),
% 39.86/5.50      inference(global_propositional_subsumption,
% 39.86/5.50                [status(thm)],
% 39.86/5.50                [c_154030,c_38,c_24,c_665,c_7560,c_25732]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_6,plain,
% 39.86/5.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 39.86/5.50      | v1_relat_1(X0) ),
% 39.86/5.50      inference(cnf_transformation,[],[f50]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_153056,plain,
% 39.86/5.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 39.86/5.50      | v1_relat_1(X0) = iProver_top ),
% 39.86/5.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_153516,plain,
% 39.86/5.50      ( v1_relat_1(sK3) = iProver_top ),
% 39.86/5.50      inference(superposition,[status(thm)],[c_153045,c_153056]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_4,plain,
% 39.86/5.50      ( ~ v1_relat_1(X0)
% 39.86/5.50      | ~ v1_funct_1(X0)
% 39.86/5.50      | ~ v2_funct_1(X0)
% 39.86/5.50      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
% 39.86/5.50      inference(cnf_transformation,[],[f81]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_153058,plain,
% 39.86/5.50      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
% 39.86/5.50      | v1_relat_1(X0) != iProver_top
% 39.86/5.50      | v1_funct_1(X0) != iProver_top
% 39.86/5.50      | v2_funct_1(X0) != iProver_top ),
% 39.86/5.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_153935,plain,
% 39.86/5.50      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
% 39.86/5.50      | v1_funct_1(sK3) != iProver_top
% 39.86/5.50      | v2_funct_1(sK3) != iProver_top ),
% 39.86/5.50      inference(superposition,[status(thm)],[c_153516,c_153058]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_30,negated_conjecture,
% 39.86/5.50      ( v1_funct_1(sK3) ),
% 39.86/5.50      inference(cnf_transformation,[],[f70]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_37,plain,
% 39.86/5.50      ( v1_funct_1(sK3) = iProver_top ),
% 39.86/5.50      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_42339,plain,
% 39.86/5.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 39.86/5.50      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_42345,plain,
% 39.86/5.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 39.86/5.50      | v1_relat_1(X0) = iProver_top ),
% 39.86/5.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_42476,plain,
% 39.86/5.50      ( v1_relat_1(sK3) = iProver_top ),
% 39.86/5.50      inference(superposition,[status(thm)],[c_42339,c_42345]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_42347,plain,
% 39.86/5.50      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
% 39.86/5.50      | v1_relat_1(X0) != iProver_top
% 39.86/5.50      | v1_funct_1(X0) != iProver_top
% 39.86/5.50      | v2_funct_1(X0) != iProver_top ),
% 39.86/5.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_42535,plain,
% 39.86/5.50      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
% 39.86/5.50      | v1_funct_1(sK3) != iProver_top
% 39.86/5.50      | v2_funct_1(sK3) != iProver_top ),
% 39.86/5.50      inference(superposition,[status(thm)],[c_42476,c_42347]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_154993,plain,
% 39.86/5.50      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
% 39.86/5.50      | v2_funct_1(sK3) != iProver_top ),
% 39.86/5.50      inference(global_propositional_subsumption,
% 39.86/5.50                [status(thm)],
% 39.86/5.50                [c_153935,c_37,c_42535]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_159905,plain,
% 39.86/5.50      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
% 39.86/5.50      | v2_funct_1(sK3) != iProver_top ),
% 39.86/5.50      inference(demodulation,[status(thm)],[c_159902,c_154993]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_42342,plain,
% 39.86/5.50      ( k1_relset_1(X0,X1,X2) = X0
% 39.86/5.50      | k1_xboole_0 = X1
% 39.86/5.50      | v1_funct_2(X2,X0,X1) != iProver_top
% 39.86/5.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 39.86/5.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_42560,plain,
% 39.86/5.50      ( k1_relset_1(sK1,sK0,sK3) = sK1
% 39.86/5.50      | sK0 = k1_xboole_0
% 39.86/5.50      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 39.86/5.50      inference(superposition,[status(thm)],[c_42339,c_42342]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_42344,plain,
% 39.86/5.50      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 39.86/5.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 39.86/5.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_42517,plain,
% 39.86/5.50      ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
% 39.86/5.50      inference(superposition,[status(thm)],[c_42339,c_42344]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_42564,plain,
% 39.86/5.50      ( k1_relat_1(sK3) = sK1
% 39.86/5.50      | sK0 = k1_xboole_0
% 39.86/5.50      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 39.86/5.50      inference(demodulation,[status(thm)],[c_42560,c_42517]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_42630,plain,
% 39.86/5.50      ( k1_relat_1(sK3) = sK1 ),
% 39.86/5.50      inference(global_propositional_subsumption,
% 39.86/5.50                [status(thm)],
% 39.86/5.50                [c_42564,c_38,c_24,c_665,c_7560,c_25732]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_42612,plain,
% 39.86/5.50      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
% 39.86/5.50      | v2_funct_1(sK3) != iProver_top ),
% 39.86/5.50      inference(global_propositional_subsumption,
% 39.86/5.50                [status(thm)],
% 39.86/5.50                [c_42535,c_37]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_42633,plain,
% 39.86/5.50      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
% 39.86/5.50      | v2_funct_1(sK3) != iProver_top ),
% 39.86/5.50      inference(demodulation,[status(thm)],[c_42630,c_42612]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_31,negated_conjecture,
% 39.86/5.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 39.86/5.50      inference(cnf_transformation,[],[f69]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_153042,plain,
% 39.86/5.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 39.86/5.50      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_8,plain,
% 39.86/5.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 39.86/5.50      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 39.86/5.50      inference(cnf_transformation,[],[f52]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_153054,plain,
% 39.86/5.50      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 39.86/5.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 39.86/5.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_153646,plain,
% 39.86/5.50      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 39.86/5.50      inference(superposition,[status(thm)],[c_153042,c_153054]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_27,negated_conjecture,
% 39.86/5.50      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 39.86/5.50      inference(cnf_transformation,[],[f73]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_153648,plain,
% 39.86/5.50      ( k2_relat_1(sK2) = sK1 ),
% 39.86/5.50      inference(light_normalisation,[status(thm)],[c_153646,c_27]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_0,plain,
% 39.86/5.50      ( ~ v1_relat_1(X0)
% 39.86/5.50      | ~ v1_relat_1(X1)
% 39.86/5.50      | ~ v1_funct_1(X0)
% 39.86/5.50      | ~ v1_funct_1(X1)
% 39.86/5.50      | v2_funct_1(X1)
% 39.86/5.50      | ~ v2_funct_1(k5_relat_1(X0,X1))
% 39.86/5.50      | k1_relat_1(X1) != k2_relat_1(X0) ),
% 39.86/5.50      inference(cnf_transformation,[],[f45]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_153062,plain,
% 39.86/5.50      ( k1_relat_1(X0) != k2_relat_1(X1)
% 39.86/5.50      | v1_relat_1(X1) != iProver_top
% 39.86/5.50      | v1_relat_1(X0) != iProver_top
% 39.86/5.50      | v1_funct_1(X1) != iProver_top
% 39.86/5.50      | v1_funct_1(X0) != iProver_top
% 39.86/5.50      | v2_funct_1(X0) = iProver_top
% 39.86/5.50      | v2_funct_1(k5_relat_1(X1,X0)) != iProver_top ),
% 39.86/5.50      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_159914,plain,
% 39.86/5.50      ( k2_relat_1(X0) != sK1
% 39.86/5.50      | v1_relat_1(X0) != iProver_top
% 39.86/5.50      | v1_relat_1(sK3) != iProver_top
% 39.86/5.50      | v1_funct_1(X0) != iProver_top
% 39.86/5.50      | v1_funct_1(sK3) != iProver_top
% 39.86/5.50      | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
% 39.86/5.50      | v2_funct_1(sK3) = iProver_top ),
% 39.86/5.50      inference(superposition,[status(thm)],[c_159902,c_153062]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_86233,plain,
% 39.86/5.50      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 39.86/5.50      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_85913,negated_conjecture,
% 39.86/5.50      ( m1_subset_1(sK3,k1_zfmisc_1(arAF1_k2_zfmisc_1_0_1(sK1)))
% 39.86/5.50      | ~ iProver_ARSWP_232 ),
% 39.86/5.50      inference(arg_filter_abstr,[status(unp)],[c_28]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_86212,plain,
% 39.86/5.50      ( m1_subset_1(sK3,k1_zfmisc_1(arAF1_k2_zfmisc_1_0_1(sK1))) = iProver_top
% 39.86/5.50      | iProver_ARSWP_232 != iProver_top ),
% 39.86/5.50      inference(predicate_to_equality,[status(thm)],[c_85913]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_85908,plain,
% 39.86/5.50      ( ~ v1_funct_2(X0,X1,X2)
% 39.86/5.50      | ~ m1_subset_1(X0,k1_zfmisc_1(arAF1_k2_zfmisc_1_0_1(X1)))
% 39.86/5.50      | ~ iProver_ARSWP_227
% 39.86/5.50      | k1_relset_1(X1,X2,X0) = X1
% 39.86/5.50      | k1_xboole_0 = X2 ),
% 39.86/5.50      inference(arg_filter_abstr,[status(unp)],[c_16]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_86217,plain,
% 39.86/5.50      ( k1_relset_1(X0,X1,X2) = X0
% 39.86/5.50      | k1_xboole_0 = X1
% 39.86/5.50      | v1_funct_2(X2,X0,X1) != iProver_top
% 39.86/5.50      | m1_subset_1(X2,k1_zfmisc_1(arAF1_k2_zfmisc_1_0_1(X0))) != iProver_top
% 39.86/5.50      | iProver_ARSWP_227 != iProver_top ),
% 39.86/5.50      inference(predicate_to_equality,[status(thm)],[c_85908]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_87766,plain,
% 39.86/5.50      ( k1_relset_1(sK1,X0,sK3) = sK1
% 39.86/5.50      | k1_xboole_0 = X0
% 39.86/5.50      | v1_funct_2(sK3,sK1,X0) != iProver_top
% 39.86/5.50      | iProver_ARSWP_232 != iProver_top
% 39.86/5.50      | iProver_ARSWP_227 != iProver_top ),
% 39.86/5.50      inference(superposition,[status(thm)],[c_86212,c_86217]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_89469,plain,
% 39.86/5.50      ( k1_relset_1(sK1,sK0,sK3) = sK1
% 39.86/5.50      | sK0 = k1_xboole_0
% 39.86/5.50      | iProver_ARSWP_232 != iProver_top
% 39.86/5.50      | iProver_ARSWP_227 != iProver_top ),
% 39.86/5.50      inference(superposition,[status(thm)],[c_86233,c_87766]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_25711,plain,
% 39.86/5.50      ( ~ v1_funct_2(sK3,sK1,sK0)
% 39.86/5.50      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 39.86/5.50      | k1_relset_1(sK1,sK0,sK3) = sK1
% 39.86/5.50      | k1_xboole_0 = sK0 ),
% 39.86/5.50      inference(instantiation,[status(thm)],[c_16]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_89472,plain,
% 39.86/5.50      ( k1_relset_1(sK1,sK0,sK3) = sK1 ),
% 39.86/5.50      inference(global_propositional_subsumption,
% 39.86/5.50                [status(thm)],
% 39.86/5.50                [c_89469,c_29,c_28,c_24,c_25711]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_85901,plain,
% 39.86/5.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(arAF1_k2_zfmisc_1_0_1(X1)))
% 39.86/5.50      | ~ iProver_ARSWP_220
% 39.86/5.50      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 39.86/5.50      inference(arg_filter_abstr,[status(unp)],[c_7]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_86224,plain,
% 39.86/5.50      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 39.86/5.50      | m1_subset_1(X2,k1_zfmisc_1(arAF1_k2_zfmisc_1_0_1(X0))) != iProver_top
% 39.86/5.50      | iProver_ARSWP_220 != iProver_top ),
% 39.86/5.50      inference(predicate_to_equality,[status(thm)],[c_85901]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_87329,plain,
% 39.86/5.50      ( k1_relset_1(sK1,X0,sK3) = k1_relat_1(sK3)
% 39.86/5.50      | iProver_ARSWP_232 != iProver_top
% 39.86/5.50      | iProver_ARSWP_220 != iProver_top ),
% 39.86/5.50      inference(superposition,[status(thm)],[c_86212,c_86224]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_89477,plain,
% 39.86/5.50      ( k1_relat_1(sK3) = sK1
% 39.86/5.50      | iProver_ARSWP_232 != iProver_top
% 39.86/5.50      | iProver_ARSWP_220 != iProver_top ),
% 39.86/5.50      inference(superposition,[status(thm)],[c_89472,c_87329]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_89538,plain,
% 39.86/5.50      ( k1_relat_1(sK3) = sK1 ),
% 39.86/5.50      inference(global_propositional_subsumption,
% 39.86/5.50                [status(thm)],
% 39.86/5.50                [c_89477,c_38,c_24,c_665,c_7560,c_25732]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_86240,plain,
% 39.86/5.50      ( k1_relat_1(X0) != k2_relat_1(X1)
% 39.86/5.50      | v1_relat_1(X1) != iProver_top
% 39.86/5.50      | v1_relat_1(X0) != iProver_top
% 39.86/5.50      | v1_funct_1(X1) != iProver_top
% 39.86/5.50      | v1_funct_1(X0) != iProver_top
% 39.86/5.50      | v2_funct_1(X0) = iProver_top
% 39.86/5.50      | v2_funct_1(k5_relat_1(X1,X0)) != iProver_top ),
% 39.86/5.50      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_89571,plain,
% 39.86/5.50      ( k2_relat_1(X0) != sK1
% 39.86/5.50      | v1_relat_1(X0) != iProver_top
% 39.86/5.50      | v1_relat_1(sK3) != iProver_top
% 39.86/5.50      | v1_funct_1(X0) != iProver_top
% 39.86/5.50      | v1_funct_1(sK3) != iProver_top
% 39.86/5.50      | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
% 39.86/5.50      | v2_funct_1(sK3) = iProver_top ),
% 39.86/5.50      inference(superposition,[status(thm)],[c_89538,c_86240]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_39,plain,
% 39.86/5.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 39.86/5.50      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_42451,plain,
% 39.86/5.50      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 39.86/5.50      | v1_relat_1(sK3) ),
% 39.86/5.50      inference(instantiation,[status(thm)],[c_6]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_42452,plain,
% 39.86/5.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 39.86/5.50      | v1_relat_1(sK3) = iProver_top ),
% 39.86/5.50      inference(predicate_to_equality,[status(thm)],[c_42451]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_89925,plain,
% 39.86/5.50      ( v1_funct_1(X0) != iProver_top
% 39.86/5.50      | k2_relat_1(X0) != sK1
% 39.86/5.50      | v1_relat_1(X0) != iProver_top
% 39.86/5.50      | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
% 39.86/5.50      | v2_funct_1(sK3) = iProver_top ),
% 39.86/5.50      inference(global_propositional_subsumption,
% 39.86/5.50                [status(thm)],
% 39.86/5.50                [c_89571,c_37,c_39,c_42452]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_89926,plain,
% 39.86/5.50      ( k2_relat_1(X0) != sK1
% 39.86/5.50      | v1_relat_1(X0) != iProver_top
% 39.86/5.50      | v1_funct_1(X0) != iProver_top
% 39.86/5.50      | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
% 39.86/5.50      | v2_funct_1(sK3) = iProver_top ),
% 39.86/5.50      inference(renaming,[status(thm)],[c_89925]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_192895,plain,
% 39.86/5.50      ( v1_funct_1(X0) != iProver_top
% 39.86/5.50      | k2_relat_1(X0) != sK1
% 39.86/5.50      | v1_relat_1(X0) != iProver_top
% 39.86/5.50      | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
% 39.86/5.50      | v2_funct_1(sK3) = iProver_top ),
% 39.86/5.50      inference(global_propositional_subsumption,
% 39.86/5.50                [status(thm)],
% 39.86/5.50                [c_159914,c_37,c_39,c_42452,c_89571]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_192896,plain,
% 39.86/5.50      ( k2_relat_1(X0) != sK1
% 39.86/5.50      | v1_relat_1(X0) != iProver_top
% 39.86/5.50      | v1_funct_1(X0) != iProver_top
% 39.86/5.50      | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
% 39.86/5.50      | v2_funct_1(sK3) = iProver_top ),
% 39.86/5.50      inference(renaming,[status(thm)],[c_192895]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_192905,plain,
% 39.86/5.50      ( v1_relat_1(sK2) != iProver_top
% 39.86/5.50      | v1_funct_1(sK2) != iProver_top
% 39.86/5.50      | v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
% 39.86/5.50      | v2_funct_1(sK3) = iProver_top ),
% 39.86/5.50      inference(superposition,[status(thm)],[c_153648,c_192896]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_17,plain,
% 39.86/5.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 39.86/5.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 39.86/5.50      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 39.86/5.50      | ~ v1_funct_1(X0)
% 39.86/5.50      | ~ v1_funct_1(X3) ),
% 39.86/5.50      inference(cnf_transformation,[],[f62]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_152760,plain,
% 39.86/5.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 39.86/5.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 39.86/5.50      | m1_subset_1(arAF1_k1_partfun1_0_1_2(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 39.86/5.50      | ~ v1_funct_1(X0)
% 39.86/5.50      | ~ v1_funct_1(X3)
% 39.86/5.50      | ~ iProver_ARSWP_239 ),
% 39.86/5.50      inference(arg_filter_abstr,[status(unp)],[c_17]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_153035,plain,
% 39.86/5.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 39.86/5.50      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 39.86/5.50      | m1_subset_1(arAF1_k1_partfun1_0_1_2(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 39.86/5.50      | v1_funct_1(X3) != iProver_top
% 39.86/5.50      | v1_funct_1(X0) != iProver_top
% 39.86/5.50      | iProver_ARSWP_239 != iProver_top ),
% 39.86/5.50      inference(predicate_to_equality,[status(thm)],[c_152760]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_154889,plain,
% 39.86/5.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 39.86/5.50      | m1_subset_1(arAF1_k1_partfun1_0_1_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,sK0))) = iProver_top
% 39.86/5.50      | v1_funct_1(X0) != iProver_top
% 39.86/5.50      | v1_funct_1(sK3) != iProver_top
% 39.86/5.50      | iProver_ARSWP_239 != iProver_top ),
% 39.86/5.50      inference(superposition,[status(thm)],[c_153045,c_153035]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_155033,plain,
% 39.86/5.50      ( v1_funct_1(X0) != iProver_top
% 39.86/5.50      | m1_subset_1(arAF1_k1_partfun1_0_1_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,sK0))) = iProver_top
% 39.86/5.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 39.86/5.50      | iProver_ARSWP_239 != iProver_top ),
% 39.86/5.50      inference(global_propositional_subsumption,
% 39.86/5.50                [status(thm)],
% 39.86/5.50                [c_154889,c_37]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_155034,plain,
% 39.86/5.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 39.86/5.50      | m1_subset_1(arAF1_k1_partfun1_0_1_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,sK0))) = iProver_top
% 39.86/5.50      | v1_funct_1(X0) != iProver_top
% 39.86/5.50      | iProver_ARSWP_239 != iProver_top ),
% 39.86/5.50      inference(renaming,[status(thm)],[c_155033]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_155045,plain,
% 39.86/5.50      ( m1_subset_1(arAF1_k1_partfun1_0_1_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 39.86/5.50      | v1_funct_1(sK2) != iProver_top
% 39.86/5.50      | iProver_ARSWP_239 != iProver_top ),
% 39.86/5.50      inference(superposition,[status(thm)],[c_153042,c_155034]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_33,negated_conjecture,
% 39.86/5.50      ( v1_funct_1(sK2) ),
% 39.86/5.50      inference(cnf_transformation,[],[f67]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_34,plain,
% 39.86/5.50      ( v1_funct_1(sK2) = iProver_top ),
% 39.86/5.50      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_155240,plain,
% 39.86/5.50      ( m1_subset_1(arAF1_k1_partfun1_0_1_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 39.86/5.50      | iProver_ARSWP_239 != iProver_top ),
% 39.86/5.50      inference(global_propositional_subsumption,
% 39.86/5.50                [status(thm)],
% 39.86/5.50                [c_155045,c_34]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_10,plain,
% 39.86/5.50      ( ~ r2_relset_1(X0,X1,X2,X3)
% 39.86/5.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 39.86/5.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 39.86/5.50      | X3 = X2 ),
% 39.86/5.50      inference(cnf_transformation,[],[f53]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_26,negated_conjecture,
% 39.86/5.50      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 39.86/5.50      inference(cnf_transformation,[],[f74]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_373,plain,
% 39.86/5.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 39.86/5.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 39.86/5.50      | X3 = X0
% 39.86/5.50      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 39.86/5.50      | k6_partfun1(sK0) != X3
% 39.86/5.50      | sK0 != X2
% 39.86/5.50      | sK0 != X1 ),
% 39.86/5.50      inference(resolution_lifted,[status(thm)],[c_10,c_26]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_374,plain,
% 39.86/5.50      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 39.86/5.50      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 39.86/5.50      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 39.86/5.50      inference(unflattening,[status(thm)],[c_373]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_19,plain,
% 39.86/5.50      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 39.86/5.50      inference(cnf_transformation,[],[f63]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_382,plain,
% 39.86/5.50      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 39.86/5.50      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 39.86/5.50      inference(forward_subsumption_resolution,
% 39.86/5.50                [status(thm)],
% 39.86/5.50                [c_374,c_19]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_152764,plain,
% 39.86/5.50      ( ~ m1_subset_1(arAF1_k1_partfun1_0_1_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 39.86/5.50      | ~ iProver_ARSWP_243
% 39.86/5.50      | k6_partfun1(sK0) = arAF1_k1_partfun1_0_1_2(sK0,sK1) ),
% 39.86/5.50      inference(arg_filter_abstr,[status(unp)],[c_382]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_153031,plain,
% 39.86/5.50      ( k6_partfun1(sK0) = arAF1_k1_partfun1_0_1_2(sK0,sK1)
% 39.86/5.50      | m1_subset_1(arAF1_k1_partfun1_0_1_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 39.86/5.50      | iProver_ARSWP_243 != iProver_top ),
% 39.86/5.50      inference(predicate_to_equality,[status(thm)],[c_152764]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_155259,plain,
% 39.86/5.50      ( arAF1_k1_partfun1_0_1_2(sK0,sK1) = k6_partfun1(sK0)
% 39.86/5.50      | iProver_ARSWP_243 != iProver_top
% 39.86/5.50      | iProver_ARSWP_239 != iProver_top ),
% 39.86/5.50      inference(superposition,[status(thm)],[c_155240,c_153031]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_20,plain,
% 39.86/5.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 39.86/5.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 39.86/5.50      | ~ v1_funct_1(X0)
% 39.86/5.50      | ~ v1_funct_1(X3)
% 39.86/5.50      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 39.86/5.50      inference(cnf_transformation,[],[f64]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_152762,plain,
% 39.86/5.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 39.86/5.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 39.86/5.50      | ~ v1_funct_1(X0)
% 39.86/5.50      | ~ v1_funct_1(X3)
% 39.86/5.50      | ~ iProver_ARSWP_241
% 39.86/5.50      | arAF1_k1_partfun1_0_1_2(X4,X5) = k5_relat_1(X3,X0) ),
% 39.86/5.50      inference(arg_filter_abstr,[status(unp)],[c_20]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_153033,plain,
% 39.86/5.50      ( arAF1_k1_partfun1_0_1_2(X0,X1) = k5_relat_1(X2,X3)
% 39.86/5.50      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 39.86/5.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 39.86/5.50      | v1_funct_1(X2) != iProver_top
% 39.86/5.50      | v1_funct_1(X3) != iProver_top
% 39.86/5.50      | iProver_ARSWP_241 != iProver_top ),
% 39.86/5.50      inference(predicate_to_equality,[status(thm)],[c_152762]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_153877,plain,
% 39.86/5.50      ( k5_relat_1(sK2,X0) = arAF1_k1_partfun1_0_1_2(sK0,sK1)
% 39.86/5.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 39.86/5.50      | v1_funct_1(X0) != iProver_top
% 39.86/5.50      | v1_funct_1(sK2) != iProver_top
% 39.86/5.50      | iProver_ARSWP_241 != iProver_top ),
% 39.86/5.50      inference(superposition,[status(thm)],[c_153042,c_153033]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_154214,plain,
% 39.86/5.50      ( v1_funct_1(X0) != iProver_top
% 39.86/5.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 39.86/5.50      | k5_relat_1(sK2,X0) = arAF1_k1_partfun1_0_1_2(sK0,sK1)
% 39.86/5.50      | iProver_ARSWP_241 != iProver_top ),
% 39.86/5.50      inference(global_propositional_subsumption,
% 39.86/5.50                [status(thm)],
% 39.86/5.50                [c_153877,c_34]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_154215,plain,
% 39.86/5.50      ( k5_relat_1(sK2,X0) = arAF1_k1_partfun1_0_1_2(sK0,sK1)
% 39.86/5.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 39.86/5.50      | v1_funct_1(X0) != iProver_top
% 39.86/5.50      | iProver_ARSWP_241 != iProver_top ),
% 39.86/5.50      inference(renaming,[status(thm)],[c_154214]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_154225,plain,
% 39.86/5.50      ( arAF1_k1_partfun1_0_1_2(sK0,sK1) = k5_relat_1(sK2,sK3)
% 39.86/5.50      | v1_funct_1(sK3) != iProver_top
% 39.86/5.50      | iProver_ARSWP_241 != iProver_top ),
% 39.86/5.50      inference(superposition,[status(thm)],[c_153045,c_154215]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_154260,plain,
% 39.86/5.50      ( arAF1_k1_partfun1_0_1_2(sK0,sK1) = k5_relat_1(sK2,sK3)
% 39.86/5.50      | iProver_ARSWP_241 != iProver_top ),
% 39.86/5.50      inference(global_propositional_subsumption,
% 39.86/5.50                [status(thm)],
% 39.86/5.50                [c_154225,c_37]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_156074,plain,
% 39.86/5.50      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 39.86/5.50      | iProver_ARSWP_243 != iProver_top
% 39.86/5.50      | iProver_ARSWP_241 != iProver_top
% 39.86/5.50      | iProver_ARSWP_239 != iProver_top ),
% 39.86/5.50      inference(superposition,[status(thm)],[c_155259,c_154260]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_36,plain,
% 39.86/5.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 39.86/5.50      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_119896,plain,
% 39.86/5.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 39.86/5.50      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_119899,plain,
% 39.86/5.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 39.86/5.50      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_119901,plain,
% 39.86/5.50      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 39.86/5.50      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 39.86/5.50      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 39.86/5.50      | v1_funct_1(X4) != iProver_top
% 39.86/5.50      | v1_funct_1(X5) != iProver_top ),
% 39.86/5.50      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_120312,plain,
% 39.86/5.50      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 39.86/5.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 39.86/5.50      | v1_funct_1(X2) != iProver_top
% 39.86/5.50      | v1_funct_1(sK3) != iProver_top ),
% 39.86/5.50      inference(superposition,[status(thm)],[c_119899,c_119901]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_85442,plain,
% 39.86/5.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 39.86/5.50      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_85444,plain,
% 39.86/5.50      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 39.86/5.50      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 39.86/5.50      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 39.86/5.50      | v1_funct_1(X4) != iProver_top
% 39.86/5.50      | v1_funct_1(X5) != iProver_top ),
% 39.86/5.50      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_85715,plain,
% 39.86/5.50      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 39.86/5.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 39.86/5.50      | v1_funct_1(X2) != iProver_top
% 39.86/5.50      | v1_funct_1(sK3) != iProver_top ),
% 39.86/5.50      inference(superposition,[status(thm)],[c_85442,c_85444]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_120351,plain,
% 39.86/5.50      ( v1_funct_1(X2) != iProver_top
% 39.86/5.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 39.86/5.50      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 39.86/5.50      inference(global_propositional_subsumption,
% 39.86/5.50                [status(thm)],
% 39.86/5.50                [c_120312,c_37,c_85715]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_120352,plain,
% 39.86/5.50      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 39.86/5.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 39.86/5.50      | v1_funct_1(X2) != iProver_top ),
% 39.86/5.50      inference(renaming,[status(thm)],[c_120351]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_120360,plain,
% 39.86/5.50      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 39.86/5.50      | v1_funct_1(sK2) != iProver_top ),
% 39.86/5.50      inference(superposition,[status(thm)],[c_119896,c_120352]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_85545,plain,
% 39.86/5.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 39.86/5.50      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 39.86/5.50      | ~ v1_funct_1(X0)
% 39.86/5.50      | ~ v1_funct_1(sK3)
% 39.86/5.50      | k1_partfun1(X1,X2,sK1,sK0,X0,sK3) = k5_relat_1(X0,sK3) ),
% 39.86/5.50      inference(instantiation,[status(thm)],[c_20]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_85614,plain,
% 39.86/5.50      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 39.86/5.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 39.86/5.50      | ~ v1_funct_1(sK3)
% 39.86/5.50      | ~ v1_funct_1(sK2)
% 39.86/5.50      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 39.86/5.50      inference(instantiation,[status(thm)],[c_85545]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_120386,plain,
% 39.86/5.50      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 39.86/5.50      inference(global_propositional_subsumption,
% 39.86/5.50                [status(thm)],
% 39.86/5.50                [c_120360,c_33,c_31,c_30,c_28,c_85614]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_119893,plain,
% 39.86/5.50      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 39.86/5.50      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 39.86/5.50      inference(predicate_to_equality,[status(thm)],[c_382]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_120389,plain,
% 39.86/5.50      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 39.86/5.50      | m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 39.86/5.50      inference(demodulation,[status(thm)],[c_120386,c_119893]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_119904,plain,
% 39.86/5.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 39.86/5.50      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 39.86/5.50      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 39.86/5.50      | v1_funct_1(X3) != iProver_top
% 39.86/5.50      | v1_funct_1(X0) != iProver_top ),
% 39.86/5.50      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_120513,plain,
% 39.86/5.50      ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 39.86/5.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 39.86/5.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 39.86/5.50      | v1_funct_1(sK3) != iProver_top
% 39.86/5.50      | v1_funct_1(sK2) != iProver_top ),
% 39.86/5.50      inference(superposition,[status(thm)],[c_120386,c_119904]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_159685,plain,
% 39.86/5.50      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 39.86/5.50      inference(global_propositional_subsumption,
% 39.86/5.50                [status(thm)],
% 39.86/5.50                [c_156074,c_34,c_36,c_37,c_39,c_120389,c_120513]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_192955,plain,
% 39.86/5.50      ( v1_relat_1(sK2) != iProver_top
% 39.86/5.50      | v1_funct_1(sK2) != iProver_top
% 39.86/5.50      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 39.86/5.50      | v2_funct_1(sK3) = iProver_top ),
% 39.86/5.50      inference(light_normalisation,[status(thm)],[c_192905,c_159685]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_85572,plain,
% 39.86/5.50      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 39.86/5.50      | v1_relat_1(sK2) ),
% 39.86/5.50      inference(instantiation,[status(thm)],[c_6]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_85573,plain,
% 39.86/5.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 39.86/5.50      | v1_relat_1(sK2) = iProver_top ),
% 39.86/5.50      inference(predicate_to_equality,[status(thm)],[c_85572]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_192980,plain,
% 39.86/5.50      ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 39.86/5.50      | v2_funct_1(sK3) = iProver_top ),
% 39.86/5.50      inference(global_propositional_subsumption,
% 39.86/5.50                [status(thm)],
% 39.86/5.50                [c_192955,c_34,c_36,c_85573]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_2,plain,
% 39.86/5.50      ( v2_funct_1(k6_partfun1(X0)) ),
% 39.86/5.50      inference(cnf_transformation,[],[f79]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_153060,plain,
% 39.86/5.50      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 39.86/5.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_192986,plain,
% 39.86/5.50      ( v2_funct_1(sK3) = iProver_top ),
% 39.86/5.50      inference(forward_subsumption_resolution,
% 39.86/5.50                [status(thm)],
% 39.86/5.50                [c_192980,c_153060]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_195818,plain,
% 39.86/5.50      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
% 39.86/5.50      inference(global_propositional_subsumption,
% 39.86/5.50                [status(thm)],
% 39.86/5.50                [c_159905,c_42633,c_192986]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_154226,plain,
% 39.86/5.50      ( arAF1_k1_partfun1_0_1_2(sK0,sK1) = k5_relat_1(sK2,sK2)
% 39.86/5.50      | v1_funct_1(sK2) != iProver_top
% 39.86/5.50      | iProver_ARSWP_241 != iProver_top ),
% 39.86/5.50      inference(superposition,[status(thm)],[c_153042,c_154215]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_154337,plain,
% 39.86/5.50      ( arAF1_k1_partfun1_0_1_2(sK0,sK1) = k5_relat_1(sK2,sK2)
% 39.86/5.50      | iProver_ARSWP_241 != iProver_top ),
% 39.86/5.50      inference(global_propositional_subsumption,
% 39.86/5.50                [status(thm)],
% 39.86/5.50                [c_154226,c_34]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_154343,plain,
% 39.86/5.50      ( k5_relat_1(sK2,sK2) = k5_relat_1(sK2,sK3)
% 39.86/5.50      | iProver_ARSWP_241 != iProver_top ),
% 39.86/5.50      inference(superposition,[status(thm)],[c_154260,c_154337]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_5,plain,
% 39.86/5.50      ( ~ v1_relat_1(X0)
% 39.86/5.50      | ~ v1_relat_1(X1)
% 39.86/5.50      | ~ v1_funct_1(X0)
% 39.86/5.50      | ~ v1_funct_1(X1)
% 39.86/5.50      | ~ v2_funct_1(X1)
% 39.86/5.50      | k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 39.86/5.50      | k2_funct_1(X1) = X0
% 39.86/5.50      | k1_relat_1(X1) != k2_relat_1(X0) ),
% 39.86/5.50      inference(cnf_transformation,[],[f82]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_153057,plain,
% 39.86/5.50      ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 39.86/5.50      | k2_funct_1(X1) = X0
% 39.86/5.50      | k1_relat_1(X1) != k2_relat_1(X0)
% 39.86/5.50      | v1_relat_1(X0) != iProver_top
% 39.86/5.50      | v1_relat_1(X1) != iProver_top
% 39.86/5.50      | v1_funct_1(X0) != iProver_top
% 39.86/5.50      | v1_funct_1(X1) != iProver_top
% 39.86/5.50      | v2_funct_1(X1) != iProver_top ),
% 39.86/5.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_154795,plain,
% 39.86/5.50      ( k2_funct_1(sK3) = sK2
% 39.86/5.50      | k6_partfun1(k2_relat_1(sK3)) != k5_relat_1(sK2,sK2)
% 39.86/5.50      | k1_relat_1(sK3) != k2_relat_1(sK2)
% 39.86/5.50      | v1_relat_1(sK3) != iProver_top
% 39.86/5.50      | v1_relat_1(sK2) != iProver_top
% 39.86/5.50      | v1_funct_1(sK3) != iProver_top
% 39.86/5.50      | v1_funct_1(sK2) != iProver_top
% 39.86/5.50      | v2_funct_1(sK3) != iProver_top
% 39.86/5.50      | iProver_ARSWP_241 != iProver_top ),
% 39.86/5.50      inference(superposition,[status(thm)],[c_154343,c_153057]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_153645,plain,
% 39.86/5.50      ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 39.86/5.50      inference(superposition,[status(thm)],[c_153045,c_153054]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_21,plain,
% 39.86/5.50      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 39.86/5.50      | ~ v1_funct_2(X3,X1,X0)
% 39.86/5.50      | ~ v1_funct_2(X2,X0,X1)
% 39.86/5.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 39.86/5.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 39.86/5.50      | ~ v1_funct_1(X2)
% 39.86/5.50      | ~ v1_funct_1(X3)
% 39.86/5.50      | k2_relset_1(X1,X0,X3) = X0 ),
% 39.86/5.50      inference(cnf_transformation,[],[f66]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_386,plain,
% 39.86/5.50      ( ~ v1_funct_2(X0,X1,X2)
% 39.86/5.50      | ~ v1_funct_2(X3,X2,X1)
% 39.86/5.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 39.86/5.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 39.86/5.50      | ~ v1_funct_1(X3)
% 39.86/5.50      | ~ v1_funct_1(X0)
% 39.86/5.50      | k1_partfun1(X1,X2,X2,X1,X0,X3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 39.86/5.50      | k2_relset_1(X2,X1,X3) = X1
% 39.86/5.50      | k6_partfun1(X1) != k6_partfun1(sK0)
% 39.86/5.50      | sK0 != X1 ),
% 39.86/5.50      inference(resolution_lifted,[status(thm)],[c_21,c_26]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_387,plain,
% 39.86/5.50      ( ~ v1_funct_2(X0,X1,sK0)
% 39.86/5.50      | ~ v1_funct_2(X2,sK0,X1)
% 39.86/5.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 39.86/5.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 39.86/5.50      | ~ v1_funct_1(X2)
% 39.86/5.50      | ~ v1_funct_1(X0)
% 39.86/5.50      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 39.86/5.50      | k2_relset_1(X1,sK0,X0) = sK0
% 39.86/5.50      | k6_partfun1(sK0) != k6_partfun1(sK0) ),
% 39.86/5.50      inference(unflattening,[status(thm)],[c_386]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_470,plain,
% 39.86/5.50      ( ~ v1_funct_2(X0,X1,sK0)
% 39.86/5.50      | ~ v1_funct_2(X2,sK0,X1)
% 39.86/5.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 39.86/5.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 39.86/5.50      | ~ v1_funct_1(X0)
% 39.86/5.50      | ~ v1_funct_1(X2)
% 39.86/5.50      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 39.86/5.50      | k2_relset_1(X1,sK0,X0) = sK0 ),
% 39.86/5.50      inference(equality_resolution_simp,[status(thm)],[c_387]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_152765,plain,
% 39.86/5.50      ( ~ v1_funct_2(X0,X1,sK0)
% 39.86/5.50      | ~ v1_funct_2(X2,sK0,X1)
% 39.86/5.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 39.86/5.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 39.86/5.50      | ~ v1_funct_1(X0)
% 39.86/5.50      | ~ v1_funct_1(X2)
% 39.86/5.50      | ~ iProver_ARSWP_244
% 39.86/5.50      | k2_relset_1(X1,sK0,X0) = sK0
% 39.86/5.50      | arAF1_k1_partfun1_0_1_2(sK0,X1) != arAF1_k1_partfun1_0_1_2(sK0,sK1) ),
% 39.86/5.50      inference(arg_filter_abstr,[status(unp)],[c_470]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_153030,plain,
% 39.86/5.50      ( k2_relset_1(X0,sK0,X1) = sK0
% 39.86/5.50      | arAF1_k1_partfun1_0_1_2(sK0,X0) != arAF1_k1_partfun1_0_1_2(sK0,sK1)
% 39.86/5.50      | v1_funct_2(X1,X0,sK0) != iProver_top
% 39.86/5.50      | v1_funct_2(X2,sK0,X0) != iProver_top
% 39.86/5.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 39.86/5.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 39.86/5.50      | v1_funct_1(X2) != iProver_top
% 39.86/5.50      | v1_funct_1(X1) != iProver_top
% 39.86/5.50      | iProver_ARSWP_244 != iProver_top ),
% 39.86/5.50      inference(predicate_to_equality,[status(thm)],[c_152765]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_153404,plain,
% 39.86/5.50      ( k2_relset_1(sK1,sK0,X0) = sK0
% 39.86/5.50      | v1_funct_2(X1,sK0,sK1) != iProver_top
% 39.86/5.50      | v1_funct_2(X0,sK1,sK0) != iProver_top
% 39.86/5.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 39.86/5.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 39.86/5.50      | v1_funct_1(X0) != iProver_top
% 39.86/5.50      | v1_funct_1(X1) != iProver_top
% 39.86/5.50      | iProver_ARSWP_244 != iProver_top ),
% 39.86/5.50      inference(equality_resolution,[status(thm)],[c_153030]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_153462,plain,
% 39.86/5.50      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 39.86/5.50      | v1_funct_2(X0,sK0,sK1) != iProver_top
% 39.86/5.50      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 39.86/5.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 39.86/5.50      | v1_funct_1(X0) != iProver_top
% 39.86/5.50      | v1_funct_1(sK3) != iProver_top
% 39.86/5.50      | iProver_ARSWP_244 != iProver_top ),
% 39.86/5.50      inference(superposition,[status(thm)],[c_153045,c_153404]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_32,negated_conjecture,
% 39.86/5.50      ( v1_funct_2(sK2,sK0,sK1) ),
% 39.86/5.50      inference(cnf_transformation,[],[f68]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_35,plain,
% 39.86/5.50      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 39.86/5.50      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_119892,plain,
% 39.86/5.50      ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 39.86/5.50      | k2_relset_1(X0,sK0,X2) = sK0
% 39.86/5.50      | v1_funct_2(X2,X0,sK0) != iProver_top
% 39.86/5.50      | v1_funct_2(X1,sK0,X0) != iProver_top
% 39.86/5.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 39.86/5.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 39.86/5.50      | v1_funct_1(X1) != iProver_top
% 39.86/5.50      | v1_funct_1(X2) != iProver_top ),
% 39.86/5.50      inference(predicate_to_equality,[status(thm)],[c_470]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_120097,plain,
% 39.86/5.50      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 39.86/5.50      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 39.86/5.50      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 39.86/5.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 39.86/5.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 39.86/5.50      | v1_funct_1(sK3) != iProver_top
% 39.86/5.50      | v1_funct_1(sK2) != iProver_top ),
% 39.86/5.50      inference(equality_resolution,[status(thm)],[c_119892]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_153487,plain,
% 39.86/5.50      ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 39.86/5.50      inference(global_propositional_subsumption,
% 39.86/5.50                [status(thm)],
% 39.86/5.50                [c_153462,c_34,c_35,c_36,c_37,c_38,c_39,c_120097]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_153651,plain,
% 39.86/5.50      ( k2_relat_1(sK3) = sK0 ),
% 39.86/5.50      inference(light_normalisation,[status(thm)],[c_153645,c_153487]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_154796,plain,
% 39.86/5.50      ( k5_relat_1(sK2,sK2) != k6_partfun1(sK0)
% 39.86/5.50      | k2_funct_1(sK3) = sK2
% 39.86/5.50      | k1_relat_1(sK3) != sK1
% 39.86/5.50      | v1_relat_1(sK3) != iProver_top
% 39.86/5.50      | v1_relat_1(sK2) != iProver_top
% 39.86/5.50      | v1_funct_1(sK3) != iProver_top
% 39.86/5.50      | v1_funct_1(sK2) != iProver_top
% 39.86/5.50      | v2_funct_1(sK3) != iProver_top
% 39.86/5.50      | iProver_ARSWP_241 != iProver_top ),
% 39.86/5.50      inference(light_normalisation,
% 39.86/5.50                [status(thm)],
% 39.86/5.50                [c_154795,c_153648,c_153651]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_120743,plain,
% 39.86/5.50      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 39.86/5.50      inference(global_propositional_subsumption,
% 39.86/5.50                [status(thm)],
% 39.86/5.50                [c_120389,c_34,c_36,c_37,c_39,c_120513]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_119910,plain,
% 39.86/5.50      ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 39.86/5.50      | k2_funct_1(X1) = X0
% 39.86/5.50      | k1_relat_1(X1) != k2_relat_1(X0)
% 39.86/5.50      | v1_relat_1(X0) != iProver_top
% 39.86/5.50      | v1_relat_1(X1) != iProver_top
% 39.86/5.50      | v1_funct_1(X0) != iProver_top
% 39.86/5.50      | v1_funct_1(X1) != iProver_top
% 39.86/5.50      | v2_funct_1(X1) != iProver_top ),
% 39.86/5.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_120747,plain,
% 39.86/5.50      ( k2_funct_1(sK3) = sK2
% 39.86/5.50      | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
% 39.86/5.50      | k1_relat_1(sK3) != k2_relat_1(sK2)
% 39.86/5.50      | v1_relat_1(sK3) != iProver_top
% 39.86/5.50      | v1_relat_1(sK2) != iProver_top
% 39.86/5.50      | v1_funct_1(sK3) != iProver_top
% 39.86/5.50      | v1_funct_1(sK2) != iProver_top
% 39.86/5.50      | v2_funct_1(sK3) != iProver_top ),
% 39.86/5.50      inference(superposition,[status(thm)],[c_120743,c_119910]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_119907,plain,
% 39.86/5.50      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 39.86/5.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 39.86/5.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_120208,plain,
% 39.86/5.50      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 39.86/5.50      inference(superposition,[status(thm)],[c_119896,c_119907]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_120210,plain,
% 39.86/5.50      ( k2_relat_1(sK2) = sK1 ),
% 39.86/5.50      inference(light_normalisation,[status(thm)],[c_120208,c_27]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_120207,plain,
% 39.86/5.50      ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 39.86/5.50      inference(superposition,[status(thm)],[c_119899,c_119907]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_120142,plain,
% 39.86/5.50      ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 39.86/5.50      inference(global_propositional_subsumption,
% 39.86/5.50                [status(thm)],
% 39.86/5.50                [c_120097,c_34,c_35,c_36,c_37,c_38,c_39]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_120213,plain,
% 39.86/5.50      ( k2_relat_1(sK3) = sK0 ),
% 39.86/5.50      inference(light_normalisation,[status(thm)],[c_120207,c_120142]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_119905,plain,
% 39.86/5.50      ( k1_relset_1(X0,X1,X2) = X0
% 39.86/5.50      | k1_xboole_0 = X1
% 39.86/5.50      | v1_funct_2(X2,X0,X1) != iProver_top
% 39.86/5.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 39.86/5.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_120255,plain,
% 39.86/5.50      ( k1_relset_1(sK1,sK0,sK3) = sK1
% 39.86/5.50      | sK0 = k1_xboole_0
% 39.86/5.50      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 39.86/5.50      inference(superposition,[status(thm)],[c_119899,c_119905]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_120727,plain,
% 39.86/5.50      ( k1_relset_1(sK1,sK0,sK3) = sK1 ),
% 39.86/5.50      inference(global_propositional_subsumption,
% 39.86/5.50                [status(thm)],
% 39.86/5.50                [c_120255,c_29,c_28,c_24,c_25711]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_119908,plain,
% 39.86/5.50      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 39.86/5.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 39.86/5.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_120230,plain,
% 39.86/5.50      ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
% 39.86/5.50      inference(superposition,[status(thm)],[c_119899,c_119908]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_120730,plain,
% 39.86/5.50      ( k1_relat_1(sK3) = sK1 ),
% 39.86/5.50      inference(demodulation,[status(thm)],[c_120727,c_120230]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_120748,plain,
% 39.86/5.50      ( k2_funct_1(sK3) = sK2
% 39.86/5.50      | k6_partfun1(sK0) != k6_partfun1(sK0)
% 39.86/5.50      | sK1 != sK1
% 39.86/5.50      | v1_relat_1(sK3) != iProver_top
% 39.86/5.50      | v1_relat_1(sK2) != iProver_top
% 39.86/5.50      | v1_funct_1(sK3) != iProver_top
% 39.86/5.50      | v1_funct_1(sK2) != iProver_top
% 39.86/5.50      | v2_funct_1(sK3) != iProver_top ),
% 39.86/5.50      inference(light_normalisation,
% 39.86/5.50                [status(thm)],
% 39.86/5.50                [c_120747,c_120210,c_120213,c_120730]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_120749,plain,
% 39.86/5.50      ( k2_funct_1(sK3) = sK2
% 39.86/5.50      | v1_relat_1(sK3) != iProver_top
% 39.86/5.50      | v1_relat_1(sK2) != iProver_top
% 39.86/5.50      | v1_funct_1(sK3) != iProver_top
% 39.86/5.50      | v1_funct_1(sK2) != iProver_top
% 39.86/5.50      | v2_funct_1(sK3) != iProver_top ),
% 39.86/5.50      inference(equality_resolution_simp,[status(thm)],[c_120748]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_154799,plain,
% 39.86/5.50      ( v2_funct_1(sK3) != iProver_top | k2_funct_1(sK3) = sK2 ),
% 39.86/5.50      inference(global_propositional_subsumption,
% 39.86/5.50                [status(thm)],
% 39.86/5.50                [c_154796,c_34,c_36,c_37,c_39,c_42452,c_85573,c_120749]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_154800,plain,
% 39.86/5.50      ( k2_funct_1(sK3) = sK2 | v2_funct_1(sK3) != iProver_top ),
% 39.86/5.50      inference(renaming,[status(thm)],[c_154799]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_192989,plain,
% 39.86/5.50      ( k2_funct_1(sK3) = sK2 ),
% 39.86/5.50      inference(superposition,[status(thm)],[c_192986,c_154800]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_195820,plain,
% 39.86/5.50      ( k5_relat_1(sK3,sK2) = k6_partfun1(sK1) ),
% 39.86/5.50      inference(light_normalisation,[status(thm)],[c_195818,c_192989]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_196460,plain,
% 39.86/5.50      ( k2_funct_1(sK2) = sK3
% 39.86/5.50      | k6_partfun1(k2_relat_1(sK2)) != k6_partfun1(sK1)
% 39.86/5.50      | k1_relat_1(sK2) != k2_relat_1(sK3)
% 39.86/5.50      | v1_relat_1(sK3) != iProver_top
% 39.86/5.50      | v1_relat_1(sK2) != iProver_top
% 39.86/5.50      | v1_funct_1(sK3) != iProver_top
% 39.86/5.50      | v1_funct_1(sK2) != iProver_top
% 39.86/5.50      | v2_funct_1(sK2) != iProver_top ),
% 39.86/5.50      inference(superposition,[status(thm)],[c_195820,c_153057]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_154019,plain,
% 39.86/5.50      ( k1_relset_1(sK0,sK1,sK2) = sK0
% 39.86/5.50      | sK1 = k1_xboole_0
% 39.86/5.50      | v1_funct_2(sK2,sK0,sK1) != iProver_top ),
% 39.86/5.50      inference(superposition,[status(thm)],[c_153042,c_153048]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_153699,plain,
% 39.86/5.50      ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
% 39.86/5.50      inference(superposition,[status(thm)],[c_153042,c_153055]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_154023,plain,
% 39.86/5.50      ( k1_relat_1(sK2) = sK0
% 39.86/5.50      | sK1 = k1_xboole_0
% 39.86/5.50      | v1_funct_2(sK2,sK0,sK1) != iProver_top ),
% 39.86/5.50      inference(demodulation,[status(thm)],[c_154019,c_153699]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_23,negated_conjecture,
% 39.86/5.50      ( k1_xboole_0 != sK1 ),
% 39.86/5.50      inference(cnf_transformation,[],[f77]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_7557,plain,
% 39.86/5.50      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 39.86/5.50      inference(instantiation,[status(thm)],[c_639]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_7558,plain,
% 39.86/5.50      ( sK1 != k1_xboole_0
% 39.86/5.50      | k1_xboole_0 = sK1
% 39.86/5.50      | k1_xboole_0 != k1_xboole_0 ),
% 39.86/5.50      inference(instantiation,[status(thm)],[c_7557]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_85439,plain,
% 39.86/5.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 39.86/5.50      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_85445,plain,
% 39.86/5.50      ( k1_relset_1(X0,X1,X2) = X0
% 39.86/5.50      | k1_xboole_0 = X1
% 39.86/5.50      | v1_funct_2(X2,X0,X1) != iProver_top
% 39.86/5.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 39.86/5.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_85692,plain,
% 39.86/5.50      ( k1_relset_1(sK0,sK1,sK2) = sK0
% 39.86/5.50      | sK1 = k1_xboole_0
% 39.86/5.50      | v1_funct_2(sK2,sK0,sK1) != iProver_top ),
% 39.86/5.50      inference(superposition,[status(thm)],[c_85439,c_85445]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_85447,plain,
% 39.86/5.50      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 39.86/5.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 39.86/5.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_85621,plain,
% 39.86/5.50      ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
% 39.86/5.50      inference(superposition,[status(thm)],[c_85439,c_85447]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_85696,plain,
% 39.86/5.50      ( k1_relat_1(sK2) = sK0
% 39.86/5.50      | sK1 = k1_xboole_0
% 39.86/5.50      | v1_funct_2(sK2,sK0,sK1) != iProver_top ),
% 39.86/5.50      inference(demodulation,[status(thm)],[c_85692,c_85621]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_159277,plain,
% 39.86/5.50      ( k1_relat_1(sK2) = sK0 ),
% 39.86/5.50      inference(global_propositional_subsumption,
% 39.86/5.50                [status(thm)],
% 39.86/5.50                [c_154023,c_35,c_23,c_665,c_7558,c_85696]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_196461,plain,
% 39.86/5.50      ( k2_funct_1(sK2) = sK3
% 39.86/5.50      | k6_partfun1(sK1) != k6_partfun1(sK1)
% 39.86/5.50      | sK0 != sK0
% 39.86/5.50      | v1_relat_1(sK3) != iProver_top
% 39.86/5.50      | v1_relat_1(sK2) != iProver_top
% 39.86/5.50      | v1_funct_1(sK3) != iProver_top
% 39.86/5.50      | v1_funct_1(sK2) != iProver_top
% 39.86/5.50      | v2_funct_1(sK2) != iProver_top ),
% 39.86/5.50      inference(light_normalisation,
% 39.86/5.50                [status(thm)],
% 39.86/5.50                [c_196460,c_153648,c_153651,c_159277]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_196462,plain,
% 39.86/5.50      ( k2_funct_1(sK2) = sK3
% 39.86/5.50      | v1_relat_1(sK3) != iProver_top
% 39.86/5.50      | v1_relat_1(sK2) != iProver_top
% 39.86/5.50      | v1_funct_1(sK3) != iProver_top
% 39.86/5.50      | v1_funct_1(sK2) != iProver_top
% 39.86/5.50      | v2_funct_1(sK2) != iProver_top ),
% 39.86/5.50      inference(equality_resolution_simp,[status(thm)],[c_196461]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_22,negated_conjecture,
% 39.86/5.50      ( k2_funct_1(sK2) != sK3 ),
% 39.86/5.50      inference(cnf_transformation,[],[f78]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_25,negated_conjecture,
% 39.86/5.50      ( v2_funct_1(sK2) ),
% 39.86/5.50      inference(cnf_transformation,[],[f75]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(c_41,plain,
% 39.86/5.50      ( v2_funct_1(sK2) = iProver_top ),
% 39.86/5.50      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 39.86/5.50  
% 39.86/5.50  cnf(contradiction,plain,
% 39.86/5.50      ( $false ),
% 39.86/5.50      inference(minisat,
% 39.86/5.50                [status(thm)],
% 39.86/5.50                [c_196462,c_85573,c_42452,c_22,c_41,c_39,c_37,c_36,c_34]) ).
% 39.86/5.50  
% 39.86/5.50  
% 39.86/5.50  % SZS output end CNFRefutation for theBenchmark.p
% 39.86/5.50  
% 39.86/5.50  ------                               Statistics
% 39.86/5.50  
% 39.86/5.50  ------ Selected
% 39.86/5.50  
% 39.86/5.50  total_time:                             4.953
% 39.86/5.50  
%------------------------------------------------------------------------------
