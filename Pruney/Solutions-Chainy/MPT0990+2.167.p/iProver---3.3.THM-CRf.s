%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:32 EST 2020

% Result     : Theorem 2.92s
% Output     : CNFRefutation 2.92s
% Verified   : 
% Statistics : Number of formulae       :  176 ( 818 expanded)
%              Number of clauses        :  106 ( 218 expanded)
%              Number of leaves         :   16 ( 217 expanded)
%              Depth                    :   24
%              Number of atoms          :  682 (7171 expanded)
%              Number of equality atoms :  341 (2669 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
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

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f37,plain,(
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

fof(f36,plain,
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

fof(f38,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f33,f37,f36])).

fof(f64,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f38])).

fof(f67,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f38])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f28])).

fof(f58,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f65,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f62,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f22])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f69,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f38])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f8])).

fof(f12,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f79,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f49,f59])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f26])).

fof(f57,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f18,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f44,plain,(
    ! [X0] :
      ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f76,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f44,f59])).

fof(f70,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f63,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f13,axiom,(
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

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f68,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f38])).

fof(f72,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f38])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f74,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f42,f59])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,X1)
              & k1_relat_1(X1) = k2_relat_1(X0)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
          | k1_relat_1(X1) != k2_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
          | k1_relat_1(X1) != k2_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
      | k1_relat_1(X1) != k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
      | k1_relat_1(X1) != k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f45,f59])).

fof(f43,plain,(
    ! [X0] :
      ( k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f77,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f43,f59])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

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

fof(f24,plain,(
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

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f66,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f71,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f38])).

fof(f73,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1319,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1321,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1322,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2802,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1321,c_1322])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_37,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_3382,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2802,c_37])).

cnf(c_3383,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_3382])).

cnf(c_3394,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1319,c_3383])).

cnf(c_33,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_34,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_3764,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3394,c_34])).

cnf(c_9,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_26,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_321,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_26])).

cnf(c_322,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_321])).

cnf(c_10,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_330,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_322,c_10])).

cnf(c_1317,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_330])).

cnf(c_3767,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3764,c_1317])).

cnf(c_36,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_39,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1324,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3769,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3764,c_1324])).

cnf(c_4101,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3767,c_34,c_36,c_37,c_39,c_3769])).

cnf(c_4,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_25,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_435,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_25])).

cnf(c_436,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(unflattening,[status(thm)],[c_435])).

cnf(c_438,plain,
    ( ~ v1_relat_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_436,c_33])).

cnf(c_1314,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_438])).

cnf(c_32,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_364,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_25])).

cnf(c_365,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(X1)
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_364])).

cnf(c_369,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(sK2,X0,X1)
    | k2_relset_1(X0,X1,sK2) != X1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(X1)
    | k1_xboole_0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_365,c_33])).

cnf(c_370,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_relset_1(X0,X1,sK2) != X1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(X1)
    | k1_xboole_0 = X1 ),
    inference(renaming,[status(thm)],[c_369])).

cnf(c_690,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_relset_1(X0,X1,sK2) != X1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(X1)
    | sK0 != X0
    | sK1 != X1
    | sK2 != sK2
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_370])).

cnf(c_691,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k2_relset_1(sK0,sK1,sK2) != sK1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_690])).

cnf(c_27,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_23,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_693,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_691,c_31,c_27,c_23])).

cnf(c_1361,plain,
    ( k6_partfun1(k2_relat_1(sK2)) = k6_partfun1(sK1)
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1314,c_693])).

cnf(c_1498,plain,
    ( ~ v1_relat_1(sK2)
    | k6_partfun1(k2_relat_1(sK2)) = k6_partfun1(sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1361])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1551,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1701,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1551])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1759,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2093,plain,
    ( k6_partfun1(k2_relat_1(sK2)) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1361,c_31,c_1498,c_1701,c_1759])).

cnf(c_2,plain,
    ( k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2097,plain,
    ( k2_relat_1(k6_partfun1(sK1)) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2093,c_2])).

cnf(c_2099,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(demodulation,[status(thm)],[c_2097,c_2])).

cnf(c_6,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
    | k2_funct_1(X0) = X1
    | k1_relat_1(X1) != k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_391,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(X1,X0) != k6_partfun1(k1_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k1_relat_1(X0) != k2_relat_1(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_25])).

cnf(c_392,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
    | k2_funct_1(sK2) = X0
    | k1_relat_1(X0) != k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_391])).

cnf(c_396,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
    | k2_funct_1(sK2) = X0
    | k1_relat_1(X0) != k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_392,c_33])).

cnf(c_1316,plain,
    ( k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
    | k2_funct_1(sK2) = X0
    | k1_relat_1(X0) != k2_relat_1(sK2)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_396])).

cnf(c_393,plain,
    ( k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
    | k2_funct_1(sK2) = X0
    | k1_relat_1(X0) != k2_relat_1(sK2)
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_392])).

cnf(c_1702,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1701])).

cnf(c_1760,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1759])).

cnf(c_2237,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | k1_relat_1(X0) != k2_relat_1(sK2)
    | k2_funct_1(sK2) = X0
    | k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1316,c_34,c_36,c_393,c_1702,c_1760])).

cnf(c_2238,plain,
    ( k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
    | k2_funct_1(sK2) = X0
    | k1_relat_1(X0) != k2_relat_1(sK2)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2237])).

cnf(c_2401,plain,
    ( k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
    | k2_funct_1(sK2) = X0
    | k1_relat_1(X0) != sK1
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2099,c_2238])).

cnf(c_5,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_421,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_25])).

cnf(c_422,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
    inference(unflattening,[status(thm)],[c_421])).

cnf(c_424,plain,
    ( ~ v1_relat_1(sK2)
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_422,c_33])).

cnf(c_1315,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_424])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_337,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_25])).

cnf(c_338,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_337])).

cnf(c_342,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(sK2,X0,X1)
    | k2_relset_1(X0,X1,sK2) != X1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
    | k1_xboole_0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_338,c_33])).

cnf(c_343,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_relset_1(X0,X1,sK2) != X1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
    | k1_xboole_0 = X1 ),
    inference(renaming,[status(thm)],[c_342])).

cnf(c_698,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_relset_1(X0,X1,sK2) != X1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
    | sK0 != X0
    | sK1 != X1
    | sK2 != sK2
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_343])).

cnf(c_699,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k2_relset_1(sK0,sK1,sK2) != sK1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_698])).

cnf(c_701,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_699,c_31,c_27,c_23])).

cnf(c_1366,plain,
    ( k6_partfun1(k1_relat_1(sK2)) = k6_partfun1(sK0)
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1315,c_701])).

cnf(c_1492,plain,
    ( ~ v1_relat_1(sK2)
    | k6_partfun1(k1_relat_1(sK2)) = k6_partfun1(sK0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1366])).

cnf(c_2168,plain,
    ( k6_partfun1(k1_relat_1(sK2)) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1366,c_31,c_1492,c_1701,c_1759])).

cnf(c_2172,plain,
    ( k2_relat_1(k6_partfun1(sK0)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2168,c_2])).

cnf(c_2174,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(demodulation,[status(thm)],[c_2172,c_2])).

cnf(c_2734,plain,
    ( k5_relat_1(sK2,X0) != k6_partfun1(sK0)
    | k2_funct_1(sK2) = X0
    | k1_relat_1(X0) != sK1
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2401,c_2174])).

cnf(c_4105,plain,
    ( k2_funct_1(sK2) = sK3
    | k1_relat_1(sK3) != sK1
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4101,c_2734])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1326,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2461,plain,
    ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1321,c_1326])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_596,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK0 != X2
    | sK1 != X1
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_29])).

cnf(c_597,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k1_relset_1(sK1,sK0,sK3) = sK1
    | k1_xboole_0 = sK0 ),
    inference(unflattening,[status(thm)],[c_596])).

cnf(c_24,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_599,plain,
    ( k1_relset_1(sK1,sK0,sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_597,c_28,c_24])).

cnf(c_2466,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2461,c_599])).

cnf(c_4106,plain,
    ( k2_funct_1(sK2) = sK3
    | sK1 != sK1
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4105,c_2466])).

cnf(c_4107,plain,
    ( k2_funct_1(sK2) = sK3
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4106])).

cnf(c_1756,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1757,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1756])).

cnf(c_1698,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1551])).

cnf(c_1699,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1698])).

cnf(c_22,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f73])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4107,c_1757,c_1699,c_22,c_39,c_37])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:49:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.92/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.92/0.97  
% 2.92/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.92/0.97  
% 2.92/0.97  ------  iProver source info
% 2.92/0.97  
% 2.92/0.97  git: date: 2020-06-30 10:37:57 +0100
% 2.92/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.92/0.97  git: non_committed_changes: false
% 2.92/0.97  git: last_make_outside_of_git: false
% 2.92/0.97  
% 2.92/0.97  ------ 
% 2.92/0.97  
% 2.92/0.97  ------ Input Options
% 2.92/0.97  
% 2.92/0.97  --out_options                           all
% 2.92/0.97  --tptp_safe_out                         true
% 2.92/0.97  --problem_path                          ""
% 2.92/0.97  --include_path                          ""
% 2.92/0.97  --clausifier                            res/vclausify_rel
% 2.92/0.97  --clausifier_options                    --mode clausify
% 2.92/0.97  --stdin                                 false
% 2.92/0.97  --stats_out                             all
% 2.92/0.97  
% 2.92/0.97  ------ General Options
% 2.92/0.97  
% 2.92/0.97  --fof                                   false
% 2.92/0.97  --time_out_real                         305.
% 2.92/0.97  --time_out_virtual                      -1.
% 2.92/0.97  --symbol_type_check                     false
% 2.92/0.97  --clausify_out                          false
% 2.92/0.97  --sig_cnt_out                           false
% 2.92/0.97  --trig_cnt_out                          false
% 2.92/0.97  --trig_cnt_out_tolerance                1.
% 2.92/0.97  --trig_cnt_out_sk_spl                   false
% 2.92/0.97  --abstr_cl_out                          false
% 2.92/0.97  
% 2.92/0.97  ------ Global Options
% 2.92/0.97  
% 2.92/0.97  --schedule                              default
% 2.92/0.97  --add_important_lit                     false
% 2.92/0.97  --prop_solver_per_cl                    1000
% 2.92/0.97  --min_unsat_core                        false
% 2.92/0.97  --soft_assumptions                      false
% 2.92/0.97  --soft_lemma_size                       3
% 2.92/0.97  --prop_impl_unit_size                   0
% 2.92/0.97  --prop_impl_unit                        []
% 2.92/0.97  --share_sel_clauses                     true
% 2.92/0.97  --reset_solvers                         false
% 2.92/0.97  --bc_imp_inh                            [conj_cone]
% 2.92/0.97  --conj_cone_tolerance                   3.
% 2.92/0.97  --extra_neg_conj                        none
% 2.92/0.97  --large_theory_mode                     true
% 2.92/0.97  --prolific_symb_bound                   200
% 2.92/0.97  --lt_threshold                          2000
% 2.92/0.97  --clause_weak_htbl                      true
% 2.92/0.97  --gc_record_bc_elim                     false
% 2.92/0.97  
% 2.92/0.97  ------ Preprocessing Options
% 2.92/0.97  
% 2.92/0.97  --preprocessing_flag                    true
% 2.92/0.97  --time_out_prep_mult                    0.1
% 2.92/0.97  --splitting_mode                        input
% 2.92/0.97  --splitting_grd                         true
% 2.92/0.97  --splitting_cvd                         false
% 2.92/0.97  --splitting_cvd_svl                     false
% 2.92/0.97  --splitting_nvd                         32
% 2.92/0.97  --sub_typing                            true
% 2.92/0.97  --prep_gs_sim                           true
% 2.92/0.97  --prep_unflatten                        true
% 2.92/0.97  --prep_res_sim                          true
% 2.92/0.97  --prep_upred                            true
% 2.92/0.97  --prep_sem_filter                       exhaustive
% 2.92/0.97  --prep_sem_filter_out                   false
% 2.92/0.97  --pred_elim                             true
% 2.92/0.97  --res_sim_input                         true
% 2.92/0.97  --eq_ax_congr_red                       true
% 2.92/0.97  --pure_diseq_elim                       true
% 2.92/0.97  --brand_transform                       false
% 2.92/0.97  --non_eq_to_eq                          false
% 2.92/0.97  --prep_def_merge                        true
% 2.92/0.97  --prep_def_merge_prop_impl              false
% 2.92/0.97  --prep_def_merge_mbd                    true
% 2.92/0.97  --prep_def_merge_tr_red                 false
% 2.92/0.97  --prep_def_merge_tr_cl                  false
% 2.92/0.97  --smt_preprocessing                     true
% 2.92/0.97  --smt_ac_axioms                         fast
% 2.92/0.97  --preprocessed_out                      false
% 2.92/0.97  --preprocessed_stats                    false
% 2.92/0.97  
% 2.92/0.97  ------ Abstraction refinement Options
% 2.92/0.97  
% 2.92/0.97  --abstr_ref                             []
% 2.92/0.97  --abstr_ref_prep                        false
% 2.92/0.97  --abstr_ref_until_sat                   false
% 2.92/0.97  --abstr_ref_sig_restrict                funpre
% 2.92/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.92/0.97  --abstr_ref_under                       []
% 2.92/0.97  
% 2.92/0.97  ------ SAT Options
% 2.92/0.97  
% 2.92/0.97  --sat_mode                              false
% 2.92/0.97  --sat_fm_restart_options                ""
% 2.92/0.97  --sat_gr_def                            false
% 2.92/0.97  --sat_epr_types                         true
% 2.92/0.97  --sat_non_cyclic_types                  false
% 2.92/0.97  --sat_finite_models                     false
% 2.92/0.97  --sat_fm_lemmas                         false
% 2.92/0.97  --sat_fm_prep                           false
% 2.92/0.97  --sat_fm_uc_incr                        true
% 2.92/0.97  --sat_out_model                         small
% 2.92/0.97  --sat_out_clauses                       false
% 2.92/0.97  
% 2.92/0.97  ------ QBF Options
% 2.92/0.97  
% 2.92/0.97  --qbf_mode                              false
% 2.92/0.97  --qbf_elim_univ                         false
% 2.92/0.97  --qbf_dom_inst                          none
% 2.92/0.97  --qbf_dom_pre_inst                      false
% 2.92/0.97  --qbf_sk_in                             false
% 2.92/0.97  --qbf_pred_elim                         true
% 2.92/0.97  --qbf_split                             512
% 2.92/0.97  
% 2.92/0.97  ------ BMC1 Options
% 2.92/0.97  
% 2.92/0.97  --bmc1_incremental                      false
% 2.92/0.97  --bmc1_axioms                           reachable_all
% 2.92/0.97  --bmc1_min_bound                        0
% 2.92/0.97  --bmc1_max_bound                        -1
% 2.92/0.97  --bmc1_max_bound_default                -1
% 2.92/0.97  --bmc1_symbol_reachability              true
% 2.92/0.97  --bmc1_property_lemmas                  false
% 2.92/0.97  --bmc1_k_induction                      false
% 2.92/0.97  --bmc1_non_equiv_states                 false
% 2.92/0.97  --bmc1_deadlock                         false
% 2.92/0.97  --bmc1_ucm                              false
% 2.92/0.97  --bmc1_add_unsat_core                   none
% 2.92/0.97  --bmc1_unsat_core_children              false
% 2.92/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.92/0.97  --bmc1_out_stat                         full
% 2.92/0.97  --bmc1_ground_init                      false
% 2.92/0.97  --bmc1_pre_inst_next_state              false
% 2.92/0.97  --bmc1_pre_inst_state                   false
% 2.92/0.97  --bmc1_pre_inst_reach_state             false
% 2.92/0.97  --bmc1_out_unsat_core                   false
% 2.92/0.97  --bmc1_aig_witness_out                  false
% 2.92/0.97  --bmc1_verbose                          false
% 2.92/0.97  --bmc1_dump_clauses_tptp                false
% 2.92/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.92/0.97  --bmc1_dump_file                        -
% 2.92/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.92/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.92/0.97  --bmc1_ucm_extend_mode                  1
% 2.92/0.97  --bmc1_ucm_init_mode                    2
% 2.92/0.97  --bmc1_ucm_cone_mode                    none
% 2.92/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.92/0.97  --bmc1_ucm_relax_model                  4
% 2.92/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.92/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.92/0.97  --bmc1_ucm_layered_model                none
% 2.92/0.97  --bmc1_ucm_max_lemma_size               10
% 2.92/0.97  
% 2.92/0.97  ------ AIG Options
% 2.92/0.97  
% 2.92/0.97  --aig_mode                              false
% 2.92/0.97  
% 2.92/0.97  ------ Instantiation Options
% 2.92/0.97  
% 2.92/0.97  --instantiation_flag                    true
% 2.92/0.97  --inst_sos_flag                         false
% 2.92/0.97  --inst_sos_phase                        true
% 2.92/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.92/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.92/0.97  --inst_lit_sel_side                     num_symb
% 2.92/0.97  --inst_solver_per_active                1400
% 2.92/0.97  --inst_solver_calls_frac                1.
% 2.92/0.97  --inst_passive_queue_type               priority_queues
% 2.92/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.92/0.97  --inst_passive_queues_freq              [25;2]
% 2.92/0.97  --inst_dismatching                      true
% 2.92/0.97  --inst_eager_unprocessed_to_passive     true
% 2.92/0.97  --inst_prop_sim_given                   true
% 2.92/0.97  --inst_prop_sim_new                     false
% 2.92/0.97  --inst_subs_new                         false
% 2.92/0.97  --inst_eq_res_simp                      false
% 2.92/0.97  --inst_subs_given                       false
% 2.92/0.97  --inst_orphan_elimination               true
% 2.92/0.97  --inst_learning_loop_flag               true
% 2.92/0.97  --inst_learning_start                   3000
% 2.92/0.97  --inst_learning_factor                  2
% 2.92/0.97  --inst_start_prop_sim_after_learn       3
% 2.92/0.97  --inst_sel_renew                        solver
% 2.92/0.97  --inst_lit_activity_flag                true
% 2.92/0.97  --inst_restr_to_given                   false
% 2.92/0.97  --inst_activity_threshold               500
% 2.92/0.97  --inst_out_proof                        true
% 2.92/0.97  
% 2.92/0.97  ------ Resolution Options
% 2.92/0.97  
% 2.92/0.97  --resolution_flag                       true
% 2.92/0.97  --res_lit_sel                           adaptive
% 2.92/0.97  --res_lit_sel_side                      none
% 2.92/0.97  --res_ordering                          kbo
% 2.92/0.97  --res_to_prop_solver                    active
% 2.92/0.97  --res_prop_simpl_new                    false
% 2.92/0.97  --res_prop_simpl_given                  true
% 2.92/0.97  --res_passive_queue_type                priority_queues
% 2.92/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.92/0.97  --res_passive_queues_freq               [15;5]
% 2.92/0.97  --res_forward_subs                      full
% 2.92/0.97  --res_backward_subs                     full
% 2.92/0.97  --res_forward_subs_resolution           true
% 2.92/0.97  --res_backward_subs_resolution          true
% 2.92/0.97  --res_orphan_elimination                true
% 2.92/0.97  --res_time_limit                        2.
% 2.92/0.97  --res_out_proof                         true
% 2.92/0.97  
% 2.92/0.97  ------ Superposition Options
% 2.92/0.97  
% 2.92/0.97  --superposition_flag                    true
% 2.92/0.97  --sup_passive_queue_type                priority_queues
% 2.92/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.92/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.92/0.97  --demod_completeness_check              fast
% 2.92/0.97  --demod_use_ground                      true
% 2.92/0.97  --sup_to_prop_solver                    passive
% 2.92/0.97  --sup_prop_simpl_new                    true
% 2.92/0.97  --sup_prop_simpl_given                  true
% 2.92/0.97  --sup_fun_splitting                     false
% 2.92/0.97  --sup_smt_interval                      50000
% 2.92/0.97  
% 2.92/0.97  ------ Superposition Simplification Setup
% 2.92/0.97  
% 2.92/0.97  --sup_indices_passive                   []
% 2.92/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.92/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.92/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.92/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.92/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.92/0.97  --sup_full_bw                           [BwDemod]
% 2.92/0.97  --sup_immed_triv                        [TrivRules]
% 2.92/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.92/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.92/0.97  --sup_immed_bw_main                     []
% 2.92/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.92/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.92/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.92/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.92/0.97  
% 2.92/0.97  ------ Combination Options
% 2.92/0.97  
% 2.92/0.97  --comb_res_mult                         3
% 2.92/0.97  --comb_sup_mult                         2
% 2.92/0.97  --comb_inst_mult                        10
% 2.92/0.97  
% 2.92/0.97  ------ Debug Options
% 2.92/0.97  
% 2.92/0.97  --dbg_backtrace                         false
% 2.92/0.97  --dbg_dump_prop_clauses                 false
% 2.92/0.97  --dbg_dump_prop_clauses_file            -
% 2.92/0.97  --dbg_out_stat                          false
% 2.92/0.97  ------ Parsing...
% 2.92/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.92/0.97  
% 2.92/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.92/0.97  
% 2.92/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.92/0.97  
% 2.92/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.92/0.97  ------ Proving...
% 2.92/0.97  ------ Problem Properties 
% 2.92/0.97  
% 2.92/0.97  
% 2.92/0.97  clauses                                 33
% 2.92/0.97  conjectures                             8
% 2.92/0.97  EPR                                     4
% 2.92/0.97  Horn                                    31
% 2.92/0.97  unary                                   16
% 2.92/0.97  binary                                  4
% 2.92/0.97  lits                                    78
% 2.92/0.97  lits eq                                 40
% 2.92/0.97  fd_pure                                 0
% 2.92/0.97  fd_pseudo                               0
% 2.92/0.97  fd_cond                                 3
% 2.92/0.97  fd_pseudo_cond                          0
% 2.92/0.97  AC symbols                              0
% 2.92/0.97  
% 2.92/0.97  ------ Schedule dynamic 5 is on 
% 2.92/0.97  
% 2.92/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.92/0.97  
% 2.92/0.97  
% 2.92/0.97  ------ 
% 2.92/0.97  Current options:
% 2.92/0.97  ------ 
% 2.92/0.97  
% 2.92/0.97  ------ Input Options
% 2.92/0.97  
% 2.92/0.97  --out_options                           all
% 2.92/0.97  --tptp_safe_out                         true
% 2.92/0.97  --problem_path                          ""
% 2.92/0.97  --include_path                          ""
% 2.92/0.97  --clausifier                            res/vclausify_rel
% 2.92/0.97  --clausifier_options                    --mode clausify
% 2.92/0.97  --stdin                                 false
% 2.92/0.97  --stats_out                             all
% 2.92/0.97  
% 2.92/0.97  ------ General Options
% 2.92/0.97  
% 2.92/0.97  --fof                                   false
% 2.92/0.97  --time_out_real                         305.
% 2.92/0.97  --time_out_virtual                      -1.
% 2.92/0.97  --symbol_type_check                     false
% 2.92/0.97  --clausify_out                          false
% 2.92/0.97  --sig_cnt_out                           false
% 2.92/0.97  --trig_cnt_out                          false
% 2.92/0.97  --trig_cnt_out_tolerance                1.
% 2.92/0.97  --trig_cnt_out_sk_spl                   false
% 2.92/0.97  --abstr_cl_out                          false
% 2.92/0.97  
% 2.92/0.97  ------ Global Options
% 2.92/0.97  
% 2.92/0.97  --schedule                              default
% 2.92/0.97  --add_important_lit                     false
% 2.92/0.97  --prop_solver_per_cl                    1000
% 2.92/0.97  --min_unsat_core                        false
% 2.92/0.97  --soft_assumptions                      false
% 2.92/0.97  --soft_lemma_size                       3
% 2.92/0.97  --prop_impl_unit_size                   0
% 2.92/0.97  --prop_impl_unit                        []
% 2.92/0.97  --share_sel_clauses                     true
% 2.92/0.97  --reset_solvers                         false
% 2.92/0.97  --bc_imp_inh                            [conj_cone]
% 2.92/0.97  --conj_cone_tolerance                   3.
% 2.92/0.97  --extra_neg_conj                        none
% 2.92/0.97  --large_theory_mode                     true
% 2.92/0.97  --prolific_symb_bound                   200
% 2.92/0.97  --lt_threshold                          2000
% 2.92/0.97  --clause_weak_htbl                      true
% 2.92/0.97  --gc_record_bc_elim                     false
% 2.92/0.97  
% 2.92/0.97  ------ Preprocessing Options
% 2.92/0.97  
% 2.92/0.97  --preprocessing_flag                    true
% 2.92/0.97  --time_out_prep_mult                    0.1
% 2.92/0.97  --splitting_mode                        input
% 2.92/0.97  --splitting_grd                         true
% 2.92/0.97  --splitting_cvd                         false
% 2.92/0.97  --splitting_cvd_svl                     false
% 2.92/0.97  --splitting_nvd                         32
% 2.92/0.97  --sub_typing                            true
% 2.92/0.97  --prep_gs_sim                           true
% 2.92/0.97  --prep_unflatten                        true
% 2.92/0.97  --prep_res_sim                          true
% 2.92/0.97  --prep_upred                            true
% 2.92/0.97  --prep_sem_filter                       exhaustive
% 2.92/0.97  --prep_sem_filter_out                   false
% 2.92/0.97  --pred_elim                             true
% 2.92/0.97  --res_sim_input                         true
% 2.92/0.97  --eq_ax_congr_red                       true
% 2.92/0.97  --pure_diseq_elim                       true
% 2.92/0.97  --brand_transform                       false
% 2.92/0.97  --non_eq_to_eq                          false
% 2.92/0.97  --prep_def_merge                        true
% 2.92/0.97  --prep_def_merge_prop_impl              false
% 2.92/0.97  --prep_def_merge_mbd                    true
% 2.92/0.97  --prep_def_merge_tr_red                 false
% 2.92/0.97  --prep_def_merge_tr_cl                  false
% 2.92/0.97  --smt_preprocessing                     true
% 2.92/0.97  --smt_ac_axioms                         fast
% 2.92/0.97  --preprocessed_out                      false
% 2.92/0.97  --preprocessed_stats                    false
% 2.92/0.97  
% 2.92/0.97  ------ Abstraction refinement Options
% 2.92/0.97  
% 2.92/0.97  --abstr_ref                             []
% 2.92/0.97  --abstr_ref_prep                        false
% 2.92/0.97  --abstr_ref_until_sat                   false
% 2.92/0.97  --abstr_ref_sig_restrict                funpre
% 2.92/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.92/0.97  --abstr_ref_under                       []
% 2.92/0.97  
% 2.92/0.97  ------ SAT Options
% 2.92/0.97  
% 2.92/0.97  --sat_mode                              false
% 2.92/0.97  --sat_fm_restart_options                ""
% 2.92/0.97  --sat_gr_def                            false
% 2.92/0.97  --sat_epr_types                         true
% 2.92/0.97  --sat_non_cyclic_types                  false
% 2.92/0.97  --sat_finite_models                     false
% 2.92/0.97  --sat_fm_lemmas                         false
% 2.92/0.97  --sat_fm_prep                           false
% 2.92/0.97  --sat_fm_uc_incr                        true
% 2.92/0.97  --sat_out_model                         small
% 2.92/0.97  --sat_out_clauses                       false
% 2.92/0.97  
% 2.92/0.97  ------ QBF Options
% 2.92/0.97  
% 2.92/0.97  --qbf_mode                              false
% 2.92/0.97  --qbf_elim_univ                         false
% 2.92/0.97  --qbf_dom_inst                          none
% 2.92/0.97  --qbf_dom_pre_inst                      false
% 2.92/0.97  --qbf_sk_in                             false
% 2.92/0.97  --qbf_pred_elim                         true
% 2.92/0.97  --qbf_split                             512
% 2.92/0.97  
% 2.92/0.97  ------ BMC1 Options
% 2.92/0.97  
% 2.92/0.97  --bmc1_incremental                      false
% 2.92/0.97  --bmc1_axioms                           reachable_all
% 2.92/0.97  --bmc1_min_bound                        0
% 2.92/0.97  --bmc1_max_bound                        -1
% 2.92/0.97  --bmc1_max_bound_default                -1
% 2.92/0.97  --bmc1_symbol_reachability              true
% 2.92/0.97  --bmc1_property_lemmas                  false
% 2.92/0.97  --bmc1_k_induction                      false
% 2.92/0.97  --bmc1_non_equiv_states                 false
% 2.92/0.97  --bmc1_deadlock                         false
% 2.92/0.97  --bmc1_ucm                              false
% 2.92/0.97  --bmc1_add_unsat_core                   none
% 2.92/0.97  --bmc1_unsat_core_children              false
% 2.92/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.92/0.97  --bmc1_out_stat                         full
% 2.92/0.97  --bmc1_ground_init                      false
% 2.92/0.97  --bmc1_pre_inst_next_state              false
% 2.92/0.97  --bmc1_pre_inst_state                   false
% 2.92/0.97  --bmc1_pre_inst_reach_state             false
% 2.92/0.97  --bmc1_out_unsat_core                   false
% 2.92/0.97  --bmc1_aig_witness_out                  false
% 2.92/0.97  --bmc1_verbose                          false
% 2.92/0.97  --bmc1_dump_clauses_tptp                false
% 2.92/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.92/0.97  --bmc1_dump_file                        -
% 2.92/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.92/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.92/0.97  --bmc1_ucm_extend_mode                  1
% 2.92/0.97  --bmc1_ucm_init_mode                    2
% 2.92/0.97  --bmc1_ucm_cone_mode                    none
% 2.92/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.92/0.97  --bmc1_ucm_relax_model                  4
% 2.92/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.92/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.92/0.97  --bmc1_ucm_layered_model                none
% 2.92/0.97  --bmc1_ucm_max_lemma_size               10
% 2.92/0.97  
% 2.92/0.97  ------ AIG Options
% 2.92/0.97  
% 2.92/0.97  --aig_mode                              false
% 2.92/0.97  
% 2.92/0.97  ------ Instantiation Options
% 2.92/0.97  
% 2.92/0.97  --instantiation_flag                    true
% 2.92/0.97  --inst_sos_flag                         false
% 2.92/0.97  --inst_sos_phase                        true
% 2.92/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.92/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.92/0.97  --inst_lit_sel_side                     none
% 2.92/0.97  --inst_solver_per_active                1400
% 2.92/0.97  --inst_solver_calls_frac                1.
% 2.92/0.97  --inst_passive_queue_type               priority_queues
% 2.92/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.92/0.97  --inst_passive_queues_freq              [25;2]
% 2.92/0.97  --inst_dismatching                      true
% 2.92/0.97  --inst_eager_unprocessed_to_passive     true
% 2.92/0.97  --inst_prop_sim_given                   true
% 2.92/0.97  --inst_prop_sim_new                     false
% 2.92/0.97  --inst_subs_new                         false
% 2.92/0.97  --inst_eq_res_simp                      false
% 2.92/0.97  --inst_subs_given                       false
% 2.92/0.97  --inst_orphan_elimination               true
% 2.92/0.97  --inst_learning_loop_flag               true
% 2.92/0.97  --inst_learning_start                   3000
% 2.92/0.97  --inst_learning_factor                  2
% 2.92/0.97  --inst_start_prop_sim_after_learn       3
% 2.92/0.97  --inst_sel_renew                        solver
% 2.92/0.97  --inst_lit_activity_flag                true
% 2.92/0.97  --inst_restr_to_given                   false
% 2.92/0.97  --inst_activity_threshold               500
% 2.92/0.97  --inst_out_proof                        true
% 2.92/0.97  
% 2.92/0.97  ------ Resolution Options
% 2.92/0.97  
% 2.92/0.97  --resolution_flag                       false
% 2.92/0.97  --res_lit_sel                           adaptive
% 2.92/0.97  --res_lit_sel_side                      none
% 2.92/0.97  --res_ordering                          kbo
% 2.92/0.97  --res_to_prop_solver                    active
% 2.92/0.97  --res_prop_simpl_new                    false
% 2.92/0.97  --res_prop_simpl_given                  true
% 2.92/0.97  --res_passive_queue_type                priority_queues
% 2.92/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.92/0.97  --res_passive_queues_freq               [15;5]
% 2.92/0.97  --res_forward_subs                      full
% 2.92/0.97  --res_backward_subs                     full
% 2.92/0.97  --res_forward_subs_resolution           true
% 2.92/0.97  --res_backward_subs_resolution          true
% 2.92/0.97  --res_orphan_elimination                true
% 2.92/0.97  --res_time_limit                        2.
% 2.92/0.97  --res_out_proof                         true
% 2.92/0.97  
% 2.92/0.97  ------ Superposition Options
% 2.92/0.97  
% 2.92/0.97  --superposition_flag                    true
% 2.92/0.97  --sup_passive_queue_type                priority_queues
% 2.92/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.92/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.92/0.97  --demod_completeness_check              fast
% 2.92/0.97  --demod_use_ground                      true
% 2.92/0.97  --sup_to_prop_solver                    passive
% 2.92/0.97  --sup_prop_simpl_new                    true
% 2.92/0.97  --sup_prop_simpl_given                  true
% 2.92/0.97  --sup_fun_splitting                     false
% 2.92/0.97  --sup_smt_interval                      50000
% 2.92/0.97  
% 2.92/0.97  ------ Superposition Simplification Setup
% 2.92/0.97  
% 2.92/0.97  --sup_indices_passive                   []
% 2.92/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.92/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.92/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.92/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.92/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.92/0.97  --sup_full_bw                           [BwDemod]
% 2.92/0.97  --sup_immed_triv                        [TrivRules]
% 2.92/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.92/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.92/0.97  --sup_immed_bw_main                     []
% 2.92/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.92/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.92/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.92/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.92/0.97  
% 2.92/0.97  ------ Combination Options
% 2.92/0.97  
% 2.92/0.97  --comb_res_mult                         3
% 2.92/0.97  --comb_sup_mult                         2
% 2.92/0.97  --comb_inst_mult                        10
% 2.92/0.97  
% 2.92/0.97  ------ Debug Options
% 2.92/0.97  
% 2.92/0.97  --dbg_backtrace                         false
% 2.92/0.97  --dbg_dump_prop_clauses                 false
% 2.92/0.97  --dbg_dump_prop_clauses_file            -
% 2.92/0.97  --dbg_out_stat                          false
% 2.92/0.97  
% 2.92/0.97  
% 2.92/0.97  
% 2.92/0.97  
% 2.92/0.97  ------ Proving...
% 2.92/0.97  
% 2.92/0.97  
% 2.92/0.97  % SZS status Theorem for theBenchmark.p
% 2.92/0.97  
% 2.92/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 2.92/0.97  
% 2.92/0.97  fof(f14,conjecture,(
% 2.92/0.97    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.92/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.92/0.97  
% 2.92/0.97  fof(f15,negated_conjecture,(
% 2.92/0.97    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.92/0.97    inference(negated_conjecture,[],[f14])).
% 2.92/0.97  
% 2.92/0.97  fof(f32,plain,(
% 2.92/0.97    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.92/0.97    inference(ennf_transformation,[],[f15])).
% 2.92/0.97  
% 2.92/0.97  fof(f33,plain,(
% 2.92/0.97    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.92/0.97    inference(flattening,[],[f32])).
% 2.92/0.97  
% 2.92/0.97  fof(f37,plain,(
% 2.92/0.97    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 2.92/0.97    introduced(choice_axiom,[])).
% 2.92/0.97  
% 2.92/0.97  fof(f36,plain,(
% 2.92/0.97    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 2.92/0.97    introduced(choice_axiom,[])).
% 2.92/0.97  
% 2.92/0.97  fof(f38,plain,(
% 2.92/0.97    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 2.92/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f33,f37,f36])).
% 2.92/0.97  
% 2.92/0.97  fof(f64,plain,(
% 2.92/0.97    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.92/0.97    inference(cnf_transformation,[],[f38])).
% 2.92/0.97  
% 2.92/0.97  fof(f67,plain,(
% 2.92/0.97    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.92/0.97    inference(cnf_transformation,[],[f38])).
% 2.92/0.97  
% 2.92/0.97  fof(f11,axiom,(
% 2.92/0.97    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 2.92/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.92/0.97  
% 2.92/0.97  fof(f28,plain,(
% 2.92/0.97    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.92/0.97    inference(ennf_transformation,[],[f11])).
% 2.92/0.97  
% 2.92/0.97  fof(f29,plain,(
% 2.92/0.97    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.92/0.97    inference(flattening,[],[f28])).
% 2.92/0.97  
% 2.92/0.97  fof(f58,plain,(
% 2.92/0.97    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.92/0.97    inference(cnf_transformation,[],[f29])).
% 2.92/0.97  
% 2.92/0.97  fof(f65,plain,(
% 2.92/0.97    v1_funct_1(sK3)),
% 2.92/0.97    inference(cnf_transformation,[],[f38])).
% 2.92/0.97  
% 2.92/0.97  fof(f62,plain,(
% 2.92/0.97    v1_funct_1(sK2)),
% 2.92/0.97    inference(cnf_transformation,[],[f38])).
% 2.92/0.97  
% 2.92/0.97  fof(f7,axiom,(
% 2.92/0.97    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.92/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.92/0.97  
% 2.92/0.97  fof(f22,plain,(
% 2.92/0.97    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.92/0.97    inference(ennf_transformation,[],[f7])).
% 2.92/0.97  
% 2.92/0.97  fof(f23,plain,(
% 2.92/0.97    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.92/0.97    inference(flattening,[],[f22])).
% 2.92/0.97  
% 2.92/0.97  fof(f34,plain,(
% 2.92/0.97    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.92/0.97    inference(nnf_transformation,[],[f23])).
% 2.92/0.97  
% 2.92/0.97  fof(f47,plain,(
% 2.92/0.97    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.92/0.97    inference(cnf_transformation,[],[f34])).
% 2.92/0.97  
% 2.92/0.97  fof(f69,plain,(
% 2.92/0.97    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.92/0.97    inference(cnf_transformation,[],[f38])).
% 2.92/0.97  
% 2.92/0.97  fof(f8,axiom,(
% 2.92/0.97    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 2.92/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.92/0.97  
% 2.92/0.97  fof(f49,plain,(
% 2.92/0.97    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.92/0.97    inference(cnf_transformation,[],[f8])).
% 2.92/0.97  
% 2.92/0.97  fof(f12,axiom,(
% 2.92/0.97    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.92/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.92/0.97  
% 2.92/0.97  fof(f59,plain,(
% 2.92/0.97    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.92/0.97    inference(cnf_transformation,[],[f12])).
% 2.92/0.97  
% 2.92/0.97  fof(f79,plain,(
% 2.92/0.97    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.92/0.97    inference(definition_unfolding,[],[f49,f59])).
% 2.92/0.97  
% 2.92/0.97  fof(f10,axiom,(
% 2.92/0.97    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 2.92/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.92/0.97  
% 2.92/0.97  fof(f26,plain,(
% 2.92/0.97    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.92/0.97    inference(ennf_transformation,[],[f10])).
% 2.92/0.97  
% 2.92/0.97  fof(f27,plain,(
% 2.92/0.97    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.92/0.97    inference(flattening,[],[f26])).
% 2.92/0.97  
% 2.92/0.97  fof(f57,plain,(
% 2.92/0.97    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.92/0.97    inference(cnf_transformation,[],[f27])).
% 2.92/0.97  
% 2.92/0.97  fof(f4,axiom,(
% 2.92/0.97    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)))))),
% 2.92/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.92/0.97  
% 2.92/0.97  fof(f17,plain,(
% 2.92/0.97    ! [X0] : (((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.92/0.97    inference(ennf_transformation,[],[f4])).
% 2.92/0.97  
% 2.92/0.97  fof(f18,plain,(
% 2.92/0.97    ! [X0] : ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.92/0.97    inference(flattening,[],[f17])).
% 2.92/0.97  
% 2.92/0.97  fof(f44,plain,(
% 2.92/0.97    ( ! [X0] : (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.92/0.97    inference(cnf_transformation,[],[f18])).
% 2.92/0.97  
% 2.92/0.97  fof(f76,plain,(
% 2.92/0.97    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.92/0.97    inference(definition_unfolding,[],[f44,f59])).
% 2.92/0.97  
% 2.92/0.97  fof(f70,plain,(
% 2.92/0.97    v2_funct_1(sK2)),
% 2.92/0.97    inference(cnf_transformation,[],[f38])).
% 2.92/0.97  
% 2.92/0.97  fof(f63,plain,(
% 2.92/0.97    v1_funct_2(sK2,sK0,sK1)),
% 2.92/0.97    inference(cnf_transformation,[],[f38])).
% 2.92/0.97  
% 2.92/0.97  fof(f13,axiom,(
% 2.92/0.97    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 2.92/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.92/0.97  
% 2.92/0.97  fof(f30,plain,(
% 2.92/0.97    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.92/0.97    inference(ennf_transformation,[],[f13])).
% 2.92/0.97  
% 2.92/0.97  fof(f31,plain,(
% 2.92/0.97    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.92/0.97    inference(flattening,[],[f30])).
% 2.92/0.97  
% 2.92/0.97  fof(f61,plain,(
% 2.92/0.97    ( ! [X2,X0,X1] : (k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.92/0.97    inference(cnf_transformation,[],[f31])).
% 2.92/0.97  
% 2.92/0.97  fof(f68,plain,(
% 2.92/0.97    k2_relset_1(sK0,sK1,sK2) = sK1),
% 2.92/0.97    inference(cnf_transformation,[],[f38])).
% 2.92/0.97  
% 2.92/0.97  fof(f72,plain,(
% 2.92/0.97    k1_xboole_0 != sK1),
% 2.92/0.97    inference(cnf_transformation,[],[f38])).
% 2.92/0.97  
% 2.92/0.97  fof(f1,axiom,(
% 2.92/0.97    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.92/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.92/0.97  
% 2.92/0.97  fof(f16,plain,(
% 2.92/0.97    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.92/0.97    inference(ennf_transformation,[],[f1])).
% 2.92/0.97  
% 2.92/0.97  fof(f39,plain,(
% 2.92/0.97    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.92/0.97    inference(cnf_transformation,[],[f16])).
% 2.92/0.97  
% 2.92/0.97  fof(f2,axiom,(
% 2.92/0.97    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.92/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.92/0.97  
% 2.92/0.97  fof(f40,plain,(
% 2.92/0.97    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.92/0.97    inference(cnf_transformation,[],[f2])).
% 2.92/0.97  
% 2.92/0.97  fof(f3,axiom,(
% 2.92/0.97    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.92/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.92/0.97  
% 2.92/0.97  fof(f42,plain,(
% 2.92/0.97    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 2.92/0.97    inference(cnf_transformation,[],[f3])).
% 2.92/0.97  
% 2.92/0.97  fof(f74,plain,(
% 2.92/0.97    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 2.92/0.97    inference(definition_unfolding,[],[f42,f59])).
% 2.92/0.97  
% 2.92/0.97  fof(f5,axiom,(
% 2.92/0.97    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,X1) & k1_relat_1(X1) = k2_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 2.92/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.92/0.97  
% 2.92/0.97  fof(f19,plain,(
% 2.92/0.97    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | k1_relat_1(X1) != k2_relat_1(X0) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.92/0.97    inference(ennf_transformation,[],[f5])).
% 2.92/0.97  
% 2.92/0.97  fof(f20,plain,(
% 2.92/0.97    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | k1_relat_1(X1) != k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.92/0.97    inference(flattening,[],[f19])).
% 2.92/0.97  
% 2.92/0.97  fof(f45,plain,(
% 2.92/0.97    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | k1_relat_1(X1) != k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.92/0.97    inference(cnf_transformation,[],[f20])).
% 2.92/0.97  
% 2.92/0.97  fof(f78,plain,(
% 2.92/0.97    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0)) | k1_relat_1(X1) != k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.92/0.97    inference(definition_unfolding,[],[f45,f59])).
% 2.92/0.97  
% 2.92/0.97  fof(f43,plain,(
% 2.92/0.97    ( ! [X0] : (k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.92/0.97    inference(cnf_transformation,[],[f18])).
% 2.92/0.97  
% 2.92/0.97  fof(f77,plain,(
% 2.92/0.97    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.92/0.97    inference(definition_unfolding,[],[f43,f59])).
% 2.92/0.97  
% 2.92/0.97  fof(f60,plain,(
% 2.92/0.97    ( ! [X2,X0,X1] : (k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.92/0.97    inference(cnf_transformation,[],[f31])).
% 2.92/0.97  
% 2.92/0.97  fof(f6,axiom,(
% 2.92/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.92/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.92/0.97  
% 2.92/0.97  fof(f21,plain,(
% 2.92/0.97    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.92/0.97    inference(ennf_transformation,[],[f6])).
% 2.92/0.97  
% 2.92/0.97  fof(f46,plain,(
% 2.92/0.97    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.92/0.97    inference(cnf_transformation,[],[f21])).
% 2.92/0.97  
% 2.92/0.97  fof(f9,axiom,(
% 2.92/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.92/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.92/0.97  
% 2.92/0.97  fof(f24,plain,(
% 2.92/0.97    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.92/0.97    inference(ennf_transformation,[],[f9])).
% 2.92/0.97  
% 2.92/0.97  fof(f25,plain,(
% 2.92/0.97    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.92/0.97    inference(flattening,[],[f24])).
% 2.92/0.97  
% 2.92/0.97  fof(f35,plain,(
% 2.92/0.97    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.92/0.97    inference(nnf_transformation,[],[f25])).
% 2.92/0.97  
% 2.92/0.97  fof(f50,plain,(
% 2.92/0.97    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.92/0.97    inference(cnf_transformation,[],[f35])).
% 2.92/0.97  
% 2.92/0.97  fof(f66,plain,(
% 2.92/0.97    v1_funct_2(sK3,sK1,sK0)),
% 2.92/0.97    inference(cnf_transformation,[],[f38])).
% 2.92/0.97  
% 2.92/0.97  fof(f71,plain,(
% 2.92/0.97    k1_xboole_0 != sK0),
% 2.92/0.97    inference(cnf_transformation,[],[f38])).
% 2.92/0.97  
% 2.92/0.97  fof(f73,plain,(
% 2.92/0.97    k2_funct_1(sK2) != sK3),
% 2.92/0.97    inference(cnf_transformation,[],[f38])).
% 2.92/0.97  
% 2.92/0.97  cnf(c_31,negated_conjecture,
% 2.92/0.97      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.92/0.97      inference(cnf_transformation,[],[f64]) ).
% 2.92/0.97  
% 2.92/0.97  cnf(c_1319,plain,
% 2.92/0.97      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.92/0.97      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.92/0.97  
% 2.92/0.97  cnf(c_28,negated_conjecture,
% 2.92/0.97      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 2.92/0.97      inference(cnf_transformation,[],[f67]) ).
% 2.92/0.97  
% 2.92/0.97  cnf(c_1321,plain,
% 2.92/0.97      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 2.92/0.97      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.92/0.97  
% 2.92/0.97  cnf(c_19,plain,
% 2.92/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.92/0.97      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 2.92/0.97      | ~ v1_funct_1(X0)
% 2.92/0.97      | ~ v1_funct_1(X3)
% 2.92/0.97      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 2.92/0.97      inference(cnf_transformation,[],[f58]) ).
% 2.92/0.97  
% 2.92/0.97  cnf(c_1322,plain,
% 2.92/0.97      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 2.92/0.97      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 2.92/0.97      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.92/0.97      | v1_funct_1(X5) != iProver_top
% 2.92/0.97      | v1_funct_1(X4) != iProver_top ),
% 2.92/0.97      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.92/0.97  
% 2.92/0.97  cnf(c_2802,plain,
% 2.92/0.97      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 2.92/0.97      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.92/0.97      | v1_funct_1(X2) != iProver_top
% 2.92/0.97      | v1_funct_1(sK3) != iProver_top ),
% 2.92/0.97      inference(superposition,[status(thm)],[c_1321,c_1322]) ).
% 2.92/0.97  
% 2.92/0.97  cnf(c_30,negated_conjecture,
% 2.92/0.97      ( v1_funct_1(sK3) ),
% 2.92/0.97      inference(cnf_transformation,[],[f65]) ).
% 2.92/0.97  
% 2.92/0.97  cnf(c_37,plain,
% 2.92/0.97      ( v1_funct_1(sK3) = iProver_top ),
% 2.92/0.97      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.92/0.97  
% 2.92/0.97  cnf(c_3382,plain,
% 2.92/0.97      ( v1_funct_1(X2) != iProver_top
% 2.92/0.97      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.92/0.97      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 2.92/0.97      inference(global_propositional_subsumption,
% 2.92/0.97                [status(thm)],
% 2.92/0.97                [c_2802,c_37]) ).
% 2.92/0.97  
% 2.92/0.97  cnf(c_3383,plain,
% 2.92/0.97      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 2.92/0.97      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.92/0.97      | v1_funct_1(X2) != iProver_top ),
% 2.92/0.97      inference(renaming,[status(thm)],[c_3382]) ).
% 2.92/0.97  
% 2.92/0.97  cnf(c_3394,plain,
% 2.92/0.97      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 2.92/0.97      | v1_funct_1(sK2) != iProver_top ),
% 2.92/0.97      inference(superposition,[status(thm)],[c_1319,c_3383]) ).
% 2.92/0.97  
% 2.92/0.97  cnf(c_33,negated_conjecture,
% 2.92/0.97      ( v1_funct_1(sK2) ),
% 2.92/0.97      inference(cnf_transformation,[],[f62]) ).
% 2.92/0.97  
% 2.92/0.97  cnf(c_34,plain,
% 2.92/0.97      ( v1_funct_1(sK2) = iProver_top ),
% 2.92/0.97      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 2.92/0.97  
% 2.92/0.97  cnf(c_3764,plain,
% 2.92/0.97      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 2.92/0.97      inference(global_propositional_subsumption,
% 2.92/0.97                [status(thm)],
% 2.92/0.97                [c_3394,c_34]) ).
% 2.92/0.97  
% 2.92/0.97  cnf(c_9,plain,
% 2.92/0.97      ( ~ r2_relset_1(X0,X1,X2,X3)
% 2.92/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.92/0.97      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.92/0.97      | X3 = X2 ),
% 2.92/0.97      inference(cnf_transformation,[],[f47]) ).
% 2.92/0.97  
% 2.92/0.97  cnf(c_26,negated_conjecture,
% 2.92/0.97      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 2.92/0.97      inference(cnf_transformation,[],[f69]) ).
% 2.92/0.97  
% 2.92/0.97  cnf(c_321,plain,
% 2.92/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.92/0.97      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.92/0.97      | X3 = X0
% 2.92/0.97      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 2.92/0.97      | k6_partfun1(sK0) != X3
% 2.92/0.97      | sK0 != X2
% 2.92/0.97      | sK0 != X1 ),
% 2.92/0.97      inference(resolution_lifted,[status(thm)],[c_9,c_26]) ).
% 2.92/0.97  
% 2.92/0.97  cnf(c_322,plain,
% 2.92/0.97      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.92/0.97      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.92/0.97      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 2.92/0.97      inference(unflattening,[status(thm)],[c_321]) ).
% 2.92/0.97  
% 2.92/0.97  cnf(c_10,plain,
% 2.92/0.97      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 2.92/0.97      inference(cnf_transformation,[],[f79]) ).
% 2.92/0.97  
% 2.92/0.97  cnf(c_330,plain,
% 2.92/0.97      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.92/0.97      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 2.92/0.97      inference(forward_subsumption_resolution,
% 2.92/0.97                [status(thm)],
% 2.92/0.97                [c_322,c_10]) ).
% 2.92/0.97  
% 2.92/0.97  cnf(c_1317,plain,
% 2.92/0.97      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 2.92/0.97      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 2.92/0.97      inference(predicate_to_equality,[status(thm)],[c_330]) ).
% 2.92/0.97  
% 2.92/0.97  cnf(c_3767,plain,
% 2.92/0.97      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 2.92/0.97      | m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 2.92/0.97      inference(demodulation,[status(thm)],[c_3764,c_1317]) ).
% 2.92/0.97  
% 2.92/0.97  cnf(c_36,plain,
% 2.92/0.97      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.92/0.97      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.92/0.97  
% 2.92/0.97  cnf(c_39,plain,
% 2.92/0.97      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 2.92/0.97      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.92/0.97  
% 2.92/0.97  cnf(c_17,plain,
% 2.92/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.92/0.97      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 2.92/0.97      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 2.92/0.97      | ~ v1_funct_1(X0)
% 2.92/0.97      | ~ v1_funct_1(X3) ),
% 2.92/0.97      inference(cnf_transformation,[],[f57]) ).
% 2.92/0.97  
% 2.92/0.97  cnf(c_1324,plain,
% 2.92/0.97      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.92/0.97      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 2.92/0.97      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 2.92/0.97      | v1_funct_1(X0) != iProver_top
% 2.92/0.97      | v1_funct_1(X3) != iProver_top ),
% 2.92/0.97      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.92/0.97  
% 2.92/0.97  cnf(c_3769,plain,
% 2.92/0.97      ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 2.92/0.97      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.92/0.97      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.92/0.97      | v1_funct_1(sK3) != iProver_top
% 2.92/0.97      | v1_funct_1(sK2) != iProver_top ),
% 2.92/0.97      inference(superposition,[status(thm)],[c_3764,c_1324]) ).
% 2.92/0.97  
% 2.92/0.97  cnf(c_4101,plain,
% 2.92/0.97      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 2.92/0.97      inference(global_propositional_subsumption,
% 2.92/0.97                [status(thm)],
% 2.92/0.97                [c_3767,c_34,c_36,c_37,c_39,c_3769]) ).
% 2.92/0.97  
% 2.92/0.97  cnf(c_4,plain,
% 2.92/0.98      ( ~ v1_funct_1(X0)
% 2.92/0.98      | ~ v2_funct_1(X0)
% 2.92/0.98      | ~ v1_relat_1(X0)
% 2.92/0.98      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
% 2.92/0.98      inference(cnf_transformation,[],[f76]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_25,negated_conjecture,
% 2.92/0.98      ( v2_funct_1(sK2) ),
% 2.92/0.98      inference(cnf_transformation,[],[f70]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_435,plain,
% 2.92/0.98      ( ~ v1_funct_1(X0)
% 2.92/0.98      | ~ v1_relat_1(X0)
% 2.92/0.98      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
% 2.92/0.98      | sK2 != X0 ),
% 2.92/0.98      inference(resolution_lifted,[status(thm)],[c_4,c_25]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_436,plain,
% 2.92/0.98      ( ~ v1_funct_1(sK2)
% 2.92/0.98      | ~ v1_relat_1(sK2)
% 2.92/0.98      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 2.92/0.98      inference(unflattening,[status(thm)],[c_435]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_438,plain,
% 2.92/0.98      ( ~ v1_relat_1(sK2)
% 2.92/0.98      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 2.92/0.98      inference(global_propositional_subsumption,
% 2.92/0.98                [status(thm)],
% 2.92/0.98                [c_436,c_33]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_1314,plain,
% 2.92/0.98      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
% 2.92/0.98      | v1_relat_1(sK2) != iProver_top ),
% 2.92/0.98      inference(predicate_to_equality,[status(thm)],[c_438]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_32,negated_conjecture,
% 2.92/0.98      ( v1_funct_2(sK2,sK0,sK1) ),
% 2.92/0.98      inference(cnf_transformation,[],[f63]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_20,plain,
% 2.92/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.92/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.92/0.98      | ~ v1_funct_1(X0)
% 2.92/0.98      | ~ v2_funct_1(X0)
% 2.92/0.98      | k2_relset_1(X1,X2,X0) != X2
% 2.92/0.98      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
% 2.92/0.98      | k1_xboole_0 = X2 ),
% 2.92/0.98      inference(cnf_transformation,[],[f61]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_364,plain,
% 2.92/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.92/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.92/0.98      | ~ v1_funct_1(X0)
% 2.92/0.98      | k2_relset_1(X1,X2,X0) != X2
% 2.92/0.98      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
% 2.92/0.98      | sK2 != X0
% 2.92/0.98      | k1_xboole_0 = X2 ),
% 2.92/0.98      inference(resolution_lifted,[status(thm)],[c_20,c_25]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_365,plain,
% 2.92/0.98      ( ~ v1_funct_2(sK2,X0,X1)
% 2.92/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.92/0.98      | ~ v1_funct_1(sK2)
% 2.92/0.98      | k2_relset_1(X0,X1,sK2) != X1
% 2.92/0.98      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(X1)
% 2.92/0.98      | k1_xboole_0 = X1 ),
% 2.92/0.98      inference(unflattening,[status(thm)],[c_364]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_369,plain,
% 2.92/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.92/0.98      | ~ v1_funct_2(sK2,X0,X1)
% 2.92/0.98      | k2_relset_1(X0,X1,sK2) != X1
% 2.92/0.98      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(X1)
% 2.92/0.98      | k1_xboole_0 = X1 ),
% 2.92/0.98      inference(global_propositional_subsumption,
% 2.92/0.98                [status(thm)],
% 2.92/0.98                [c_365,c_33]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_370,plain,
% 2.92/0.98      ( ~ v1_funct_2(sK2,X0,X1)
% 2.92/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.92/0.98      | k2_relset_1(X0,X1,sK2) != X1
% 2.92/0.98      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(X1)
% 2.92/0.98      | k1_xboole_0 = X1 ),
% 2.92/0.98      inference(renaming,[status(thm)],[c_369]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_690,plain,
% 2.92/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.92/0.98      | k2_relset_1(X0,X1,sK2) != X1
% 2.92/0.98      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(X1)
% 2.92/0.98      | sK0 != X0
% 2.92/0.98      | sK1 != X1
% 2.92/0.98      | sK2 != sK2
% 2.92/0.98      | k1_xboole_0 = X1 ),
% 2.92/0.98      inference(resolution_lifted,[status(thm)],[c_32,c_370]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_691,plain,
% 2.92/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.92/0.98      | k2_relset_1(sK0,sK1,sK2) != sK1
% 2.92/0.98      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 2.92/0.98      | k1_xboole_0 = sK1 ),
% 2.92/0.98      inference(unflattening,[status(thm)],[c_690]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_27,negated_conjecture,
% 2.92/0.98      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 2.92/0.98      inference(cnf_transformation,[],[f68]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_23,negated_conjecture,
% 2.92/0.98      ( k1_xboole_0 != sK1 ),
% 2.92/0.98      inference(cnf_transformation,[],[f72]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_693,plain,
% 2.92/0.98      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
% 2.92/0.98      inference(global_propositional_subsumption,
% 2.92/0.98                [status(thm)],
% 2.92/0.98                [c_691,c_31,c_27,c_23]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_1361,plain,
% 2.92/0.98      ( k6_partfun1(k2_relat_1(sK2)) = k6_partfun1(sK1)
% 2.92/0.98      | v1_relat_1(sK2) != iProver_top ),
% 2.92/0.98      inference(light_normalisation,[status(thm)],[c_1314,c_693]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_1498,plain,
% 2.92/0.98      ( ~ v1_relat_1(sK2)
% 2.92/0.98      | k6_partfun1(k2_relat_1(sK2)) = k6_partfun1(sK1) ),
% 2.92/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_1361]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_0,plain,
% 2.92/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.92/0.98      | ~ v1_relat_1(X1)
% 2.92/0.98      | v1_relat_1(X0) ),
% 2.92/0.98      inference(cnf_transformation,[],[f39]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_1551,plain,
% 2.92/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.92/0.98      | v1_relat_1(X0)
% 2.92/0.98      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 2.92/0.98      inference(instantiation,[status(thm)],[c_0]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_1701,plain,
% 2.92/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.92/0.98      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
% 2.92/0.98      | v1_relat_1(sK2) ),
% 2.92/0.98      inference(instantiation,[status(thm)],[c_1551]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_1,plain,
% 2.92/0.98      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.92/0.98      inference(cnf_transformation,[],[f40]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_1759,plain,
% 2.92/0.98      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 2.92/0.98      inference(instantiation,[status(thm)],[c_1]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_2093,plain,
% 2.92/0.98      ( k6_partfun1(k2_relat_1(sK2)) = k6_partfun1(sK1) ),
% 2.92/0.98      inference(global_propositional_subsumption,
% 2.92/0.98                [status(thm)],
% 2.92/0.98                [c_1361,c_31,c_1498,c_1701,c_1759]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_2,plain,
% 2.92/0.98      ( k2_relat_1(k6_partfun1(X0)) = X0 ),
% 2.92/0.98      inference(cnf_transformation,[],[f74]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_2097,plain,
% 2.92/0.98      ( k2_relat_1(k6_partfun1(sK1)) = k2_relat_1(sK2) ),
% 2.92/0.98      inference(superposition,[status(thm)],[c_2093,c_2]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_2099,plain,
% 2.92/0.98      ( k2_relat_1(sK2) = sK1 ),
% 2.92/0.98      inference(demodulation,[status(thm)],[c_2097,c_2]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_6,plain,
% 2.92/0.98      ( ~ v1_funct_1(X0)
% 2.92/0.98      | ~ v1_funct_1(X1)
% 2.92/0.98      | ~ v2_funct_1(X0)
% 2.92/0.98      | ~ v1_relat_1(X0)
% 2.92/0.98      | ~ v1_relat_1(X1)
% 2.92/0.98      | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
% 2.92/0.98      | k2_funct_1(X0) = X1
% 2.92/0.98      | k1_relat_1(X1) != k2_relat_1(X0) ),
% 2.92/0.98      inference(cnf_transformation,[],[f78]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_391,plain,
% 2.92/0.98      ( ~ v1_funct_1(X0)
% 2.92/0.98      | ~ v1_funct_1(X1)
% 2.92/0.98      | ~ v1_relat_1(X0)
% 2.92/0.98      | ~ v1_relat_1(X1)
% 2.92/0.98      | k5_relat_1(X1,X0) != k6_partfun1(k1_relat_1(X1))
% 2.92/0.98      | k2_funct_1(X1) = X0
% 2.92/0.98      | k1_relat_1(X0) != k2_relat_1(X1)
% 2.92/0.98      | sK2 != X1 ),
% 2.92/0.98      inference(resolution_lifted,[status(thm)],[c_6,c_25]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_392,plain,
% 2.92/0.98      ( ~ v1_funct_1(X0)
% 2.92/0.98      | ~ v1_funct_1(sK2)
% 2.92/0.98      | ~ v1_relat_1(X0)
% 2.92/0.98      | ~ v1_relat_1(sK2)
% 2.92/0.98      | k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
% 2.92/0.98      | k2_funct_1(sK2) = X0
% 2.92/0.98      | k1_relat_1(X0) != k2_relat_1(sK2) ),
% 2.92/0.98      inference(unflattening,[status(thm)],[c_391]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_396,plain,
% 2.92/0.98      ( ~ v1_funct_1(X0)
% 2.92/0.98      | ~ v1_relat_1(X0)
% 2.92/0.98      | ~ v1_relat_1(sK2)
% 2.92/0.98      | k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
% 2.92/0.98      | k2_funct_1(sK2) = X0
% 2.92/0.98      | k1_relat_1(X0) != k2_relat_1(sK2) ),
% 2.92/0.98      inference(global_propositional_subsumption,
% 2.92/0.98                [status(thm)],
% 2.92/0.98                [c_392,c_33]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_1316,plain,
% 2.92/0.98      ( k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
% 2.92/0.98      | k2_funct_1(sK2) = X0
% 2.92/0.98      | k1_relat_1(X0) != k2_relat_1(sK2)
% 2.92/0.98      | v1_funct_1(X0) != iProver_top
% 2.92/0.98      | v1_relat_1(X0) != iProver_top
% 2.92/0.98      | v1_relat_1(sK2) != iProver_top ),
% 2.92/0.98      inference(predicate_to_equality,[status(thm)],[c_396]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_393,plain,
% 2.92/0.98      ( k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
% 2.92/0.98      | k2_funct_1(sK2) = X0
% 2.92/0.98      | k1_relat_1(X0) != k2_relat_1(sK2)
% 2.92/0.98      | v1_funct_1(X0) != iProver_top
% 2.92/0.98      | v1_funct_1(sK2) != iProver_top
% 2.92/0.98      | v1_relat_1(X0) != iProver_top
% 2.92/0.98      | v1_relat_1(sK2) != iProver_top ),
% 2.92/0.98      inference(predicate_to_equality,[status(thm)],[c_392]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_1702,plain,
% 2.92/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.92/0.98      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 2.92/0.98      | v1_relat_1(sK2) = iProver_top ),
% 2.92/0.98      inference(predicate_to_equality,[status(thm)],[c_1701]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_1760,plain,
% 2.92/0.98      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 2.92/0.98      inference(predicate_to_equality,[status(thm)],[c_1759]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_2237,plain,
% 2.92/0.98      ( v1_relat_1(X0) != iProver_top
% 2.92/0.98      | v1_funct_1(X0) != iProver_top
% 2.92/0.98      | k1_relat_1(X0) != k2_relat_1(sK2)
% 2.92/0.98      | k2_funct_1(sK2) = X0
% 2.92/0.98      | k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2)) ),
% 2.92/0.98      inference(global_propositional_subsumption,
% 2.92/0.98                [status(thm)],
% 2.92/0.98                [c_1316,c_34,c_36,c_393,c_1702,c_1760]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_2238,plain,
% 2.92/0.98      ( k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
% 2.92/0.98      | k2_funct_1(sK2) = X0
% 2.92/0.98      | k1_relat_1(X0) != k2_relat_1(sK2)
% 2.92/0.98      | v1_funct_1(X0) != iProver_top
% 2.92/0.98      | v1_relat_1(X0) != iProver_top ),
% 2.92/0.98      inference(renaming,[status(thm)],[c_2237]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_2401,plain,
% 2.92/0.98      ( k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
% 2.92/0.98      | k2_funct_1(sK2) = X0
% 2.92/0.98      | k1_relat_1(X0) != sK1
% 2.92/0.98      | v1_funct_1(X0) != iProver_top
% 2.92/0.98      | v1_relat_1(X0) != iProver_top ),
% 2.92/0.98      inference(demodulation,[status(thm)],[c_2099,c_2238]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_5,plain,
% 2.92/0.98      ( ~ v1_funct_1(X0)
% 2.92/0.98      | ~ v2_funct_1(X0)
% 2.92/0.98      | ~ v1_relat_1(X0)
% 2.92/0.98      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
% 2.92/0.98      inference(cnf_transformation,[],[f77]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_421,plain,
% 2.92/0.98      ( ~ v1_funct_1(X0)
% 2.92/0.98      | ~ v1_relat_1(X0)
% 2.92/0.98      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
% 2.92/0.98      | sK2 != X0 ),
% 2.92/0.98      inference(resolution_lifted,[status(thm)],[c_5,c_25]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_422,plain,
% 2.92/0.98      ( ~ v1_funct_1(sK2)
% 2.92/0.98      | ~ v1_relat_1(sK2)
% 2.92/0.98      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
% 2.92/0.98      inference(unflattening,[status(thm)],[c_421]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_424,plain,
% 2.92/0.98      ( ~ v1_relat_1(sK2)
% 2.92/0.98      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
% 2.92/0.98      inference(global_propositional_subsumption,
% 2.92/0.98                [status(thm)],
% 2.92/0.98                [c_422,c_33]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_1315,plain,
% 2.92/0.98      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
% 2.92/0.98      | v1_relat_1(sK2) != iProver_top ),
% 2.92/0.98      inference(predicate_to_equality,[status(thm)],[c_424]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_21,plain,
% 2.92/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.92/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.92/0.98      | ~ v1_funct_1(X0)
% 2.92/0.98      | ~ v2_funct_1(X0)
% 2.92/0.98      | k2_relset_1(X1,X2,X0) != X2
% 2.92/0.98      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 2.92/0.98      | k1_xboole_0 = X2 ),
% 2.92/0.98      inference(cnf_transformation,[],[f60]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_337,plain,
% 2.92/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.92/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.92/0.98      | ~ v1_funct_1(X0)
% 2.92/0.98      | k2_relset_1(X1,X2,X0) != X2
% 2.92/0.98      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 2.92/0.98      | sK2 != X0
% 2.92/0.98      | k1_xboole_0 = X2 ),
% 2.92/0.98      inference(resolution_lifted,[status(thm)],[c_21,c_25]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_338,plain,
% 2.92/0.98      ( ~ v1_funct_2(sK2,X0,X1)
% 2.92/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.92/0.98      | ~ v1_funct_1(sK2)
% 2.92/0.98      | k2_relset_1(X0,X1,sK2) != X1
% 2.92/0.98      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
% 2.92/0.98      | k1_xboole_0 = X1 ),
% 2.92/0.98      inference(unflattening,[status(thm)],[c_337]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_342,plain,
% 2.92/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.92/0.98      | ~ v1_funct_2(sK2,X0,X1)
% 2.92/0.98      | k2_relset_1(X0,X1,sK2) != X1
% 2.92/0.98      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
% 2.92/0.98      | k1_xboole_0 = X1 ),
% 2.92/0.98      inference(global_propositional_subsumption,
% 2.92/0.98                [status(thm)],
% 2.92/0.98                [c_338,c_33]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_343,plain,
% 2.92/0.98      ( ~ v1_funct_2(sK2,X0,X1)
% 2.92/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.92/0.98      | k2_relset_1(X0,X1,sK2) != X1
% 2.92/0.98      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
% 2.92/0.98      | k1_xboole_0 = X1 ),
% 2.92/0.98      inference(renaming,[status(thm)],[c_342]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_698,plain,
% 2.92/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.92/0.98      | k2_relset_1(X0,X1,sK2) != X1
% 2.92/0.98      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
% 2.92/0.98      | sK0 != X0
% 2.92/0.98      | sK1 != X1
% 2.92/0.98      | sK2 != sK2
% 2.92/0.98      | k1_xboole_0 = X1 ),
% 2.92/0.98      inference(resolution_lifted,[status(thm)],[c_32,c_343]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_699,plain,
% 2.92/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.92/0.98      | k2_relset_1(sK0,sK1,sK2) != sK1
% 2.92/0.98      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
% 2.92/0.98      | k1_xboole_0 = sK1 ),
% 2.92/0.98      inference(unflattening,[status(thm)],[c_698]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_701,plain,
% 2.92/0.98      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
% 2.92/0.98      inference(global_propositional_subsumption,
% 2.92/0.98                [status(thm)],
% 2.92/0.98                [c_699,c_31,c_27,c_23]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_1366,plain,
% 2.92/0.98      ( k6_partfun1(k1_relat_1(sK2)) = k6_partfun1(sK0)
% 2.92/0.98      | v1_relat_1(sK2) != iProver_top ),
% 2.92/0.98      inference(light_normalisation,[status(thm)],[c_1315,c_701]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_1492,plain,
% 2.92/0.98      ( ~ v1_relat_1(sK2)
% 2.92/0.98      | k6_partfun1(k1_relat_1(sK2)) = k6_partfun1(sK0) ),
% 2.92/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_1366]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_2168,plain,
% 2.92/0.98      ( k6_partfun1(k1_relat_1(sK2)) = k6_partfun1(sK0) ),
% 2.92/0.98      inference(global_propositional_subsumption,
% 2.92/0.98                [status(thm)],
% 2.92/0.98                [c_1366,c_31,c_1492,c_1701,c_1759]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_2172,plain,
% 2.92/0.98      ( k2_relat_1(k6_partfun1(sK0)) = k1_relat_1(sK2) ),
% 2.92/0.98      inference(superposition,[status(thm)],[c_2168,c_2]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_2174,plain,
% 2.92/0.98      ( k1_relat_1(sK2) = sK0 ),
% 2.92/0.98      inference(demodulation,[status(thm)],[c_2172,c_2]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_2734,plain,
% 2.92/0.98      ( k5_relat_1(sK2,X0) != k6_partfun1(sK0)
% 2.92/0.98      | k2_funct_1(sK2) = X0
% 2.92/0.98      | k1_relat_1(X0) != sK1
% 2.92/0.98      | v1_funct_1(X0) != iProver_top
% 2.92/0.98      | v1_relat_1(X0) != iProver_top ),
% 2.92/0.98      inference(light_normalisation,[status(thm)],[c_2401,c_2174]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_4105,plain,
% 2.92/0.98      ( k2_funct_1(sK2) = sK3
% 2.92/0.98      | k1_relat_1(sK3) != sK1
% 2.92/0.98      | v1_funct_1(sK3) != iProver_top
% 2.92/0.98      | v1_relat_1(sK3) != iProver_top ),
% 2.92/0.98      inference(superposition,[status(thm)],[c_4101,c_2734]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_7,plain,
% 2.92/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.92/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.92/0.98      inference(cnf_transformation,[],[f46]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_1326,plain,
% 2.92/0.98      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.92/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.92/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_2461,plain,
% 2.92/0.98      ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
% 2.92/0.98      inference(superposition,[status(thm)],[c_1321,c_1326]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_16,plain,
% 2.92/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.92/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.92/0.98      | k1_relset_1(X1,X2,X0) = X1
% 2.92/0.98      | k1_xboole_0 = X2 ),
% 2.92/0.98      inference(cnf_transformation,[],[f50]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_29,negated_conjecture,
% 2.92/0.98      ( v1_funct_2(sK3,sK1,sK0) ),
% 2.92/0.98      inference(cnf_transformation,[],[f66]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_596,plain,
% 2.92/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.92/0.98      | k1_relset_1(X1,X2,X0) = X1
% 2.92/0.98      | sK0 != X2
% 2.92/0.98      | sK1 != X1
% 2.92/0.98      | sK3 != X0
% 2.92/0.98      | k1_xboole_0 = X2 ),
% 2.92/0.98      inference(resolution_lifted,[status(thm)],[c_16,c_29]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_597,plain,
% 2.92/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.92/0.98      | k1_relset_1(sK1,sK0,sK3) = sK1
% 2.92/0.98      | k1_xboole_0 = sK0 ),
% 2.92/0.98      inference(unflattening,[status(thm)],[c_596]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_24,negated_conjecture,
% 2.92/0.98      ( k1_xboole_0 != sK0 ),
% 2.92/0.98      inference(cnf_transformation,[],[f71]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_599,plain,
% 2.92/0.98      ( k1_relset_1(sK1,sK0,sK3) = sK1 ),
% 2.92/0.98      inference(global_propositional_subsumption,
% 2.92/0.98                [status(thm)],
% 2.92/0.98                [c_597,c_28,c_24]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_2466,plain,
% 2.92/0.98      ( k1_relat_1(sK3) = sK1 ),
% 2.92/0.98      inference(light_normalisation,[status(thm)],[c_2461,c_599]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_4106,plain,
% 2.92/0.98      ( k2_funct_1(sK2) = sK3
% 2.92/0.98      | sK1 != sK1
% 2.92/0.98      | v1_funct_1(sK3) != iProver_top
% 2.92/0.98      | v1_relat_1(sK3) != iProver_top ),
% 2.92/0.98      inference(light_normalisation,[status(thm)],[c_4105,c_2466]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_4107,plain,
% 2.92/0.98      ( k2_funct_1(sK2) = sK3
% 2.92/0.98      | v1_funct_1(sK3) != iProver_top
% 2.92/0.98      | v1_relat_1(sK3) != iProver_top ),
% 2.92/0.98      inference(equality_resolution_simp,[status(thm)],[c_4106]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_1756,plain,
% 2.92/0.98      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
% 2.92/0.98      inference(instantiation,[status(thm)],[c_1]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_1757,plain,
% 2.92/0.98      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
% 2.92/0.98      inference(predicate_to_equality,[status(thm)],[c_1756]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_1698,plain,
% 2.92/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.92/0.98      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
% 2.92/0.98      | v1_relat_1(sK3) ),
% 2.92/0.98      inference(instantiation,[status(thm)],[c_1551]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_1699,plain,
% 2.92/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.92/0.98      | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 2.92/0.98      | v1_relat_1(sK3) = iProver_top ),
% 2.92/0.98      inference(predicate_to_equality,[status(thm)],[c_1698]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(c_22,negated_conjecture,
% 2.92/0.98      ( k2_funct_1(sK2) != sK3 ),
% 2.92/0.98      inference(cnf_transformation,[],[f73]) ).
% 2.92/0.98  
% 2.92/0.98  cnf(contradiction,plain,
% 2.92/0.98      ( $false ),
% 2.92/0.98      inference(minisat,
% 2.92/0.98                [status(thm)],
% 2.92/0.98                [c_4107,c_1757,c_1699,c_22,c_39,c_37]) ).
% 2.92/0.98  
% 2.92/0.98  
% 2.92/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.92/0.98  
% 2.92/0.98  ------                               Statistics
% 2.92/0.98  
% 2.92/0.98  ------ General
% 2.92/0.98  
% 2.92/0.98  abstr_ref_over_cycles:                  0
% 2.92/0.98  abstr_ref_under_cycles:                 0
% 2.92/0.98  gc_basic_clause_elim:                   0
% 2.92/0.98  forced_gc_time:                         0
% 2.92/0.98  parsing_time:                           0.01
% 2.92/0.98  unif_index_cands_time:                  0.
% 2.92/0.98  unif_index_add_time:                    0.
% 2.92/0.98  orderings_time:                         0.
% 2.92/0.98  out_proof_time:                         0.012
% 2.92/0.98  total_time:                             0.142
% 2.92/0.98  num_of_symbols:                         52
% 2.92/0.98  num_of_terms:                           4752
% 2.92/0.98  
% 2.92/0.98  ------ Preprocessing
% 2.92/0.98  
% 2.92/0.98  num_of_splits:                          0
% 2.92/0.98  num_of_split_atoms:                     0
% 2.92/0.98  num_of_reused_defs:                     0
% 2.92/0.98  num_eq_ax_congr_red:                    2
% 2.92/0.98  num_of_sem_filtered_clauses:            1
% 2.92/0.98  num_of_subtypes:                        0
% 2.92/0.98  monotx_restored_types:                  0
% 2.92/0.98  sat_num_of_epr_types:                   0
% 2.92/0.98  sat_num_of_non_cyclic_types:            0
% 2.92/0.98  sat_guarded_non_collapsed_types:        0
% 2.92/0.98  num_pure_diseq_elim:                    0
% 2.92/0.98  simp_replaced_by:                       0
% 2.92/0.98  res_preprocessed:                       164
% 2.92/0.98  prep_upred:                             0
% 2.92/0.98  prep_unflattend:                        71
% 2.92/0.98  smt_new_axioms:                         0
% 2.92/0.98  pred_elim_cands:                        3
% 2.92/0.98  pred_elim:                              3
% 2.92/0.98  pred_elim_cl:                           1
% 2.92/0.98  pred_elim_cycles:                       5
% 2.92/0.98  merged_defs:                            0
% 2.92/0.98  merged_defs_ncl:                        0
% 2.92/0.98  bin_hyper_res:                          0
% 2.92/0.98  prep_cycles:                            4
% 2.92/0.98  pred_elim_time:                         0.012
% 2.92/0.98  splitting_time:                         0.
% 2.92/0.98  sem_filter_time:                        0.
% 2.92/0.98  monotx_time:                            0.
% 2.92/0.98  subtype_inf_time:                       0.
% 2.92/0.98  
% 2.92/0.98  ------ Problem properties
% 2.92/0.98  
% 2.92/0.98  clauses:                                33
% 2.92/0.98  conjectures:                            8
% 2.92/0.98  epr:                                    4
% 2.92/0.98  horn:                                   31
% 2.92/0.98  ground:                                 21
% 2.92/0.98  unary:                                  16
% 2.92/0.98  binary:                                 4
% 2.92/0.98  lits:                                   78
% 2.92/0.98  lits_eq:                                40
% 2.92/0.98  fd_pure:                                0
% 2.92/0.98  fd_pseudo:                              0
% 2.92/0.98  fd_cond:                                3
% 2.92/0.98  fd_pseudo_cond:                         0
% 2.92/0.98  ac_symbols:                             0
% 2.92/0.98  
% 2.92/0.98  ------ Propositional Solver
% 2.92/0.98  
% 2.92/0.98  prop_solver_calls:                      26
% 2.92/0.98  prop_fast_solver_calls:                 1119
% 2.92/0.98  smt_solver_calls:                       0
% 2.92/0.98  smt_fast_solver_calls:                  0
% 2.92/0.98  prop_num_of_clauses:                    1638
% 2.92/0.98  prop_preprocess_simplified:             5500
% 2.92/0.98  prop_fo_subsumed:                       43
% 2.92/0.98  prop_solver_time:                       0.
% 2.92/0.98  smt_solver_time:                        0.
% 2.92/0.98  smt_fast_solver_time:                   0.
% 2.92/0.98  prop_fast_solver_time:                  0.
% 2.92/0.98  prop_unsat_core_time:                   0.
% 2.92/0.98  
% 2.92/0.98  ------ QBF
% 2.92/0.98  
% 2.92/0.98  qbf_q_res:                              0
% 2.92/0.98  qbf_num_tautologies:                    0
% 2.92/0.98  qbf_prep_cycles:                        0
% 2.92/0.98  
% 2.92/0.98  ------ BMC1
% 2.92/0.98  
% 2.92/0.98  bmc1_current_bound:                     -1
% 2.92/0.98  bmc1_last_solved_bound:                 -1
% 2.92/0.98  bmc1_unsat_core_size:                   -1
% 2.92/0.98  bmc1_unsat_core_parents_size:           -1
% 2.92/0.98  bmc1_merge_next_fun:                    0
% 2.92/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.92/0.98  
% 2.92/0.98  ------ Instantiation
% 2.92/0.98  
% 2.92/0.98  inst_num_of_clauses:                    444
% 2.92/0.98  inst_num_in_passive:                    168
% 2.92/0.98  inst_num_in_active:                     251
% 2.92/0.98  inst_num_in_unprocessed:                25
% 2.92/0.98  inst_num_of_loops:                      260
% 2.92/0.98  inst_num_of_learning_restarts:          0
% 2.92/0.98  inst_num_moves_active_passive:          7
% 2.92/0.98  inst_lit_activity:                      0
% 2.92/0.98  inst_lit_activity_moves:                0
% 2.92/0.98  inst_num_tautologies:                   0
% 2.92/0.98  inst_num_prop_implied:                  0
% 2.92/0.98  inst_num_existing_simplified:           0
% 2.92/0.98  inst_num_eq_res_simplified:             0
% 2.92/0.98  inst_num_child_elim:                    0
% 2.92/0.98  inst_num_of_dismatching_blockings:      8
% 2.92/0.98  inst_num_of_non_proper_insts:           275
% 2.92/0.98  inst_num_of_duplicates:                 0
% 2.92/0.98  inst_inst_num_from_inst_to_res:         0
% 2.92/0.98  inst_dismatching_checking_time:         0.
% 2.92/0.98  
% 2.92/0.98  ------ Resolution
% 2.92/0.98  
% 2.92/0.98  res_num_of_clauses:                     0
% 2.92/0.98  res_num_in_passive:                     0
% 2.92/0.98  res_num_in_active:                      0
% 2.92/0.98  res_num_of_loops:                       168
% 2.92/0.98  res_forward_subset_subsumed:            22
% 2.92/0.98  res_backward_subset_subsumed:           0
% 2.92/0.98  res_forward_subsumed:                   0
% 2.92/0.98  res_backward_subsumed:                  2
% 2.92/0.98  res_forward_subsumption_resolution:     1
% 2.92/0.98  res_backward_subsumption_resolution:    0
% 2.92/0.98  res_clause_to_clause_subsumption:       167
% 2.92/0.98  res_orphan_elimination:                 0
% 2.92/0.98  res_tautology_del:                      23
% 2.92/0.98  res_num_eq_res_simplified:              0
% 2.92/0.98  res_num_sel_changes:                    0
% 2.92/0.98  res_moves_from_active_to_pass:          0
% 2.92/0.98  
% 2.92/0.98  ------ Superposition
% 2.92/0.98  
% 2.92/0.98  sup_time_total:                         0.
% 2.92/0.98  sup_time_generating:                    0.
% 2.92/0.98  sup_time_sim_full:                      0.
% 2.92/0.98  sup_time_sim_immed:                     0.
% 2.92/0.98  
% 2.92/0.98  sup_num_of_clauses:                     64
% 2.92/0.98  sup_num_in_active:                      46
% 2.92/0.98  sup_num_in_passive:                     18
% 2.92/0.98  sup_num_of_loops:                       50
% 2.92/0.98  sup_fw_superposition:                   25
% 2.92/0.98  sup_bw_superposition:                   17
% 2.92/0.98  sup_immediate_simplified:               10
% 2.92/0.98  sup_given_eliminated:                   2
% 2.92/0.98  comparisons_done:                       0
% 2.92/0.98  comparisons_avoided:                    0
% 2.92/0.98  
% 2.92/0.98  ------ Simplifications
% 2.92/0.98  
% 2.92/0.98  
% 2.92/0.98  sim_fw_subset_subsumed:                 0
% 2.92/0.98  sim_bw_subset_subsumed:                 1
% 2.92/0.98  sim_fw_subsumed:                        0
% 2.92/0.98  sim_bw_subsumed:                        0
% 2.92/0.98  sim_fw_subsumption_res:                 1
% 2.92/0.98  sim_bw_subsumption_res:                 0
% 2.92/0.98  sim_tautology_del:                      0
% 2.92/0.98  sim_eq_tautology_del:                   7
% 2.92/0.98  sim_eq_res_simp:                        1
% 2.92/0.98  sim_fw_demodulated:                     9
% 2.92/0.98  sim_bw_demodulated:                     5
% 2.92/0.98  sim_light_normalised:                   10
% 2.92/0.98  sim_joinable_taut:                      0
% 2.92/0.98  sim_joinable_simp:                      0
% 2.92/0.98  sim_ac_normalised:                      0
% 2.92/0.98  sim_smt_subsumption:                    0
% 2.92/0.98  
%------------------------------------------------------------------------------
