%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:33 EST 2020

% Result     : Theorem 3.48s
% Output     : CNFRefutation 3.48s
% Verified   : 
% Statistics : Number of formulae       :  183 ( 731 expanded)
%              Number of clauses        :  115 ( 223 expanded)
%              Number of leaves         :   18 ( 187 expanded)
%              Depth                    :   19
%              Number of atoms          :  660 (6325 expanded)
%              Number of equality atoms :  320 (2324 expanded)
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

fof(f35,plain,(
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

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f40,plain,(
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

fof(f39,plain,
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

fof(f41,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f36,f40,f39])).

fof(f66,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f41])).

fof(f69,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f41])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f31])).

fof(f59,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f67,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f64,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f41])).

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

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f71,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f41])).

fof(f10,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f58,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f25])).

fof(f49,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f22])).

fof(f47,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
              & k2_relat_1(X0) = k1_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
      | k2_relat_1(X0) != k1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f12,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
      | k2_relat_1(X0) != k1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f46,f60])).

fof(f72,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f75,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f41])).

fof(f70,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f41])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f65,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f41])).

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

fof(f38,plain,(
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

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f19,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f44,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f73,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f41])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f74,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f41])).

fof(f68,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1127,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1130,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1131,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1967,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1130,c_1131])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_36,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_2466,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1967,c_36])).

cnf(c_2467,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_2466])).

cnf(c_2474,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1127,c_2467])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_33,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_2946,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2474,c_33])).

cnf(c_9,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_25,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_327,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_25])).

cnf(c_328,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_327])).

cnf(c_16,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_336,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_328,c_16])).

cnf(c_1124,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_336])).

cnf(c_2948,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2946,c_1124])).

cnf(c_35,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_38,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | k4_relset_1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1139,plain,
    ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2930,plain,
    ( k4_relset_1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1130,c_1139])).

cnf(c_3053,plain,
    ( k4_relset_1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(superposition,[status(thm)],[c_1127,c_2930])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1141,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3371,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3053,c_1141])).

cnf(c_6542,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2948,c_35,c_38,c_3371])).

cnf(c_4,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
    | k1_relat_1(X1) != k2_relat_1(X0)
    | k2_funct_1(X0) = X1 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_24,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_415,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(X1,X0) != k6_partfun1(k1_relat_1(X1))
    | k1_relat_1(X0) != k2_relat_1(X1)
    | k2_funct_1(X1) = X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_24])).

cnf(c_416,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
    | k1_relat_1(X0) != k2_relat_1(sK2)
    | k2_funct_1(sK2) = X0 ),
    inference(unflattening,[status(thm)],[c_415])).

cnf(c_420,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
    | k1_relat_1(X0) != k2_relat_1(sK2)
    | k2_funct_1(sK2) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_416,c_32])).

cnf(c_1120,plain,
    ( k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
    | k1_relat_1(X0) != k2_relat_1(sK2)
    | k2_funct_1(sK2) = X0
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_420])).

cnf(c_417,plain,
    ( k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
    | k1_relat_1(X0) != k2_relat_1(sK2)
    | k2_funct_1(sK2) = X0
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_416])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1226,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
    | ~ v1_relat_1(X0)
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1373,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1226])).

cnf(c_1602,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1373])).

cnf(c_1603,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1602])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1662,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1663,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1662])).

cnf(c_1814,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | k2_funct_1(sK2) = X0
    | k1_relat_1(X0) != k2_relat_1(sK2)
    | k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1120,c_33,c_35,c_417,c_1603,c_1663])).

cnf(c_1815,plain,
    ( k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
    | k1_relat_1(X0) != k2_relat_1(sK2)
    | k2_funct_1(sK2) = X0
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1814])).

cnf(c_6546,plain,
    ( k6_partfun1(k1_relat_1(sK2)) != k6_partfun1(sK0)
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | k2_funct_1(sK2) = sK3
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6542,c_1815])).

cnf(c_21,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1142,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1143,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2035,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1130,c_1143])).

cnf(c_2309,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1142,c_2035])).

cnf(c_13852,plain,
    ( k1_relat_1(sK3) != k2_relat_1(sK2)
    | k6_partfun1(k1_relat_1(sK2)) != k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6546,c_36,c_21,c_2309])).

cnf(c_13853,plain,
    ( k6_partfun1(k1_relat_1(sK2)) != k6_partfun1(sK0)
    | k1_relat_1(sK3) != k2_relat_1(sK2) ),
    inference(renaming,[status(thm)],[c_13852])).

cnf(c_26,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_391,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_24])).

cnf(c_392,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(unflattening,[status(thm)],[c_391])).

cnf(c_396,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_2(sK2,X0,X1)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_392,c_32])).

cnf(c_397,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(renaming,[status(thm)],[c_396])).

cnf(c_1121,plain,
    ( k2_relset_1(X0,X1,sK2) != X1
    | v1_funct_2(sK2,X0,X1) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_397])).

cnf(c_1780,plain,
    ( v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_26,c_1121])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_34,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_1253,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k2_relset_1(sK0,sK1,sK2) != sK1 ),
    inference(instantiation,[status(thm)],[c_397])).

cnf(c_1254,plain,
    ( k2_relset_1(sK0,sK1,sK2) != sK1
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1253])).

cnf(c_1809,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1780,c_34,c_35,c_26,c_1254])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1133,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2597,plain,
    ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(k2_funct_1(sK2),sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1809,c_1133])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1140,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2031,plain,
    ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_1809,c_1140])).

cnf(c_2036,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1127,c_1143])).

cnf(c_2376,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2036,c_35,c_1603,c_1663])).

cnf(c_3,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_445,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_24])).

cnf(c_446,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_445])).

cnf(c_448,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_446,c_32])).

cnf(c_1119,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_448])).

cnf(c_2380,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2376,c_1119])).

cnf(c_2598,plain,
    ( k2_relat_1(sK2) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(k2_funct_1(sK2),sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2597,c_2031,c_2380])).

cnf(c_23,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_679,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_710,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_679])).

cnf(c_680,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1219,plain,
    ( sK0 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_680])).

cnf(c_1220,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1219])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_367,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_24])).

cnf(c_368,plain,
    ( v1_funct_2(k2_funct_1(sK2),X0,X1)
    | ~ v1_funct_2(sK2,X1,X0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X1,X0,sK2) != X0 ),
    inference(unflattening,[status(thm)],[c_367])).

cnf(c_372,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_2(sK2,X1,X0)
    | v1_funct_2(k2_funct_1(sK2),X0,X1)
    | k2_relset_1(X1,X0,sK2) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_368,c_32])).

cnf(c_373,plain,
    ( v1_funct_2(k2_funct_1(sK2),X0,X1)
    | ~ v1_funct_2(sK2,X1,X0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | k2_relset_1(X1,X0,sK2) != X0 ),
    inference(renaming,[status(thm)],[c_372])).

cnf(c_1246,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k2_relset_1(sK0,sK1,sK2) != sK1 ),
    inference(instantiation,[status(thm)],[c_373])).

cnf(c_1247,plain,
    ( k2_relset_1(sK0,sK1,sK2) != sK1
    | v1_funct_2(k2_funct_1(sK2),sK1,sK0) = iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1246])).

cnf(c_6742,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2598,c_34,c_35,c_26,c_23,c_710,c_1220,c_1247])).

cnf(c_2596,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1127,c_1133])).

cnf(c_2030,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1127,c_1140])).

cnf(c_2599,plain,
    ( k1_relat_1(sK2) = sK0
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2596,c_2030])).

cnf(c_22,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1201,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_680])).

cnf(c_1202,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1201])).

cnf(c_7812,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2599,c_34,c_22,c_710,c_1202])).

cnf(c_2595,plain,
    ( k1_relset_1(sK1,sK0,sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1130,c_1133])).

cnf(c_2029,plain,
    ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1130,c_1140])).

cnf(c_2600,plain,
    ( k1_relat_1(sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2595,c_2029])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_37,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_8852,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2600,c_37,c_23,c_710,c_1220])).

cnf(c_13854,plain,
    ( k6_partfun1(sK0) != k6_partfun1(sK0)
    | sK1 != sK1 ),
    inference(light_normalisation,[status(thm)],[c_13853,c_6742,c_7812,c_8852])).

cnf(c_13855,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_13854])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:00:35 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.48/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.48/1.01  
% 3.48/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.48/1.01  
% 3.48/1.01  ------  iProver source info
% 3.48/1.01  
% 3.48/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.48/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.48/1.01  git: non_committed_changes: false
% 3.48/1.01  git: last_make_outside_of_git: false
% 3.48/1.01  
% 3.48/1.01  ------ 
% 3.48/1.01  
% 3.48/1.01  ------ Input Options
% 3.48/1.01  
% 3.48/1.01  --out_options                           all
% 3.48/1.01  --tptp_safe_out                         true
% 3.48/1.01  --problem_path                          ""
% 3.48/1.01  --include_path                          ""
% 3.48/1.01  --clausifier                            res/vclausify_rel
% 3.48/1.01  --clausifier_options                    ""
% 3.48/1.01  --stdin                                 false
% 3.48/1.01  --stats_out                             all
% 3.48/1.01  
% 3.48/1.01  ------ General Options
% 3.48/1.01  
% 3.48/1.01  --fof                                   false
% 3.48/1.01  --time_out_real                         305.
% 3.48/1.01  --time_out_virtual                      -1.
% 3.48/1.01  --symbol_type_check                     false
% 3.48/1.01  --clausify_out                          false
% 3.48/1.01  --sig_cnt_out                           false
% 3.48/1.01  --trig_cnt_out                          false
% 3.48/1.01  --trig_cnt_out_tolerance                1.
% 3.48/1.01  --trig_cnt_out_sk_spl                   false
% 3.48/1.01  --abstr_cl_out                          false
% 3.48/1.01  
% 3.48/1.01  ------ Global Options
% 3.48/1.01  
% 3.48/1.01  --schedule                              default
% 3.48/1.01  --add_important_lit                     false
% 3.48/1.01  --prop_solver_per_cl                    1000
% 3.48/1.01  --min_unsat_core                        false
% 3.48/1.01  --soft_assumptions                      false
% 3.48/1.01  --soft_lemma_size                       3
% 3.48/1.01  --prop_impl_unit_size                   0
% 3.48/1.01  --prop_impl_unit                        []
% 3.48/1.01  --share_sel_clauses                     true
% 3.48/1.01  --reset_solvers                         false
% 3.48/1.01  --bc_imp_inh                            [conj_cone]
% 3.48/1.01  --conj_cone_tolerance                   3.
% 3.48/1.01  --extra_neg_conj                        none
% 3.48/1.01  --large_theory_mode                     true
% 3.48/1.01  --prolific_symb_bound                   200
% 3.48/1.01  --lt_threshold                          2000
% 3.48/1.01  --clause_weak_htbl                      true
% 3.48/1.01  --gc_record_bc_elim                     false
% 3.48/1.01  
% 3.48/1.01  ------ Preprocessing Options
% 3.48/1.01  
% 3.48/1.01  --preprocessing_flag                    true
% 3.48/1.01  --time_out_prep_mult                    0.1
% 3.48/1.01  --splitting_mode                        input
% 3.48/1.01  --splitting_grd                         true
% 3.48/1.01  --splitting_cvd                         false
% 3.48/1.01  --splitting_cvd_svl                     false
% 3.48/1.01  --splitting_nvd                         32
% 3.48/1.01  --sub_typing                            true
% 3.48/1.01  --prep_gs_sim                           true
% 3.48/1.01  --prep_unflatten                        true
% 3.48/1.01  --prep_res_sim                          true
% 3.48/1.01  --prep_upred                            true
% 3.48/1.01  --prep_sem_filter                       exhaustive
% 3.48/1.01  --prep_sem_filter_out                   false
% 3.48/1.01  --pred_elim                             true
% 3.48/1.01  --res_sim_input                         true
% 3.48/1.01  --eq_ax_congr_red                       true
% 3.48/1.01  --pure_diseq_elim                       true
% 3.48/1.01  --brand_transform                       false
% 3.48/1.01  --non_eq_to_eq                          false
% 3.48/1.01  --prep_def_merge                        true
% 3.48/1.01  --prep_def_merge_prop_impl              false
% 3.48/1.01  --prep_def_merge_mbd                    true
% 3.48/1.01  --prep_def_merge_tr_red                 false
% 3.48/1.01  --prep_def_merge_tr_cl                  false
% 3.48/1.01  --smt_preprocessing                     true
% 3.48/1.01  --smt_ac_axioms                         fast
% 3.48/1.01  --preprocessed_out                      false
% 3.48/1.01  --preprocessed_stats                    false
% 3.48/1.01  
% 3.48/1.01  ------ Abstraction refinement Options
% 3.48/1.01  
% 3.48/1.01  --abstr_ref                             []
% 3.48/1.01  --abstr_ref_prep                        false
% 3.48/1.01  --abstr_ref_until_sat                   false
% 3.48/1.01  --abstr_ref_sig_restrict                funpre
% 3.48/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.48/1.01  --abstr_ref_under                       []
% 3.48/1.01  
% 3.48/1.01  ------ SAT Options
% 3.48/1.01  
% 3.48/1.01  --sat_mode                              false
% 3.48/1.01  --sat_fm_restart_options                ""
% 3.48/1.01  --sat_gr_def                            false
% 3.48/1.01  --sat_epr_types                         true
% 3.48/1.01  --sat_non_cyclic_types                  false
% 3.48/1.01  --sat_finite_models                     false
% 3.48/1.01  --sat_fm_lemmas                         false
% 3.48/1.01  --sat_fm_prep                           false
% 3.48/1.01  --sat_fm_uc_incr                        true
% 3.48/1.01  --sat_out_model                         small
% 3.48/1.01  --sat_out_clauses                       false
% 3.48/1.01  
% 3.48/1.01  ------ QBF Options
% 3.48/1.01  
% 3.48/1.01  --qbf_mode                              false
% 3.48/1.01  --qbf_elim_univ                         false
% 3.48/1.01  --qbf_dom_inst                          none
% 3.48/1.01  --qbf_dom_pre_inst                      false
% 3.48/1.01  --qbf_sk_in                             false
% 3.48/1.01  --qbf_pred_elim                         true
% 3.48/1.01  --qbf_split                             512
% 3.48/1.01  
% 3.48/1.01  ------ BMC1 Options
% 3.48/1.01  
% 3.48/1.01  --bmc1_incremental                      false
% 3.48/1.01  --bmc1_axioms                           reachable_all
% 3.48/1.01  --bmc1_min_bound                        0
% 3.48/1.01  --bmc1_max_bound                        -1
% 3.48/1.01  --bmc1_max_bound_default                -1
% 3.48/1.01  --bmc1_symbol_reachability              true
% 3.48/1.01  --bmc1_property_lemmas                  false
% 3.48/1.01  --bmc1_k_induction                      false
% 3.48/1.01  --bmc1_non_equiv_states                 false
% 3.48/1.01  --bmc1_deadlock                         false
% 3.48/1.01  --bmc1_ucm                              false
% 3.48/1.01  --bmc1_add_unsat_core                   none
% 3.48/1.01  --bmc1_unsat_core_children              false
% 3.48/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.48/1.01  --bmc1_out_stat                         full
% 3.48/1.01  --bmc1_ground_init                      false
% 3.48/1.01  --bmc1_pre_inst_next_state              false
% 3.48/1.01  --bmc1_pre_inst_state                   false
% 3.48/1.01  --bmc1_pre_inst_reach_state             false
% 3.48/1.01  --bmc1_out_unsat_core                   false
% 3.48/1.01  --bmc1_aig_witness_out                  false
% 3.48/1.01  --bmc1_verbose                          false
% 3.48/1.01  --bmc1_dump_clauses_tptp                false
% 3.48/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.48/1.01  --bmc1_dump_file                        -
% 3.48/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.48/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.48/1.01  --bmc1_ucm_extend_mode                  1
% 3.48/1.01  --bmc1_ucm_init_mode                    2
% 3.48/1.01  --bmc1_ucm_cone_mode                    none
% 3.48/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.48/1.01  --bmc1_ucm_relax_model                  4
% 3.48/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.48/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.48/1.01  --bmc1_ucm_layered_model                none
% 3.48/1.01  --bmc1_ucm_max_lemma_size               10
% 3.48/1.01  
% 3.48/1.01  ------ AIG Options
% 3.48/1.01  
% 3.48/1.01  --aig_mode                              false
% 3.48/1.01  
% 3.48/1.01  ------ Instantiation Options
% 3.48/1.01  
% 3.48/1.01  --instantiation_flag                    true
% 3.48/1.01  --inst_sos_flag                         true
% 3.48/1.01  --inst_sos_phase                        true
% 3.48/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.48/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.48/1.01  --inst_lit_sel_side                     num_symb
% 3.48/1.01  --inst_solver_per_active                1400
% 3.48/1.01  --inst_solver_calls_frac                1.
% 3.48/1.01  --inst_passive_queue_type               priority_queues
% 3.48/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.48/1.01  --inst_passive_queues_freq              [25;2]
% 3.48/1.01  --inst_dismatching                      true
% 3.48/1.01  --inst_eager_unprocessed_to_passive     true
% 3.48/1.01  --inst_prop_sim_given                   true
% 3.48/1.01  --inst_prop_sim_new                     false
% 3.48/1.01  --inst_subs_new                         false
% 3.48/1.01  --inst_eq_res_simp                      false
% 3.48/1.01  --inst_subs_given                       false
% 3.48/1.01  --inst_orphan_elimination               true
% 3.48/1.01  --inst_learning_loop_flag               true
% 3.48/1.01  --inst_learning_start                   3000
% 3.48/1.01  --inst_learning_factor                  2
% 3.48/1.01  --inst_start_prop_sim_after_learn       3
% 3.48/1.01  --inst_sel_renew                        solver
% 3.48/1.01  --inst_lit_activity_flag                true
% 3.48/1.01  --inst_restr_to_given                   false
% 3.48/1.01  --inst_activity_threshold               500
% 3.48/1.01  --inst_out_proof                        true
% 3.48/1.01  
% 3.48/1.01  ------ Resolution Options
% 3.48/1.01  
% 3.48/1.01  --resolution_flag                       true
% 3.48/1.01  --res_lit_sel                           adaptive
% 3.48/1.01  --res_lit_sel_side                      none
% 3.48/1.01  --res_ordering                          kbo
% 3.48/1.01  --res_to_prop_solver                    active
% 3.48/1.01  --res_prop_simpl_new                    false
% 3.48/1.01  --res_prop_simpl_given                  true
% 3.48/1.01  --res_passive_queue_type                priority_queues
% 3.48/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.48/1.01  --res_passive_queues_freq               [15;5]
% 3.48/1.01  --res_forward_subs                      full
% 3.48/1.01  --res_backward_subs                     full
% 3.48/1.01  --res_forward_subs_resolution           true
% 3.48/1.01  --res_backward_subs_resolution          true
% 3.48/1.01  --res_orphan_elimination                true
% 3.48/1.01  --res_time_limit                        2.
% 3.48/1.01  --res_out_proof                         true
% 3.48/1.01  
% 3.48/1.01  ------ Superposition Options
% 3.48/1.01  
% 3.48/1.01  --superposition_flag                    true
% 3.48/1.01  --sup_passive_queue_type                priority_queues
% 3.48/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.48/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.48/1.01  --demod_completeness_check              fast
% 3.48/1.01  --demod_use_ground                      true
% 3.48/1.01  --sup_to_prop_solver                    passive
% 3.48/1.01  --sup_prop_simpl_new                    true
% 3.48/1.01  --sup_prop_simpl_given                  true
% 3.48/1.01  --sup_fun_splitting                     true
% 3.48/1.01  --sup_smt_interval                      50000
% 3.48/1.01  
% 3.48/1.01  ------ Superposition Simplification Setup
% 3.48/1.01  
% 3.48/1.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.48/1.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.48/1.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.48/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.48/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.48/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.48/1.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.48/1.01  --sup_immed_triv                        [TrivRules]
% 3.48/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.48/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.48/1.01  --sup_immed_bw_main                     []
% 3.48/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.48/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.48/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.48/1.01  --sup_input_bw                          []
% 3.48/1.01  
% 3.48/1.01  ------ Combination Options
% 3.48/1.01  
% 3.48/1.01  --comb_res_mult                         3
% 3.48/1.01  --comb_sup_mult                         2
% 3.48/1.01  --comb_inst_mult                        10
% 3.48/1.01  
% 3.48/1.01  ------ Debug Options
% 3.48/1.01  
% 3.48/1.01  --dbg_backtrace                         false
% 3.48/1.01  --dbg_dump_prop_clauses                 false
% 3.48/1.01  --dbg_dump_prop_clauses_file            -
% 3.48/1.01  --dbg_out_stat                          false
% 3.48/1.01  ------ Parsing...
% 3.48/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.48/1.01  
% 3.48/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.48/1.01  
% 3.48/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.48/1.01  
% 3.48/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.48/1.01  ------ Proving...
% 3.48/1.01  ------ Problem Properties 
% 3.48/1.01  
% 3.48/1.01  
% 3.48/1.01  clauses                                 30
% 3.48/1.01  conjectures                             10
% 3.48/1.01  EPR                                     6
% 3.48/1.01  Horn                                    26
% 3.48/1.01  unary                                   12
% 3.48/1.01  binary                                  4
% 3.48/1.01  lits                                    73
% 3.48/1.01  lits eq                                 25
% 3.48/1.01  fd_pure                                 0
% 3.48/1.01  fd_pseudo                               0
% 3.48/1.01  fd_cond                                 4
% 3.48/1.01  fd_pseudo_cond                          0
% 3.48/1.01  AC symbols                              0
% 3.48/1.01  
% 3.48/1.01  ------ Schedule dynamic 5 is on 
% 3.48/1.01  
% 3.48/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.48/1.01  
% 3.48/1.01  
% 3.48/1.01  ------ 
% 3.48/1.01  Current options:
% 3.48/1.01  ------ 
% 3.48/1.01  
% 3.48/1.01  ------ Input Options
% 3.48/1.01  
% 3.48/1.01  --out_options                           all
% 3.48/1.01  --tptp_safe_out                         true
% 3.48/1.01  --problem_path                          ""
% 3.48/1.01  --include_path                          ""
% 3.48/1.01  --clausifier                            res/vclausify_rel
% 3.48/1.01  --clausifier_options                    ""
% 3.48/1.01  --stdin                                 false
% 3.48/1.01  --stats_out                             all
% 3.48/1.01  
% 3.48/1.01  ------ General Options
% 3.48/1.01  
% 3.48/1.01  --fof                                   false
% 3.48/1.01  --time_out_real                         305.
% 3.48/1.01  --time_out_virtual                      -1.
% 3.48/1.01  --symbol_type_check                     false
% 3.48/1.01  --clausify_out                          false
% 3.48/1.01  --sig_cnt_out                           false
% 3.48/1.01  --trig_cnt_out                          false
% 3.48/1.01  --trig_cnt_out_tolerance                1.
% 3.48/1.01  --trig_cnt_out_sk_spl                   false
% 3.48/1.01  --abstr_cl_out                          false
% 3.48/1.01  
% 3.48/1.01  ------ Global Options
% 3.48/1.01  
% 3.48/1.01  --schedule                              default
% 3.48/1.01  --add_important_lit                     false
% 3.48/1.01  --prop_solver_per_cl                    1000
% 3.48/1.01  --min_unsat_core                        false
% 3.48/1.01  --soft_assumptions                      false
% 3.48/1.01  --soft_lemma_size                       3
% 3.48/1.01  --prop_impl_unit_size                   0
% 3.48/1.01  --prop_impl_unit                        []
% 3.48/1.01  --share_sel_clauses                     true
% 3.48/1.01  --reset_solvers                         false
% 3.48/1.01  --bc_imp_inh                            [conj_cone]
% 3.48/1.01  --conj_cone_tolerance                   3.
% 3.48/1.01  --extra_neg_conj                        none
% 3.48/1.01  --large_theory_mode                     true
% 3.48/1.01  --prolific_symb_bound                   200
% 3.48/1.01  --lt_threshold                          2000
% 3.48/1.01  --clause_weak_htbl                      true
% 3.48/1.01  --gc_record_bc_elim                     false
% 3.48/1.01  
% 3.48/1.01  ------ Preprocessing Options
% 3.48/1.01  
% 3.48/1.01  --preprocessing_flag                    true
% 3.48/1.01  --time_out_prep_mult                    0.1
% 3.48/1.01  --splitting_mode                        input
% 3.48/1.01  --splitting_grd                         true
% 3.48/1.01  --splitting_cvd                         false
% 3.48/1.01  --splitting_cvd_svl                     false
% 3.48/1.01  --splitting_nvd                         32
% 3.48/1.01  --sub_typing                            true
% 3.48/1.01  --prep_gs_sim                           true
% 3.48/1.01  --prep_unflatten                        true
% 3.48/1.01  --prep_res_sim                          true
% 3.48/1.01  --prep_upred                            true
% 3.48/1.01  --prep_sem_filter                       exhaustive
% 3.48/1.01  --prep_sem_filter_out                   false
% 3.48/1.01  --pred_elim                             true
% 3.48/1.01  --res_sim_input                         true
% 3.48/1.01  --eq_ax_congr_red                       true
% 3.48/1.01  --pure_diseq_elim                       true
% 3.48/1.01  --brand_transform                       false
% 3.48/1.01  --non_eq_to_eq                          false
% 3.48/1.01  --prep_def_merge                        true
% 3.48/1.01  --prep_def_merge_prop_impl              false
% 3.48/1.01  --prep_def_merge_mbd                    true
% 3.48/1.01  --prep_def_merge_tr_red                 false
% 3.48/1.01  --prep_def_merge_tr_cl                  false
% 3.48/1.01  --smt_preprocessing                     true
% 3.48/1.01  --smt_ac_axioms                         fast
% 3.48/1.01  --preprocessed_out                      false
% 3.48/1.01  --preprocessed_stats                    false
% 3.48/1.01  
% 3.48/1.01  ------ Abstraction refinement Options
% 3.48/1.01  
% 3.48/1.01  --abstr_ref                             []
% 3.48/1.01  --abstr_ref_prep                        false
% 3.48/1.01  --abstr_ref_until_sat                   false
% 3.48/1.01  --abstr_ref_sig_restrict                funpre
% 3.48/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.48/1.01  --abstr_ref_under                       []
% 3.48/1.01  
% 3.48/1.01  ------ SAT Options
% 3.48/1.01  
% 3.48/1.01  --sat_mode                              false
% 3.48/1.01  --sat_fm_restart_options                ""
% 3.48/1.01  --sat_gr_def                            false
% 3.48/1.01  --sat_epr_types                         true
% 3.48/1.01  --sat_non_cyclic_types                  false
% 3.48/1.01  --sat_finite_models                     false
% 3.48/1.01  --sat_fm_lemmas                         false
% 3.48/1.01  --sat_fm_prep                           false
% 3.48/1.01  --sat_fm_uc_incr                        true
% 3.48/1.01  --sat_out_model                         small
% 3.48/1.01  --sat_out_clauses                       false
% 3.48/1.01  
% 3.48/1.01  ------ QBF Options
% 3.48/1.01  
% 3.48/1.01  --qbf_mode                              false
% 3.48/1.01  --qbf_elim_univ                         false
% 3.48/1.01  --qbf_dom_inst                          none
% 3.48/1.01  --qbf_dom_pre_inst                      false
% 3.48/1.01  --qbf_sk_in                             false
% 3.48/1.01  --qbf_pred_elim                         true
% 3.48/1.01  --qbf_split                             512
% 3.48/1.01  
% 3.48/1.01  ------ BMC1 Options
% 3.48/1.01  
% 3.48/1.01  --bmc1_incremental                      false
% 3.48/1.01  --bmc1_axioms                           reachable_all
% 3.48/1.01  --bmc1_min_bound                        0
% 3.48/1.01  --bmc1_max_bound                        -1
% 3.48/1.01  --bmc1_max_bound_default                -1
% 3.48/1.01  --bmc1_symbol_reachability              true
% 3.48/1.01  --bmc1_property_lemmas                  false
% 3.48/1.01  --bmc1_k_induction                      false
% 3.48/1.01  --bmc1_non_equiv_states                 false
% 3.48/1.01  --bmc1_deadlock                         false
% 3.48/1.01  --bmc1_ucm                              false
% 3.48/1.01  --bmc1_add_unsat_core                   none
% 3.48/1.01  --bmc1_unsat_core_children              false
% 3.48/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.48/1.01  --bmc1_out_stat                         full
% 3.48/1.01  --bmc1_ground_init                      false
% 3.48/1.01  --bmc1_pre_inst_next_state              false
% 3.48/1.01  --bmc1_pre_inst_state                   false
% 3.48/1.01  --bmc1_pre_inst_reach_state             false
% 3.48/1.01  --bmc1_out_unsat_core                   false
% 3.48/1.01  --bmc1_aig_witness_out                  false
% 3.48/1.01  --bmc1_verbose                          false
% 3.48/1.01  --bmc1_dump_clauses_tptp                false
% 3.48/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.48/1.01  --bmc1_dump_file                        -
% 3.48/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.48/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.48/1.01  --bmc1_ucm_extend_mode                  1
% 3.48/1.01  --bmc1_ucm_init_mode                    2
% 3.48/1.01  --bmc1_ucm_cone_mode                    none
% 3.48/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.48/1.01  --bmc1_ucm_relax_model                  4
% 3.48/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.48/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.48/1.01  --bmc1_ucm_layered_model                none
% 3.48/1.01  --bmc1_ucm_max_lemma_size               10
% 3.48/1.01  
% 3.48/1.01  ------ AIG Options
% 3.48/1.01  
% 3.48/1.01  --aig_mode                              false
% 3.48/1.01  
% 3.48/1.01  ------ Instantiation Options
% 3.48/1.01  
% 3.48/1.01  --instantiation_flag                    true
% 3.48/1.01  --inst_sos_flag                         true
% 3.48/1.01  --inst_sos_phase                        true
% 3.48/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.48/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.48/1.01  --inst_lit_sel_side                     none
% 3.48/1.01  --inst_solver_per_active                1400
% 3.48/1.01  --inst_solver_calls_frac                1.
% 3.48/1.01  --inst_passive_queue_type               priority_queues
% 3.48/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.48/1.01  --inst_passive_queues_freq              [25;2]
% 3.48/1.01  --inst_dismatching                      true
% 3.48/1.01  --inst_eager_unprocessed_to_passive     true
% 3.48/1.01  --inst_prop_sim_given                   true
% 3.48/1.01  --inst_prop_sim_new                     false
% 3.48/1.01  --inst_subs_new                         false
% 3.48/1.01  --inst_eq_res_simp                      false
% 3.48/1.01  --inst_subs_given                       false
% 3.48/1.01  --inst_orphan_elimination               true
% 3.48/1.01  --inst_learning_loop_flag               true
% 3.48/1.01  --inst_learning_start                   3000
% 3.48/1.01  --inst_learning_factor                  2
% 3.48/1.01  --inst_start_prop_sim_after_learn       3
% 3.48/1.01  --inst_sel_renew                        solver
% 3.48/1.01  --inst_lit_activity_flag                true
% 3.48/1.01  --inst_restr_to_given                   false
% 3.48/1.01  --inst_activity_threshold               500
% 3.48/1.01  --inst_out_proof                        true
% 3.48/1.01  
% 3.48/1.01  ------ Resolution Options
% 3.48/1.01  
% 3.48/1.01  --resolution_flag                       false
% 3.48/1.01  --res_lit_sel                           adaptive
% 3.48/1.01  --res_lit_sel_side                      none
% 3.48/1.01  --res_ordering                          kbo
% 3.48/1.01  --res_to_prop_solver                    active
% 3.48/1.01  --res_prop_simpl_new                    false
% 3.48/1.01  --res_prop_simpl_given                  true
% 3.48/1.01  --res_passive_queue_type                priority_queues
% 3.48/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.48/1.01  --res_passive_queues_freq               [15;5]
% 3.48/1.01  --res_forward_subs                      full
% 3.48/1.01  --res_backward_subs                     full
% 3.48/1.01  --res_forward_subs_resolution           true
% 3.48/1.01  --res_backward_subs_resolution          true
% 3.48/1.01  --res_orphan_elimination                true
% 3.48/1.01  --res_time_limit                        2.
% 3.48/1.01  --res_out_proof                         true
% 3.48/1.01  
% 3.48/1.01  ------ Superposition Options
% 3.48/1.01  
% 3.48/1.01  --superposition_flag                    true
% 3.48/1.01  --sup_passive_queue_type                priority_queues
% 3.48/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.48/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.48/1.01  --demod_completeness_check              fast
% 3.48/1.01  --demod_use_ground                      true
% 3.48/1.01  --sup_to_prop_solver                    passive
% 3.48/1.01  --sup_prop_simpl_new                    true
% 3.48/1.01  --sup_prop_simpl_given                  true
% 3.48/1.01  --sup_fun_splitting                     true
% 3.48/1.01  --sup_smt_interval                      50000
% 3.48/1.01  
% 3.48/1.01  ------ Superposition Simplification Setup
% 3.48/1.01  
% 3.48/1.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.48/1.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.48/1.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.48/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.48/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.48/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.48/1.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.48/1.01  --sup_immed_triv                        [TrivRules]
% 3.48/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.48/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.48/1.01  --sup_immed_bw_main                     []
% 3.48/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.48/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.48/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.48/1.01  --sup_input_bw                          []
% 3.48/1.01  
% 3.48/1.01  ------ Combination Options
% 3.48/1.01  
% 3.48/1.01  --comb_res_mult                         3
% 3.48/1.01  --comb_sup_mult                         2
% 3.48/1.01  --comb_inst_mult                        10
% 3.48/1.01  
% 3.48/1.01  ------ Debug Options
% 3.48/1.01  
% 3.48/1.01  --dbg_backtrace                         false
% 3.48/1.01  --dbg_dump_prop_clauses                 false
% 3.48/1.01  --dbg_dump_prop_clauses_file            -
% 3.48/1.01  --dbg_out_stat                          false
% 3.48/1.01  
% 3.48/1.01  
% 3.48/1.01  
% 3.48/1.01  
% 3.48/1.01  ------ Proving...
% 3.48/1.01  
% 3.48/1.01  
% 3.48/1.01  % SZS status Theorem for theBenchmark.p
% 3.48/1.01  
% 3.48/1.01   Resolution empty clause
% 3.48/1.01  
% 3.48/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.48/1.01  
% 3.48/1.01  fof(f14,conjecture,(
% 3.48/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 3.48/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.48/1.01  
% 3.48/1.01  fof(f15,negated_conjecture,(
% 3.48/1.01    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 3.48/1.01    inference(negated_conjecture,[],[f14])).
% 3.48/1.01  
% 3.48/1.01  fof(f35,plain,(
% 3.48/1.01    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.48/1.01    inference(ennf_transformation,[],[f15])).
% 3.48/1.01  
% 3.48/1.01  fof(f36,plain,(
% 3.48/1.01    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.48/1.01    inference(flattening,[],[f35])).
% 3.48/1.01  
% 3.48/1.01  fof(f40,plain,(
% 3.48/1.01    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 3.48/1.01    introduced(choice_axiom,[])).
% 3.48/1.01  
% 3.48/1.01  fof(f39,plain,(
% 3.48/1.01    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 3.48/1.01    introduced(choice_axiom,[])).
% 3.48/1.01  
% 3.48/1.01  fof(f41,plain,(
% 3.48/1.01    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 3.48/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f36,f40,f39])).
% 3.48/1.01  
% 3.48/1.01  fof(f66,plain,(
% 3.48/1.01    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.48/1.01    inference(cnf_transformation,[],[f41])).
% 3.48/1.01  
% 3.48/1.01  fof(f69,plain,(
% 3.48/1.01    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 3.48/1.01    inference(cnf_transformation,[],[f41])).
% 3.48/1.01  
% 3.48/1.01  fof(f11,axiom,(
% 3.48/1.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.48/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.48/1.01  
% 3.48/1.01  fof(f31,plain,(
% 3.48/1.01    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.48/1.01    inference(ennf_transformation,[],[f11])).
% 3.48/1.01  
% 3.48/1.01  fof(f32,plain,(
% 3.48/1.01    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.48/1.01    inference(flattening,[],[f31])).
% 3.48/1.01  
% 3.48/1.01  fof(f59,plain,(
% 3.48/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.48/1.01    inference(cnf_transformation,[],[f32])).
% 3.48/1.01  
% 3.48/1.01  fof(f67,plain,(
% 3.48/1.01    v1_funct_1(sK3)),
% 3.48/1.01    inference(cnf_transformation,[],[f41])).
% 3.48/1.01  
% 3.48/1.01  fof(f64,plain,(
% 3.48/1.01    v1_funct_1(sK2)),
% 3.48/1.01    inference(cnf_transformation,[],[f41])).
% 3.48/1.01  
% 3.48/1.01  fof(f8,axiom,(
% 3.48/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.48/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.48/1.01  
% 3.48/1.01  fof(f27,plain,(
% 3.48/1.01    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.48/1.01    inference(ennf_transformation,[],[f8])).
% 3.48/1.01  
% 3.48/1.01  fof(f28,plain,(
% 3.48/1.01    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.48/1.01    inference(flattening,[],[f27])).
% 3.48/1.01  
% 3.48/1.01  fof(f37,plain,(
% 3.48/1.01    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.48/1.01    inference(nnf_transformation,[],[f28])).
% 3.48/1.01  
% 3.48/1.01  fof(f50,plain,(
% 3.48/1.01    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.48/1.01    inference(cnf_transformation,[],[f37])).
% 3.48/1.01  
% 3.48/1.01  fof(f71,plain,(
% 3.48/1.01    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 3.48/1.01    inference(cnf_transformation,[],[f41])).
% 3.48/1.01  
% 3.48/1.01  fof(f10,axiom,(
% 3.48/1.01    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 3.48/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.48/1.01  
% 3.48/1.01  fof(f16,plain,(
% 3.48/1.01    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.48/1.01    inference(pure_predicate_removal,[],[f10])).
% 3.48/1.01  
% 3.48/1.01  fof(f58,plain,(
% 3.48/1.01    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.48/1.01    inference(cnf_transformation,[],[f16])).
% 3.48/1.01  
% 3.48/1.01  fof(f7,axiom,(
% 3.48/1.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5))),
% 3.48/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.48/1.01  
% 3.48/1.01  fof(f25,plain,(
% 3.48/1.01    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.48/1.01    inference(ennf_transformation,[],[f7])).
% 3.48/1.01  
% 3.48/1.01  fof(f26,plain,(
% 3.48/1.01    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.48/1.01    inference(flattening,[],[f25])).
% 3.48/1.01  
% 3.48/1.01  fof(f49,plain,(
% 3.48/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.48/1.01    inference(cnf_transformation,[],[f26])).
% 3.48/1.01  
% 3.48/1.01  fof(f5,axiom,(
% 3.48/1.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))))),
% 3.48/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.48/1.01  
% 3.48/1.01  fof(f22,plain,(
% 3.48/1.01    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.48/1.01    inference(ennf_transformation,[],[f5])).
% 3.48/1.01  
% 3.48/1.01  fof(f23,plain,(
% 3.48/1.01    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.48/1.01    inference(flattening,[],[f22])).
% 3.48/1.01  
% 3.48/1.01  fof(f47,plain,(
% 3.48/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.48/1.01    inference(cnf_transformation,[],[f23])).
% 3.48/1.01  
% 3.48/1.01  fof(f4,axiom,(
% 3.48/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 3.48/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.48/1.01  
% 3.48/1.01  fof(f20,plain,(
% 3.48/1.01    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.48/1.01    inference(ennf_transformation,[],[f4])).
% 3.48/1.01  
% 3.48/1.01  fof(f21,plain,(
% 3.48/1.01    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.48/1.01    inference(flattening,[],[f20])).
% 3.48/1.01  
% 3.48/1.01  fof(f46,plain,(
% 3.48/1.01    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.48/1.01    inference(cnf_transformation,[],[f21])).
% 3.48/1.01  
% 3.48/1.01  fof(f12,axiom,(
% 3.48/1.01    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.48/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.48/1.01  
% 3.48/1.01  fof(f60,plain,(
% 3.48/1.01    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.48/1.01    inference(cnf_transformation,[],[f12])).
% 3.48/1.01  
% 3.48/1.01  fof(f76,plain,(
% 3.48/1.01    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0)) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.48/1.01    inference(definition_unfolding,[],[f46,f60])).
% 3.48/1.01  
% 3.48/1.01  fof(f72,plain,(
% 3.48/1.01    v2_funct_1(sK2)),
% 3.48/1.01    inference(cnf_transformation,[],[f41])).
% 3.48/1.01  
% 3.48/1.01  fof(f1,axiom,(
% 3.48/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.48/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.48/1.01  
% 3.48/1.01  fof(f17,plain,(
% 3.48/1.01    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.48/1.01    inference(ennf_transformation,[],[f1])).
% 3.48/1.01  
% 3.48/1.01  fof(f42,plain,(
% 3.48/1.01    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.48/1.01    inference(cnf_transformation,[],[f17])).
% 3.48/1.01  
% 3.48/1.01  fof(f2,axiom,(
% 3.48/1.01    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.48/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.48/1.01  
% 3.48/1.01  fof(f43,plain,(
% 3.48/1.01    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.48/1.01    inference(cnf_transformation,[],[f2])).
% 3.48/1.01  
% 3.48/1.01  fof(f75,plain,(
% 3.48/1.01    k2_funct_1(sK2) != sK3),
% 3.48/1.01    inference(cnf_transformation,[],[f41])).
% 3.48/1.01  
% 3.48/1.01  fof(f70,plain,(
% 3.48/1.01    k2_relset_1(sK0,sK1,sK2) = sK1),
% 3.48/1.01    inference(cnf_transformation,[],[f41])).
% 3.48/1.01  
% 3.48/1.01  fof(f13,axiom,(
% 3.48/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.48/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.48/1.01  
% 3.48/1.01  fof(f33,plain,(
% 3.48/1.01    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.48/1.01    inference(ennf_transformation,[],[f13])).
% 3.48/1.01  
% 3.48/1.01  fof(f34,plain,(
% 3.48/1.01    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.48/1.01    inference(flattening,[],[f33])).
% 3.48/1.01  
% 3.48/1.01  fof(f63,plain,(
% 3.48/1.01    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.48/1.01    inference(cnf_transformation,[],[f34])).
% 3.48/1.01  
% 3.48/1.01  fof(f65,plain,(
% 3.48/1.01    v1_funct_2(sK2,sK0,sK1)),
% 3.48/1.01    inference(cnf_transformation,[],[f41])).
% 3.48/1.01  
% 3.48/1.01  fof(f9,axiom,(
% 3.48/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.48/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.48/1.01  
% 3.48/1.01  fof(f29,plain,(
% 3.48/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.48/1.01    inference(ennf_transformation,[],[f9])).
% 3.48/1.01  
% 3.48/1.01  fof(f30,plain,(
% 3.48/1.01    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.48/1.01    inference(flattening,[],[f29])).
% 3.48/1.01  
% 3.48/1.01  fof(f38,plain,(
% 3.48/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.48/1.01    inference(nnf_transformation,[],[f30])).
% 3.48/1.01  
% 3.48/1.01  fof(f52,plain,(
% 3.48/1.01    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.48/1.01    inference(cnf_transformation,[],[f38])).
% 3.48/1.01  
% 3.48/1.01  fof(f6,axiom,(
% 3.48/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.48/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.48/1.01  
% 3.48/1.01  fof(f24,plain,(
% 3.48/1.01    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.48/1.01    inference(ennf_transformation,[],[f6])).
% 3.48/1.01  
% 3.48/1.01  fof(f48,plain,(
% 3.48/1.01    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.48/1.01    inference(cnf_transformation,[],[f24])).
% 3.48/1.01  
% 3.48/1.01  fof(f3,axiom,(
% 3.48/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 3.48/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.48/1.01  
% 3.48/1.01  fof(f18,plain,(
% 3.48/1.01    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.48/1.01    inference(ennf_transformation,[],[f3])).
% 3.48/1.01  
% 3.48/1.01  fof(f19,plain,(
% 3.48/1.01    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.48/1.01    inference(flattening,[],[f18])).
% 3.48/1.01  
% 3.48/1.01  fof(f44,plain,(
% 3.48/1.01    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.48/1.01    inference(cnf_transformation,[],[f19])).
% 3.48/1.01  
% 3.48/1.01  fof(f73,plain,(
% 3.48/1.01    k1_xboole_0 != sK0),
% 3.48/1.01    inference(cnf_transformation,[],[f41])).
% 3.48/1.01  
% 3.48/1.01  fof(f62,plain,(
% 3.48/1.01    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.48/1.01    inference(cnf_transformation,[],[f34])).
% 3.48/1.01  
% 3.48/1.01  fof(f74,plain,(
% 3.48/1.01    k1_xboole_0 != sK1),
% 3.48/1.01    inference(cnf_transformation,[],[f41])).
% 3.48/1.01  
% 3.48/1.01  fof(f68,plain,(
% 3.48/1.01    v1_funct_2(sK3,sK1,sK0)),
% 3.48/1.01    inference(cnf_transformation,[],[f41])).
% 3.48/1.01  
% 3.48/1.01  cnf(c_30,negated_conjecture,
% 3.48/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.48/1.01      inference(cnf_transformation,[],[f66]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_1127,plain,
% 3.48/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.48/1.01      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_27,negated_conjecture,
% 3.48/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 3.48/1.01      inference(cnf_transformation,[],[f69]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_1130,plain,
% 3.48/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.48/1.01      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_17,plain,
% 3.48/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.48/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.48/1.01      | ~ v1_funct_1(X0)
% 3.48/1.01      | ~ v1_funct_1(X3)
% 3.48/1.01      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.48/1.01      inference(cnf_transformation,[],[f59]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_1131,plain,
% 3.48/1.01      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 3.48/1.01      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 3.48/1.01      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.48/1.01      | v1_funct_1(X5) != iProver_top
% 3.48/1.01      | v1_funct_1(X4) != iProver_top ),
% 3.48/1.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_1967,plain,
% 3.48/1.01      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 3.48/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.48/1.01      | v1_funct_1(X2) != iProver_top
% 3.48/1.01      | v1_funct_1(sK3) != iProver_top ),
% 3.48/1.01      inference(superposition,[status(thm)],[c_1130,c_1131]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_29,negated_conjecture,
% 3.48/1.01      ( v1_funct_1(sK3) ),
% 3.48/1.01      inference(cnf_transformation,[],[f67]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_36,plain,
% 3.48/1.01      ( v1_funct_1(sK3) = iProver_top ),
% 3.48/1.01      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_2466,plain,
% 3.48/1.01      ( v1_funct_1(X2) != iProver_top
% 3.48/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.48/1.01      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 3.48/1.01      inference(global_propositional_subsumption,[status(thm)],[c_1967,c_36]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_2467,plain,
% 3.48/1.01      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 3.48/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.48/1.01      | v1_funct_1(X2) != iProver_top ),
% 3.48/1.01      inference(renaming,[status(thm)],[c_2466]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_2474,plain,
% 3.48/1.01      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 3.48/1.01      | v1_funct_1(sK2) != iProver_top ),
% 3.48/1.01      inference(superposition,[status(thm)],[c_1127,c_2467]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_32,negated_conjecture,
% 3.48/1.01      ( v1_funct_1(sK2) ),
% 3.48/1.01      inference(cnf_transformation,[],[f64]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_33,plain,
% 3.48/1.01      ( v1_funct_1(sK2) = iProver_top ),
% 3.48/1.01      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_2946,plain,
% 3.48/1.01      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 3.48/1.01      inference(global_propositional_subsumption,[status(thm)],[c_2474,c_33]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_9,plain,
% 3.48/1.01      ( ~ r2_relset_1(X0,X1,X2,X3)
% 3.48/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.48/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.48/1.01      | X3 = X2 ),
% 3.48/1.01      inference(cnf_transformation,[],[f50]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_25,negated_conjecture,
% 3.48/1.01      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 3.48/1.01      inference(cnf_transformation,[],[f71]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_327,plain,
% 3.48/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.48/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.48/1.01      | X3 = X0
% 3.48/1.01      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 3.48/1.01      | k6_partfun1(sK0) != X3
% 3.48/1.01      | sK0 != X2
% 3.48/1.01      | sK0 != X1 ),
% 3.48/1.01      inference(resolution_lifted,[status(thm)],[c_9,c_25]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_328,plain,
% 3.48/1.01      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.48/1.01      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.48/1.01      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.48/1.01      inference(unflattening,[status(thm)],[c_327]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_16,plain,
% 3.48/1.01      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.48/1.01      inference(cnf_transformation,[],[f58]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_336,plain,
% 3.48/1.01      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.48/1.01      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.48/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_328,c_16]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_1124,plain,
% 3.48/1.01      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.48/1.01      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.48/1.01      inference(predicate_to_equality,[status(thm)],[c_336]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_2948,plain,
% 3.48/1.01      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 3.48/1.01      | m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.48/1.01      inference(demodulation,[status(thm)],[c_2946,c_1124]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_35,plain,
% 3.48/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.48/1.01      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_38,plain,
% 3.48/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.48/1.01      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_7,plain,
% 3.48/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.48/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.48/1.01      | k4_relset_1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.48/1.01      inference(cnf_transformation,[],[f49]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_1139,plain,
% 3.48/1.01      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 3.48/1.01      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 3.48/1.01      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.48/1.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_2930,plain,
% 3.48/1.01      ( k4_relset_1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 3.48/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.48/1.01      inference(superposition,[status(thm)],[c_1130,c_1139]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_3053,plain,
% 3.48/1.01      ( k4_relset_1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 3.48/1.01      inference(superposition,[status(thm)],[c_1127,c_2930]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_5,plain,
% 3.48/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.48/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.48/1.01      | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) ),
% 3.48/1.01      inference(cnf_transformation,[],[f47]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_1141,plain,
% 3.48/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.48/1.01      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 3.48/1.01      | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top ),
% 3.48/1.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_3371,plain,
% 3.48/1.01      ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 3.48/1.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.48/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 3.48/1.01      inference(superposition,[status(thm)],[c_3053,c_1141]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_6542,plain,
% 3.48/1.01      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 3.48/1.01      inference(global_propositional_subsumption,
% 3.48/1.01                [status(thm)],
% 3.48/1.01                [c_2948,c_35,c_38,c_3371]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_4,plain,
% 3.48/1.01      ( ~ v1_funct_1(X0)
% 3.48/1.01      | ~ v1_funct_1(X1)
% 3.48/1.01      | ~ v2_funct_1(X0)
% 3.48/1.01      | ~ v1_relat_1(X0)
% 3.48/1.01      | ~ v1_relat_1(X1)
% 3.48/1.01      | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
% 3.48/1.01      | k1_relat_1(X1) != k2_relat_1(X0)
% 3.48/1.01      | k2_funct_1(X0) = X1 ),
% 3.48/1.01      inference(cnf_transformation,[],[f76]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_24,negated_conjecture,
% 3.48/1.01      ( v2_funct_1(sK2) ),
% 3.48/1.01      inference(cnf_transformation,[],[f72]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_415,plain,
% 3.48/1.01      ( ~ v1_funct_1(X0)
% 3.48/1.01      | ~ v1_funct_1(X1)
% 3.48/1.01      | ~ v1_relat_1(X0)
% 3.48/1.01      | ~ v1_relat_1(X1)
% 3.48/1.01      | k5_relat_1(X1,X0) != k6_partfun1(k1_relat_1(X1))
% 3.48/1.01      | k1_relat_1(X0) != k2_relat_1(X1)
% 3.48/1.01      | k2_funct_1(X1) = X0
% 3.48/1.01      | sK2 != X1 ),
% 3.48/1.01      inference(resolution_lifted,[status(thm)],[c_4,c_24]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_416,plain,
% 3.48/1.01      ( ~ v1_funct_1(X0)
% 3.48/1.01      | ~ v1_funct_1(sK2)
% 3.48/1.01      | ~ v1_relat_1(X0)
% 3.48/1.01      | ~ v1_relat_1(sK2)
% 3.48/1.01      | k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
% 3.48/1.01      | k1_relat_1(X0) != k2_relat_1(sK2)
% 3.48/1.01      | k2_funct_1(sK2) = X0 ),
% 3.48/1.01      inference(unflattening,[status(thm)],[c_415]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_420,plain,
% 3.48/1.01      ( ~ v1_funct_1(X0)
% 3.48/1.01      | ~ v1_relat_1(X0)
% 3.48/1.01      | ~ v1_relat_1(sK2)
% 3.48/1.01      | k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
% 3.48/1.01      | k1_relat_1(X0) != k2_relat_1(sK2)
% 3.48/1.01      | k2_funct_1(sK2) = X0 ),
% 3.48/1.01      inference(global_propositional_subsumption,[status(thm)],[c_416,c_32]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_1120,plain,
% 3.48/1.01      ( k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
% 3.48/1.01      | k1_relat_1(X0) != k2_relat_1(sK2)
% 3.48/1.01      | k2_funct_1(sK2) = X0
% 3.48/1.01      | v1_funct_1(X0) != iProver_top
% 3.48/1.01      | v1_relat_1(X0) != iProver_top
% 3.48/1.01      | v1_relat_1(sK2) != iProver_top ),
% 3.48/1.01      inference(predicate_to_equality,[status(thm)],[c_420]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_417,plain,
% 3.48/1.01      ( k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
% 3.48/1.01      | k1_relat_1(X0) != k2_relat_1(sK2)
% 3.48/1.01      | k2_funct_1(sK2) = X0
% 3.48/1.01      | v1_funct_1(X0) != iProver_top
% 3.48/1.01      | v1_funct_1(sK2) != iProver_top
% 3.48/1.01      | v1_relat_1(X0) != iProver_top
% 3.48/1.01      | v1_relat_1(sK2) != iProver_top ),
% 3.48/1.01      inference(predicate_to_equality,[status(thm)],[c_416]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_0,plain,
% 3.48/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.48/1.01      inference(cnf_transformation,[],[f42]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_1226,plain,
% 3.48/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
% 3.48/1.01      | ~ v1_relat_1(X0)
% 3.48/1.01      | v1_relat_1(sK2) ),
% 3.48/1.01      inference(instantiation,[status(thm)],[c_0]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_1373,plain,
% 3.48/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.48/1.01      | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
% 3.48/1.01      | v1_relat_1(sK2) ),
% 3.48/1.01      inference(instantiation,[status(thm)],[c_1226]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_1602,plain,
% 3.48/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.48/1.01      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
% 3.48/1.01      | v1_relat_1(sK2) ),
% 3.48/1.01      inference(instantiation,[status(thm)],[c_1373]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_1603,plain,
% 3.48/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.48/1.01      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 3.48/1.01      | v1_relat_1(sK2) = iProver_top ),
% 3.48/1.01      inference(predicate_to_equality,[status(thm)],[c_1602]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_1,plain,
% 3.48/1.01      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.48/1.01      inference(cnf_transformation,[],[f43]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_1662,plain,
% 3.48/1.01      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 3.48/1.01      inference(instantiation,[status(thm)],[c_1]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_1663,plain,
% 3.48/1.01      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 3.48/1.01      inference(predicate_to_equality,[status(thm)],[c_1662]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_1814,plain,
% 3.48/1.01      ( v1_relat_1(X0) != iProver_top
% 3.48/1.01      | v1_funct_1(X0) != iProver_top
% 3.48/1.01      | k2_funct_1(sK2) = X0
% 3.48/1.01      | k1_relat_1(X0) != k2_relat_1(sK2)
% 3.48/1.01      | k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2)) ),
% 3.48/1.01      inference(global_propositional_subsumption,
% 3.48/1.01                [status(thm)],
% 3.48/1.01                [c_1120,c_33,c_35,c_417,c_1603,c_1663]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_1815,plain,
% 3.48/1.01      ( k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
% 3.48/1.01      | k1_relat_1(X0) != k2_relat_1(sK2)
% 3.48/1.01      | k2_funct_1(sK2) = X0
% 3.48/1.01      | v1_funct_1(X0) != iProver_top
% 3.48/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.48/1.01      inference(renaming,[status(thm)],[c_1814]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_6546,plain,
% 3.48/1.01      ( k6_partfun1(k1_relat_1(sK2)) != k6_partfun1(sK0)
% 3.48/1.01      | k1_relat_1(sK3) != k2_relat_1(sK2)
% 3.48/1.01      | k2_funct_1(sK2) = sK3
% 3.48/1.01      | v1_funct_1(sK3) != iProver_top
% 3.48/1.01      | v1_relat_1(sK3) != iProver_top ),
% 3.48/1.01      inference(superposition,[status(thm)],[c_6542,c_1815]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_21,negated_conjecture,
% 3.48/1.01      ( k2_funct_1(sK2) != sK3 ),
% 3.48/1.01      inference(cnf_transformation,[],[f75]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_1142,plain,
% 3.48/1.01      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.48/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_1143,plain,
% 3.48/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.48/1.01      | v1_relat_1(X1) != iProver_top
% 3.48/1.01      | v1_relat_1(X0) = iProver_top ),
% 3.48/1.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_2035,plain,
% 3.48/1.01      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 3.48/1.01      | v1_relat_1(sK3) = iProver_top ),
% 3.48/1.01      inference(superposition,[status(thm)],[c_1130,c_1143]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_2309,plain,
% 3.48/1.01      ( v1_relat_1(sK3) = iProver_top ),
% 3.48/1.01      inference(superposition,[status(thm)],[c_1142,c_2035]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_13852,plain,
% 3.48/1.01      ( k1_relat_1(sK3) != k2_relat_1(sK2)
% 3.48/1.01      | k6_partfun1(k1_relat_1(sK2)) != k6_partfun1(sK0) ),
% 3.48/1.01      inference(global_propositional_subsumption,
% 3.48/1.01                [status(thm)],
% 3.48/1.01                [c_6546,c_36,c_21,c_2309]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_13853,plain,
% 3.48/1.01      ( k6_partfun1(k1_relat_1(sK2)) != k6_partfun1(sK0)
% 3.48/1.01      | k1_relat_1(sK3) != k2_relat_1(sK2) ),
% 3.48/1.01      inference(renaming,[status(thm)],[c_13852]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_26,negated_conjecture,
% 3.48/1.01      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 3.48/1.01      inference(cnf_transformation,[],[f70]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_18,plain,
% 3.48/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 3.48/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.48/1.01      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.48/1.01      | ~ v1_funct_1(X0)
% 3.48/1.01      | ~ v2_funct_1(X0)
% 3.48/1.01      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.48/1.01      inference(cnf_transformation,[],[f63]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_391,plain,
% 3.48/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 3.48/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.48/1.01      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.48/1.01      | ~ v1_funct_1(X0)
% 3.48/1.01      | k2_relset_1(X1,X2,X0) != X2
% 3.48/1.01      | sK2 != X0 ),
% 3.48/1.01      inference(resolution_lifted,[status(thm)],[c_18,c_24]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_392,plain,
% 3.48/1.01      ( ~ v1_funct_2(sK2,X0,X1)
% 3.48/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.48/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.48/1.01      | ~ v1_funct_1(sK2)
% 3.48/1.01      | k2_relset_1(X0,X1,sK2) != X1 ),
% 3.48/1.01      inference(unflattening,[status(thm)],[c_391]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_396,plain,
% 3.48/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.48/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.48/1.01      | ~ v1_funct_2(sK2,X0,X1)
% 3.48/1.01      | k2_relset_1(X0,X1,sK2) != X1 ),
% 3.48/1.01      inference(global_propositional_subsumption,[status(thm)],[c_392,c_32]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_397,plain,
% 3.48/1.01      ( ~ v1_funct_2(sK2,X0,X1)
% 3.48/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.48/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.48/1.01      | k2_relset_1(X0,X1,sK2) != X1 ),
% 3.48/1.01      inference(renaming,[status(thm)],[c_396]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_1121,plain,
% 3.48/1.01      ( k2_relset_1(X0,X1,sK2) != X1
% 3.48/1.01      | v1_funct_2(sK2,X0,X1) != iProver_top
% 3.48/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
% 3.48/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.48/1.01      inference(predicate_to_equality,[status(thm)],[c_397]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_1780,plain,
% 3.48/1.01      ( v1_funct_2(sK2,sK0,sK1) != iProver_top
% 3.48/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
% 3.48/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 3.48/1.01      inference(superposition,[status(thm)],[c_26,c_1121]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_31,negated_conjecture,
% 3.48/1.01      ( v1_funct_2(sK2,sK0,sK1) ),
% 3.48/1.01      inference(cnf_transformation,[],[f65]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_34,plain,
% 3.48/1.01      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 3.48/1.01      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_1253,plain,
% 3.48/1.01      ( ~ v1_funct_2(sK2,sK0,sK1)
% 3.48/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.48/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.48/1.01      | k2_relset_1(sK0,sK1,sK2) != sK1 ),
% 3.48/1.01      inference(instantiation,[status(thm)],[c_397]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_1254,plain,
% 3.48/1.01      ( k2_relset_1(sK0,sK1,sK2) != sK1
% 3.48/1.01      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 3.48/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
% 3.48/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 3.48/1.01      inference(predicate_to_equality,[status(thm)],[c_1253]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_1809,plain,
% 3.48/1.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.48/1.01      inference(global_propositional_subsumption,
% 3.48/1.01                [status(thm)],
% 3.48/1.01                [c_1780,c_34,c_35,c_26,c_1254]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_15,plain,
% 3.48/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 3.48/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.48/1.01      | k1_relset_1(X1,X2,X0) = X1
% 3.48/1.01      | k1_xboole_0 = X2 ),
% 3.48/1.01      inference(cnf_transformation,[],[f52]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_1133,plain,
% 3.48/1.01      ( k1_relset_1(X0,X1,X2) = X0
% 3.48/1.01      | k1_xboole_0 = X1
% 3.48/1.01      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.48/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.48/1.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_2597,plain,
% 3.48/1.01      ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) = sK1
% 3.48/1.01      | sK0 = k1_xboole_0
% 3.48/1.01      | v1_funct_2(k2_funct_1(sK2),sK1,sK0) != iProver_top ),
% 3.48/1.01      inference(superposition,[status(thm)],[c_1809,c_1133]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_6,plain,
% 3.48/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.48/1.01      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.48/1.01      inference(cnf_transformation,[],[f48]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_1140,plain,
% 3.48/1.01      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.48/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.48/1.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_2031,plain,
% 3.48/1.01      ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
% 3.48/1.01      inference(superposition,[status(thm)],[c_1809,c_1140]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_2036,plain,
% 3.48/1.01      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 3.48/1.01      | v1_relat_1(sK2) = iProver_top ),
% 3.48/1.01      inference(superposition,[status(thm)],[c_1127,c_1143]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_2376,plain,
% 3.48/1.01      ( v1_relat_1(sK2) = iProver_top ),
% 3.48/1.01      inference(global_propositional_subsumption,
% 3.48/1.01                [status(thm)],
% 3.48/1.01                [c_2036,c_35,c_1603,c_1663]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_3,plain,
% 3.48/1.01      ( ~ v1_funct_1(X0)
% 3.48/1.01      | ~ v2_funct_1(X0)
% 3.48/1.01      | ~ v1_relat_1(X0)
% 3.48/1.01      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 3.48/1.01      inference(cnf_transformation,[],[f44]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_445,plain,
% 3.48/1.01      ( ~ v1_funct_1(X0)
% 3.48/1.01      | ~ v1_relat_1(X0)
% 3.48/1.01      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 3.48/1.01      | sK2 != X0 ),
% 3.48/1.01      inference(resolution_lifted,[status(thm)],[c_3,c_24]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_446,plain,
% 3.48/1.01      ( ~ v1_funct_1(sK2)
% 3.48/1.01      | ~ v1_relat_1(sK2)
% 3.48/1.01      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 3.48/1.01      inference(unflattening,[status(thm)],[c_445]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_448,plain,
% 3.48/1.01      ( ~ v1_relat_1(sK2) | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 3.48/1.01      inference(global_propositional_subsumption,[status(thm)],[c_446,c_32]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_1119,plain,
% 3.48/1.01      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 3.48/1.01      | v1_relat_1(sK2) != iProver_top ),
% 3.48/1.01      inference(predicate_to_equality,[status(thm)],[c_448]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_2380,plain,
% 3.48/1.01      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 3.48/1.01      inference(superposition,[status(thm)],[c_2376,c_1119]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_2598,plain,
% 3.48/1.01      ( k2_relat_1(sK2) = sK1
% 3.48/1.01      | sK0 = k1_xboole_0
% 3.48/1.01      | v1_funct_2(k2_funct_1(sK2),sK1,sK0) != iProver_top ),
% 3.48/1.01      inference(demodulation,[status(thm)],[c_2597,c_2031,c_2380]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_23,negated_conjecture,
% 3.48/1.01      ( k1_xboole_0 != sK0 ),
% 3.48/1.01      inference(cnf_transformation,[],[f73]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_679,plain,( X0 = X0 ),theory(equality) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_710,plain,
% 3.48/1.01      ( k1_xboole_0 = k1_xboole_0 ),
% 3.48/1.01      inference(instantiation,[status(thm)],[c_679]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_680,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_1219,plain,
% 3.48/1.01      ( sK0 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK0 ),
% 3.48/1.01      inference(instantiation,[status(thm)],[c_680]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_1220,plain,
% 3.48/1.01      ( sK0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 != k1_xboole_0 ),
% 3.48/1.01      inference(instantiation,[status(thm)],[c_1219]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_19,plain,
% 3.48/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 3.48/1.01      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 3.48/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.48/1.01      | ~ v1_funct_1(X0)
% 3.48/1.01      | ~ v2_funct_1(X0)
% 3.48/1.01      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.48/1.01      inference(cnf_transformation,[],[f62]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_367,plain,
% 3.48/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 3.48/1.01      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 3.48/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.48/1.01      | ~ v1_funct_1(X0)
% 3.48/1.01      | k2_relset_1(X1,X2,X0) != X2
% 3.48/1.01      | sK2 != X0 ),
% 3.48/1.01      inference(resolution_lifted,[status(thm)],[c_19,c_24]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_368,plain,
% 3.48/1.01      ( v1_funct_2(k2_funct_1(sK2),X0,X1)
% 3.48/1.01      | ~ v1_funct_2(sK2,X1,X0)
% 3.48/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.48/1.01      | ~ v1_funct_1(sK2)
% 3.48/1.01      | k2_relset_1(X1,X0,sK2) != X0 ),
% 3.48/1.01      inference(unflattening,[status(thm)],[c_367]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_372,plain,
% 3.48/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.48/1.01      | ~ v1_funct_2(sK2,X1,X0)
% 3.48/1.01      | v1_funct_2(k2_funct_1(sK2),X0,X1)
% 3.48/1.01      | k2_relset_1(X1,X0,sK2) != X0 ),
% 3.48/1.01      inference(global_propositional_subsumption,[status(thm)],[c_368,c_32]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_373,plain,
% 3.48/1.01      ( v1_funct_2(k2_funct_1(sK2),X0,X1)
% 3.48/1.01      | ~ v1_funct_2(sK2,X1,X0)
% 3.48/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.48/1.01      | k2_relset_1(X1,X0,sK2) != X0 ),
% 3.48/1.01      inference(renaming,[status(thm)],[c_372]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_1246,plain,
% 3.48/1.01      ( v1_funct_2(k2_funct_1(sK2),sK1,sK0)
% 3.48/1.01      | ~ v1_funct_2(sK2,sK0,sK1)
% 3.48/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.48/1.01      | k2_relset_1(sK0,sK1,sK2) != sK1 ),
% 3.48/1.01      inference(instantiation,[status(thm)],[c_373]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_1247,plain,
% 3.48/1.01      ( k2_relset_1(sK0,sK1,sK2) != sK1
% 3.48/1.01      | v1_funct_2(k2_funct_1(sK2),sK1,sK0) = iProver_top
% 3.48/1.01      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 3.48/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 3.48/1.01      inference(predicate_to_equality,[status(thm)],[c_1246]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_6742,plain,
% 3.48/1.01      ( k2_relat_1(sK2) = sK1 ),
% 3.48/1.01      inference(global_propositional_subsumption,
% 3.48/1.01                [status(thm)],
% 3.48/1.01                [c_2598,c_34,c_35,c_26,c_23,c_710,c_1220,c_1247]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_2596,plain,
% 3.48/1.01      ( k1_relset_1(sK0,sK1,sK2) = sK0
% 3.48/1.01      | sK1 = k1_xboole_0
% 3.48/1.01      | v1_funct_2(sK2,sK0,sK1) != iProver_top ),
% 3.48/1.01      inference(superposition,[status(thm)],[c_1127,c_1133]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_2030,plain,
% 3.48/1.01      ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
% 3.48/1.01      inference(superposition,[status(thm)],[c_1127,c_1140]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_2599,plain,
% 3.48/1.01      ( k1_relat_1(sK2) = sK0
% 3.48/1.01      | sK1 = k1_xboole_0
% 3.48/1.01      | v1_funct_2(sK2,sK0,sK1) != iProver_top ),
% 3.48/1.01      inference(demodulation,[status(thm)],[c_2596,c_2030]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_22,negated_conjecture,
% 3.48/1.01      ( k1_xboole_0 != sK1 ),
% 3.48/1.01      inference(cnf_transformation,[],[f74]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_1201,plain,
% 3.48/1.01      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 3.48/1.01      inference(instantiation,[status(thm)],[c_680]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_1202,plain,
% 3.48/1.01      ( sK1 != k1_xboole_0 | k1_xboole_0 = sK1 | k1_xboole_0 != k1_xboole_0 ),
% 3.48/1.01      inference(instantiation,[status(thm)],[c_1201]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_7812,plain,
% 3.48/1.01      ( k1_relat_1(sK2) = sK0 ),
% 3.48/1.01      inference(global_propositional_subsumption,
% 3.48/1.01                [status(thm)],
% 3.48/1.01                [c_2599,c_34,c_22,c_710,c_1202]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_2595,plain,
% 3.48/1.01      ( k1_relset_1(sK1,sK0,sK3) = sK1
% 3.48/1.01      | sK0 = k1_xboole_0
% 3.48/1.01      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 3.48/1.01      inference(superposition,[status(thm)],[c_1130,c_1133]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_2029,plain,
% 3.48/1.01      ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
% 3.48/1.01      inference(superposition,[status(thm)],[c_1130,c_1140]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_2600,plain,
% 3.48/1.01      ( k1_relat_1(sK3) = sK1
% 3.48/1.01      | sK0 = k1_xboole_0
% 3.48/1.01      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 3.48/1.01      inference(demodulation,[status(thm)],[c_2595,c_2029]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_28,negated_conjecture,
% 3.48/1.01      ( v1_funct_2(sK3,sK1,sK0) ),
% 3.48/1.01      inference(cnf_transformation,[],[f68]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_37,plain,
% 3.48/1.01      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 3.48/1.01      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_8852,plain,
% 3.48/1.01      ( k1_relat_1(sK3) = sK1 ),
% 3.48/1.01      inference(global_propositional_subsumption,
% 3.48/1.01                [status(thm)],
% 3.48/1.01                [c_2600,c_37,c_23,c_710,c_1220]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_13854,plain,
% 3.48/1.01      ( k6_partfun1(sK0) != k6_partfun1(sK0) | sK1 != sK1 ),
% 3.48/1.01      inference(light_normalisation,
% 3.48/1.01                [status(thm)],
% 3.48/1.01                [c_13853,c_6742,c_7812,c_8852]) ).
% 3.48/1.01  
% 3.48/1.01  cnf(c_13855,plain,
% 3.48/1.01      ( $false ),
% 3.48/1.01      inference(equality_resolution_simp,[status(thm)],[c_13854]) ).
% 3.48/1.01  
% 3.48/1.01  
% 3.48/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.48/1.01  
% 3.48/1.01  ------                               Statistics
% 3.48/1.01  
% 3.48/1.01  ------ General
% 3.48/1.01  
% 3.48/1.01  abstr_ref_over_cycles:                  0
% 3.48/1.01  abstr_ref_under_cycles:                 0
% 3.48/1.01  gc_basic_clause_elim:                   0
% 3.48/1.01  forced_gc_time:                         0
% 3.48/1.01  parsing_time:                           0.02
% 3.48/1.01  unif_index_cands_time:                  0.
% 3.48/1.01  unif_index_add_time:                    0.
% 3.48/1.01  orderings_time:                         0.
% 3.48/1.01  out_proof_time:                         0.015
% 3.48/1.01  total_time:                             0.436
% 3.48/1.01  num_of_symbols:                         53
% 3.48/1.01  num_of_terms:                           16181
% 3.48/1.01  
% 3.48/1.01  ------ Preprocessing
% 3.48/1.01  
% 3.48/1.01  num_of_splits:                          0
% 3.48/1.01  num_of_split_atoms:                     0
% 3.48/1.01  num_of_reused_defs:                     0
% 3.48/1.01  num_eq_ax_congr_red:                    28
% 3.48/1.01  num_of_sem_filtered_clauses:            1
% 3.48/1.01  num_of_subtypes:                        0
% 3.48/1.01  monotx_restored_types:                  0
% 3.48/1.01  sat_num_of_epr_types:                   0
% 3.48/1.01  sat_num_of_non_cyclic_types:            0
% 3.48/1.01  sat_guarded_non_collapsed_types:        0
% 3.48/1.01  num_pure_diseq_elim:                    0
% 3.48/1.01  simp_replaced_by:                       0
% 3.48/1.01  res_preprocessed:                       156
% 3.48/1.01  prep_upred:                             0
% 3.48/1.01  prep_unflattend:                        14
% 3.48/1.01  smt_new_axioms:                         0
% 3.48/1.01  pred_elim_cands:                        4
% 3.48/1.01  pred_elim:                              2
% 3.48/1.01  pred_elim_cl:                           3
% 3.48/1.01  pred_elim_cycles:                       4
% 3.48/1.01  merged_defs:                            0
% 3.48/1.01  merged_defs_ncl:                        0
% 3.48/1.01  bin_hyper_res:                          0
% 3.48/1.01  prep_cycles:                            4
% 3.48/1.01  pred_elim_time:                         0.003
% 3.48/1.01  splitting_time:                         0.
% 3.48/1.01  sem_filter_time:                        0.
% 3.48/1.01  monotx_time:                            0.
% 3.48/1.01  subtype_inf_time:                       0.
% 3.48/1.01  
% 3.48/1.01  ------ Problem properties
% 3.48/1.01  
% 3.48/1.01  clauses:                                30
% 3.48/1.01  conjectures:                            10
% 3.48/1.01  epr:                                    6
% 3.48/1.01  horn:                                   26
% 3.48/1.01  ground:                                 13
% 3.48/1.01  unary:                                  12
% 3.48/1.01  binary:                                 4
% 3.48/1.01  lits:                                   73
% 3.48/1.01  lits_eq:                                25
% 3.48/1.01  fd_pure:                                0
% 3.48/1.01  fd_pseudo:                              0
% 3.48/1.01  fd_cond:                                4
% 3.48/1.01  fd_pseudo_cond:                         0
% 3.48/1.01  ac_symbols:                             0
% 3.48/1.01  
% 3.48/1.01  ------ Propositional Solver
% 3.48/1.01  
% 3.48/1.01  prop_solver_calls:                      32
% 3.48/1.01  prop_fast_solver_calls:                 1205
% 3.48/1.01  smt_solver_calls:                       0
% 3.48/1.01  smt_fast_solver_calls:                  0
% 3.48/1.01  prop_num_of_clauses:                    5946
% 3.48/1.01  prop_preprocess_simplified:             12431
% 3.48/1.01  prop_fo_subsumed:                       52
% 3.48/1.01  prop_solver_time:                       0.
% 3.48/1.01  smt_solver_time:                        0.
% 3.48/1.01  smt_fast_solver_time:                   0.
% 3.48/1.01  prop_fast_solver_time:                  0.
% 3.48/1.01  prop_unsat_core_time:                   0.
% 3.48/1.01  
% 3.48/1.01  ------ QBF
% 3.48/1.01  
% 3.48/1.01  qbf_q_res:                              0
% 3.48/1.01  qbf_num_tautologies:                    0
% 3.48/1.01  qbf_prep_cycles:                        0
% 3.48/1.01  
% 3.48/1.01  ------ BMC1
% 3.48/1.01  
% 3.48/1.01  bmc1_current_bound:                     -1
% 3.48/1.01  bmc1_last_solved_bound:                 -1
% 3.48/1.01  bmc1_unsat_core_size:                   -1
% 3.48/1.01  bmc1_unsat_core_parents_size:           -1
% 3.48/1.01  bmc1_merge_next_fun:                    0
% 3.48/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.48/1.01  
% 3.48/1.01  ------ Instantiation
% 3.48/1.01  
% 3.48/1.01  inst_num_of_clauses:                    2137
% 3.48/1.01  inst_num_in_passive:                    560
% 3.48/1.01  inst_num_in_active:                     764
% 3.48/1.01  inst_num_in_unprocessed:                813
% 3.48/1.01  inst_num_of_loops:                      790
% 3.48/1.01  inst_num_of_learning_restarts:          0
% 3.48/1.01  inst_num_moves_active_passive:          23
% 3.48/1.01  inst_lit_activity:                      0
% 3.48/1.01  inst_lit_activity_moves:                1
% 3.48/1.01  inst_num_tautologies:                   0
% 3.48/1.01  inst_num_prop_implied:                  0
% 3.48/1.01  inst_num_existing_simplified:           0
% 3.48/1.01  inst_num_eq_res_simplified:             0
% 3.48/1.01  inst_num_child_elim:                    0
% 3.48/1.01  inst_num_of_dismatching_blockings:      2079
% 3.48/1.01  inst_num_of_non_proper_insts:           2522
% 3.48/1.01  inst_num_of_duplicates:                 0
% 3.48/1.01  inst_inst_num_from_inst_to_res:         0
% 3.48/1.01  inst_dismatching_checking_time:         0.
% 3.48/1.01  
% 3.48/1.01  ------ Resolution
% 3.48/1.01  
% 3.48/1.01  res_num_of_clauses:                     0
% 3.48/1.01  res_num_in_passive:                     0
% 3.48/1.01  res_num_in_active:                      0
% 3.48/1.01  res_num_of_loops:                       160
% 3.48/1.01  res_forward_subset_subsumed:            138
% 3.48/1.01  res_backward_subset_subsumed:           0
% 3.48/1.01  res_forward_subsumed:                   0
% 3.48/1.01  res_backward_subsumed:                  0
% 3.48/1.01  res_forward_subsumption_resolution:     1
% 3.48/1.01  res_backward_subsumption_resolution:    0
% 3.48/1.01  res_clause_to_clause_subsumption:       532
% 3.48/1.01  res_orphan_elimination:                 0
% 3.48/1.01  res_tautology_del:                      63
% 3.48/1.01  res_num_eq_res_simplified:              0
% 3.48/1.01  res_num_sel_changes:                    0
% 3.48/1.01  res_moves_from_active_to_pass:          0
% 3.48/1.01  
% 3.48/1.01  ------ Superposition
% 3.48/1.01  
% 3.48/1.01  sup_time_total:                         0.
% 3.48/1.01  sup_time_generating:                    0.
% 3.48/1.01  sup_time_sim_full:                      0.
% 3.48/1.01  sup_time_sim_immed:                     0.
% 3.48/1.01  
% 3.48/1.01  sup_num_of_clauses:                     280
% 3.48/1.01  sup_num_in_active:                      140
% 3.48/1.01  sup_num_in_passive:                     140
% 3.48/1.01  sup_num_of_loops:                       156
% 3.48/1.01  sup_fw_superposition:                   142
% 3.48/1.01  sup_bw_superposition:                   129
% 3.48/1.01  sup_immediate_simplified:               24
% 3.48/1.01  sup_given_eliminated:                   0
% 3.48/1.01  comparisons_done:                       0
% 3.48/1.01  comparisons_avoided:                    0
% 3.48/1.01  
% 3.48/1.01  ------ Simplifications
% 3.48/1.01  
% 3.48/1.01  
% 3.48/1.01  sim_fw_subset_subsumed:                 11
% 3.48/1.01  sim_bw_subset_subsumed:                 4
% 3.48/1.01  sim_fw_subsumed:                        3
% 3.48/1.01  sim_bw_subsumed:                        3
% 3.48/1.01  sim_fw_subsumption_res:                 0
% 3.48/1.01  sim_bw_subsumption_res:                 0
% 3.48/1.01  sim_tautology_del:                      0
% 3.48/1.01  sim_eq_tautology_del:                   1
% 3.48/1.01  sim_eq_res_simp:                        0
% 3.48/1.01  sim_fw_demodulated:                     10
% 3.48/1.01  sim_bw_demodulated:                     10
% 3.48/1.01  sim_light_normalised:                   2
% 3.48/1.01  sim_joinable_taut:                      0
% 3.48/1.01  sim_joinable_simp:                      0
% 3.48/1.01  sim_ac_normalised:                      0
% 3.48/1.01  sim_smt_subsumption:                    0
% 3.48/1.01  
%------------------------------------------------------------------------------
