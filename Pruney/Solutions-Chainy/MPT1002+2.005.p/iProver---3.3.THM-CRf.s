%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:04:23 EST 2020

% Result     : Theorem 2.35s
% Output     : CNFRefutation 2.35s
% Verified   : 
% Statistics : Number of formulae       :  173 (1208 expanded)
%              Number of clauses        :  115 ( 497 expanded)
%              Number of leaves         :   18 ( 222 expanded)
%              Depth                    :   23
%              Number of atoms          :  446 (4626 expanded)
%              Number of equality atoms :  239 (1518 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f31])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f66,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f42])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f39,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k8_relset_1(X0,X1,X2,X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X2,X0)
       => ( r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X2,X0)
         => ( r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f27,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f28,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f27])).

fof(f35,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ~ r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2)))
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_tarski(sK2,sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ~ r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2)))
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f28,f35])).

fof(f58,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f57,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f59,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f36])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f60,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f62,plain,(
    ~ r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2))) ),
    inference(cnf_transformation,[],[f36])).

fof(f61,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f36])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_5,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1215,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_15,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_11,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_295,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_15,c_11])).

cnf(c_1204,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_295])).

cnf(c_1869,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1215,c_1204])).

cnf(c_3417,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_1869])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1218,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3755,plain,
    ( k1_relat_1(X0) = k1_xboole_0
    | r1_tarski(X0,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3417,c_1218])).

cnf(c_3774,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k1_relat_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3755])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k8_relset_1(X1,X2,X0,X2) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_331,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k8_relset_1(X1,X2,X0,X2) = X1
    | sK3 != X0
    | sK1 != X2
    | sK0 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_24])).

cnf(c_332,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | k8_relset_1(sK0,sK1,sK3,sK1) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_331])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_334,plain,
    ( k8_relset_1(sK0,sK1,sK3,sK1) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_332,c_25,c_23])).

cnf(c_1206,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1209,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2218,plain,
    ( k8_relset_1(sK0,sK1,sK3,X0) = k10_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_1206,c_1209])).

cnf(c_2379,plain,
    ( k10_relat_1(sK3,sK1) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_334,c_2218])).

cnf(c_13,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1212,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2589,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(sK0,k1_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2379,c_1212])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1214,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1798,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1206,c_1214])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_173,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_7])).

cnf(c_174,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_173])).

cnf(c_218,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_9,c_174])).

cnf(c_1205,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_218])).

cnf(c_1983,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1798,c_1205])).

cnf(c_12,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1213,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2594,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1983,c_1213])).

cnf(c_3048,plain,
    ( r1_tarski(sK0,k1_relat_1(sK3)) = iProver_top
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2589,c_2594])).

cnf(c_3049,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(sK0,k1_relat_1(sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_3048])).

cnf(c_3055,plain,
    ( sK1 = k1_xboole_0
    | v1_relat_1(k1_relat_1(sK3)) != iProver_top
    | v1_relat_1(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3049,c_1205])).

cnf(c_22,negated_conjecture,
    ( r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_29,plain,
    ( r1_tarski(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1558,plain,
    ( r1_tarski(k1_relat_1(sK3),sK0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1206,c_1204])).

cnf(c_2171,plain,
    ( k1_relat_1(sK3) = sK0
    | r1_tarski(sK0,k1_relat_1(sK3)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1558,c_1218])).

cnf(c_2698,plain,
    ( r1_tarski(sK0,k1_relat_1(sK3)) != iProver_top
    | k1_relat_1(sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2171,c_2594])).

cnf(c_2699,plain,
    ( k1_relat_1(sK3) = sK0
    | r1_tarski(sK0,k1_relat_1(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2698])).

cnf(c_3056,plain,
    ( k1_relat_1(sK3) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3049,c_2699])).

cnf(c_14,plain,
    ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1211,plain,
    ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) = iProver_top
    | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1210,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2794,plain,
    ( k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_1206,c_1210])).

cnf(c_20,negated_conjecture,
    ( ~ r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1208,plain,
    ( r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2377,plain,
    ( r1_tarski(sK2,k10_relat_1(sK3,k7_relset_1(sK0,sK1,sK3,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2218,c_1208])).

cnf(c_2969,plain,
    ( r1_tarski(sK2,k10_relat_1(sK3,k9_relat_1(sK3,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2794,c_2377])).

cnf(c_2973,plain,
    ( r1_tarski(sK2,k1_relat_1(sK3)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1211,c_2969])).

cnf(c_3069,plain,
    ( r1_tarski(sK2,k1_relat_1(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2973,c_2594])).

cnf(c_3138,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(sK2,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3056,c_3069])).

cnf(c_3163,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3055,c_29,c_3138])).

cnf(c_2170,plain,
    ( k2_zfmisc_1(sK0,sK1) = sK3
    | r1_tarski(k2_zfmisc_1(sK0,sK1),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1798,c_1218])).

cnf(c_3167,plain,
    ( k2_zfmisc_1(sK0,k1_xboole_0) = sK3
    | r1_tarski(k2_zfmisc_1(sK0,k1_xboole_0),sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3163,c_2170])).

cnf(c_21,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_3174,plain,
    ( sK0 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3163,c_21])).

cnf(c_3175,plain,
    ( sK0 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_3174])).

cnf(c_3195,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = sK3
    | r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3167,c_3175])).

cnf(c_3198,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3195,c_5])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1216,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3593,plain,
    ( sK3 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3198,c_1216])).

cnf(c_3596,plain,
    ( r1_tarski(sK2,k1_relat_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3593,c_3069])).

cnf(c_793,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1529,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,sK2)
    | X2 != X0
    | sK2 != X1 ),
    inference(instantiation,[status(thm)],[c_793])).

cnf(c_2123,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK0,sK2)
    | sK0 != X0
    | sK2 != X1 ),
    inference(instantiation,[status(thm)],[c_1529])).

cnf(c_2825,plain,
    ( ~ r1_tarski(X0,sK2)
    | r1_tarski(sK0,sK2)
    | sK0 != X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_2123])).

cnf(c_2827,plain,
    ( r1_tarski(sK0,sK2)
    | ~ r1_tarski(k1_xboole_0,sK2)
    | sK0 != k1_xboole_0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_2825])).

cnf(c_792,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1420,plain,
    ( X0 != X1
    | sK2 != X1
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_792])).

cnf(c_2606,plain,
    ( X0 != sK0
    | sK2 = X0
    | sK2 != sK0 ),
    inference(instantiation,[status(thm)],[c_1420])).

cnf(c_2607,plain,
    ( sK2 != sK0
    | sK2 = k1_xboole_0
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_2606])).

cnf(c_1707,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,k1_relat_1(X3))
    | X2 != X0
    | k1_relat_1(X3) != X1 ),
    inference(instantiation,[status(thm)],[c_793])).

cnf(c_2400,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK2,k1_relat_1(X2))
    | k1_relat_1(X2) != X1
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_1707])).

cnf(c_2401,plain,
    ( k1_relat_1(X0) != X1
    | sK2 != X2
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(sK2,k1_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2400])).

cnf(c_2403,plain,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0
    | sK2 != k1_xboole_0
    | r1_tarski(sK2,k1_relat_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2401])).

cnf(c_1409,plain,
    ( ~ r1_tarski(X0,sK2)
    | ~ r1_tarski(sK2,X0)
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1963,plain,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_tarski(sK2,sK0)
    | sK2 = sK0 ),
    inference(instantiation,[status(thm)],[c_1409])).

cnf(c_1689,plain,
    ( r1_tarski(k1_xboole_0,k1_relat_1(X0)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1692,plain,
    ( r1_tarski(k1_xboole_0,k1_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1689])).

cnf(c_1694,plain,
    ( r1_tarski(k1_xboole_0,k1_relat_1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1692])).

cnf(c_1551,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_792])).

cnf(c_1552,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1551])).

cnf(c_1524,plain,
    ( r1_tarski(k1_xboole_0,sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1442,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1445,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1442])).

cnf(c_1347,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_218])).

cnf(c_1441,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1))
    | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1347])).

cnf(c_1443,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) != iProver_top
    | v1_relat_1(k2_zfmisc_1(X0,X1)) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1441])).

cnf(c_791,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1433,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_791])).

cnf(c_1364,plain,
    ( sK0 != X0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_792])).

cnf(c_1432,plain,
    ( sK0 != sK0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1364])).

cnf(c_1415,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_791])).

cnf(c_70,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_72,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_70])).

cnf(c_69,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_6,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_68,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_52,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3775,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(grounding,[status(thm)],[c_1445:[bind(X1,$fot(k1_xboole_0)),bind(X0,$fot(k1_xboole_0))]])).

cnf(c_3776,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
    | v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(grounding,[status(thm)],[c_1443:[bind(X1,$fot(k1_xboole_0)),bind(X0,$fot(k1_xboole_0))]])).

cnf(c_3777,plain,
    ( v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(grounding,[status(thm)],[c_52:[bind(X1,$fot(k1_xboole_0)),bind(X0,$fot(k1_xboole_0))]])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3774,c_3596,c_3138,c_2827,c_2607,c_2403,c_1963,c_1694,c_1552,c_1524,c_3775,c_3776,c_1433,c_1432,c_1415,c_72,c_69,c_68,c_3777,c_21,c_29,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:24:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.35/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.35/0.99  
% 2.35/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.35/0.99  
% 2.35/0.99  ------  iProver source info
% 2.35/0.99  
% 2.35/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.35/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.35/0.99  git: non_committed_changes: false
% 2.35/0.99  git: last_make_outside_of_git: false
% 2.35/0.99  
% 2.35/0.99  ------ 
% 2.35/0.99  
% 2.35/0.99  ------ Input Options
% 2.35/0.99  
% 2.35/0.99  --out_options                           all
% 2.35/0.99  --tptp_safe_out                         true
% 2.35/0.99  --problem_path                          ""
% 2.35/0.99  --include_path                          ""
% 2.35/0.99  --clausifier                            res/vclausify_rel
% 2.35/0.99  --clausifier_options                    --mode clausify
% 2.35/0.99  --stdin                                 false
% 2.35/0.99  --stats_out                             all
% 2.35/0.99  
% 2.35/0.99  ------ General Options
% 2.35/0.99  
% 2.35/0.99  --fof                                   false
% 2.35/0.99  --time_out_real                         305.
% 2.35/0.99  --time_out_virtual                      -1.
% 2.35/0.99  --symbol_type_check                     false
% 2.35/0.99  --clausify_out                          false
% 2.35/0.99  --sig_cnt_out                           false
% 2.35/0.99  --trig_cnt_out                          false
% 2.35/0.99  --trig_cnt_out_tolerance                1.
% 2.35/0.99  --trig_cnt_out_sk_spl                   false
% 2.35/0.99  --abstr_cl_out                          false
% 2.35/0.99  
% 2.35/0.99  ------ Global Options
% 2.35/0.99  
% 2.35/0.99  --schedule                              default
% 2.35/0.99  --add_important_lit                     false
% 2.35/0.99  --prop_solver_per_cl                    1000
% 2.35/0.99  --min_unsat_core                        false
% 2.35/0.99  --soft_assumptions                      false
% 2.35/0.99  --soft_lemma_size                       3
% 2.35/0.99  --prop_impl_unit_size                   0
% 2.35/0.99  --prop_impl_unit                        []
% 2.35/0.99  --share_sel_clauses                     true
% 2.35/0.99  --reset_solvers                         false
% 2.35/0.99  --bc_imp_inh                            [conj_cone]
% 2.35/0.99  --conj_cone_tolerance                   3.
% 2.35/0.99  --extra_neg_conj                        none
% 2.35/0.99  --large_theory_mode                     true
% 2.35/0.99  --prolific_symb_bound                   200
% 2.35/0.99  --lt_threshold                          2000
% 2.35/0.99  --clause_weak_htbl                      true
% 2.35/0.99  --gc_record_bc_elim                     false
% 2.35/0.99  
% 2.35/0.99  ------ Preprocessing Options
% 2.35/0.99  
% 2.35/0.99  --preprocessing_flag                    true
% 2.35/0.99  --time_out_prep_mult                    0.1
% 2.35/0.99  --splitting_mode                        input
% 2.35/0.99  --splitting_grd                         true
% 2.35/0.99  --splitting_cvd                         false
% 2.35/0.99  --splitting_cvd_svl                     false
% 2.35/0.99  --splitting_nvd                         32
% 2.35/0.99  --sub_typing                            true
% 2.35/0.99  --prep_gs_sim                           true
% 2.35/0.99  --prep_unflatten                        true
% 2.35/0.99  --prep_res_sim                          true
% 2.35/0.99  --prep_upred                            true
% 2.35/0.99  --prep_sem_filter                       exhaustive
% 2.35/0.99  --prep_sem_filter_out                   false
% 2.35/0.99  --pred_elim                             true
% 2.35/0.99  --res_sim_input                         true
% 2.35/0.99  --eq_ax_congr_red                       true
% 2.35/0.99  --pure_diseq_elim                       true
% 2.35/0.99  --brand_transform                       false
% 2.35/0.99  --non_eq_to_eq                          false
% 2.35/0.99  --prep_def_merge                        true
% 2.35/0.99  --prep_def_merge_prop_impl              false
% 2.35/0.99  --prep_def_merge_mbd                    true
% 2.35/0.99  --prep_def_merge_tr_red                 false
% 2.35/0.99  --prep_def_merge_tr_cl                  false
% 2.35/0.99  --smt_preprocessing                     true
% 2.35/0.99  --smt_ac_axioms                         fast
% 2.35/0.99  --preprocessed_out                      false
% 2.35/0.99  --preprocessed_stats                    false
% 2.35/0.99  
% 2.35/0.99  ------ Abstraction refinement Options
% 2.35/0.99  
% 2.35/0.99  --abstr_ref                             []
% 2.35/0.99  --abstr_ref_prep                        false
% 2.35/0.99  --abstr_ref_until_sat                   false
% 2.35/0.99  --abstr_ref_sig_restrict                funpre
% 2.35/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.35/0.99  --abstr_ref_under                       []
% 2.35/0.99  
% 2.35/0.99  ------ SAT Options
% 2.35/0.99  
% 2.35/0.99  --sat_mode                              false
% 2.35/0.99  --sat_fm_restart_options                ""
% 2.35/0.99  --sat_gr_def                            false
% 2.35/0.99  --sat_epr_types                         true
% 2.35/0.99  --sat_non_cyclic_types                  false
% 2.35/0.99  --sat_finite_models                     false
% 2.35/0.99  --sat_fm_lemmas                         false
% 2.35/0.99  --sat_fm_prep                           false
% 2.35/0.99  --sat_fm_uc_incr                        true
% 2.35/0.99  --sat_out_model                         small
% 2.35/0.99  --sat_out_clauses                       false
% 2.35/0.99  
% 2.35/0.99  ------ QBF Options
% 2.35/0.99  
% 2.35/0.99  --qbf_mode                              false
% 2.35/0.99  --qbf_elim_univ                         false
% 2.35/0.99  --qbf_dom_inst                          none
% 2.35/0.99  --qbf_dom_pre_inst                      false
% 2.35/0.99  --qbf_sk_in                             false
% 2.35/0.99  --qbf_pred_elim                         true
% 2.35/0.99  --qbf_split                             512
% 2.35/0.99  
% 2.35/0.99  ------ BMC1 Options
% 2.35/0.99  
% 2.35/0.99  --bmc1_incremental                      false
% 2.35/0.99  --bmc1_axioms                           reachable_all
% 2.35/0.99  --bmc1_min_bound                        0
% 2.35/0.99  --bmc1_max_bound                        -1
% 2.35/0.99  --bmc1_max_bound_default                -1
% 2.35/0.99  --bmc1_symbol_reachability              true
% 2.35/0.99  --bmc1_property_lemmas                  false
% 2.35/0.99  --bmc1_k_induction                      false
% 2.35/0.99  --bmc1_non_equiv_states                 false
% 2.35/0.99  --bmc1_deadlock                         false
% 2.35/0.99  --bmc1_ucm                              false
% 2.35/0.99  --bmc1_add_unsat_core                   none
% 2.35/0.99  --bmc1_unsat_core_children              false
% 2.35/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.35/0.99  --bmc1_out_stat                         full
% 2.35/0.99  --bmc1_ground_init                      false
% 2.35/0.99  --bmc1_pre_inst_next_state              false
% 2.35/0.99  --bmc1_pre_inst_state                   false
% 2.35/0.99  --bmc1_pre_inst_reach_state             false
% 2.35/0.99  --bmc1_out_unsat_core                   false
% 2.35/0.99  --bmc1_aig_witness_out                  false
% 2.35/0.99  --bmc1_verbose                          false
% 2.35/0.99  --bmc1_dump_clauses_tptp                false
% 2.35/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.35/0.99  --bmc1_dump_file                        -
% 2.35/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.35/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.35/0.99  --bmc1_ucm_extend_mode                  1
% 2.35/0.99  --bmc1_ucm_init_mode                    2
% 2.35/0.99  --bmc1_ucm_cone_mode                    none
% 2.35/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.35/0.99  --bmc1_ucm_relax_model                  4
% 2.35/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.35/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.35/0.99  --bmc1_ucm_layered_model                none
% 2.35/0.99  --bmc1_ucm_max_lemma_size               10
% 2.35/0.99  
% 2.35/0.99  ------ AIG Options
% 2.35/0.99  
% 2.35/0.99  --aig_mode                              false
% 2.35/0.99  
% 2.35/0.99  ------ Instantiation Options
% 2.35/0.99  
% 2.35/0.99  --instantiation_flag                    true
% 2.35/0.99  --inst_sos_flag                         false
% 2.35/0.99  --inst_sos_phase                        true
% 2.35/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.35/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.35/0.99  --inst_lit_sel_side                     num_symb
% 2.35/0.99  --inst_solver_per_active                1400
% 2.35/0.99  --inst_solver_calls_frac                1.
% 2.35/0.99  --inst_passive_queue_type               priority_queues
% 2.35/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.35/0.99  --inst_passive_queues_freq              [25;2]
% 2.35/0.99  --inst_dismatching                      true
% 2.35/0.99  --inst_eager_unprocessed_to_passive     true
% 2.35/0.99  --inst_prop_sim_given                   true
% 2.35/0.99  --inst_prop_sim_new                     false
% 2.35/0.99  --inst_subs_new                         false
% 2.35/0.99  --inst_eq_res_simp                      false
% 2.35/0.99  --inst_subs_given                       false
% 2.35/0.99  --inst_orphan_elimination               true
% 2.35/0.99  --inst_learning_loop_flag               true
% 2.35/0.99  --inst_learning_start                   3000
% 2.35/0.99  --inst_learning_factor                  2
% 2.35/0.99  --inst_start_prop_sim_after_learn       3
% 2.35/0.99  --inst_sel_renew                        solver
% 2.35/0.99  --inst_lit_activity_flag                true
% 2.35/0.99  --inst_restr_to_given                   false
% 2.35/0.99  --inst_activity_threshold               500
% 2.35/0.99  --inst_out_proof                        true
% 2.35/0.99  
% 2.35/0.99  ------ Resolution Options
% 2.35/0.99  
% 2.35/0.99  --resolution_flag                       true
% 2.35/0.99  --res_lit_sel                           adaptive
% 2.35/0.99  --res_lit_sel_side                      none
% 2.35/0.99  --res_ordering                          kbo
% 2.35/0.99  --res_to_prop_solver                    active
% 2.35/0.99  --res_prop_simpl_new                    false
% 2.35/0.99  --res_prop_simpl_given                  true
% 2.35/0.99  --res_passive_queue_type                priority_queues
% 2.35/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.35/0.99  --res_passive_queues_freq               [15;5]
% 2.35/0.99  --res_forward_subs                      full
% 2.35/0.99  --res_backward_subs                     full
% 2.35/0.99  --res_forward_subs_resolution           true
% 2.35/0.99  --res_backward_subs_resolution          true
% 2.35/0.99  --res_orphan_elimination                true
% 2.35/0.99  --res_time_limit                        2.
% 2.35/0.99  --res_out_proof                         true
% 2.35/0.99  
% 2.35/0.99  ------ Superposition Options
% 2.35/0.99  
% 2.35/0.99  --superposition_flag                    true
% 2.35/0.99  --sup_passive_queue_type                priority_queues
% 2.35/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.35/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.35/0.99  --demod_completeness_check              fast
% 2.35/0.99  --demod_use_ground                      true
% 2.35/0.99  --sup_to_prop_solver                    passive
% 2.35/0.99  --sup_prop_simpl_new                    true
% 2.35/0.99  --sup_prop_simpl_given                  true
% 2.35/0.99  --sup_fun_splitting                     false
% 2.35/0.99  --sup_smt_interval                      50000
% 2.35/0.99  
% 2.35/0.99  ------ Superposition Simplification Setup
% 2.35/0.99  
% 2.35/0.99  --sup_indices_passive                   []
% 2.35/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.35/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.35/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.35/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.35/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.35/0.99  --sup_full_bw                           [BwDemod]
% 2.35/0.99  --sup_immed_triv                        [TrivRules]
% 2.35/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.35/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.35/0.99  --sup_immed_bw_main                     []
% 2.35/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.35/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.35/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.35/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.35/0.99  
% 2.35/0.99  ------ Combination Options
% 2.35/0.99  
% 2.35/0.99  --comb_res_mult                         3
% 2.35/0.99  --comb_sup_mult                         2
% 2.35/0.99  --comb_inst_mult                        10
% 2.35/0.99  
% 2.35/0.99  ------ Debug Options
% 2.35/0.99  
% 2.35/0.99  --dbg_backtrace                         false
% 2.35/0.99  --dbg_dump_prop_clauses                 false
% 2.35/0.99  --dbg_dump_prop_clauses_file            -
% 2.35/0.99  --dbg_out_stat                          false
% 2.35/0.99  ------ Parsing...
% 2.35/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.35/0.99  
% 2.35/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.35/0.99  
% 2.35/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.35/0.99  
% 2.35/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.35/0.99  ------ Proving...
% 2.35/0.99  ------ Problem Properties 
% 2.35/0.99  
% 2.35/0.99  
% 2.35/0.99  clauses                                 21
% 2.35/0.99  conjectures                             4
% 2.35/0.99  EPR                                     6
% 2.35/0.99  Horn                                    19
% 2.35/0.99  unary                                   8
% 2.35/0.99  binary                                  7
% 2.35/0.99  lits                                    40
% 2.35/0.99  lits eq                                 14
% 2.35/0.99  fd_pure                                 0
% 2.35/0.99  fd_pseudo                               0
% 2.35/0.99  fd_cond                                 1
% 2.35/0.99  fd_pseudo_cond                          1
% 2.35/0.99  AC symbols                              0
% 2.35/0.99  
% 2.35/0.99  ------ Schedule dynamic 5 is on 
% 2.35/0.99  
% 2.35/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.35/0.99  
% 2.35/0.99  
% 2.35/0.99  ------ 
% 2.35/0.99  Current options:
% 2.35/0.99  ------ 
% 2.35/0.99  
% 2.35/0.99  ------ Input Options
% 2.35/0.99  
% 2.35/0.99  --out_options                           all
% 2.35/0.99  --tptp_safe_out                         true
% 2.35/0.99  --problem_path                          ""
% 2.35/0.99  --include_path                          ""
% 2.35/0.99  --clausifier                            res/vclausify_rel
% 2.35/0.99  --clausifier_options                    --mode clausify
% 2.35/0.99  --stdin                                 false
% 2.35/0.99  --stats_out                             all
% 2.35/0.99  
% 2.35/0.99  ------ General Options
% 2.35/0.99  
% 2.35/0.99  --fof                                   false
% 2.35/0.99  --time_out_real                         305.
% 2.35/0.99  --time_out_virtual                      -1.
% 2.35/0.99  --symbol_type_check                     false
% 2.35/0.99  --clausify_out                          false
% 2.35/0.99  --sig_cnt_out                           false
% 2.35/0.99  --trig_cnt_out                          false
% 2.35/0.99  --trig_cnt_out_tolerance                1.
% 2.35/0.99  --trig_cnt_out_sk_spl                   false
% 2.35/0.99  --abstr_cl_out                          false
% 2.35/0.99  
% 2.35/0.99  ------ Global Options
% 2.35/0.99  
% 2.35/0.99  --schedule                              default
% 2.35/0.99  --add_important_lit                     false
% 2.35/0.99  --prop_solver_per_cl                    1000
% 2.35/0.99  --min_unsat_core                        false
% 2.35/0.99  --soft_assumptions                      false
% 2.35/0.99  --soft_lemma_size                       3
% 2.35/0.99  --prop_impl_unit_size                   0
% 2.35/0.99  --prop_impl_unit                        []
% 2.35/0.99  --share_sel_clauses                     true
% 2.35/0.99  --reset_solvers                         false
% 2.35/0.99  --bc_imp_inh                            [conj_cone]
% 2.35/0.99  --conj_cone_tolerance                   3.
% 2.35/0.99  --extra_neg_conj                        none
% 2.35/0.99  --large_theory_mode                     true
% 2.35/0.99  --prolific_symb_bound                   200
% 2.35/0.99  --lt_threshold                          2000
% 2.35/0.99  --clause_weak_htbl                      true
% 2.35/0.99  --gc_record_bc_elim                     false
% 2.35/0.99  
% 2.35/0.99  ------ Preprocessing Options
% 2.35/0.99  
% 2.35/0.99  --preprocessing_flag                    true
% 2.35/0.99  --time_out_prep_mult                    0.1
% 2.35/0.99  --splitting_mode                        input
% 2.35/0.99  --splitting_grd                         true
% 2.35/0.99  --splitting_cvd                         false
% 2.35/0.99  --splitting_cvd_svl                     false
% 2.35/0.99  --splitting_nvd                         32
% 2.35/0.99  --sub_typing                            true
% 2.35/0.99  --prep_gs_sim                           true
% 2.35/0.99  --prep_unflatten                        true
% 2.35/0.99  --prep_res_sim                          true
% 2.35/0.99  --prep_upred                            true
% 2.35/0.99  --prep_sem_filter                       exhaustive
% 2.35/0.99  --prep_sem_filter_out                   false
% 2.35/0.99  --pred_elim                             true
% 2.35/0.99  --res_sim_input                         true
% 2.35/0.99  --eq_ax_congr_red                       true
% 2.35/0.99  --pure_diseq_elim                       true
% 2.35/0.99  --brand_transform                       false
% 2.35/0.99  --non_eq_to_eq                          false
% 2.35/0.99  --prep_def_merge                        true
% 2.35/0.99  --prep_def_merge_prop_impl              false
% 2.35/0.99  --prep_def_merge_mbd                    true
% 2.35/0.99  --prep_def_merge_tr_red                 false
% 2.35/0.99  --prep_def_merge_tr_cl                  false
% 2.35/0.99  --smt_preprocessing                     true
% 2.35/0.99  --smt_ac_axioms                         fast
% 2.35/0.99  --preprocessed_out                      false
% 2.35/0.99  --preprocessed_stats                    false
% 2.35/0.99  
% 2.35/0.99  ------ Abstraction refinement Options
% 2.35/0.99  
% 2.35/0.99  --abstr_ref                             []
% 2.35/0.99  --abstr_ref_prep                        false
% 2.35/0.99  --abstr_ref_until_sat                   false
% 2.35/0.99  --abstr_ref_sig_restrict                funpre
% 2.35/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.35/0.99  --abstr_ref_under                       []
% 2.35/0.99  
% 2.35/0.99  ------ SAT Options
% 2.35/0.99  
% 2.35/0.99  --sat_mode                              false
% 2.35/0.99  --sat_fm_restart_options                ""
% 2.35/0.99  --sat_gr_def                            false
% 2.35/0.99  --sat_epr_types                         true
% 2.35/0.99  --sat_non_cyclic_types                  false
% 2.35/0.99  --sat_finite_models                     false
% 2.35/0.99  --sat_fm_lemmas                         false
% 2.35/0.99  --sat_fm_prep                           false
% 2.35/0.99  --sat_fm_uc_incr                        true
% 2.35/0.99  --sat_out_model                         small
% 2.35/0.99  --sat_out_clauses                       false
% 2.35/0.99  
% 2.35/0.99  ------ QBF Options
% 2.35/0.99  
% 2.35/0.99  --qbf_mode                              false
% 2.35/0.99  --qbf_elim_univ                         false
% 2.35/0.99  --qbf_dom_inst                          none
% 2.35/0.99  --qbf_dom_pre_inst                      false
% 2.35/0.99  --qbf_sk_in                             false
% 2.35/0.99  --qbf_pred_elim                         true
% 2.35/0.99  --qbf_split                             512
% 2.35/0.99  
% 2.35/0.99  ------ BMC1 Options
% 2.35/0.99  
% 2.35/0.99  --bmc1_incremental                      false
% 2.35/0.99  --bmc1_axioms                           reachable_all
% 2.35/0.99  --bmc1_min_bound                        0
% 2.35/0.99  --bmc1_max_bound                        -1
% 2.35/0.99  --bmc1_max_bound_default                -1
% 2.35/0.99  --bmc1_symbol_reachability              true
% 2.35/0.99  --bmc1_property_lemmas                  false
% 2.35/0.99  --bmc1_k_induction                      false
% 2.35/0.99  --bmc1_non_equiv_states                 false
% 2.35/0.99  --bmc1_deadlock                         false
% 2.35/0.99  --bmc1_ucm                              false
% 2.35/0.99  --bmc1_add_unsat_core                   none
% 2.35/0.99  --bmc1_unsat_core_children              false
% 2.35/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.35/0.99  --bmc1_out_stat                         full
% 2.35/0.99  --bmc1_ground_init                      false
% 2.35/0.99  --bmc1_pre_inst_next_state              false
% 2.35/0.99  --bmc1_pre_inst_state                   false
% 2.35/0.99  --bmc1_pre_inst_reach_state             false
% 2.35/0.99  --bmc1_out_unsat_core                   false
% 2.35/0.99  --bmc1_aig_witness_out                  false
% 2.35/0.99  --bmc1_verbose                          false
% 2.35/0.99  --bmc1_dump_clauses_tptp                false
% 2.35/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.35/0.99  --bmc1_dump_file                        -
% 2.35/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.35/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.35/0.99  --bmc1_ucm_extend_mode                  1
% 2.35/0.99  --bmc1_ucm_init_mode                    2
% 2.35/0.99  --bmc1_ucm_cone_mode                    none
% 2.35/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.35/0.99  --bmc1_ucm_relax_model                  4
% 2.35/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.35/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.35/0.99  --bmc1_ucm_layered_model                none
% 2.35/0.99  --bmc1_ucm_max_lemma_size               10
% 2.35/0.99  
% 2.35/0.99  ------ AIG Options
% 2.35/0.99  
% 2.35/0.99  --aig_mode                              false
% 2.35/0.99  
% 2.35/0.99  ------ Instantiation Options
% 2.35/0.99  
% 2.35/0.99  --instantiation_flag                    true
% 2.35/0.99  --inst_sos_flag                         false
% 2.35/0.99  --inst_sos_phase                        true
% 2.35/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.35/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.35/0.99  --inst_lit_sel_side                     none
% 2.35/0.99  --inst_solver_per_active                1400
% 2.35/0.99  --inst_solver_calls_frac                1.
% 2.35/0.99  --inst_passive_queue_type               priority_queues
% 2.35/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.35/0.99  --inst_passive_queues_freq              [25;2]
% 2.35/0.99  --inst_dismatching                      true
% 2.35/0.99  --inst_eager_unprocessed_to_passive     true
% 2.35/0.99  --inst_prop_sim_given                   true
% 2.35/0.99  --inst_prop_sim_new                     false
% 2.35/0.99  --inst_subs_new                         false
% 2.35/0.99  --inst_eq_res_simp                      false
% 2.35/0.99  --inst_subs_given                       false
% 2.35/0.99  --inst_orphan_elimination               true
% 2.35/0.99  --inst_learning_loop_flag               true
% 2.35/0.99  --inst_learning_start                   3000
% 2.35/0.99  --inst_learning_factor                  2
% 2.35/0.99  --inst_start_prop_sim_after_learn       3
% 2.35/0.99  --inst_sel_renew                        solver
% 2.35/0.99  --inst_lit_activity_flag                true
% 2.35/0.99  --inst_restr_to_given                   false
% 2.35/0.99  --inst_activity_threshold               500
% 2.35/0.99  --inst_out_proof                        true
% 2.35/0.99  
% 2.35/0.99  ------ Resolution Options
% 2.35/0.99  
% 2.35/0.99  --resolution_flag                       false
% 2.35/0.99  --res_lit_sel                           adaptive
% 2.35/0.99  --res_lit_sel_side                      none
% 2.35/0.99  --res_ordering                          kbo
% 2.35/0.99  --res_to_prop_solver                    active
% 2.35/0.99  --res_prop_simpl_new                    false
% 2.35/0.99  --res_prop_simpl_given                  true
% 2.35/0.99  --res_passive_queue_type                priority_queues
% 2.35/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.35/0.99  --res_passive_queues_freq               [15;5]
% 2.35/0.99  --res_forward_subs                      full
% 2.35/0.99  --res_backward_subs                     full
% 2.35/0.99  --res_forward_subs_resolution           true
% 2.35/0.99  --res_backward_subs_resolution          true
% 2.35/0.99  --res_orphan_elimination                true
% 2.35/0.99  --res_time_limit                        2.
% 2.35/0.99  --res_out_proof                         true
% 2.35/0.99  
% 2.35/0.99  ------ Superposition Options
% 2.35/0.99  
% 2.35/0.99  --superposition_flag                    true
% 2.35/0.99  --sup_passive_queue_type                priority_queues
% 2.35/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.35/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.35/0.99  --demod_completeness_check              fast
% 2.35/0.99  --demod_use_ground                      true
% 2.35/0.99  --sup_to_prop_solver                    passive
% 2.35/0.99  --sup_prop_simpl_new                    true
% 2.35/0.99  --sup_prop_simpl_given                  true
% 2.35/0.99  --sup_fun_splitting                     false
% 2.35/0.99  --sup_smt_interval                      50000
% 2.35/0.99  
% 2.35/0.99  ------ Superposition Simplification Setup
% 2.35/0.99  
% 2.35/0.99  --sup_indices_passive                   []
% 2.35/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.35/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.35/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.35/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.35/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.35/0.99  --sup_full_bw                           [BwDemod]
% 2.35/0.99  --sup_immed_triv                        [TrivRules]
% 2.35/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.35/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.35/0.99  --sup_immed_bw_main                     []
% 2.35/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.35/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.35/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.35/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.35/0.99  
% 2.35/0.99  ------ Combination Options
% 2.35/0.99  
% 2.35/0.99  --comb_res_mult                         3
% 2.35/0.99  --comb_sup_mult                         2
% 2.35/0.99  --comb_inst_mult                        10
% 2.35/0.99  
% 2.35/0.99  ------ Debug Options
% 2.35/0.99  
% 2.35/0.99  --dbg_backtrace                         false
% 2.35/0.99  --dbg_dump_prop_clauses                 false
% 2.35/0.99  --dbg_dump_prop_clauses_file            -
% 2.35/0.99  --dbg_out_stat                          false
% 2.35/0.99  
% 2.35/0.99  
% 2.35/0.99  
% 2.35/0.99  
% 2.35/0.99  ------ Proving...
% 2.35/0.99  
% 2.35/0.99  
% 2.35/0.99  % SZS status Theorem for theBenchmark.p
% 2.35/0.99  
% 2.35/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.35/0.99  
% 2.35/0.99  fof(f3,axiom,(
% 2.35/0.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.35/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.35/0.99  
% 2.35/0.99  fof(f31,plain,(
% 2.35/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.35/0.99    inference(nnf_transformation,[],[f3])).
% 2.35/0.99  
% 2.35/0.99  fof(f32,plain,(
% 2.35/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.35/0.99    inference(flattening,[],[f31])).
% 2.35/0.99  
% 2.35/0.99  fof(f42,plain,(
% 2.35/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.35/0.99    inference(cnf_transformation,[],[f32])).
% 2.35/0.99  
% 2.35/0.99  fof(f66,plain,(
% 2.35/0.99    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.35/0.99    inference(equality_resolution,[],[f42])).
% 2.35/0.99  
% 2.35/0.99  fof(f4,axiom,(
% 2.35/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.35/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.35/0.99  
% 2.35/0.99  fof(f33,plain,(
% 2.35/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.35/0.99    inference(nnf_transformation,[],[f4])).
% 2.35/0.99  
% 2.35/0.99  fof(f45,plain,(
% 2.35/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.35/0.99    inference(cnf_transformation,[],[f33])).
% 2.35/0.99  
% 2.35/0.99  fof(f10,axiom,(
% 2.35/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.35/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.35/0.99  
% 2.35/0.99  fof(f16,plain,(
% 2.35/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.35/0.99    inference(pure_predicate_removal,[],[f10])).
% 2.35/0.99  
% 2.35/0.99  fof(f22,plain,(
% 2.35/0.99    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.35/0.99    inference(ennf_transformation,[],[f16])).
% 2.35/0.99  
% 2.35/0.99  fof(f52,plain,(
% 2.35/0.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.35/0.99    inference(cnf_transformation,[],[f22])).
% 2.35/0.99  
% 2.35/0.99  fof(f6,axiom,(
% 2.35/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.35/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.35/0.99  
% 2.35/0.99  fof(f18,plain,(
% 2.35/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.35/0.99    inference(ennf_transformation,[],[f6])).
% 2.35/0.99  
% 2.35/0.99  fof(f34,plain,(
% 2.35/0.99    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.35/0.99    inference(nnf_transformation,[],[f18])).
% 2.35/0.99  
% 2.35/0.99  fof(f47,plain,(
% 2.35/0.99    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.35/0.99    inference(cnf_transformation,[],[f34])).
% 2.35/0.99  
% 2.35/0.99  fof(f1,axiom,(
% 2.35/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.35/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.35/0.99  
% 2.35/0.99  fof(f29,plain,(
% 2.35/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.35/0.99    inference(nnf_transformation,[],[f1])).
% 2.35/0.99  
% 2.35/0.99  fof(f30,plain,(
% 2.35/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.35/0.99    inference(flattening,[],[f29])).
% 2.35/0.99  
% 2.35/0.99  fof(f39,plain,(
% 2.35/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.35/0.99    inference(cnf_transformation,[],[f30])).
% 2.35/0.99  
% 2.35/0.99  fof(f13,axiom,(
% 2.35/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k8_relset_1(X0,X1,X2,X1) = X0))),
% 2.35/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.35/0.99  
% 2.35/0.99  fof(f25,plain,(
% 2.35/0.99    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.35/0.99    inference(ennf_transformation,[],[f13])).
% 2.35/0.99  
% 2.35/0.99  fof(f26,plain,(
% 2.35/0.99    ! [X0,X1,X2] : (k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.35/0.99    inference(flattening,[],[f25])).
% 2.35/0.99  
% 2.35/0.99  fof(f55,plain,(
% 2.35/0.99    ( ! [X2,X0,X1] : (k8_relset_1(X0,X1,X2,X1) = X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.35/0.99    inference(cnf_transformation,[],[f26])).
% 2.35/0.99  
% 2.35/0.99  fof(f14,conjecture,(
% 2.35/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => (r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 2.35/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.35/0.99  
% 2.35/0.99  fof(f15,negated_conjecture,(
% 2.35/0.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => (r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 2.35/0.99    inference(negated_conjecture,[],[f14])).
% 2.35/0.99  
% 2.35/0.99  fof(f27,plain,(
% 2.35/0.99    ? [X0,X1,X2,X3] : (((~r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 2.35/0.99    inference(ennf_transformation,[],[f15])).
% 2.35/0.99  
% 2.35/0.99  fof(f28,plain,(
% 2.35/0.99    ? [X0,X1,X2,X3] : (~r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 2.35/0.99    inference(flattening,[],[f27])).
% 2.35/0.99  
% 2.35/0.99  fof(f35,plain,(
% 2.35/0.99    ? [X0,X1,X2,X3] : (~r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (~r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 2.35/0.99    introduced(choice_axiom,[])).
% 2.35/0.99  
% 2.35/0.99  fof(f36,plain,(
% 2.35/0.99    ~r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 2.35/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f28,f35])).
% 2.35/0.99  
% 2.35/0.99  fof(f58,plain,(
% 2.35/0.99    v1_funct_2(sK3,sK0,sK1)),
% 2.35/0.99    inference(cnf_transformation,[],[f36])).
% 2.35/0.99  
% 2.35/0.99  fof(f57,plain,(
% 2.35/0.99    v1_funct_1(sK3)),
% 2.35/0.99    inference(cnf_transformation,[],[f36])).
% 2.35/0.99  
% 2.35/0.99  fof(f59,plain,(
% 2.35/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.35/0.99    inference(cnf_transformation,[],[f36])).
% 2.35/0.99  
% 2.35/0.99  fof(f12,axiom,(
% 2.35/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 2.35/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.35/0.99  
% 2.35/0.99  fof(f24,plain,(
% 2.35/0.99    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.35/0.99    inference(ennf_transformation,[],[f12])).
% 2.35/0.99  
% 2.35/0.99  fof(f54,plain,(
% 2.35/0.99    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.35/0.99    inference(cnf_transformation,[],[f24])).
% 2.35/0.99  
% 2.35/0.99  fof(f8,axiom,(
% 2.35/0.99    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 2.35/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.35/0.99  
% 2.35/0.99  fof(f19,plain,(
% 2.35/0.99    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.35/0.99    inference(ennf_transformation,[],[f8])).
% 2.35/0.99  
% 2.35/0.99  fof(f50,plain,(
% 2.35/0.99    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.35/0.99    inference(cnf_transformation,[],[f19])).
% 2.35/0.99  
% 2.35/0.99  fof(f44,plain,(
% 2.35/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.35/0.99    inference(cnf_transformation,[],[f33])).
% 2.35/0.99  
% 2.35/0.99  fof(f5,axiom,(
% 2.35/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.35/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.35/0.99  
% 2.35/0.99  fof(f17,plain,(
% 2.35/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.35/0.99    inference(ennf_transformation,[],[f5])).
% 2.35/0.99  
% 2.35/0.99  fof(f46,plain,(
% 2.35/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.35/0.99    inference(cnf_transformation,[],[f17])).
% 2.35/0.99  
% 2.35/0.99  fof(f7,axiom,(
% 2.35/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.35/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.35/0.99  
% 2.35/0.99  fof(f49,plain,(
% 2.35/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.35/0.99    inference(cnf_transformation,[],[f7])).
% 2.35/0.99  
% 2.35/0.99  fof(f60,plain,(
% 2.35/0.99    r1_tarski(sK2,sK0)),
% 2.35/0.99    inference(cnf_transformation,[],[f36])).
% 2.35/0.99  
% 2.35/0.99  fof(f9,axiom,(
% 2.35/0.99    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 2.35/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.35/0.99  
% 2.35/0.99  fof(f20,plain,(
% 2.35/0.99    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 2.35/0.99    inference(ennf_transformation,[],[f9])).
% 2.35/0.99  
% 2.35/0.99  fof(f21,plain,(
% 2.35/0.99    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.35/0.99    inference(flattening,[],[f20])).
% 2.35/0.99  
% 2.35/0.99  fof(f51,plain,(
% 2.35/0.99    ( ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.35/0.99    inference(cnf_transformation,[],[f21])).
% 2.35/0.99  
% 2.35/0.99  fof(f11,axiom,(
% 2.35/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 2.35/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.35/0.99  
% 2.35/0.99  fof(f23,plain,(
% 2.35/0.99    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.35/0.99    inference(ennf_transformation,[],[f11])).
% 2.35/0.99  
% 2.35/0.99  fof(f53,plain,(
% 2.35/0.99    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.35/0.99    inference(cnf_transformation,[],[f23])).
% 2.35/0.99  
% 2.35/0.99  fof(f62,plain,(
% 2.35/0.99    ~r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2)))),
% 2.35/0.99    inference(cnf_transformation,[],[f36])).
% 2.35/0.99  
% 2.35/0.99  fof(f61,plain,(
% 2.35/0.99    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 2.35/0.99    inference(cnf_transformation,[],[f36])).
% 2.35/0.99  
% 2.35/0.99  fof(f2,axiom,(
% 2.35/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.35/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.35/0.99  
% 2.35/0.99  fof(f40,plain,(
% 2.35/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.35/0.99    inference(cnf_transformation,[],[f2])).
% 2.35/0.99  
% 2.35/0.99  fof(f41,plain,(
% 2.35/0.99    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 2.35/0.99    inference(cnf_transformation,[],[f32])).
% 2.35/0.99  
% 2.35/0.99  cnf(c_5,plain,
% 2.35/0.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.35/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_7,plain,
% 2.35/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.35/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1215,plain,
% 2.35/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 2.35/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 2.35/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_15,plain,
% 2.35/0.99      ( v4_relat_1(X0,X1)
% 2.35/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.35/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_11,plain,
% 2.35/0.99      ( ~ v4_relat_1(X0,X1)
% 2.35/0.99      | r1_tarski(k1_relat_1(X0),X1)
% 2.35/0.99      | ~ v1_relat_1(X0) ),
% 2.35/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_295,plain,
% 2.35/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.35/0.99      | r1_tarski(k1_relat_1(X0),X1)
% 2.35/0.99      | ~ v1_relat_1(X0) ),
% 2.35/0.99      inference(resolution,[status(thm)],[c_15,c_11]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1204,plain,
% 2.35/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.35/0.99      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 2.35/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.35/0.99      inference(predicate_to_equality,[status(thm)],[c_295]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1869,plain,
% 2.35/0.99      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 2.35/0.99      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 2.35/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.35/0.99      inference(superposition,[status(thm)],[c_1215,c_1204]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_3417,plain,
% 2.35/0.99      ( r1_tarski(X0,k1_xboole_0) != iProver_top
% 2.35/0.99      | r1_tarski(k1_relat_1(X0),k1_xboole_0) = iProver_top
% 2.35/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.35/0.99      inference(superposition,[status(thm)],[c_5,c_1869]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_0,plain,
% 2.35/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.35/0.99      inference(cnf_transformation,[],[f39]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1218,plain,
% 2.35/0.99      ( X0 = X1
% 2.35/0.99      | r1_tarski(X0,X1) != iProver_top
% 2.35/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 2.35/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_3755,plain,
% 2.35/0.99      ( k1_relat_1(X0) = k1_xboole_0
% 2.35/0.99      | r1_tarski(X0,k1_xboole_0) != iProver_top
% 2.35/0.99      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 2.35/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.35/0.99      inference(superposition,[status(thm)],[c_3417,c_1218]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_3774,plain,
% 2.35/0.99      ( k1_relat_1(k1_xboole_0) = k1_xboole_0
% 2.35/0.99      | r1_tarski(k1_xboole_0,k1_relat_1(k1_xboole_0)) != iProver_top
% 2.35/0.99      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 2.35/0.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 2.35/0.99      inference(instantiation,[status(thm)],[c_3755]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_19,plain,
% 2.35/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.35/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.35/0.99      | ~ v1_funct_1(X0)
% 2.35/0.99      | k8_relset_1(X1,X2,X0,X2) = X1
% 2.35/0.99      | k1_xboole_0 = X2 ),
% 2.35/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_24,negated_conjecture,
% 2.35/0.99      ( v1_funct_2(sK3,sK0,sK1) ),
% 2.35/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_331,plain,
% 2.35/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.35/0.99      | ~ v1_funct_1(X0)
% 2.35/0.99      | k8_relset_1(X1,X2,X0,X2) = X1
% 2.35/0.99      | sK3 != X0
% 2.35/0.99      | sK1 != X2
% 2.35/0.99      | sK0 != X1
% 2.35/0.99      | k1_xboole_0 = X2 ),
% 2.35/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_24]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_332,plain,
% 2.35/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.35/0.99      | ~ v1_funct_1(sK3)
% 2.35/0.99      | k8_relset_1(sK0,sK1,sK3,sK1) = sK0
% 2.35/0.99      | k1_xboole_0 = sK1 ),
% 2.35/0.99      inference(unflattening,[status(thm)],[c_331]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_25,negated_conjecture,
% 2.35/0.99      ( v1_funct_1(sK3) ),
% 2.35/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_23,negated_conjecture,
% 2.35/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.35/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_334,plain,
% 2.35/0.99      ( k8_relset_1(sK0,sK1,sK3,sK1) = sK0 | k1_xboole_0 = sK1 ),
% 2.35/0.99      inference(global_propositional_subsumption,
% 2.35/0.99                [status(thm)],
% 2.35/0.99                [c_332,c_25,c_23]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1206,plain,
% 2.35/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.35/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_17,plain,
% 2.35/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.35/0.99      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 2.35/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1209,plain,
% 2.35/0.99      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 2.35/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.35/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_2218,plain,
% 2.35/0.99      ( k8_relset_1(sK0,sK1,sK3,X0) = k10_relat_1(sK3,X0) ),
% 2.35/0.99      inference(superposition,[status(thm)],[c_1206,c_1209]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_2379,plain,
% 2.35/0.99      ( k10_relat_1(sK3,sK1) = sK0 | sK1 = k1_xboole_0 ),
% 2.35/0.99      inference(superposition,[status(thm)],[c_334,c_2218]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_13,plain,
% 2.35/0.99      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 2.35/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1212,plain,
% 2.35/0.99      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) = iProver_top
% 2.35/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.35/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_2589,plain,
% 2.35/0.99      ( sK1 = k1_xboole_0
% 2.35/0.99      | r1_tarski(sK0,k1_relat_1(sK3)) = iProver_top
% 2.35/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.35/0.99      inference(superposition,[status(thm)],[c_2379,c_1212]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_8,plain,
% 2.35/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.35/0.99      inference(cnf_transformation,[],[f44]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1214,plain,
% 2.35/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.35/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 2.35/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1798,plain,
% 2.35/0.99      ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 2.35/0.99      inference(superposition,[status(thm)],[c_1206,c_1214]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_9,plain,
% 2.35/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.35/0.99      | ~ v1_relat_1(X1)
% 2.35/0.99      | v1_relat_1(X0) ),
% 2.35/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_173,plain,
% 2.35/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.35/0.99      inference(prop_impl,[status(thm)],[c_7]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_174,plain,
% 2.35/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.35/0.99      inference(renaming,[status(thm)],[c_173]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_218,plain,
% 2.35/0.99      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 2.35/0.99      inference(bin_hyper_res,[status(thm)],[c_9,c_174]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1205,plain,
% 2.35/0.99      ( r1_tarski(X0,X1) != iProver_top
% 2.35/0.99      | v1_relat_1(X1) != iProver_top
% 2.35/0.99      | v1_relat_1(X0) = iProver_top ),
% 2.35/0.99      inference(predicate_to_equality,[status(thm)],[c_218]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1983,plain,
% 2.35/0.99      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 2.35/0.99      | v1_relat_1(sK3) = iProver_top ),
% 2.35/0.99      inference(superposition,[status(thm)],[c_1798,c_1205]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_12,plain,
% 2.35/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.35/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1213,plain,
% 2.35/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 2.35/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_2594,plain,
% 2.35/0.99      ( v1_relat_1(sK3) = iProver_top ),
% 2.35/0.99      inference(forward_subsumption_resolution,
% 2.35/0.99                [status(thm)],
% 2.35/0.99                [c_1983,c_1213]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_3048,plain,
% 2.35/0.99      ( r1_tarski(sK0,k1_relat_1(sK3)) = iProver_top
% 2.35/0.99      | sK1 = k1_xboole_0 ),
% 2.35/0.99      inference(global_propositional_subsumption,
% 2.35/0.99                [status(thm)],
% 2.35/0.99                [c_2589,c_2594]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_3049,plain,
% 2.35/0.99      ( sK1 = k1_xboole_0
% 2.35/0.99      | r1_tarski(sK0,k1_relat_1(sK3)) = iProver_top ),
% 2.35/0.99      inference(renaming,[status(thm)],[c_3048]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_3055,plain,
% 2.35/0.99      ( sK1 = k1_xboole_0
% 2.35/0.99      | v1_relat_1(k1_relat_1(sK3)) != iProver_top
% 2.35/0.99      | v1_relat_1(sK0) = iProver_top ),
% 2.35/0.99      inference(superposition,[status(thm)],[c_3049,c_1205]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_22,negated_conjecture,
% 2.35/0.99      ( r1_tarski(sK2,sK0) ),
% 2.35/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_29,plain,
% 2.35/0.99      ( r1_tarski(sK2,sK0) = iProver_top ),
% 2.35/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1558,plain,
% 2.35/0.99      ( r1_tarski(k1_relat_1(sK3),sK0) = iProver_top
% 2.35/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.35/0.99      inference(superposition,[status(thm)],[c_1206,c_1204]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_2171,plain,
% 2.35/0.99      ( k1_relat_1(sK3) = sK0
% 2.35/0.99      | r1_tarski(sK0,k1_relat_1(sK3)) != iProver_top
% 2.35/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.35/0.99      inference(superposition,[status(thm)],[c_1558,c_1218]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_2698,plain,
% 2.35/0.99      ( r1_tarski(sK0,k1_relat_1(sK3)) != iProver_top
% 2.35/0.99      | k1_relat_1(sK3) = sK0 ),
% 2.35/0.99      inference(global_propositional_subsumption,
% 2.35/0.99                [status(thm)],
% 2.35/0.99                [c_2171,c_2594]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_2699,plain,
% 2.35/0.99      ( k1_relat_1(sK3) = sK0
% 2.35/0.99      | r1_tarski(sK0,k1_relat_1(sK3)) != iProver_top ),
% 2.35/0.99      inference(renaming,[status(thm)],[c_2698]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_3056,plain,
% 2.35/0.99      ( k1_relat_1(sK3) = sK0 | sK1 = k1_xboole_0 ),
% 2.35/0.99      inference(superposition,[status(thm)],[c_3049,c_2699]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_14,plain,
% 2.35/0.99      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
% 2.35/0.99      | ~ r1_tarski(X0,k1_relat_1(X1))
% 2.35/0.99      | ~ v1_relat_1(X1) ),
% 2.35/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1211,plain,
% 2.35/0.99      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) = iProver_top
% 2.35/0.99      | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
% 2.35/0.99      | v1_relat_1(X1) != iProver_top ),
% 2.35/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_16,plain,
% 2.35/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.35/0.99      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 2.35/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1210,plain,
% 2.35/0.99      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 2.35/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.35/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_2794,plain,
% 2.35/0.99      ( k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
% 2.35/0.99      inference(superposition,[status(thm)],[c_1206,c_1210]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_20,negated_conjecture,
% 2.35/0.99      ( ~ r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2))) ),
% 2.35/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1208,plain,
% 2.35/0.99      ( r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2))) != iProver_top ),
% 2.35/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_2377,plain,
% 2.35/0.99      ( r1_tarski(sK2,k10_relat_1(sK3,k7_relset_1(sK0,sK1,sK3,sK2))) != iProver_top ),
% 2.35/0.99      inference(demodulation,[status(thm)],[c_2218,c_1208]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_2969,plain,
% 2.35/0.99      ( r1_tarski(sK2,k10_relat_1(sK3,k9_relat_1(sK3,sK2))) != iProver_top ),
% 2.35/0.99      inference(demodulation,[status(thm)],[c_2794,c_2377]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_2973,plain,
% 2.35/0.99      ( r1_tarski(sK2,k1_relat_1(sK3)) != iProver_top
% 2.35/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.35/0.99      inference(superposition,[status(thm)],[c_1211,c_2969]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_3069,plain,
% 2.35/0.99      ( r1_tarski(sK2,k1_relat_1(sK3)) != iProver_top ),
% 2.35/0.99      inference(global_propositional_subsumption,
% 2.35/0.99                [status(thm)],
% 2.35/0.99                [c_2973,c_2594]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_3138,plain,
% 2.35/0.99      ( sK1 = k1_xboole_0 | r1_tarski(sK2,sK0) != iProver_top ),
% 2.35/0.99      inference(superposition,[status(thm)],[c_3056,c_3069]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_3163,plain,
% 2.35/0.99      ( sK1 = k1_xboole_0 ),
% 2.35/0.99      inference(global_propositional_subsumption,
% 2.35/0.99                [status(thm)],
% 2.35/0.99                [c_3055,c_29,c_3138]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_2170,plain,
% 2.35/0.99      ( k2_zfmisc_1(sK0,sK1) = sK3
% 2.35/0.99      | r1_tarski(k2_zfmisc_1(sK0,sK1),sK3) != iProver_top ),
% 2.35/0.99      inference(superposition,[status(thm)],[c_1798,c_1218]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_3167,plain,
% 2.35/0.99      ( k2_zfmisc_1(sK0,k1_xboole_0) = sK3
% 2.35/0.99      | r1_tarski(k2_zfmisc_1(sK0,k1_xboole_0),sK3) != iProver_top ),
% 2.35/0.99      inference(demodulation,[status(thm)],[c_3163,c_2170]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_21,negated_conjecture,
% 2.35/0.99      ( k1_xboole_0 != sK1 | k1_xboole_0 = sK0 ),
% 2.35/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_3174,plain,
% 2.35/0.99      ( sK0 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 2.35/0.99      inference(demodulation,[status(thm)],[c_3163,c_21]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_3175,plain,
% 2.35/0.99      ( sK0 = k1_xboole_0 ),
% 2.35/0.99      inference(equality_resolution_simp,[status(thm)],[c_3174]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_3195,plain,
% 2.35/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = sK3
% 2.35/0.99      | r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),sK3) != iProver_top ),
% 2.35/0.99      inference(light_normalisation,[status(thm)],[c_3167,c_3175]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_3198,plain,
% 2.35/0.99      ( sK3 = k1_xboole_0 | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
% 2.35/0.99      inference(demodulation,[status(thm)],[c_3195,c_5]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_3,plain,
% 2.35/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 2.35/0.99      inference(cnf_transformation,[],[f40]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1216,plain,
% 2.35/0.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.35/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_3593,plain,
% 2.35/0.99      ( sK3 = k1_xboole_0 ),
% 2.35/0.99      inference(forward_subsumption_resolution,
% 2.35/0.99                [status(thm)],
% 2.35/0.99                [c_3198,c_1216]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_3596,plain,
% 2.35/0.99      ( r1_tarski(sK2,k1_relat_1(k1_xboole_0)) != iProver_top ),
% 2.35/0.99      inference(demodulation,[status(thm)],[c_3593,c_3069]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_793,plain,
% 2.35/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.35/0.99      theory(equality) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1529,plain,
% 2.35/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,sK2) | X2 != X0 | sK2 != X1 ),
% 2.35/0.99      inference(instantiation,[status(thm)],[c_793]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_2123,plain,
% 2.35/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(sK0,sK2) | sK0 != X0 | sK2 != X1 ),
% 2.35/0.99      inference(instantiation,[status(thm)],[c_1529]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_2825,plain,
% 2.35/0.99      ( ~ r1_tarski(X0,sK2)
% 2.35/0.99      | r1_tarski(sK0,sK2)
% 2.35/0.99      | sK0 != X0
% 2.35/0.99      | sK2 != sK2 ),
% 2.35/0.99      inference(instantiation,[status(thm)],[c_2123]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_2827,plain,
% 2.35/0.99      ( r1_tarski(sK0,sK2)
% 2.35/0.99      | ~ r1_tarski(k1_xboole_0,sK2)
% 2.35/0.99      | sK0 != k1_xboole_0
% 2.35/0.99      | sK2 != sK2 ),
% 2.35/0.99      inference(instantiation,[status(thm)],[c_2825]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_792,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1420,plain,
% 2.35/0.99      ( X0 != X1 | sK2 != X1 | sK2 = X0 ),
% 2.35/0.99      inference(instantiation,[status(thm)],[c_792]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_2606,plain,
% 2.35/0.99      ( X0 != sK0 | sK2 = X0 | sK2 != sK0 ),
% 2.35/0.99      inference(instantiation,[status(thm)],[c_1420]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_2607,plain,
% 2.35/0.99      ( sK2 != sK0 | sK2 = k1_xboole_0 | k1_xboole_0 != sK0 ),
% 2.35/0.99      inference(instantiation,[status(thm)],[c_2606]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1707,plain,
% 2.35/0.99      ( ~ r1_tarski(X0,X1)
% 2.35/0.99      | r1_tarski(X2,k1_relat_1(X3))
% 2.35/0.99      | X2 != X0
% 2.35/0.99      | k1_relat_1(X3) != X1 ),
% 2.35/0.99      inference(instantiation,[status(thm)],[c_793]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_2400,plain,
% 2.35/0.99      ( ~ r1_tarski(X0,X1)
% 2.35/0.99      | r1_tarski(sK2,k1_relat_1(X2))
% 2.35/0.99      | k1_relat_1(X2) != X1
% 2.35/0.99      | sK2 != X0 ),
% 2.35/0.99      inference(instantiation,[status(thm)],[c_1707]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_2401,plain,
% 2.35/0.99      ( k1_relat_1(X0) != X1
% 2.35/0.99      | sK2 != X2
% 2.35/0.99      | r1_tarski(X2,X1) != iProver_top
% 2.35/0.99      | r1_tarski(sK2,k1_relat_1(X0)) = iProver_top ),
% 2.35/0.99      inference(predicate_to_equality,[status(thm)],[c_2400]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_2403,plain,
% 2.35/0.99      ( k1_relat_1(k1_xboole_0) != k1_xboole_0
% 2.35/0.99      | sK2 != k1_xboole_0
% 2.35/0.99      | r1_tarski(sK2,k1_relat_1(k1_xboole_0)) = iProver_top
% 2.35/0.99      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 2.35/0.99      inference(instantiation,[status(thm)],[c_2401]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1409,plain,
% 2.35/0.99      ( ~ r1_tarski(X0,sK2) | ~ r1_tarski(sK2,X0) | sK2 = X0 ),
% 2.35/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1963,plain,
% 2.35/0.99      ( ~ r1_tarski(sK0,sK2) | ~ r1_tarski(sK2,sK0) | sK2 = sK0 ),
% 2.35/0.99      inference(instantiation,[status(thm)],[c_1409]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1689,plain,
% 2.35/0.99      ( r1_tarski(k1_xboole_0,k1_relat_1(X0)) ),
% 2.35/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1692,plain,
% 2.35/0.99      ( r1_tarski(k1_xboole_0,k1_relat_1(X0)) = iProver_top ),
% 2.35/0.99      inference(predicate_to_equality,[status(thm)],[c_1689]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1694,plain,
% 2.35/0.99      ( r1_tarski(k1_xboole_0,k1_relat_1(k1_xboole_0)) = iProver_top ),
% 2.35/0.99      inference(instantiation,[status(thm)],[c_1692]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1551,plain,
% 2.35/0.99      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 2.35/0.99      inference(instantiation,[status(thm)],[c_792]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1552,plain,
% 2.35/0.99      ( sK1 != k1_xboole_0
% 2.35/0.99      | k1_xboole_0 = sK1
% 2.35/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 2.35/0.99      inference(instantiation,[status(thm)],[c_1551]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1524,plain,
% 2.35/0.99      ( r1_tarski(k1_xboole_0,sK2) ),
% 2.35/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1442,plain,
% 2.35/0.99      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) ),
% 2.35/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1445,plain,
% 2.35/0.99      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) = iProver_top ),
% 2.35/0.99      inference(predicate_to_equality,[status(thm)],[c_1442]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1347,plain,
% 2.35/0.99      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 2.35/0.99      | v1_relat_1(X0)
% 2.35/0.99      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 2.35/0.99      inference(instantiation,[status(thm)],[c_218]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1441,plain,
% 2.35/0.99      ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1))
% 2.35/0.99      | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
% 2.35/0.99      | v1_relat_1(k1_xboole_0) ),
% 2.35/0.99      inference(instantiation,[status(thm)],[c_1347]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1443,plain,
% 2.35/0.99      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) != iProver_top
% 2.35/0.99      | v1_relat_1(k2_zfmisc_1(X0,X1)) != iProver_top
% 2.35/0.99      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 2.35/0.99      inference(predicate_to_equality,[status(thm)],[c_1441]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_791,plain,( X0 = X0 ),theory(equality) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1433,plain,
% 2.35/0.99      ( sK0 = sK0 ),
% 2.35/0.99      inference(instantiation,[status(thm)],[c_791]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1364,plain,
% 2.35/0.99      ( sK0 != X0 | sK0 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 2.35/0.99      inference(instantiation,[status(thm)],[c_792]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1432,plain,
% 2.35/0.99      ( sK0 != sK0 | sK0 = k1_xboole_0 | k1_xboole_0 != sK0 ),
% 2.35/0.99      inference(instantiation,[status(thm)],[c_1364]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1415,plain,
% 2.35/0.99      ( sK2 = sK2 ),
% 2.35/0.99      inference(instantiation,[status(thm)],[c_791]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_70,plain,
% 2.35/0.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.35/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_72,plain,
% 2.35/0.99      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 2.35/0.99      inference(instantiation,[status(thm)],[c_70]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_69,plain,
% 2.35/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 2.35/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_6,plain,
% 2.35/0.99      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 2.35/0.99      | k1_xboole_0 = X1
% 2.35/0.99      | k1_xboole_0 = X0 ),
% 2.35/0.99      inference(cnf_transformation,[],[f41]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_68,plain,
% 2.35/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 2.35/0.99      | k1_xboole_0 = k1_xboole_0 ),
% 2.35/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_52,plain,
% 2.35/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 2.35/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_3775,plain,
% 2.35/0.99      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 2.35/0.99      inference(grounding,
% 2.35/0.99                [status(thm)],
% 2.35/0.99                [c_1445:[bind(X1,$fot(k1_xboole_0)),
% 2.35/0.99                 bind(X0,$fot(k1_xboole_0))]]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_3776,plain,
% 2.35/0.99      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
% 2.35/0.99      | v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
% 2.35/0.99      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 2.35/0.99      inference(grounding,
% 2.35/0.99                [status(thm)],
% 2.35/0.99                [c_1443:[bind(X1,$fot(k1_xboole_0)),
% 2.35/0.99                 bind(X0,$fot(k1_xboole_0))]]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_3777,plain,
% 2.35/0.99      ( v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 2.35/0.99      inference(grounding,
% 2.35/0.99                [status(thm)],
% 2.35/0.99                [c_52:[bind(X1,$fot(k1_xboole_0)),
% 2.35/0.99                 bind(X0,$fot(k1_xboole_0))]]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(contradiction,plain,
% 2.35/0.99      ( $false ),
% 2.35/0.99      inference(minisat,
% 2.35/0.99                [status(thm)],
% 2.35/0.99                [c_3774,c_3596,c_3138,c_2827,c_2607,c_2403,c_1963,c_1694,
% 2.35/0.99                 c_1552,c_1524,c_3775,c_3776,c_1433,c_1432,c_1415,c_72,
% 2.35/0.99                 c_69,c_68,c_3777,c_21,c_29,c_22]) ).
% 2.35/0.99  
% 2.35/0.99  
% 2.35/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.35/0.99  
% 2.35/0.99  ------                               Statistics
% 2.35/0.99  
% 2.35/0.99  ------ General
% 2.35/0.99  
% 2.35/0.99  abstr_ref_over_cycles:                  0
% 2.35/0.99  abstr_ref_under_cycles:                 0
% 2.35/0.99  gc_basic_clause_elim:                   0
% 2.35/0.99  forced_gc_time:                         0
% 2.35/0.99  parsing_time:                           0.008
% 2.35/0.99  unif_index_cands_time:                  0.
% 2.35/0.99  unif_index_add_time:                    0.
% 2.35/0.99  orderings_time:                         0.
% 2.35/0.99  out_proof_time:                         0.009
% 2.35/0.99  total_time:                             0.136
% 2.35/0.99  num_of_symbols:                         49
% 2.35/0.99  num_of_terms:                           3397
% 2.35/0.99  
% 2.35/0.99  ------ Preprocessing
% 2.35/0.99  
% 2.35/0.99  num_of_splits:                          0
% 2.35/0.99  num_of_split_atoms:                     0
% 2.35/0.99  num_of_reused_defs:                     0
% 2.35/0.99  num_eq_ax_congr_red:                    14
% 2.35/0.99  num_of_sem_filtered_clauses:            1
% 2.35/0.99  num_of_subtypes:                        0
% 2.35/0.99  monotx_restored_types:                  0
% 2.35/0.99  sat_num_of_epr_types:                   0
% 2.35/0.99  sat_num_of_non_cyclic_types:            0
% 2.35/0.99  sat_guarded_non_collapsed_types:        0
% 2.35/0.99  num_pure_diseq_elim:                    0
% 2.35/0.99  simp_replaced_by:                       0
% 2.35/0.99  res_preprocessed:                       109
% 2.35/0.99  prep_upred:                             0
% 2.35/0.99  prep_unflattend:                        21
% 2.35/0.99  smt_new_axioms:                         0
% 2.35/0.99  pred_elim_cands:                        3
% 2.35/0.99  pred_elim:                              3
% 2.35/0.99  pred_elim_cl:                           4
% 2.35/0.99  pred_elim_cycles:                       5
% 2.35/0.99  merged_defs:                            8
% 2.35/0.99  merged_defs_ncl:                        0
% 2.35/0.99  bin_hyper_res:                          9
% 2.35/0.99  prep_cycles:                            4
% 2.35/0.99  pred_elim_time:                         0.006
% 2.35/0.99  splitting_time:                         0.
% 2.35/0.99  sem_filter_time:                        0.
% 2.35/0.99  monotx_time:                            0.
% 2.35/0.99  subtype_inf_time:                       0.
% 2.35/0.99  
% 2.35/0.99  ------ Problem properties
% 2.35/0.99  
% 2.35/0.99  clauses:                                21
% 2.35/0.99  conjectures:                            4
% 2.35/0.99  epr:                                    6
% 2.35/0.99  horn:                                   19
% 2.35/0.99  ground:                                 6
% 2.35/0.99  unary:                                  8
% 2.35/0.99  binary:                                 7
% 2.35/0.99  lits:                                   40
% 2.35/0.99  lits_eq:                                14
% 2.35/0.99  fd_pure:                                0
% 2.35/0.99  fd_pseudo:                              0
% 2.35/0.99  fd_cond:                                1
% 2.35/0.99  fd_pseudo_cond:                         1
% 2.35/0.99  ac_symbols:                             0
% 2.35/0.99  
% 2.35/0.99  ------ Propositional Solver
% 2.35/0.99  
% 2.35/0.99  prop_solver_calls:                      28
% 2.35/0.99  prop_fast_solver_calls:                 650
% 2.35/0.99  smt_solver_calls:                       0
% 2.35/0.99  smt_fast_solver_calls:                  0
% 2.35/0.99  prop_num_of_clauses:                    1336
% 2.35/0.99  prop_preprocess_simplified:             4153
% 2.35/0.99  prop_fo_subsumed:                       9
% 2.35/0.99  prop_solver_time:                       0.
% 2.35/0.99  smt_solver_time:                        0.
% 2.35/0.99  smt_fast_solver_time:                   0.
% 2.35/0.99  prop_fast_solver_time:                  0.
% 2.35/0.99  prop_unsat_core_time:                   0.
% 2.35/0.99  
% 2.35/0.99  ------ QBF
% 2.35/0.99  
% 2.35/0.99  qbf_q_res:                              0
% 2.35/0.99  qbf_num_tautologies:                    0
% 2.35/0.99  qbf_prep_cycles:                        0
% 2.35/0.99  
% 2.35/0.99  ------ BMC1
% 2.35/0.99  
% 2.35/0.99  bmc1_current_bound:                     -1
% 2.35/0.99  bmc1_last_solved_bound:                 -1
% 2.35/0.99  bmc1_unsat_core_size:                   -1
% 2.35/0.99  bmc1_unsat_core_parents_size:           -1
% 2.35/0.99  bmc1_merge_next_fun:                    0
% 2.35/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.35/0.99  
% 2.35/0.99  ------ Instantiation
% 2.35/0.99  
% 2.35/0.99  inst_num_of_clauses:                    397
% 2.35/0.99  inst_num_in_passive:                    55
% 2.35/0.99  inst_num_in_active:                     213
% 2.35/0.99  inst_num_in_unprocessed:                130
% 2.35/0.99  inst_num_of_loops:                      260
% 2.35/0.99  inst_num_of_learning_restarts:          0
% 2.35/0.99  inst_num_moves_active_passive:          44
% 2.35/0.99  inst_lit_activity:                      0
% 2.35/0.99  inst_lit_activity_moves:                0
% 2.35/0.99  inst_num_tautologies:                   0
% 2.35/0.99  inst_num_prop_implied:                  0
% 2.35/0.99  inst_num_existing_simplified:           0
% 2.35/0.99  inst_num_eq_res_simplified:             0
% 2.35/0.99  inst_num_child_elim:                    0
% 2.35/0.99  inst_num_of_dismatching_blockings:      113
% 2.35/0.99  inst_num_of_non_proper_insts:           440
% 2.35/0.99  inst_num_of_duplicates:                 0
% 2.35/0.99  inst_inst_num_from_inst_to_res:         0
% 2.35/0.99  inst_dismatching_checking_time:         0.
% 2.35/0.99  
% 2.35/0.99  ------ Resolution
% 2.35/0.99  
% 2.35/0.99  res_num_of_clauses:                     0
% 2.35/0.99  res_num_in_passive:                     0
% 2.35/0.99  res_num_in_active:                      0
% 2.35/0.99  res_num_of_loops:                       113
% 2.35/0.99  res_forward_subset_subsumed:            28
% 2.35/0.99  res_backward_subset_subsumed:           2
% 2.35/0.99  res_forward_subsumed:                   0
% 2.35/0.99  res_backward_subsumed:                  0
% 2.35/0.99  res_forward_subsumption_resolution:     0
% 2.35/0.99  res_backward_subsumption_resolution:    0
% 2.35/0.99  res_clause_to_clause_subsumption:       229
% 2.35/0.99  res_orphan_elimination:                 0
% 2.35/0.99  res_tautology_del:                      32
% 2.35/0.99  res_num_eq_res_simplified:              0
% 2.35/0.99  res_num_sel_changes:                    0
% 2.35/0.99  res_moves_from_active_to_pass:          0
% 2.35/0.99  
% 2.35/0.99  ------ Superposition
% 2.35/0.99  
% 2.35/0.99  sup_time_total:                         0.
% 2.35/0.99  sup_time_generating:                    0.
% 2.35/0.99  sup_time_sim_full:                      0.
% 2.35/0.99  sup_time_sim_immed:                     0.
% 2.35/0.99  
% 2.35/0.99  sup_num_of_clauses:                     59
% 2.35/0.99  sup_num_in_active:                      27
% 2.35/0.99  sup_num_in_passive:                     32
% 2.35/0.99  sup_num_of_loops:                       50
% 2.35/0.99  sup_fw_superposition:                   40
% 2.35/0.99  sup_bw_superposition:                   26
% 2.35/0.99  sup_immediate_simplified:               18
% 2.35/0.99  sup_given_eliminated:                   0
% 2.35/0.99  comparisons_done:                       0
% 2.35/0.99  comparisons_avoided:                    6
% 2.35/0.99  
% 2.35/0.99  ------ Simplifications
% 2.35/0.99  
% 2.35/0.99  
% 2.35/0.99  sim_fw_subset_subsumed:                 5
% 2.35/0.99  sim_bw_subset_subsumed:                 3
% 2.35/0.99  sim_fw_subsumed:                        3
% 2.35/0.99  sim_bw_subsumed:                        1
% 2.35/0.99  sim_fw_subsumption_res:                 3
% 2.35/0.99  sim_bw_subsumption_res:                 0
% 2.35/0.99  sim_tautology_del:                      3
% 2.35/0.99  sim_eq_tautology_del:                   4
% 2.35/0.99  sim_eq_res_simp:                        2
% 2.35/0.99  sim_fw_demodulated:                     4
% 2.35/0.99  sim_bw_demodulated:                     23
% 2.35/0.99  sim_light_normalised:                   6
% 2.35/0.99  sim_joinable_taut:                      0
% 2.35/0.99  sim_joinable_simp:                      0
% 2.35/0.99  sim_ac_normalised:                      0
% 2.35/0.99  sim_smt_subsumption:                    0
% 2.35/0.99  
%------------------------------------------------------------------------------
