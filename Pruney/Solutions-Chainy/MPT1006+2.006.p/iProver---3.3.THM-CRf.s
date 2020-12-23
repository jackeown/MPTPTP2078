%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:04:31 EST 2020

% Result     : Theorem 2.20s
% Output     : CNFRefutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 780 expanded)
%              Number of clauses        :  101 ( 310 expanded)
%              Number of leaves         :   17 ( 136 expanded)
%              Depth                    :   26
%              Number of atoms          :  423 (2503 expanded)
%              Number of equality atoms :  250 (1245 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f28])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f61,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f37])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        & v1_funct_2(X2,k1_xboole_0,X0)
        & v1_funct_1(X2) )
     => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
          & v1_funct_2(X2,k1_xboole_0,X0)
          & v1_funct_1(X2) )
       => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      & v1_funct_2(X2,k1_xboole_0,X0)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      & v1_funct_2(X2,k1_xboole_0,X0)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f31,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        & v1_funct_2(X2,k1_xboole_0,X0)
        & v1_funct_1(X2) )
   => ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
      & v1_funct_2(sK2,k1_xboole_0,sK0)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    & v1_funct_2(sK2,k1_xboole_0,sK0)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f31])).

fof(f58,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    inference(cnf_transformation,[],[f32])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f60,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f38])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f34,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

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

fof(f22,plain,(
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

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f66,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f48])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f56,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f40,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f59,plain,(
    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_6,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_885,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_883,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1645,plain,
    ( k8_relset_1(X0,X1,k1_xboole_0,X2) = k10_relat_1(k1_xboole_0,X2) ),
    inference(superposition,[status(thm)],[c_885,c_883])).

cnf(c_4,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X2) = k1_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_882,plain,
    ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2375,plain,
    ( k8_relset_1(k1_xboole_0,X0,X1,X0) = k1_relset_1(k1_xboole_0,X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_882])).

cnf(c_2450,plain,
    ( k8_relset_1(k1_xboole_0,X0,k1_xboole_0,X0) = k1_relset_1(k1_xboole_0,X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_885,c_2375])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_880,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_902,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_880,c_4])).

cnf(c_3,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_884,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1524,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_884])).

cnf(c_1634,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_902,c_1524])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_79,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1640,plain,
    ( v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1634])).

cnf(c_1869,plain,
    ( v1_xboole_0(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1634,c_79,c_1640])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_886,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1874,plain,
    ( sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1869,c_886])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_2,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_21,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_241,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | X1 != X2
    | k2_relat_1(X0) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_21])).

cnf(c_242,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_241])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_302,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_242,c_26])).

cnf(c_303,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),X0)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_302])).

cnf(c_325,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | k2_relat_1(sK2) != k1_xboole_0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_303])).

cnf(c_326,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),X0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relat_1(sK2) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_325])).

cnf(c_412,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | X4 != X1
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | k1_relat_1(sK2) != k1_xboole_0
    | k2_relat_1(sK2) != k1_xboole_0
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_326])).

cnf(c_413,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
    | k1_relset_1(k1_xboole_0,X2,sK2) = k1_xboole_0
    | k1_relat_1(sK2) != k1_xboole_0
    | k2_relat_1(sK2) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_412])).

cnf(c_567,plain,
    ( sP2_iProver_split
    | sP1_iProver_split
    | k1_relat_1(sK2) != k1_xboole_0
    | k2_relat_1(sK2) != k1_xboole_0 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_413])).

cnf(c_872,plain,
    ( k1_relat_1(sK2) != k1_xboole_0
    | k2_relat_1(sK2) != k1_xboole_0
    | sP2_iProver_split = iProver_top
    | sP1_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_567])).

cnf(c_597,plain,
    ( k1_relat_1(sK2) != k1_xboole_0
    | k2_relat_1(sK2) != k1_xboole_0
    | sP2_iProver_split = iProver_top
    | sP1_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_567])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_435,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | X5 != X2
    | k1_relset_1(X1,X2,X0) = X1
    | k1_relat_1(sK2) != X1
    | k2_relat_1(sK2) != k1_xboole_0
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_326])).

cnf(c_436,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X2)))
    | k1_relset_1(k1_relat_1(sK2),X2,sK2) = k1_relat_1(sK2)
    | k2_relat_1(sK2) != k1_xboole_0
    | k1_xboole_0 = X2 ),
    inference(unflattening,[status(thm)],[c_435])).

cnf(c_20,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_259,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | X1 != X2
    | k2_relat_1(X0) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_20])).

cnf(c_260,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_259])).

cnf(c_287,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_260,c_26])).

cnf(c_288,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X0)))
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_287])).

cnf(c_340,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X3)))
    | k2_relat_1(sK2) != k1_xboole_0
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_288])).

cnf(c_341,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X2)))
    | k2_relat_1(sK2) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_340])).

cnf(c_440,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k1_relset_1(k1_relat_1(sK2),X2,sK2) = k1_relat_1(sK2)
    | k2_relat_1(sK2) != k1_xboole_0
    | k1_xboole_0 = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_436,c_341])).

cnf(c_564,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_440])).

cnf(c_870,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_564])).

cnf(c_1235,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_870])).

cnf(c_1347,plain,
    ( sP2_iProver_split = iProver_top
    | k2_relat_1(sK2) != k1_xboole_0
    | k1_relat_1(sK2) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_872,c_597,c_902,c_1235])).

cnf(c_1348,plain,
    ( k1_relat_1(sK2) != k1_xboole_0
    | k2_relat_1(sK2) != k1_xboole_0
    | sP2_iProver_split = iProver_top ),
    inference(renaming,[status(thm)],[c_1347])).

cnf(c_1878,plain,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0
    | k2_relat_1(k1_xboole_0) != k1_xboole_0
    | sP2_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_1874,c_1348])).

cnf(c_7,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_8,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1925,plain,
    ( k1_xboole_0 != k1_xboole_0
    | sP2_iProver_split = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1878,c_7,c_8])).

cnf(c_1926,plain,
    ( sP2_iProver_split = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_1925])).

cnf(c_566,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | k1_relset_1(k1_xboole_0,X0,sK2) = k1_xboole_0
    | ~ sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP2_iProver_split])],[c_413])).

cnf(c_874,plain,
    ( k1_relset_1(k1_xboole_0,X0,sK2) = k1_xboole_0
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_566])).

cnf(c_977,plain,
    ( k1_relset_1(k1_xboole_0,X0,sK2) = k1_xboole_0
    | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_874,c_4])).

cnf(c_981,plain,
    ( k1_relset_1(k1_xboole_0,X0,sK2) = k1_xboole_0
    | sP2_iProver_split != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_977,c_902])).

cnf(c_1885,plain,
    ( k1_relset_1(k1_xboole_0,X0,k1_xboole_0) = k1_xboole_0
    | sP2_iProver_split != iProver_top ),
    inference(demodulation,[status(thm)],[c_1874,c_981])).

cnf(c_1928,plain,
    ( k1_relset_1(k1_xboole_0,X0,k1_xboole_0) = k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1926,c_1885])).

cnf(c_2451,plain,
    ( k8_relset_1(k1_xboole_0,X0,k1_xboole_0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2450,c_1928])).

cnf(c_2522,plain,
    ( k10_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1645,c_2451])).

cnf(c_569,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X0)))
    | ~ sP3_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP3_iProver_split])],[c_341])).

cnf(c_879,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X0))) = iProver_top
    | sP3_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_569])).

cnf(c_1646,plain,
    ( k8_relset_1(k1_relat_1(sK2),X0,sK2,X1) = k10_relat_1(sK2,X1)
    | sP3_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_879,c_883])).

cnf(c_5,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_71,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_72,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_570,plain,
    ( sP3_iProver_split
    | sP1_iProver_split
    | k2_relat_1(sK2) != k1_xboole_0 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_341])).

cnf(c_604,plain,
    ( k2_relat_1(sK2) != k1_xboole_0
    | sP3_iProver_split = iProver_top
    | sP1_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_570])).

cnf(c_1107,plain,
    ( ~ v1_xboole_0(sK2)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1110,plain,
    ( k1_xboole_0 = sK2
    | v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1107])).

cnf(c_572,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1113,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_572])).

cnf(c_573,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1033,plain,
    ( k2_relat_1(sK2) != X0
    | k2_relat_1(sK2) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_573])).

cnf(c_1123,plain,
    ( k2_relat_1(sK2) != k2_relat_1(X0)
    | k2_relat_1(sK2) = k1_xboole_0
    | k1_xboole_0 != k2_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_1033])).

cnf(c_1125,plain,
    ( k2_relat_1(sK2) != k2_relat_1(k1_xboole_0)
    | k2_relat_1(sK2) = k1_xboole_0
    | k1_xboole_0 != k2_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1123])).

cnf(c_578,plain,
    ( X0 != X1
    | k2_relat_1(X0) = k2_relat_1(X1) ),
    theory(equality)).

cnf(c_1124,plain,
    ( k2_relat_1(sK2) = k2_relat_1(X0)
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_578])).

cnf(c_1126,plain,
    ( k2_relat_1(sK2) = k2_relat_1(k1_xboole_0)
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1124])).

cnf(c_1261,plain,
    ( k2_relat_1(X0) != X1
    | k1_xboole_0 != X1
    | k1_xboole_0 = k2_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_573])).

cnf(c_1262,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1261])).

cnf(c_1215,plain,
    ( X0 != X1
    | sK2 != X1
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_573])).

cnf(c_1687,plain,
    ( X0 != sK2
    | sK2 = X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1215])).

cnf(c_1688,plain,
    ( sK2 != sK2
    | sK2 = k1_xboole_0
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_1687])).

cnf(c_1994,plain,
    ( k8_relset_1(k1_relat_1(sK2),X0,sK2,X1) = k10_relat_1(sK2,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1646,c_7,c_71,c_72,c_79,c_604,c_902,c_1110,c_1113,c_1125,c_1126,c_1235,c_1262,c_1640,c_1688])).

cnf(c_1997,plain,
    ( k8_relset_1(k1_xboole_0,X0,k1_xboole_0,X1) = k10_relat_1(k1_xboole_0,X1) ),
    inference(light_normalisation,[status(thm)],[c_1994,c_8,c_1874])).

cnf(c_23,negated_conjecture,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1888,plain,
    ( k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1874,c_23])).

cnf(c_1999,plain,
    ( k10_relat_1(k1_xboole_0,sK1) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1997,c_1888])).

cnf(c_2530,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2522,c_1999])).

cnf(c_2531,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_2530])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:05:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.20/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.00  
% 2.20/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.20/1.00  
% 2.20/1.00  ------  iProver source info
% 2.20/1.00  
% 2.20/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.20/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.20/1.00  git: non_committed_changes: false
% 2.20/1.00  git: last_make_outside_of_git: false
% 2.20/1.00  
% 2.20/1.00  ------ 
% 2.20/1.00  
% 2.20/1.00  ------ Input Options
% 2.20/1.00  
% 2.20/1.00  --out_options                           all
% 2.20/1.00  --tptp_safe_out                         true
% 2.20/1.00  --problem_path                          ""
% 2.20/1.00  --include_path                          ""
% 2.20/1.00  --clausifier                            res/vclausify_rel
% 2.20/1.00  --clausifier_options                    --mode clausify
% 2.20/1.00  --stdin                                 false
% 2.20/1.00  --stats_out                             all
% 2.20/1.00  
% 2.20/1.00  ------ General Options
% 2.20/1.00  
% 2.20/1.00  --fof                                   false
% 2.20/1.00  --time_out_real                         305.
% 2.20/1.00  --time_out_virtual                      -1.
% 2.20/1.00  --symbol_type_check                     false
% 2.20/1.00  --clausify_out                          false
% 2.20/1.00  --sig_cnt_out                           false
% 2.20/1.00  --trig_cnt_out                          false
% 2.20/1.00  --trig_cnt_out_tolerance                1.
% 2.20/1.00  --trig_cnt_out_sk_spl                   false
% 2.20/1.00  --abstr_cl_out                          false
% 2.20/1.00  
% 2.20/1.00  ------ Global Options
% 2.20/1.00  
% 2.20/1.00  --schedule                              default
% 2.20/1.00  --add_important_lit                     false
% 2.20/1.00  --prop_solver_per_cl                    1000
% 2.20/1.00  --min_unsat_core                        false
% 2.20/1.00  --soft_assumptions                      false
% 2.20/1.00  --soft_lemma_size                       3
% 2.20/1.00  --prop_impl_unit_size                   0
% 2.20/1.00  --prop_impl_unit                        []
% 2.20/1.00  --share_sel_clauses                     true
% 2.20/1.00  --reset_solvers                         false
% 2.20/1.00  --bc_imp_inh                            [conj_cone]
% 2.20/1.00  --conj_cone_tolerance                   3.
% 2.20/1.00  --extra_neg_conj                        none
% 2.20/1.00  --large_theory_mode                     true
% 2.20/1.00  --prolific_symb_bound                   200
% 2.20/1.00  --lt_threshold                          2000
% 2.20/1.00  --clause_weak_htbl                      true
% 2.20/1.00  --gc_record_bc_elim                     false
% 2.20/1.00  
% 2.20/1.00  ------ Preprocessing Options
% 2.20/1.00  
% 2.20/1.00  --preprocessing_flag                    true
% 2.20/1.00  --time_out_prep_mult                    0.1
% 2.20/1.00  --splitting_mode                        input
% 2.20/1.00  --splitting_grd                         true
% 2.20/1.00  --splitting_cvd                         false
% 2.20/1.00  --splitting_cvd_svl                     false
% 2.20/1.00  --splitting_nvd                         32
% 2.20/1.00  --sub_typing                            true
% 2.20/1.00  --prep_gs_sim                           true
% 2.20/1.00  --prep_unflatten                        true
% 2.20/1.00  --prep_res_sim                          true
% 2.20/1.00  --prep_upred                            true
% 2.20/1.00  --prep_sem_filter                       exhaustive
% 2.20/1.00  --prep_sem_filter_out                   false
% 2.20/1.00  --pred_elim                             true
% 2.20/1.00  --res_sim_input                         true
% 2.20/1.00  --eq_ax_congr_red                       true
% 2.20/1.00  --pure_diseq_elim                       true
% 2.20/1.00  --brand_transform                       false
% 2.20/1.00  --non_eq_to_eq                          false
% 2.20/1.00  --prep_def_merge                        true
% 2.20/1.00  --prep_def_merge_prop_impl              false
% 2.20/1.00  --prep_def_merge_mbd                    true
% 2.20/1.00  --prep_def_merge_tr_red                 false
% 2.20/1.00  --prep_def_merge_tr_cl                  false
% 2.20/1.00  --smt_preprocessing                     true
% 2.20/1.00  --smt_ac_axioms                         fast
% 2.20/1.00  --preprocessed_out                      false
% 2.20/1.00  --preprocessed_stats                    false
% 2.20/1.00  
% 2.20/1.00  ------ Abstraction refinement Options
% 2.20/1.00  
% 2.20/1.00  --abstr_ref                             []
% 2.20/1.00  --abstr_ref_prep                        false
% 2.20/1.00  --abstr_ref_until_sat                   false
% 2.20/1.00  --abstr_ref_sig_restrict                funpre
% 2.20/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.20/1.00  --abstr_ref_under                       []
% 2.20/1.00  
% 2.20/1.00  ------ SAT Options
% 2.20/1.00  
% 2.20/1.00  --sat_mode                              false
% 2.20/1.00  --sat_fm_restart_options                ""
% 2.20/1.00  --sat_gr_def                            false
% 2.20/1.00  --sat_epr_types                         true
% 2.20/1.00  --sat_non_cyclic_types                  false
% 2.20/1.00  --sat_finite_models                     false
% 2.20/1.00  --sat_fm_lemmas                         false
% 2.20/1.00  --sat_fm_prep                           false
% 2.20/1.00  --sat_fm_uc_incr                        true
% 2.20/1.00  --sat_out_model                         small
% 2.20/1.00  --sat_out_clauses                       false
% 2.20/1.00  
% 2.20/1.00  ------ QBF Options
% 2.20/1.00  
% 2.20/1.00  --qbf_mode                              false
% 2.20/1.00  --qbf_elim_univ                         false
% 2.20/1.00  --qbf_dom_inst                          none
% 2.20/1.00  --qbf_dom_pre_inst                      false
% 2.20/1.00  --qbf_sk_in                             false
% 2.20/1.00  --qbf_pred_elim                         true
% 2.20/1.00  --qbf_split                             512
% 2.20/1.00  
% 2.20/1.00  ------ BMC1 Options
% 2.20/1.00  
% 2.20/1.00  --bmc1_incremental                      false
% 2.20/1.00  --bmc1_axioms                           reachable_all
% 2.20/1.00  --bmc1_min_bound                        0
% 2.20/1.00  --bmc1_max_bound                        -1
% 2.20/1.00  --bmc1_max_bound_default                -1
% 2.20/1.00  --bmc1_symbol_reachability              true
% 2.20/1.00  --bmc1_property_lemmas                  false
% 2.20/1.00  --bmc1_k_induction                      false
% 2.20/1.00  --bmc1_non_equiv_states                 false
% 2.20/1.00  --bmc1_deadlock                         false
% 2.20/1.00  --bmc1_ucm                              false
% 2.20/1.00  --bmc1_add_unsat_core                   none
% 2.20/1.00  --bmc1_unsat_core_children              false
% 2.20/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.20/1.00  --bmc1_out_stat                         full
% 2.20/1.00  --bmc1_ground_init                      false
% 2.20/1.00  --bmc1_pre_inst_next_state              false
% 2.20/1.00  --bmc1_pre_inst_state                   false
% 2.20/1.00  --bmc1_pre_inst_reach_state             false
% 2.20/1.00  --bmc1_out_unsat_core                   false
% 2.20/1.00  --bmc1_aig_witness_out                  false
% 2.20/1.00  --bmc1_verbose                          false
% 2.20/1.00  --bmc1_dump_clauses_tptp                false
% 2.20/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.20/1.00  --bmc1_dump_file                        -
% 2.20/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.20/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.20/1.00  --bmc1_ucm_extend_mode                  1
% 2.20/1.00  --bmc1_ucm_init_mode                    2
% 2.20/1.00  --bmc1_ucm_cone_mode                    none
% 2.20/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.20/1.00  --bmc1_ucm_relax_model                  4
% 2.20/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.20/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.20/1.00  --bmc1_ucm_layered_model                none
% 2.20/1.00  --bmc1_ucm_max_lemma_size               10
% 2.20/1.00  
% 2.20/1.00  ------ AIG Options
% 2.20/1.00  
% 2.20/1.00  --aig_mode                              false
% 2.20/1.00  
% 2.20/1.00  ------ Instantiation Options
% 2.20/1.00  
% 2.20/1.00  --instantiation_flag                    true
% 2.20/1.00  --inst_sos_flag                         false
% 2.20/1.00  --inst_sos_phase                        true
% 2.20/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.20/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.20/1.00  --inst_lit_sel_side                     num_symb
% 2.20/1.00  --inst_solver_per_active                1400
% 2.20/1.00  --inst_solver_calls_frac                1.
% 2.20/1.00  --inst_passive_queue_type               priority_queues
% 2.20/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.20/1.00  --inst_passive_queues_freq              [25;2]
% 2.20/1.00  --inst_dismatching                      true
% 2.20/1.00  --inst_eager_unprocessed_to_passive     true
% 2.20/1.00  --inst_prop_sim_given                   true
% 2.20/1.00  --inst_prop_sim_new                     false
% 2.20/1.00  --inst_subs_new                         false
% 2.20/1.00  --inst_eq_res_simp                      false
% 2.20/1.00  --inst_subs_given                       false
% 2.20/1.00  --inst_orphan_elimination               true
% 2.20/1.00  --inst_learning_loop_flag               true
% 2.20/1.00  --inst_learning_start                   3000
% 2.20/1.00  --inst_learning_factor                  2
% 2.20/1.00  --inst_start_prop_sim_after_learn       3
% 2.20/1.00  --inst_sel_renew                        solver
% 2.20/1.00  --inst_lit_activity_flag                true
% 2.20/1.00  --inst_restr_to_given                   false
% 2.20/1.00  --inst_activity_threshold               500
% 2.20/1.00  --inst_out_proof                        true
% 2.20/1.00  
% 2.20/1.00  ------ Resolution Options
% 2.20/1.00  
% 2.20/1.00  --resolution_flag                       true
% 2.20/1.00  --res_lit_sel                           adaptive
% 2.20/1.00  --res_lit_sel_side                      none
% 2.20/1.00  --res_ordering                          kbo
% 2.20/1.00  --res_to_prop_solver                    active
% 2.20/1.00  --res_prop_simpl_new                    false
% 2.20/1.00  --res_prop_simpl_given                  true
% 2.20/1.00  --res_passive_queue_type                priority_queues
% 2.20/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.20/1.00  --res_passive_queues_freq               [15;5]
% 2.20/1.00  --res_forward_subs                      full
% 2.20/1.00  --res_backward_subs                     full
% 2.20/1.00  --res_forward_subs_resolution           true
% 2.20/1.00  --res_backward_subs_resolution          true
% 2.20/1.00  --res_orphan_elimination                true
% 2.20/1.00  --res_time_limit                        2.
% 2.20/1.00  --res_out_proof                         true
% 2.20/1.00  
% 2.20/1.00  ------ Superposition Options
% 2.20/1.00  
% 2.20/1.00  --superposition_flag                    true
% 2.20/1.00  --sup_passive_queue_type                priority_queues
% 2.20/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.20/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.20/1.00  --demod_completeness_check              fast
% 2.20/1.00  --demod_use_ground                      true
% 2.20/1.00  --sup_to_prop_solver                    passive
% 2.20/1.00  --sup_prop_simpl_new                    true
% 2.20/1.00  --sup_prop_simpl_given                  true
% 2.20/1.00  --sup_fun_splitting                     false
% 2.20/1.00  --sup_smt_interval                      50000
% 2.20/1.00  
% 2.20/1.00  ------ Superposition Simplification Setup
% 2.20/1.00  
% 2.20/1.00  --sup_indices_passive                   []
% 2.20/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.20/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.20/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.20/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.20/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.20/1.00  --sup_full_bw                           [BwDemod]
% 2.20/1.00  --sup_immed_triv                        [TrivRules]
% 2.20/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.20/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.20/1.00  --sup_immed_bw_main                     []
% 2.20/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.20/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.20/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.20/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.20/1.00  
% 2.20/1.00  ------ Combination Options
% 2.20/1.00  
% 2.20/1.00  --comb_res_mult                         3
% 2.20/1.00  --comb_sup_mult                         2
% 2.20/1.00  --comb_inst_mult                        10
% 2.20/1.00  
% 2.20/1.00  ------ Debug Options
% 2.20/1.00  
% 2.20/1.00  --dbg_backtrace                         false
% 2.20/1.00  --dbg_dump_prop_clauses                 false
% 2.20/1.00  --dbg_dump_prop_clauses_file            -
% 2.20/1.00  --dbg_out_stat                          false
% 2.20/1.00  ------ Parsing...
% 2.20/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.20/1.00  
% 2.20/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.20/1.00  
% 2.20/1.00  ------ Preprocessing... gs_s  sp: 7 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.20/1.00  
% 2.20/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.20/1.00  ------ Proving...
% 2.20/1.00  ------ Problem Properties 
% 2.20/1.00  
% 2.20/1.00  
% 2.20/1.00  clauses                                 26
% 2.20/1.00  conjectures                             2
% 2.20/1.00  EPR                                     2
% 2.20/1.00  Horn                                    20
% 2.20/1.00  unary                                   9
% 2.20/1.00  binary                                  9
% 2.20/1.00  lits                                    53
% 2.20/1.00  lits eq                                 23
% 2.20/1.00  fd_pure                                 0
% 2.20/1.00  fd_pseudo                               0
% 2.20/1.00  fd_cond                                 3
% 2.20/1.00  fd_pseudo_cond                          0
% 2.20/1.00  AC symbols                              0
% 2.20/1.00  
% 2.20/1.00  ------ Schedule dynamic 5 is on 
% 2.20/1.00  
% 2.20/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.20/1.00  
% 2.20/1.00  
% 2.20/1.00  ------ 
% 2.20/1.00  Current options:
% 2.20/1.00  ------ 
% 2.20/1.00  
% 2.20/1.00  ------ Input Options
% 2.20/1.00  
% 2.20/1.00  --out_options                           all
% 2.20/1.00  --tptp_safe_out                         true
% 2.20/1.00  --problem_path                          ""
% 2.20/1.00  --include_path                          ""
% 2.20/1.00  --clausifier                            res/vclausify_rel
% 2.20/1.00  --clausifier_options                    --mode clausify
% 2.20/1.00  --stdin                                 false
% 2.20/1.00  --stats_out                             all
% 2.20/1.00  
% 2.20/1.00  ------ General Options
% 2.20/1.00  
% 2.20/1.00  --fof                                   false
% 2.20/1.00  --time_out_real                         305.
% 2.20/1.00  --time_out_virtual                      -1.
% 2.20/1.00  --symbol_type_check                     false
% 2.20/1.00  --clausify_out                          false
% 2.20/1.00  --sig_cnt_out                           false
% 2.20/1.00  --trig_cnt_out                          false
% 2.20/1.00  --trig_cnt_out_tolerance                1.
% 2.20/1.00  --trig_cnt_out_sk_spl                   false
% 2.20/1.00  --abstr_cl_out                          false
% 2.20/1.00  
% 2.20/1.00  ------ Global Options
% 2.20/1.00  
% 2.20/1.00  --schedule                              default
% 2.20/1.00  --add_important_lit                     false
% 2.20/1.00  --prop_solver_per_cl                    1000
% 2.20/1.00  --min_unsat_core                        false
% 2.20/1.00  --soft_assumptions                      false
% 2.20/1.00  --soft_lemma_size                       3
% 2.20/1.00  --prop_impl_unit_size                   0
% 2.20/1.00  --prop_impl_unit                        []
% 2.20/1.00  --share_sel_clauses                     true
% 2.20/1.00  --reset_solvers                         false
% 2.20/1.00  --bc_imp_inh                            [conj_cone]
% 2.20/1.00  --conj_cone_tolerance                   3.
% 2.20/1.00  --extra_neg_conj                        none
% 2.20/1.00  --large_theory_mode                     true
% 2.20/1.00  --prolific_symb_bound                   200
% 2.20/1.00  --lt_threshold                          2000
% 2.20/1.00  --clause_weak_htbl                      true
% 2.20/1.00  --gc_record_bc_elim                     false
% 2.20/1.00  
% 2.20/1.00  ------ Preprocessing Options
% 2.20/1.00  
% 2.20/1.00  --preprocessing_flag                    true
% 2.20/1.00  --time_out_prep_mult                    0.1
% 2.20/1.00  --splitting_mode                        input
% 2.20/1.00  --splitting_grd                         true
% 2.20/1.00  --splitting_cvd                         false
% 2.20/1.00  --splitting_cvd_svl                     false
% 2.20/1.00  --splitting_nvd                         32
% 2.20/1.00  --sub_typing                            true
% 2.20/1.00  --prep_gs_sim                           true
% 2.20/1.00  --prep_unflatten                        true
% 2.20/1.00  --prep_res_sim                          true
% 2.20/1.00  --prep_upred                            true
% 2.20/1.00  --prep_sem_filter                       exhaustive
% 2.20/1.00  --prep_sem_filter_out                   false
% 2.20/1.00  --pred_elim                             true
% 2.20/1.00  --res_sim_input                         true
% 2.20/1.00  --eq_ax_congr_red                       true
% 2.20/1.00  --pure_diseq_elim                       true
% 2.20/1.00  --brand_transform                       false
% 2.20/1.00  --non_eq_to_eq                          false
% 2.20/1.00  --prep_def_merge                        true
% 2.20/1.00  --prep_def_merge_prop_impl              false
% 2.20/1.00  --prep_def_merge_mbd                    true
% 2.20/1.00  --prep_def_merge_tr_red                 false
% 2.20/1.00  --prep_def_merge_tr_cl                  false
% 2.20/1.00  --smt_preprocessing                     true
% 2.20/1.00  --smt_ac_axioms                         fast
% 2.20/1.00  --preprocessed_out                      false
% 2.20/1.00  --preprocessed_stats                    false
% 2.20/1.00  
% 2.20/1.00  ------ Abstraction refinement Options
% 2.20/1.00  
% 2.20/1.00  --abstr_ref                             []
% 2.20/1.00  --abstr_ref_prep                        false
% 2.20/1.00  --abstr_ref_until_sat                   false
% 2.20/1.00  --abstr_ref_sig_restrict                funpre
% 2.20/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.20/1.00  --abstr_ref_under                       []
% 2.20/1.00  
% 2.20/1.00  ------ SAT Options
% 2.20/1.00  
% 2.20/1.00  --sat_mode                              false
% 2.20/1.00  --sat_fm_restart_options                ""
% 2.20/1.00  --sat_gr_def                            false
% 2.20/1.00  --sat_epr_types                         true
% 2.20/1.00  --sat_non_cyclic_types                  false
% 2.20/1.00  --sat_finite_models                     false
% 2.20/1.00  --sat_fm_lemmas                         false
% 2.20/1.00  --sat_fm_prep                           false
% 2.20/1.00  --sat_fm_uc_incr                        true
% 2.20/1.00  --sat_out_model                         small
% 2.20/1.00  --sat_out_clauses                       false
% 2.20/1.00  
% 2.20/1.00  ------ QBF Options
% 2.20/1.00  
% 2.20/1.00  --qbf_mode                              false
% 2.20/1.00  --qbf_elim_univ                         false
% 2.20/1.00  --qbf_dom_inst                          none
% 2.20/1.00  --qbf_dom_pre_inst                      false
% 2.20/1.00  --qbf_sk_in                             false
% 2.20/1.00  --qbf_pred_elim                         true
% 2.20/1.00  --qbf_split                             512
% 2.20/1.00  
% 2.20/1.00  ------ BMC1 Options
% 2.20/1.00  
% 2.20/1.00  --bmc1_incremental                      false
% 2.20/1.00  --bmc1_axioms                           reachable_all
% 2.20/1.00  --bmc1_min_bound                        0
% 2.20/1.00  --bmc1_max_bound                        -1
% 2.20/1.00  --bmc1_max_bound_default                -1
% 2.20/1.00  --bmc1_symbol_reachability              true
% 2.20/1.00  --bmc1_property_lemmas                  false
% 2.20/1.00  --bmc1_k_induction                      false
% 2.20/1.00  --bmc1_non_equiv_states                 false
% 2.20/1.00  --bmc1_deadlock                         false
% 2.20/1.00  --bmc1_ucm                              false
% 2.20/1.00  --bmc1_add_unsat_core                   none
% 2.20/1.00  --bmc1_unsat_core_children              false
% 2.20/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.20/1.00  --bmc1_out_stat                         full
% 2.20/1.00  --bmc1_ground_init                      false
% 2.20/1.00  --bmc1_pre_inst_next_state              false
% 2.20/1.00  --bmc1_pre_inst_state                   false
% 2.20/1.00  --bmc1_pre_inst_reach_state             false
% 2.20/1.00  --bmc1_out_unsat_core                   false
% 2.20/1.00  --bmc1_aig_witness_out                  false
% 2.20/1.00  --bmc1_verbose                          false
% 2.20/1.00  --bmc1_dump_clauses_tptp                false
% 2.20/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.20/1.00  --bmc1_dump_file                        -
% 2.20/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.20/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.20/1.00  --bmc1_ucm_extend_mode                  1
% 2.20/1.00  --bmc1_ucm_init_mode                    2
% 2.20/1.00  --bmc1_ucm_cone_mode                    none
% 2.20/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.20/1.00  --bmc1_ucm_relax_model                  4
% 2.20/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.20/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.20/1.00  --bmc1_ucm_layered_model                none
% 2.20/1.00  --bmc1_ucm_max_lemma_size               10
% 2.20/1.00  
% 2.20/1.00  ------ AIG Options
% 2.20/1.00  
% 2.20/1.00  --aig_mode                              false
% 2.20/1.00  
% 2.20/1.00  ------ Instantiation Options
% 2.20/1.00  
% 2.20/1.00  --instantiation_flag                    true
% 2.20/1.00  --inst_sos_flag                         false
% 2.20/1.00  --inst_sos_phase                        true
% 2.20/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.20/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.20/1.00  --inst_lit_sel_side                     none
% 2.20/1.00  --inst_solver_per_active                1400
% 2.20/1.00  --inst_solver_calls_frac                1.
% 2.20/1.00  --inst_passive_queue_type               priority_queues
% 2.20/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.20/1.00  --inst_passive_queues_freq              [25;2]
% 2.20/1.00  --inst_dismatching                      true
% 2.20/1.00  --inst_eager_unprocessed_to_passive     true
% 2.20/1.00  --inst_prop_sim_given                   true
% 2.20/1.00  --inst_prop_sim_new                     false
% 2.20/1.00  --inst_subs_new                         false
% 2.20/1.00  --inst_eq_res_simp                      false
% 2.20/1.00  --inst_subs_given                       false
% 2.20/1.00  --inst_orphan_elimination               true
% 2.20/1.00  --inst_learning_loop_flag               true
% 2.20/1.00  --inst_learning_start                   3000
% 2.20/1.00  --inst_learning_factor                  2
% 2.20/1.00  --inst_start_prop_sim_after_learn       3
% 2.20/1.00  --inst_sel_renew                        solver
% 2.20/1.00  --inst_lit_activity_flag                true
% 2.20/1.00  --inst_restr_to_given                   false
% 2.20/1.00  --inst_activity_threshold               500
% 2.20/1.00  --inst_out_proof                        true
% 2.20/1.00  
% 2.20/1.00  ------ Resolution Options
% 2.20/1.00  
% 2.20/1.00  --resolution_flag                       false
% 2.20/1.00  --res_lit_sel                           adaptive
% 2.20/1.00  --res_lit_sel_side                      none
% 2.20/1.00  --res_ordering                          kbo
% 2.20/1.00  --res_to_prop_solver                    active
% 2.20/1.00  --res_prop_simpl_new                    false
% 2.20/1.00  --res_prop_simpl_given                  true
% 2.20/1.00  --res_passive_queue_type                priority_queues
% 2.20/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.20/1.00  --res_passive_queues_freq               [15;5]
% 2.20/1.00  --res_forward_subs                      full
% 2.20/1.00  --res_backward_subs                     full
% 2.20/1.00  --res_forward_subs_resolution           true
% 2.20/1.00  --res_backward_subs_resolution          true
% 2.20/1.00  --res_orphan_elimination                true
% 2.20/1.00  --res_time_limit                        2.
% 2.20/1.00  --res_out_proof                         true
% 2.20/1.00  
% 2.20/1.00  ------ Superposition Options
% 2.20/1.00  
% 2.20/1.00  --superposition_flag                    true
% 2.20/1.00  --sup_passive_queue_type                priority_queues
% 2.20/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.20/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.20/1.00  --demod_completeness_check              fast
% 2.20/1.00  --demod_use_ground                      true
% 2.20/1.00  --sup_to_prop_solver                    passive
% 2.20/1.00  --sup_prop_simpl_new                    true
% 2.20/1.00  --sup_prop_simpl_given                  true
% 2.20/1.00  --sup_fun_splitting                     false
% 2.20/1.00  --sup_smt_interval                      50000
% 2.20/1.00  
% 2.20/1.00  ------ Superposition Simplification Setup
% 2.20/1.00  
% 2.20/1.00  --sup_indices_passive                   []
% 2.20/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.20/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.20/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.20/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.20/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.20/1.00  --sup_full_bw                           [BwDemod]
% 2.20/1.00  --sup_immed_triv                        [TrivRules]
% 2.20/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.20/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.20/1.00  --sup_immed_bw_main                     []
% 2.20/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.20/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.20/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.20/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.20/1.00  
% 2.20/1.00  ------ Combination Options
% 2.20/1.00  
% 2.20/1.00  --comb_res_mult                         3
% 2.20/1.00  --comb_sup_mult                         2
% 2.20/1.00  --comb_inst_mult                        10
% 2.20/1.00  
% 2.20/1.00  ------ Debug Options
% 2.20/1.00  
% 2.20/1.00  --dbg_backtrace                         false
% 2.20/1.00  --dbg_dump_prop_clauses                 false
% 2.20/1.00  --dbg_dump_prop_clauses_file            -
% 2.20/1.00  --dbg_out_stat                          false
% 2.20/1.00  
% 2.20/1.00  
% 2.20/1.00  
% 2.20/1.00  
% 2.20/1.00  ------ Proving...
% 2.20/1.00  
% 2.20/1.00  
% 2.20/1.00  % SZS status Theorem for theBenchmark.p
% 2.20/1.00  
% 2.20/1.00   Resolution empty clause
% 2.20/1.00  
% 2.20/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.20/1.00  
% 2.20/1.00  fof(f5,axiom,(
% 2.20/1.00    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.20/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.20/1.00  
% 2.20/1.00  fof(f39,plain,(
% 2.20/1.00    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.20/1.00    inference(cnf_transformation,[],[f5])).
% 2.20/1.00  
% 2.20/1.00  fof(f10,axiom,(
% 2.20/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 2.20/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.20/1.00  
% 2.20/1.00  fof(f20,plain,(
% 2.20/1.00    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.20/1.00    inference(ennf_transformation,[],[f10])).
% 2.20/1.00  
% 2.20/1.00  fof(f44,plain,(
% 2.20/1.00    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.20/1.00    inference(cnf_transformation,[],[f20])).
% 2.20/1.00  
% 2.20/1.00  fof(f4,axiom,(
% 2.20/1.00    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.20/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.20/1.00  
% 2.20/1.00  fof(f28,plain,(
% 2.20/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.20/1.00    inference(nnf_transformation,[],[f4])).
% 2.20/1.00  
% 2.20/1.00  fof(f29,plain,(
% 2.20/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.20/1.00    inference(flattening,[],[f28])).
% 2.20/1.00  
% 2.20/1.00  fof(f37,plain,(
% 2.20/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.20/1.00    inference(cnf_transformation,[],[f29])).
% 2.20/1.00  
% 2.20/1.00  fof(f61,plain,(
% 2.20/1.00    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.20/1.00    inference(equality_resolution,[],[f37])).
% 2.20/1.00  
% 2.20/1.00  fof(f11,axiom,(
% 2.20/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)))),
% 2.20/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.20/1.00  
% 2.20/1.00  fof(f21,plain,(
% 2.20/1.00    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.20/1.00    inference(ennf_transformation,[],[f11])).
% 2.20/1.00  
% 2.20/1.00  fof(f46,plain,(
% 2.20/1.00    ( ! [X2,X0,X1] : (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.20/1.00    inference(cnf_transformation,[],[f21])).
% 2.20/1.00  
% 2.20/1.00  fof(f14,conjecture,(
% 2.20/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 2.20/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.20/1.00  
% 2.20/1.00  fof(f15,negated_conjecture,(
% 2.20/1.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 2.20/1.00    inference(negated_conjecture,[],[f14])).
% 2.20/1.00  
% 2.20/1.00  fof(f26,plain,(
% 2.20/1.00    ? [X0,X1,X2] : (k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)))),
% 2.20/1.00    inference(ennf_transformation,[],[f15])).
% 2.20/1.00  
% 2.20/1.00  fof(f27,plain,(
% 2.20/1.00    ? [X0,X1,X2] : (k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2))),
% 2.20/1.00    inference(flattening,[],[f26])).
% 2.20/1.00  
% 2.20/1.00  fof(f31,plain,(
% 2.20/1.00    ? [X0,X1,X2] : (k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => (k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) & v1_funct_2(sK2,k1_xboole_0,sK0) & v1_funct_1(sK2))),
% 2.20/1.00    introduced(choice_axiom,[])).
% 2.20/1.00  
% 2.20/1.00  fof(f32,plain,(
% 2.20/1.00    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) & v1_funct_2(sK2,k1_xboole_0,sK0) & v1_funct_1(sK2)),
% 2.20/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f31])).
% 2.20/1.00  
% 2.20/1.00  fof(f58,plain,(
% 2.20/1.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 2.20/1.00    inference(cnf_transformation,[],[f32])).
% 2.20/1.00  
% 2.20/1.00  fof(f38,plain,(
% 2.20/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 2.20/1.00    inference(cnf_transformation,[],[f29])).
% 2.20/1.00  
% 2.20/1.00  fof(f60,plain,(
% 2.20/1.00    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.20/1.00    inference(equality_resolution,[],[f38])).
% 2.20/1.00  
% 2.20/1.00  fof(f9,axiom,(
% 2.20/1.00    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 2.20/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.20/1.00  
% 2.20/1.00  fof(f19,plain,(
% 2.20/1.00    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 2.20/1.00    inference(ennf_transformation,[],[f9])).
% 2.20/1.00  
% 2.20/1.00  fof(f43,plain,(
% 2.20/1.00    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 2.20/1.00    inference(cnf_transformation,[],[f19])).
% 2.20/1.00  
% 2.20/1.00  fof(f1,axiom,(
% 2.20/1.00    v1_xboole_0(k1_xboole_0)),
% 2.20/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.20/1.00  
% 2.20/1.00  fof(f33,plain,(
% 2.20/1.00    v1_xboole_0(k1_xboole_0)),
% 2.20/1.00    inference(cnf_transformation,[],[f1])).
% 2.20/1.00  
% 2.20/1.00  fof(f2,axiom,(
% 2.20/1.00    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.20/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.20/1.00  
% 2.20/1.00  fof(f17,plain,(
% 2.20/1.00    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.20/1.00    inference(ennf_transformation,[],[f2])).
% 2.20/1.00  
% 2.20/1.00  fof(f34,plain,(
% 2.20/1.00    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.20/1.00    inference(cnf_transformation,[],[f17])).
% 2.20/1.00  
% 2.20/1.00  fof(f12,axiom,(
% 2.20/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.20/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.20/1.00  
% 2.20/1.00  fof(f22,plain,(
% 2.20/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.20/1.00    inference(ennf_transformation,[],[f12])).
% 2.20/1.00  
% 2.20/1.00  fof(f23,plain,(
% 2.20/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.20/1.00    inference(flattening,[],[f22])).
% 2.20/1.00  
% 2.20/1.00  fof(f30,plain,(
% 2.20/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.20/1.00    inference(nnf_transformation,[],[f23])).
% 2.20/1.00  
% 2.20/1.00  fof(f48,plain,(
% 2.20/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.20/1.00    inference(cnf_transformation,[],[f30])).
% 2.20/1.00  
% 2.20/1.00  fof(f66,plain,(
% 2.20/1.00    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 2.20/1.00    inference(equality_resolution,[],[f48])).
% 2.20/1.00  
% 2.20/1.00  fof(f8,axiom,(
% 2.20/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.20/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.20/1.00  
% 2.20/1.00  fof(f18,plain,(
% 2.20/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.20/1.00    inference(ennf_transformation,[],[f8])).
% 2.20/1.00  
% 2.20/1.00  fof(f42,plain,(
% 2.20/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.20/1.00    inference(cnf_transformation,[],[f18])).
% 2.20/1.00  
% 2.20/1.00  fof(f3,axiom,(
% 2.20/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.20/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.20/1.00  
% 2.20/1.00  fof(f35,plain,(
% 2.20/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.20/1.00    inference(cnf_transformation,[],[f3])).
% 2.20/1.00  
% 2.20/1.00  fof(f13,axiom,(
% 2.20/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 2.20/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.20/1.00  
% 2.20/1.00  fof(f24,plain,(
% 2.20/1.00    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.20/1.00    inference(ennf_transformation,[],[f13])).
% 2.20/1.00  
% 2.20/1.00  fof(f25,plain,(
% 2.20/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.20/1.00    inference(flattening,[],[f24])).
% 2.20/1.00  
% 2.20/1.00  fof(f54,plain,(
% 2.20/1.00    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.20/1.00    inference(cnf_transformation,[],[f25])).
% 2.20/1.00  
% 2.20/1.00  fof(f56,plain,(
% 2.20/1.00    v1_funct_1(sK2)),
% 2.20/1.00    inference(cnf_transformation,[],[f32])).
% 2.20/1.00  
% 2.20/1.00  fof(f47,plain,(
% 2.20/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.20/1.00    inference(cnf_transformation,[],[f30])).
% 2.20/1.00  
% 2.20/1.00  fof(f55,plain,(
% 2.20/1.00    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.20/1.00    inference(cnf_transformation,[],[f25])).
% 2.20/1.00  
% 2.20/1.00  fof(f7,axiom,(
% 2.20/1.00    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.20/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.20/1.00  
% 2.20/1.00  fof(f41,plain,(
% 2.20/1.00    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 2.20/1.00    inference(cnf_transformation,[],[f7])).
% 2.20/1.00  
% 2.20/1.00  fof(f40,plain,(
% 2.20/1.00    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.20/1.00    inference(cnf_transformation,[],[f7])).
% 2.20/1.00  
% 2.20/1.00  fof(f36,plain,(
% 2.20/1.00    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 2.20/1.00    inference(cnf_transformation,[],[f29])).
% 2.20/1.00  
% 2.20/1.00  fof(f59,plain,(
% 2.20/1.00    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)),
% 2.20/1.00    inference(cnf_transformation,[],[f32])).
% 2.20/1.00  
% 2.20/1.00  cnf(c_6,plain,
% 2.20/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.20/1.00      inference(cnf_transformation,[],[f39]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_885,plain,
% 2.20/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.20/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_11,plain,
% 2.20/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.20/1.00      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 2.20/1.00      inference(cnf_transformation,[],[f44]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_883,plain,
% 2.20/1.00      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 2.20/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.20/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_1645,plain,
% 2.20/1.00      ( k8_relset_1(X0,X1,k1_xboole_0,X2) = k10_relat_1(k1_xboole_0,X2) ),
% 2.20/1.00      inference(superposition,[status(thm)],[c_885,c_883]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_4,plain,
% 2.20/1.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.20/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_12,plain,
% 2.20/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.20/1.00      | k8_relset_1(X1,X2,X0,X2) = k1_relset_1(X1,X2,X0) ),
% 2.20/1.00      inference(cnf_transformation,[],[f46]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_882,plain,
% 2.20/1.00      ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
% 2.20/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.20/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_2375,plain,
% 2.20/1.00      ( k8_relset_1(k1_xboole_0,X0,X1,X0) = k1_relset_1(k1_xboole_0,X0,X1)
% 2.20/1.00      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.20/1.00      inference(superposition,[status(thm)],[c_4,c_882]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_2450,plain,
% 2.20/1.00      ( k8_relset_1(k1_xboole_0,X0,k1_xboole_0,X0) = k1_relset_1(k1_xboole_0,X0,k1_xboole_0) ),
% 2.20/1.00      inference(superposition,[status(thm)],[c_885,c_2375]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_24,negated_conjecture,
% 2.20/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
% 2.20/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_880,plain,
% 2.20/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) = iProver_top ),
% 2.20/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_902,plain,
% 2.20/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.20/1.00      inference(demodulation,[status(thm)],[c_880,c_4]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_3,plain,
% 2.20/1.00      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.20/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_10,plain,
% 2.20/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.20/1.00      | ~ v1_xboole_0(X1)
% 2.20/1.00      | v1_xboole_0(X0) ),
% 2.20/1.00      inference(cnf_transformation,[],[f43]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_884,plain,
% 2.20/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.20/1.00      | v1_xboole_0(X1) != iProver_top
% 2.20/1.00      | v1_xboole_0(X0) = iProver_top ),
% 2.20/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_1524,plain,
% 2.20/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.20/1.00      | v1_xboole_0(X1) != iProver_top
% 2.20/1.00      | v1_xboole_0(X0) = iProver_top ),
% 2.20/1.00      inference(superposition,[status(thm)],[c_3,c_884]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_1634,plain,
% 2.20/1.00      ( v1_xboole_0(X0) != iProver_top | v1_xboole_0(sK2) = iProver_top ),
% 2.20/1.00      inference(superposition,[status(thm)],[c_902,c_1524]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_0,plain,
% 2.20/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 2.20/1.00      inference(cnf_transformation,[],[f33]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_79,plain,
% 2.20/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.20/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_1640,plain,
% 2.20/1.00      ( v1_xboole_0(sK2) = iProver_top
% 2.20/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.20/1.00      inference(instantiation,[status(thm)],[c_1634]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_1869,plain,
% 2.20/1.00      ( v1_xboole_0(sK2) = iProver_top ),
% 2.20/1.00      inference(global_propositional_subsumption,
% 2.20/1.00                [status(thm)],
% 2.20/1.00                [c_1634,c_79,c_1640]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_1,plain,
% 2.20/1.00      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 2.20/1.00      inference(cnf_transformation,[],[f34]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_886,plain,
% 2.20/1.00      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 2.20/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_1874,plain,
% 2.20/1.00      ( sK2 = k1_xboole_0 ),
% 2.20/1.00      inference(superposition,[status(thm)],[c_1869,c_886]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_18,plain,
% 2.20/1.00      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 2.20/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.20/1.00      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 2.20/1.00      inference(cnf_transformation,[],[f66]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_9,plain,
% 2.20/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 2.20/1.00      inference(cnf_transformation,[],[f42]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_2,plain,
% 2.20/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 2.20/1.00      inference(cnf_transformation,[],[f35]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_21,plain,
% 2.20/1.00      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 2.20/1.00      | ~ r1_tarski(k2_relat_1(X0),X1)
% 2.20/1.00      | ~ v1_funct_1(X0)
% 2.20/1.00      | ~ v1_relat_1(X0) ),
% 2.20/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_241,plain,
% 2.20/1.00      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 2.20/1.00      | ~ v1_funct_1(X0)
% 2.20/1.00      | ~ v1_relat_1(X0)
% 2.20/1.00      | X1 != X2
% 2.20/1.00      | k2_relat_1(X0) != k1_xboole_0 ),
% 2.20/1.00      inference(resolution_lifted,[status(thm)],[c_2,c_21]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_242,plain,
% 2.20/1.00      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 2.20/1.00      | ~ v1_funct_1(X0)
% 2.20/1.00      | ~ v1_relat_1(X0)
% 2.20/1.00      | k2_relat_1(X0) != k1_xboole_0 ),
% 2.20/1.00      inference(unflattening,[status(thm)],[c_241]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_26,negated_conjecture,
% 2.20/1.00      ( v1_funct_1(sK2) ),
% 2.20/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_302,plain,
% 2.20/1.00      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 2.20/1.00      | ~ v1_relat_1(X0)
% 2.20/1.00      | k2_relat_1(X0) != k1_xboole_0
% 2.20/1.00      | sK2 != X0 ),
% 2.20/1.00      inference(resolution_lifted,[status(thm)],[c_242,c_26]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_303,plain,
% 2.20/1.00      ( v1_funct_2(sK2,k1_relat_1(sK2),X0)
% 2.20/1.00      | ~ v1_relat_1(sK2)
% 2.20/1.00      | k2_relat_1(sK2) != k1_xboole_0 ),
% 2.20/1.00      inference(unflattening,[status(thm)],[c_302]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_325,plain,
% 2.20/1.00      ( v1_funct_2(sK2,k1_relat_1(sK2),X0)
% 2.20/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 2.20/1.00      | k2_relat_1(sK2) != k1_xboole_0
% 2.20/1.00      | sK2 != X1 ),
% 2.20/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_303]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_326,plain,
% 2.20/1.00      ( v1_funct_2(sK2,k1_relat_1(sK2),X0)
% 2.20/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.20/1.00      | k2_relat_1(sK2) != k1_xboole_0 ),
% 2.20/1.00      inference(unflattening,[status(thm)],[c_325]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_412,plain,
% 2.20/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.20/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 2.20/1.00      | X4 != X1
% 2.20/1.00      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 2.20/1.00      | k1_relat_1(sK2) != k1_xboole_0
% 2.20/1.00      | k2_relat_1(sK2) != k1_xboole_0
% 2.20/1.00      | sK2 != X0 ),
% 2.20/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_326]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_413,plain,
% 2.20/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.20/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
% 2.20/1.00      | k1_relset_1(k1_xboole_0,X2,sK2) = k1_xboole_0
% 2.20/1.00      | k1_relat_1(sK2) != k1_xboole_0
% 2.20/1.00      | k2_relat_1(sK2) != k1_xboole_0 ),
% 2.20/1.00      inference(unflattening,[status(thm)],[c_412]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_567,plain,
% 2.20/1.00      ( sP2_iProver_split
% 2.20/1.00      | sP1_iProver_split
% 2.20/1.00      | k1_relat_1(sK2) != k1_xboole_0
% 2.20/1.00      | k2_relat_1(sK2) != k1_xboole_0 ),
% 2.20/1.00      inference(splitting,
% 2.20/1.00                [splitting(split),new_symbols(definition,[])],
% 2.20/1.00                [c_413]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_872,plain,
% 2.20/1.00      ( k1_relat_1(sK2) != k1_xboole_0
% 2.20/1.00      | k2_relat_1(sK2) != k1_xboole_0
% 2.20/1.00      | sP2_iProver_split = iProver_top
% 2.20/1.00      | sP1_iProver_split = iProver_top ),
% 2.20/1.00      inference(predicate_to_equality,[status(thm)],[c_567]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_597,plain,
% 2.20/1.00      ( k1_relat_1(sK2) != k1_xboole_0
% 2.20/1.00      | k2_relat_1(sK2) != k1_xboole_0
% 2.20/1.00      | sP2_iProver_split = iProver_top
% 2.20/1.00      | sP1_iProver_split = iProver_top ),
% 2.20/1.00      inference(predicate_to_equality,[status(thm)],[c_567]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_19,plain,
% 2.20/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.20/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.20/1.00      | k1_relset_1(X1,X2,X0) = X1
% 2.20/1.00      | k1_xboole_0 = X2 ),
% 2.20/1.00      inference(cnf_transformation,[],[f47]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_435,plain,
% 2.20/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.20/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 2.20/1.00      | X5 != X2
% 2.20/1.00      | k1_relset_1(X1,X2,X0) = X1
% 2.20/1.00      | k1_relat_1(sK2) != X1
% 2.20/1.00      | k2_relat_1(sK2) != k1_xboole_0
% 2.20/1.00      | sK2 != X0
% 2.20/1.00      | k1_xboole_0 = X2 ),
% 2.20/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_326]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_436,plain,
% 2.20/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.20/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X2)))
% 2.20/1.00      | k1_relset_1(k1_relat_1(sK2),X2,sK2) = k1_relat_1(sK2)
% 2.20/1.00      | k2_relat_1(sK2) != k1_xboole_0
% 2.20/1.00      | k1_xboole_0 = X2 ),
% 2.20/1.00      inference(unflattening,[status(thm)],[c_435]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_20,plain,
% 2.20/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 2.20/1.00      | ~ r1_tarski(k2_relat_1(X0),X1)
% 2.20/1.00      | ~ v1_funct_1(X0)
% 2.20/1.00      | ~ v1_relat_1(X0) ),
% 2.20/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_259,plain,
% 2.20/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 2.20/1.00      | ~ v1_funct_1(X0)
% 2.20/1.00      | ~ v1_relat_1(X0)
% 2.20/1.00      | X1 != X2
% 2.20/1.00      | k2_relat_1(X0) != k1_xboole_0 ),
% 2.20/1.00      inference(resolution_lifted,[status(thm)],[c_2,c_20]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_260,plain,
% 2.20/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 2.20/1.00      | ~ v1_funct_1(X0)
% 2.20/1.00      | ~ v1_relat_1(X0)
% 2.20/1.00      | k2_relat_1(X0) != k1_xboole_0 ),
% 2.20/1.00      inference(unflattening,[status(thm)],[c_259]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_287,plain,
% 2.20/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 2.20/1.00      | ~ v1_relat_1(X0)
% 2.20/1.00      | k2_relat_1(X0) != k1_xboole_0
% 2.20/1.00      | sK2 != X0 ),
% 2.20/1.00      inference(resolution_lifted,[status(thm)],[c_260,c_26]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_288,plain,
% 2.20/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X0)))
% 2.20/1.00      | ~ v1_relat_1(sK2)
% 2.20/1.00      | k2_relat_1(sK2) != k1_xboole_0 ),
% 2.20/1.00      inference(unflattening,[status(thm)],[c_287]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_340,plain,
% 2.20/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.20/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X3)))
% 2.20/1.00      | k2_relat_1(sK2) != k1_xboole_0
% 2.20/1.00      | sK2 != X0 ),
% 2.20/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_288]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_341,plain,
% 2.20/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.20/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X2)))
% 2.20/1.00      | k2_relat_1(sK2) != k1_xboole_0 ),
% 2.20/1.00      inference(unflattening,[status(thm)],[c_340]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_440,plain,
% 2.20/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.20/1.00      | k1_relset_1(k1_relat_1(sK2),X2,sK2) = k1_relat_1(sK2)
% 2.20/1.00      | k2_relat_1(sK2) != k1_xboole_0
% 2.20/1.00      | k1_xboole_0 = X2 ),
% 2.20/1.00      inference(global_propositional_subsumption,[status(thm)],[c_436,c_341]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_564,plain,
% 2.20/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.20/1.00      | ~ sP1_iProver_split ),
% 2.20/1.00      inference(splitting,
% 2.20/1.00                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 2.20/1.00                [c_440]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_870,plain,
% 2.20/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.20/1.00      | sP1_iProver_split != iProver_top ),
% 2.20/1.00      inference(predicate_to_equality,[status(thm)],[c_564]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_1235,plain,
% 2.20/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.20/1.00      | sP1_iProver_split != iProver_top ),
% 2.20/1.00      inference(superposition,[status(thm)],[c_3,c_870]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_1347,plain,
% 2.20/1.00      ( sP2_iProver_split = iProver_top
% 2.20/1.00      | k2_relat_1(sK2) != k1_xboole_0
% 2.20/1.00      | k1_relat_1(sK2) != k1_xboole_0 ),
% 2.20/1.00      inference(global_propositional_subsumption,
% 2.20/1.00                [status(thm)],
% 2.20/1.00                [c_872,c_597,c_902,c_1235]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_1348,plain,
% 2.20/1.00      ( k1_relat_1(sK2) != k1_xboole_0
% 2.20/1.00      | k2_relat_1(sK2) != k1_xboole_0
% 2.20/1.00      | sP2_iProver_split = iProver_top ),
% 2.20/1.00      inference(renaming,[status(thm)],[c_1347]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_1878,plain,
% 2.20/1.00      ( k1_relat_1(k1_xboole_0) != k1_xboole_0
% 2.20/1.00      | k2_relat_1(k1_xboole_0) != k1_xboole_0
% 2.20/1.00      | sP2_iProver_split = iProver_top ),
% 2.20/1.00      inference(demodulation,[status(thm)],[c_1874,c_1348]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_7,plain,
% 2.20/1.00      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.20/1.00      inference(cnf_transformation,[],[f41]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_8,plain,
% 2.20/1.00      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.20/1.00      inference(cnf_transformation,[],[f40]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_1925,plain,
% 2.20/1.00      ( k1_xboole_0 != k1_xboole_0 | sP2_iProver_split = iProver_top ),
% 2.20/1.00      inference(light_normalisation,[status(thm)],[c_1878,c_7,c_8]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_1926,plain,
% 2.20/1.00      ( sP2_iProver_split = iProver_top ),
% 2.20/1.00      inference(equality_resolution_simp,[status(thm)],[c_1925]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_566,plain,
% 2.20/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
% 2.20/1.00      | k1_relset_1(k1_xboole_0,X0,sK2) = k1_xboole_0
% 2.20/1.00      | ~ sP2_iProver_split ),
% 2.20/1.00      inference(splitting,
% 2.20/1.00                [splitting(split),new_symbols(definition,[sP2_iProver_split])],
% 2.20/1.00                [c_413]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_874,plain,
% 2.20/1.00      ( k1_relset_1(k1_xboole_0,X0,sK2) = k1_xboole_0
% 2.20/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
% 2.20/1.00      | sP2_iProver_split != iProver_top ),
% 2.20/1.00      inference(predicate_to_equality,[status(thm)],[c_566]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_977,plain,
% 2.20/1.00      ( k1_relset_1(k1_xboole_0,X0,sK2) = k1_xboole_0
% 2.20/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.20/1.00      | sP2_iProver_split != iProver_top ),
% 2.20/1.00      inference(light_normalisation,[status(thm)],[c_874,c_4]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_981,plain,
% 2.20/1.00      ( k1_relset_1(k1_xboole_0,X0,sK2) = k1_xboole_0
% 2.20/1.00      | sP2_iProver_split != iProver_top ),
% 2.20/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_977,c_902]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_1885,plain,
% 2.20/1.00      ( k1_relset_1(k1_xboole_0,X0,k1_xboole_0) = k1_xboole_0
% 2.20/1.00      | sP2_iProver_split != iProver_top ),
% 2.20/1.00      inference(demodulation,[status(thm)],[c_1874,c_981]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_1928,plain,
% 2.20/1.00      ( k1_relset_1(k1_xboole_0,X0,k1_xboole_0) = k1_xboole_0 ),
% 2.20/1.00      inference(backward_subsumption_resolution,[status(thm)],[c_1926,c_1885]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_2451,plain,
% 2.20/1.00      ( k8_relset_1(k1_xboole_0,X0,k1_xboole_0,X0) = k1_xboole_0 ),
% 2.20/1.00      inference(light_normalisation,[status(thm)],[c_2450,c_1928]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_2522,plain,
% 2.20/1.00      ( k10_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.20/1.00      inference(superposition,[status(thm)],[c_1645,c_2451]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_569,plain,
% 2.20/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X0)))
% 2.20/1.00      | ~ sP3_iProver_split ),
% 2.20/1.00      inference(splitting,
% 2.20/1.00                [splitting(split),new_symbols(definition,[sP3_iProver_split])],
% 2.20/1.00                [c_341]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_879,plain,
% 2.20/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X0))) = iProver_top
% 2.20/1.00      | sP3_iProver_split != iProver_top ),
% 2.20/1.00      inference(predicate_to_equality,[status(thm)],[c_569]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_1646,plain,
% 2.20/1.00      ( k8_relset_1(k1_relat_1(sK2),X0,sK2,X1) = k10_relat_1(sK2,X1)
% 2.20/1.00      | sP3_iProver_split != iProver_top ),
% 2.20/1.00      inference(superposition,[status(thm)],[c_879,c_883]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_5,plain,
% 2.20/1.00      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 2.20/1.00      | k1_xboole_0 = X0
% 2.20/1.00      | k1_xboole_0 = X1 ),
% 2.20/1.00      inference(cnf_transformation,[],[f36]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_71,plain,
% 2.20/1.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 2.20/1.00      | k1_xboole_0 = k1_xboole_0 ),
% 2.20/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_72,plain,
% 2.20/1.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 2.20/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_570,plain,
% 2.20/1.00      ( sP3_iProver_split
% 2.20/1.00      | sP1_iProver_split
% 2.20/1.00      | k2_relat_1(sK2) != k1_xboole_0 ),
% 2.20/1.00      inference(splitting,
% 2.20/1.00                [splitting(split),new_symbols(definition,[])],
% 2.20/1.00                [c_341]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_604,plain,
% 2.20/1.00      ( k2_relat_1(sK2) != k1_xboole_0
% 2.20/1.00      | sP3_iProver_split = iProver_top
% 2.20/1.00      | sP1_iProver_split = iProver_top ),
% 2.20/1.00      inference(predicate_to_equality,[status(thm)],[c_570]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_1107,plain,
% 2.20/1.00      ( ~ v1_xboole_0(sK2) | k1_xboole_0 = sK2 ),
% 2.20/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_1110,plain,
% 2.20/1.00      ( k1_xboole_0 = sK2 | v1_xboole_0(sK2) != iProver_top ),
% 2.20/1.00      inference(predicate_to_equality,[status(thm)],[c_1107]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_572,plain,( X0 = X0 ),theory(equality) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_1113,plain,
% 2.20/1.00      ( sK2 = sK2 ),
% 2.20/1.00      inference(instantiation,[status(thm)],[c_572]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_573,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_1033,plain,
% 2.20/1.00      ( k2_relat_1(sK2) != X0
% 2.20/1.00      | k2_relat_1(sK2) = k1_xboole_0
% 2.20/1.00      | k1_xboole_0 != X0 ),
% 2.20/1.00      inference(instantiation,[status(thm)],[c_573]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_1123,plain,
% 2.20/1.00      ( k2_relat_1(sK2) != k2_relat_1(X0)
% 2.20/1.00      | k2_relat_1(sK2) = k1_xboole_0
% 2.20/1.00      | k1_xboole_0 != k2_relat_1(X0) ),
% 2.20/1.00      inference(instantiation,[status(thm)],[c_1033]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_1125,plain,
% 2.20/1.00      ( k2_relat_1(sK2) != k2_relat_1(k1_xboole_0)
% 2.20/1.00      | k2_relat_1(sK2) = k1_xboole_0
% 2.20/1.00      | k1_xboole_0 != k2_relat_1(k1_xboole_0) ),
% 2.20/1.00      inference(instantiation,[status(thm)],[c_1123]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_578,plain,
% 2.20/1.00      ( X0 != X1 | k2_relat_1(X0) = k2_relat_1(X1) ),
% 2.20/1.00      theory(equality) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_1124,plain,
% 2.20/1.00      ( k2_relat_1(sK2) = k2_relat_1(X0) | sK2 != X0 ),
% 2.20/1.00      inference(instantiation,[status(thm)],[c_578]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_1126,plain,
% 2.20/1.00      ( k2_relat_1(sK2) = k2_relat_1(k1_xboole_0) | sK2 != k1_xboole_0 ),
% 2.20/1.00      inference(instantiation,[status(thm)],[c_1124]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_1261,plain,
% 2.20/1.00      ( k2_relat_1(X0) != X1
% 2.20/1.00      | k1_xboole_0 != X1
% 2.20/1.00      | k1_xboole_0 = k2_relat_1(X0) ),
% 2.20/1.00      inference(instantiation,[status(thm)],[c_573]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_1262,plain,
% 2.20/1.00      ( k2_relat_1(k1_xboole_0) != k1_xboole_0
% 2.20/1.00      | k1_xboole_0 = k2_relat_1(k1_xboole_0)
% 2.20/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 2.20/1.00      inference(instantiation,[status(thm)],[c_1261]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_1215,plain,
% 2.20/1.00      ( X0 != X1 | sK2 != X1 | sK2 = X0 ),
% 2.20/1.00      inference(instantiation,[status(thm)],[c_573]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_1687,plain,
% 2.20/1.00      ( X0 != sK2 | sK2 = X0 | sK2 != sK2 ),
% 2.20/1.00      inference(instantiation,[status(thm)],[c_1215]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_1688,plain,
% 2.20/1.00      ( sK2 != sK2 | sK2 = k1_xboole_0 | k1_xboole_0 != sK2 ),
% 2.20/1.00      inference(instantiation,[status(thm)],[c_1687]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_1994,plain,
% 2.20/1.00      ( k8_relset_1(k1_relat_1(sK2),X0,sK2,X1) = k10_relat_1(sK2,X1) ),
% 2.20/1.00      inference(global_propositional_subsumption,
% 2.20/1.00                [status(thm)],
% 2.20/1.00                [c_1646,c_7,c_71,c_72,c_79,c_604,c_902,c_1110,c_1113,c_1125,
% 2.20/1.00                 c_1126,c_1235,c_1262,c_1640,c_1688]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_1997,plain,
% 2.20/1.00      ( k8_relset_1(k1_xboole_0,X0,k1_xboole_0,X1) = k10_relat_1(k1_xboole_0,X1) ),
% 2.20/1.00      inference(light_normalisation,[status(thm)],[c_1994,c_8,c_1874]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_23,negated_conjecture,
% 2.20/1.00      ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
% 2.20/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_1888,plain,
% 2.20/1.00      ( k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1) != k1_xboole_0 ),
% 2.20/1.00      inference(demodulation,[status(thm)],[c_1874,c_23]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_1999,plain,
% 2.20/1.00      ( k10_relat_1(k1_xboole_0,sK1) != k1_xboole_0 ),
% 2.20/1.00      inference(demodulation,[status(thm)],[c_1997,c_1888]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_2530,plain,
% 2.20/1.00      ( k1_xboole_0 != k1_xboole_0 ),
% 2.20/1.00      inference(demodulation,[status(thm)],[c_2522,c_1999]) ).
% 2.20/1.00  
% 2.20/1.00  cnf(c_2531,plain,
% 2.20/1.00      ( $false ),
% 2.20/1.00      inference(equality_resolution_simp,[status(thm)],[c_2530]) ).
% 2.20/1.00  
% 2.20/1.00  
% 2.20/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.20/1.00  
% 2.20/1.00  ------                               Statistics
% 2.20/1.00  
% 2.20/1.00  ------ General
% 2.20/1.00  
% 2.20/1.00  abstr_ref_over_cycles:                  0
% 2.20/1.00  abstr_ref_under_cycles:                 0
% 2.20/1.00  gc_basic_clause_elim:                   0
% 2.20/1.00  forced_gc_time:                         0
% 2.20/1.00  parsing_time:                           0.01
% 2.20/1.00  unif_index_cands_time:                  0.
% 2.20/1.00  unif_index_add_time:                    0.
% 2.20/1.00  orderings_time:                         0.
% 2.20/1.00  out_proof_time:                         0.013
% 2.20/1.00  total_time:                             0.124
% 2.20/1.00  num_of_symbols:                         54
% 2.20/1.00  num_of_terms:                           2434
% 2.20/1.00  
% 2.20/1.00  ------ Preprocessing
% 2.20/1.00  
% 2.20/1.00  num_of_splits:                          7
% 2.20/1.00  num_of_split_atoms:                     4
% 2.20/1.00  num_of_reused_defs:                     3
% 2.20/1.00  num_eq_ax_congr_red:                    31
% 2.20/1.00  num_of_sem_filtered_clauses:            1
% 2.20/1.00  num_of_subtypes:                        0
% 2.20/1.00  monotx_restored_types:                  0
% 2.20/1.00  sat_num_of_epr_types:                   0
% 2.20/1.00  sat_num_of_non_cyclic_types:            0
% 2.20/1.00  sat_guarded_non_collapsed_types:        0
% 2.20/1.00  num_pure_diseq_elim:                    0
% 2.20/1.00  simp_replaced_by:                       0
% 2.20/1.00  res_preprocessed:                       112
% 2.20/1.00  prep_upred:                             0
% 2.20/1.00  prep_unflattend:                        41
% 2.20/1.00  smt_new_axioms:                         0
% 2.20/1.00  pred_elim_cands:                        2
% 2.20/1.00  pred_elim:                              4
% 2.20/1.00  pred_elim_cl:                           7
% 2.20/1.00  pred_elim_cycles:                       6
% 2.20/1.00  merged_defs:                            0
% 2.20/1.00  merged_defs_ncl:                        0
% 2.20/1.00  bin_hyper_res:                          0
% 2.20/1.00  prep_cycles:                            4
% 2.20/1.00  pred_elim_time:                         0.006
% 2.20/1.00  splitting_time:                         0.
% 2.20/1.00  sem_filter_time:                        0.
% 2.20/1.00  monotx_time:                            0.
% 2.20/1.00  subtype_inf_time:                       0.
% 2.20/1.00  
% 2.20/1.00  ------ Problem properties
% 2.20/1.00  
% 2.20/1.00  clauses:                                26
% 2.20/1.00  conjectures:                            2
% 2.20/1.00  epr:                                    2
% 2.20/1.00  horn:                                   20
% 2.20/1.00  ground:                                 10
% 2.20/1.00  unary:                                  9
% 2.20/1.00  binary:                                 9
% 2.20/1.00  lits:                                   53
% 2.20/1.00  lits_eq:                                23
% 2.20/1.00  fd_pure:                                0
% 2.20/1.00  fd_pseudo:                              0
% 2.20/1.00  fd_cond:                                3
% 2.20/1.00  fd_pseudo_cond:                         0
% 2.20/1.00  ac_symbols:                             0
% 2.20/1.00  
% 2.20/1.00  ------ Propositional Solver
% 2.20/1.00  
% 2.20/1.00  prop_solver_calls:                      27
% 2.20/1.00  prop_fast_solver_calls:                 646
% 2.20/1.00  smt_solver_calls:                       0
% 2.20/1.00  smt_fast_solver_calls:                  0
% 2.20/1.00  prop_num_of_clauses:                    904
% 2.20/1.00  prop_preprocess_simplified:             3844
% 2.20/1.00  prop_fo_subsumed:                       11
% 2.20/1.00  prop_solver_time:                       0.
% 2.20/1.00  smt_solver_time:                        0.
% 2.20/1.00  smt_fast_solver_time:                   0.
% 2.20/1.00  prop_fast_solver_time:                  0.
% 2.20/1.00  prop_unsat_core_time:                   0.
% 2.20/1.00  
% 2.20/1.00  ------ QBF
% 2.20/1.00  
% 2.20/1.00  qbf_q_res:                              0
% 2.20/1.00  qbf_num_tautologies:                    0
% 2.20/1.00  qbf_prep_cycles:                        0
% 2.20/1.00  
% 2.20/1.00  ------ BMC1
% 2.20/1.00  
% 2.20/1.00  bmc1_current_bound:                     -1
% 2.20/1.00  bmc1_last_solved_bound:                 -1
% 2.20/1.00  bmc1_unsat_core_size:                   -1
% 2.20/1.00  bmc1_unsat_core_parents_size:           -1
% 2.20/1.00  bmc1_merge_next_fun:                    0
% 2.20/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.20/1.00  
% 2.20/1.00  ------ Instantiation
% 2.20/1.00  
% 2.20/1.00  inst_num_of_clauses:                    413
% 2.20/1.00  inst_num_in_passive:                    92
% 2.20/1.00  inst_num_in_active:                     200
% 2.20/1.00  inst_num_in_unprocessed:                121
% 2.20/1.00  inst_num_of_loops:                      230
% 2.20/1.00  inst_num_of_learning_restarts:          0
% 2.20/1.00  inst_num_moves_active_passive:          28
% 2.20/1.00  inst_lit_activity:                      0
% 2.20/1.00  inst_lit_activity_moves:                0
% 2.20/1.00  inst_num_tautologies:                   0
% 2.20/1.00  inst_num_prop_implied:                  0
% 2.20/1.00  inst_num_existing_simplified:           0
% 2.20/1.00  inst_num_eq_res_simplified:             0
% 2.20/1.00  inst_num_child_elim:                    0
% 2.20/1.00  inst_num_of_dismatching_blockings:      87
% 2.20/1.00  inst_num_of_non_proper_insts:           299
% 2.20/1.00  inst_num_of_duplicates:                 0
% 2.20/1.00  inst_inst_num_from_inst_to_res:         0
% 2.20/1.00  inst_dismatching_checking_time:         0.
% 2.20/1.00  
% 2.20/1.00  ------ Resolution
% 2.20/1.00  
% 2.20/1.00  res_num_of_clauses:                     0
% 2.20/1.00  res_num_in_passive:                     0
% 2.20/1.00  res_num_in_active:                      0
% 2.20/1.00  res_num_of_loops:                       116
% 2.20/1.00  res_forward_subset_subsumed:            20
% 2.20/1.00  res_backward_subset_subsumed:           0
% 2.20/1.00  res_forward_subsumed:                   0
% 2.20/1.00  res_backward_subsumed:                  0
% 2.20/1.00  res_forward_subsumption_resolution:     1
% 2.20/1.00  res_backward_subsumption_resolution:    0
% 2.20/1.00  res_clause_to_clause_subsumption:       86
% 2.20/1.00  res_orphan_elimination:                 0
% 2.20/1.00  res_tautology_del:                      31
% 2.20/1.00  res_num_eq_res_simplified:              0
% 2.20/1.00  res_num_sel_changes:                    0
% 2.20/1.00  res_moves_from_active_to_pass:          0
% 2.20/1.00  
% 2.20/1.00  ------ Superposition
% 2.20/1.00  
% 2.20/1.00  sup_time_total:                         0.
% 2.20/1.00  sup_time_generating:                    0.
% 2.20/1.00  sup_time_sim_full:                      0.
% 2.20/1.00  sup_time_sim_immed:                     0.
% 2.20/1.00  
% 2.20/1.00  sup_num_of_clauses:                     35
% 2.20/1.00  sup_num_in_active:                      28
% 2.20/1.00  sup_num_in_passive:                     7
% 2.20/1.00  sup_num_of_loops:                       45
% 2.20/1.00  sup_fw_superposition:                   29
% 2.20/1.00  sup_bw_superposition:                   6
% 2.20/1.00  sup_immediate_simplified:               17
% 2.20/1.00  sup_given_eliminated:                   0
% 2.20/1.00  comparisons_done:                       0
% 2.20/1.00  comparisons_avoided:                    1
% 2.20/1.00  
% 2.20/1.00  ------ Simplifications
% 2.20/1.00  
% 2.20/1.00  
% 2.20/1.00  sim_fw_subset_subsumed:                 4
% 2.20/1.00  sim_bw_subset_subsumed:                 1
% 2.20/1.00  sim_fw_subsumed:                        5
% 2.20/1.00  sim_bw_subsumed:                        2
% 2.20/1.00  sim_fw_subsumption_res:                 1
% 2.20/1.00  sim_bw_subsumption_res:                 1
% 2.20/1.00  sim_tautology_del:                      0
% 2.20/1.00  sim_eq_tautology_del:                   2
% 2.20/1.00  sim_eq_res_simp:                        3
% 2.20/1.00  sim_fw_demodulated:                     3
% 2.20/1.00  sim_bw_demodulated:                     17
% 2.20/1.00  sim_light_normalised:                   8
% 2.20/1.00  sim_joinable_taut:                      0
% 2.20/1.00  sim_joinable_simp:                      0
% 2.20/1.00  sim_ac_normalised:                      0
% 2.20/1.00  sim_smt_subsumption:                    0
% 2.20/1.00  
%------------------------------------------------------------------------------
