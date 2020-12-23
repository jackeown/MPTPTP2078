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

% Result     : Theorem 1.11s
% Output     : CNFRefutation 1.11s
% Verified   : 
% Statistics : Number of formulae       :  159 ( 875 expanded)
%              Number of clauses        :  110 ( 351 expanded)
%              Number of leaves         :   17 ( 162 expanded)
%              Depth                    :   23
%              Number of atoms          :  432 (2774 expanded)
%              Number of equality atoms :  250 (1251 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        & v1_funct_2(X2,k1_xboole_0,X0)
        & v1_funct_1(X2) )
     => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
          & v1_funct_2(X2,k1_xboole_0,X0)
          & v1_funct_1(X2) )
       => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      & v1_funct_2(X2,k1_xboole_0,X0)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      & v1_funct_2(X2,k1_xboole_0,X0)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f28,plain,
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

fof(f29,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    & v1_funct_2(sK2,k1_xboole_0,sK0)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f28])).

fof(f49,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f26])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f52,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f34])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f47,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k8_relset_1(X0,X1,X2,X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f53,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k8_relset_1(k1_xboole_0,X1,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f43])).

fof(f7,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f38,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f31,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f51,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f35])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f50,plain,(
    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_783,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_803,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_783,c_4])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_784,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1369,plain,
    ( k8_relset_1(k1_xboole_0,X0,X1,X2) = k10_relat_1(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_784])).

cnf(c_1597,plain,
    ( k8_relset_1(k1_xboole_0,X0,sK2,X1) = k10_relat_1(sK2,X1) ),
    inference(superposition,[status(thm)],[c_803,c_1369])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_2,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_15,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_172,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | X1 != X2
    | k2_relat_1(X0) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_15])).

cnf(c_173,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_172])).

cnf(c_20,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_275,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_173,c_20])).

cnf(c_276,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),X0)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_275])).

cnf(c_340,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | k2_relat_1(sK2) != k1_xboole_0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_276])).

cnf(c_341,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),X0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relat_1(sK2) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_340])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_funct_1(X0)
    | k8_relset_1(k1_xboole_0,X1,X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_308,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k8_relset_1(k1_xboole_0,X1,X0,X1) = k1_xboole_0
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_20])).

cnf(c_309,plain,
    ( ~ v1_funct_2(sK2,k1_xboole_0,X0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | k8_relset_1(k1_xboole_0,X0,sK2,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_308])).

cnf(c_421,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
    | X2 != X3
    | k8_relset_1(k1_xboole_0,X2,sK2,X2) = k1_xboole_0
    | k1_relat_1(sK2) != k1_xboole_0
    | k2_relat_1(sK2) != k1_xboole_0
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_341,c_309])).

cnf(c_422,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
    | k8_relset_1(k1_xboole_0,X2,sK2,X2) = k1_xboole_0
    | k1_relat_1(sK2) != k1_xboole_0
    | k2_relat_1(sK2) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_421])).

cnf(c_520,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | k8_relset_1(k1_xboole_0,X0,sK2,X0) = k1_xboole_0
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_422])).

cnf(c_776,plain,
    ( k8_relset_1(k1_xboole_0,X0,sK2,X0) = k1_xboole_0
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_520])).

cnf(c_862,plain,
    ( k8_relset_1(k1_xboole_0,X0,sK2,X0) = k1_xboole_0
    | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_776,c_4])).

cnf(c_866,plain,
    ( k8_relset_1(k1_xboole_0,X0,sK2,X0) = k1_xboole_0
    | sP0_iProver_split != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_862,c_803])).

cnf(c_1718,plain,
    ( k10_relat_1(sK2,X0) = k1_xboole_0
    | sP0_iProver_split != iProver_top ),
    inference(demodulation,[status(thm)],[c_1597,c_866])).

cnf(c_8,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_7,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_5,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_47,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_48,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_522,plain,
    ( sP1_iProver_split
    | sP0_iProver_split
    | k1_relat_1(sK2) != k1_xboole_0
    | k2_relat_1(sK2) != k1_xboole_0 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_422])).

cnf(c_546,plain,
    ( k1_relat_1(sK2) != k1_xboole_0
    | k2_relat_1(sK2) != k1_xboole_0
    | sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_522])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_969,plain,
    ( ~ v1_xboole_0(sK2)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_528,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_975,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_528])).

cnf(c_529,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_912,plain,
    ( k2_relat_1(sK2) != X0
    | k2_relat_1(sK2) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_529])).

cnf(c_985,plain,
    ( k2_relat_1(sK2) != k2_relat_1(X0)
    | k2_relat_1(sK2) = k1_xboole_0
    | k1_xboole_0 != k2_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_912])).

cnf(c_987,plain,
    ( k2_relat_1(sK2) != k2_relat_1(k1_xboole_0)
    | k2_relat_1(sK2) = k1_xboole_0
    | k1_xboole_0 != k2_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_985])).

cnf(c_534,plain,
    ( X0 != X1
    | k2_relat_1(X0) = k2_relat_1(X1) ),
    theory(equality)).

cnf(c_986,plain,
    ( k2_relat_1(sK2) = k2_relat_1(X0)
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_534])).

cnf(c_988,plain,
    ( k2_relat_1(sK2) = k2_relat_1(k1_xboole_0)
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_986])).

cnf(c_913,plain,
    ( k1_relat_1(sK2) != X0
    | k1_relat_1(sK2) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_529])).

cnf(c_992,plain,
    ( k1_relat_1(sK2) != k1_relat_1(X0)
    | k1_relat_1(sK2) = k1_xboole_0
    | k1_xboole_0 != k1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_913])).

cnf(c_994,plain,
    ( k1_relat_1(sK2) != k1_relat_1(k1_xboole_0)
    | k1_relat_1(sK2) = k1_xboole_0
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_992])).

cnf(c_535,plain,
    ( X0 != X1
    | k1_relat_1(X0) = k1_relat_1(X1) ),
    theory(equality)).

cnf(c_993,plain,
    ( k1_relat_1(sK2) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_535])).

cnf(c_995,plain,
    ( k1_relat_1(sK2) = k1_relat_1(k1_xboole_0)
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_993])).

cnf(c_1131,plain,
    ( k2_relat_1(X0) != X1
    | k1_xboole_0 != X1
    | k1_xboole_0 = k2_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_529])).

cnf(c_1132,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1131])).

cnf(c_3,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_521,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_422])).

cnf(c_775,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_521])).

cnf(c_1138,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_775])).

cnf(c_1155,plain,
    ( k1_relat_1(X0) != X1
    | k1_xboole_0 != X1
    | k1_xboole_0 = k1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_529])).

cnf(c_1156,plain,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1155])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1020,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1453,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | v1_xboole_0(sK2)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1020])).

cnf(c_1076,plain,
    ( X0 != X1
    | sK2 != X1
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_529])).

cnf(c_1516,plain,
    ( X0 != sK2
    | sK2 = X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1076])).

cnf(c_1517,plain,
    ( sK2 != sK2
    | sK2 = k1_xboole_0
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_1516])).

cnf(c_2259,plain,
    ( k10_relat_1(sK2,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1718,c_18,c_8,c_7,c_47,c_48,c_0,c_546,c_803,c_969,c_975,c_987,c_988,c_994,c_995,c_1132,c_1138,c_1156,c_1453,c_1517])).

cnf(c_785,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1396,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_785])).

cnf(c_1607,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_803,c_1396])).

cnf(c_23,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_55,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1454,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
    | v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1453])).

cnf(c_1830,plain,
    ( v1_xboole_0(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1607,c_23,c_55,c_1454])).

cnf(c_787,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1835,plain,
    ( sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1830,c_787])).

cnf(c_2262,plain,
    ( k10_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2259,c_1835])).

cnf(c_2264,plain,
    ( k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2262])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k8_relset_1(X1,X2,X0,X2) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_290,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X2) = X1
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_20])).

cnf(c_291,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k8_relset_1(X0,X1,sK2,X1) = X0
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_290])).

cnf(c_397,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | X3 != X4
    | k8_relset_1(X2,X3,sK2,X3) = X2
    | k1_relat_1(sK2) != X2
    | k2_relat_1(sK2) != k1_xboole_0
    | sK2 != sK2
    | k1_xboole_0 = X3 ),
    inference(resolution_lifted,[status(thm)],[c_341,c_291])).

cnf(c_398,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X2)))
    | k8_relset_1(k1_relat_1(sK2),X2,sK2,X2) = k1_relat_1(sK2)
    | k2_relat_1(sK2) != k1_xboole_0
    | k1_xboole_0 = X2 ),
    inference(unflattening,[status(thm)],[c_397])).

cnf(c_14,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_190,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | X1 != X2
    | k2_relat_1(X0) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_14])).

cnf(c_191,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_190])).

cnf(c_260,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_191,c_20])).

cnf(c_261,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X0)))
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_260])).

cnf(c_355,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X3)))
    | k2_relat_1(sK2) != k1_xboole_0
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_261])).

cnf(c_356,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X2)))
    | k2_relat_1(sK2) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_355])).

cnf(c_402,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k8_relset_1(k1_relat_1(sK2),X2,sK2,X2) = k1_relat_1(sK2)
    | k2_relat_1(sK2) != k1_xboole_0
    | k1_xboole_0 = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_398,c_356])).

cnf(c_523,plain,
    ( k8_relset_1(k1_relat_1(sK2),X0,sK2,X0) = k1_relat_1(sK2)
    | k1_xboole_0 = X0
    | ~ sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP2_iProver_split])],[c_402])).

cnf(c_779,plain,
    ( k8_relset_1(k1_relat_1(sK2),X0,sK2,X0) = k1_relat_1(sK2)
    | k1_xboole_0 = X0
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_523])).

cnf(c_1842,plain,
    ( k8_relset_1(k1_relat_1(k1_xboole_0),X0,k1_xboole_0,X0) = k1_relat_1(k1_xboole_0)
    | k1_xboole_0 = X0
    | sP2_iProver_split != iProver_top ),
    inference(demodulation,[status(thm)],[c_1835,c_779])).

cnf(c_1881,plain,
    ( k8_relset_1(k1_xboole_0,X0,k1_xboole_0,X0) = k1_xboole_0
    | k1_xboole_0 = X0
    | sP2_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1842,c_8])).

cnf(c_524,plain,
    ( sP2_iProver_split
    | sP1_iProver_split
    | k2_relat_1(sK2) != k1_xboole_0 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_402])).

cnf(c_553,plain,
    ( k2_relat_1(sK2) != k1_xboole_0
    | sP2_iProver_split = iProver_top
    | sP1_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_524])).

cnf(c_2004,plain,
    ( k1_xboole_0 = X0
    | k8_relset_1(k1_xboole_0,X0,k1_xboole_0,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1881,c_18,c_7,c_47,c_48,c_0,c_553,c_803,c_969,c_975,c_987,c_988,c_1132,c_1138,c_1453,c_1517])).

cnf(c_2005,plain,
    ( k8_relset_1(k1_xboole_0,X0,k1_xboole_0,X0) = k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(renaming,[status(thm)],[c_2004])).

cnf(c_6,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_786,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1366,plain,
    ( k8_relset_1(X0,X1,k1_xboole_0,X2) = k10_relat_1(k1_xboole_0,X2) ),
    inference(superposition,[status(thm)],[c_786,c_784])).

cnf(c_2006,plain,
    ( k10_relat_1(k1_xboole_0,X0) = k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(demodulation,[status(thm)],[c_2005,c_1366])).

cnf(c_17,negated_conjecture,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1717,plain,
    ( k10_relat_1(sK2,sK1) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1597,c_17])).

cnf(c_1839,plain,
    ( k10_relat_1(k1_xboole_0,sK1) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1835,c_1717])).

cnf(c_2009,plain,
    ( sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2006,c_1839])).

cnf(c_2198,plain,
    ( k10_relat_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2009,c_1839])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2264,c_2198])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:06:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 1.11/1.07  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.11/1.07  
% 1.11/1.07  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.11/1.07  
% 1.11/1.07  ------  iProver source info
% 1.11/1.07  
% 1.11/1.07  git: date: 2020-06-30 10:37:57 +0100
% 1.11/1.07  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.11/1.07  git: non_committed_changes: false
% 1.11/1.07  git: last_make_outside_of_git: false
% 1.11/1.07  
% 1.11/1.07  ------ 
% 1.11/1.07  
% 1.11/1.07  ------ Input Options
% 1.11/1.07  
% 1.11/1.07  --out_options                           all
% 1.11/1.07  --tptp_safe_out                         true
% 1.11/1.07  --problem_path                          ""
% 1.11/1.07  --include_path                          ""
% 1.11/1.07  --clausifier                            res/vclausify_rel
% 1.11/1.07  --clausifier_options                    --mode clausify
% 1.11/1.07  --stdin                                 false
% 1.11/1.07  --stats_out                             all
% 1.11/1.07  
% 1.11/1.07  ------ General Options
% 1.11/1.07  
% 1.11/1.07  --fof                                   false
% 1.11/1.07  --time_out_real                         305.
% 1.11/1.07  --time_out_virtual                      -1.
% 1.11/1.07  --symbol_type_check                     false
% 1.11/1.07  --clausify_out                          false
% 1.11/1.07  --sig_cnt_out                           false
% 1.11/1.07  --trig_cnt_out                          false
% 1.11/1.07  --trig_cnt_out_tolerance                1.
% 1.11/1.07  --trig_cnt_out_sk_spl                   false
% 1.11/1.07  --abstr_cl_out                          false
% 1.11/1.07  
% 1.11/1.07  ------ Global Options
% 1.11/1.07  
% 1.11/1.07  --schedule                              default
% 1.11/1.07  --add_important_lit                     false
% 1.11/1.07  --prop_solver_per_cl                    1000
% 1.11/1.07  --min_unsat_core                        false
% 1.11/1.07  --soft_assumptions                      false
% 1.11/1.07  --soft_lemma_size                       3
% 1.11/1.07  --prop_impl_unit_size                   0
% 1.11/1.07  --prop_impl_unit                        []
% 1.11/1.07  --share_sel_clauses                     true
% 1.11/1.07  --reset_solvers                         false
% 1.11/1.07  --bc_imp_inh                            [conj_cone]
% 1.11/1.07  --conj_cone_tolerance                   3.
% 1.11/1.07  --extra_neg_conj                        none
% 1.11/1.07  --large_theory_mode                     true
% 1.11/1.07  --prolific_symb_bound                   200
% 1.11/1.07  --lt_threshold                          2000
% 1.11/1.07  --clause_weak_htbl                      true
% 1.11/1.07  --gc_record_bc_elim                     false
% 1.11/1.07  
% 1.11/1.07  ------ Preprocessing Options
% 1.11/1.07  
% 1.11/1.07  --preprocessing_flag                    true
% 1.11/1.07  --time_out_prep_mult                    0.1
% 1.11/1.07  --splitting_mode                        input
% 1.11/1.07  --splitting_grd                         true
% 1.11/1.07  --splitting_cvd                         false
% 1.11/1.07  --splitting_cvd_svl                     false
% 1.11/1.07  --splitting_nvd                         32
% 1.11/1.07  --sub_typing                            true
% 1.11/1.07  --prep_gs_sim                           true
% 1.11/1.07  --prep_unflatten                        true
% 1.11/1.07  --prep_res_sim                          true
% 1.11/1.07  --prep_upred                            true
% 1.11/1.07  --prep_sem_filter                       exhaustive
% 1.11/1.07  --prep_sem_filter_out                   false
% 1.11/1.07  --pred_elim                             true
% 1.11/1.07  --res_sim_input                         true
% 1.11/1.07  --eq_ax_congr_red                       true
% 1.11/1.07  --pure_diseq_elim                       true
% 1.11/1.07  --brand_transform                       false
% 1.11/1.07  --non_eq_to_eq                          false
% 1.11/1.07  --prep_def_merge                        true
% 1.11/1.07  --prep_def_merge_prop_impl              false
% 1.11/1.07  --prep_def_merge_mbd                    true
% 1.11/1.07  --prep_def_merge_tr_red                 false
% 1.11/1.07  --prep_def_merge_tr_cl                  false
% 1.11/1.07  --smt_preprocessing                     true
% 1.11/1.07  --smt_ac_axioms                         fast
% 1.11/1.07  --preprocessed_out                      false
% 1.11/1.07  --preprocessed_stats                    false
% 1.11/1.07  
% 1.11/1.07  ------ Abstraction refinement Options
% 1.11/1.07  
% 1.11/1.07  --abstr_ref                             []
% 1.11/1.07  --abstr_ref_prep                        false
% 1.11/1.07  --abstr_ref_until_sat                   false
% 1.11/1.07  --abstr_ref_sig_restrict                funpre
% 1.11/1.07  --abstr_ref_af_restrict_to_split_sk     false
% 1.11/1.07  --abstr_ref_under                       []
% 1.11/1.07  
% 1.11/1.07  ------ SAT Options
% 1.11/1.07  
% 1.11/1.07  --sat_mode                              false
% 1.11/1.07  --sat_fm_restart_options                ""
% 1.11/1.07  --sat_gr_def                            false
% 1.11/1.07  --sat_epr_types                         true
% 1.11/1.07  --sat_non_cyclic_types                  false
% 1.11/1.07  --sat_finite_models                     false
% 1.11/1.07  --sat_fm_lemmas                         false
% 1.11/1.07  --sat_fm_prep                           false
% 1.11/1.07  --sat_fm_uc_incr                        true
% 1.11/1.07  --sat_out_model                         small
% 1.11/1.07  --sat_out_clauses                       false
% 1.11/1.07  
% 1.11/1.07  ------ QBF Options
% 1.11/1.07  
% 1.11/1.07  --qbf_mode                              false
% 1.11/1.07  --qbf_elim_univ                         false
% 1.11/1.07  --qbf_dom_inst                          none
% 1.11/1.07  --qbf_dom_pre_inst                      false
% 1.11/1.07  --qbf_sk_in                             false
% 1.11/1.07  --qbf_pred_elim                         true
% 1.11/1.07  --qbf_split                             512
% 1.11/1.07  
% 1.11/1.07  ------ BMC1 Options
% 1.11/1.07  
% 1.11/1.07  --bmc1_incremental                      false
% 1.11/1.07  --bmc1_axioms                           reachable_all
% 1.11/1.07  --bmc1_min_bound                        0
% 1.11/1.07  --bmc1_max_bound                        -1
% 1.11/1.07  --bmc1_max_bound_default                -1
% 1.11/1.07  --bmc1_symbol_reachability              true
% 1.11/1.07  --bmc1_property_lemmas                  false
% 1.11/1.07  --bmc1_k_induction                      false
% 1.11/1.07  --bmc1_non_equiv_states                 false
% 1.11/1.07  --bmc1_deadlock                         false
% 1.11/1.07  --bmc1_ucm                              false
% 1.11/1.07  --bmc1_add_unsat_core                   none
% 1.11/1.07  --bmc1_unsat_core_children              false
% 1.11/1.07  --bmc1_unsat_core_extrapolate_axioms    false
% 1.11/1.07  --bmc1_out_stat                         full
% 1.11/1.07  --bmc1_ground_init                      false
% 1.11/1.07  --bmc1_pre_inst_next_state              false
% 1.11/1.07  --bmc1_pre_inst_state                   false
% 1.11/1.07  --bmc1_pre_inst_reach_state             false
% 1.11/1.07  --bmc1_out_unsat_core                   false
% 1.11/1.07  --bmc1_aig_witness_out                  false
% 1.11/1.07  --bmc1_verbose                          false
% 1.11/1.07  --bmc1_dump_clauses_tptp                false
% 1.11/1.07  --bmc1_dump_unsat_core_tptp             false
% 1.11/1.07  --bmc1_dump_file                        -
% 1.11/1.07  --bmc1_ucm_expand_uc_limit              128
% 1.11/1.07  --bmc1_ucm_n_expand_iterations          6
% 1.11/1.07  --bmc1_ucm_extend_mode                  1
% 1.11/1.07  --bmc1_ucm_init_mode                    2
% 1.11/1.07  --bmc1_ucm_cone_mode                    none
% 1.11/1.07  --bmc1_ucm_reduced_relation_type        0
% 1.11/1.07  --bmc1_ucm_relax_model                  4
% 1.11/1.07  --bmc1_ucm_full_tr_after_sat            true
% 1.11/1.07  --bmc1_ucm_expand_neg_assumptions       false
% 1.11/1.07  --bmc1_ucm_layered_model                none
% 1.11/1.07  --bmc1_ucm_max_lemma_size               10
% 1.11/1.07  
% 1.11/1.07  ------ AIG Options
% 1.11/1.07  
% 1.11/1.07  --aig_mode                              false
% 1.11/1.07  
% 1.11/1.07  ------ Instantiation Options
% 1.11/1.07  
% 1.11/1.07  --instantiation_flag                    true
% 1.11/1.07  --inst_sos_flag                         false
% 1.11/1.07  --inst_sos_phase                        true
% 1.11/1.07  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.11/1.07  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.11/1.07  --inst_lit_sel_side                     num_symb
% 1.11/1.07  --inst_solver_per_active                1400
% 1.11/1.07  --inst_solver_calls_frac                1.
% 1.11/1.07  --inst_passive_queue_type               priority_queues
% 1.11/1.07  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.11/1.07  --inst_passive_queues_freq              [25;2]
% 1.11/1.07  --inst_dismatching                      true
% 1.11/1.07  --inst_eager_unprocessed_to_passive     true
% 1.11/1.07  --inst_prop_sim_given                   true
% 1.11/1.07  --inst_prop_sim_new                     false
% 1.11/1.07  --inst_subs_new                         false
% 1.11/1.07  --inst_eq_res_simp                      false
% 1.11/1.07  --inst_subs_given                       false
% 1.11/1.07  --inst_orphan_elimination               true
% 1.11/1.07  --inst_learning_loop_flag               true
% 1.11/1.07  --inst_learning_start                   3000
% 1.11/1.07  --inst_learning_factor                  2
% 1.11/1.07  --inst_start_prop_sim_after_learn       3
% 1.11/1.07  --inst_sel_renew                        solver
% 1.11/1.07  --inst_lit_activity_flag                true
% 1.11/1.07  --inst_restr_to_given                   false
% 1.11/1.07  --inst_activity_threshold               500
% 1.11/1.07  --inst_out_proof                        true
% 1.11/1.07  
% 1.11/1.07  ------ Resolution Options
% 1.11/1.07  
% 1.11/1.07  --resolution_flag                       true
% 1.11/1.07  --res_lit_sel                           adaptive
% 1.11/1.07  --res_lit_sel_side                      none
% 1.11/1.07  --res_ordering                          kbo
% 1.11/1.07  --res_to_prop_solver                    active
% 1.11/1.07  --res_prop_simpl_new                    false
% 1.11/1.07  --res_prop_simpl_given                  true
% 1.11/1.07  --res_passive_queue_type                priority_queues
% 1.11/1.07  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.11/1.07  --res_passive_queues_freq               [15;5]
% 1.11/1.07  --res_forward_subs                      full
% 1.11/1.07  --res_backward_subs                     full
% 1.11/1.07  --res_forward_subs_resolution           true
% 1.11/1.07  --res_backward_subs_resolution          true
% 1.11/1.07  --res_orphan_elimination                true
% 1.11/1.07  --res_time_limit                        2.
% 1.11/1.07  --res_out_proof                         true
% 1.11/1.07  
% 1.11/1.07  ------ Superposition Options
% 1.11/1.07  
% 1.11/1.07  --superposition_flag                    true
% 1.11/1.07  --sup_passive_queue_type                priority_queues
% 1.11/1.07  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.11/1.07  --sup_passive_queues_freq               [8;1;4]
% 1.11/1.07  --demod_completeness_check              fast
% 1.11/1.07  --demod_use_ground                      true
% 1.11/1.07  --sup_to_prop_solver                    passive
% 1.11/1.07  --sup_prop_simpl_new                    true
% 1.11/1.07  --sup_prop_simpl_given                  true
% 1.11/1.07  --sup_fun_splitting                     false
% 1.11/1.07  --sup_smt_interval                      50000
% 1.11/1.07  
% 1.11/1.07  ------ Superposition Simplification Setup
% 1.11/1.07  
% 1.11/1.07  --sup_indices_passive                   []
% 1.11/1.07  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.11/1.07  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.11/1.07  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.11/1.07  --sup_full_triv                         [TrivRules;PropSubs]
% 1.11/1.07  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.11/1.07  --sup_full_bw                           [BwDemod]
% 1.11/1.07  --sup_immed_triv                        [TrivRules]
% 1.11/1.07  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.11/1.07  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.11/1.07  --sup_immed_bw_main                     []
% 1.11/1.07  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.11/1.07  --sup_input_triv                        [Unflattening;TrivRules]
% 1.11/1.07  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.11/1.07  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.11/1.07  
% 1.11/1.07  ------ Combination Options
% 1.11/1.07  
% 1.11/1.07  --comb_res_mult                         3
% 1.11/1.07  --comb_sup_mult                         2
% 1.11/1.07  --comb_inst_mult                        10
% 1.11/1.07  
% 1.11/1.07  ------ Debug Options
% 1.11/1.07  
% 1.11/1.07  --dbg_backtrace                         false
% 1.11/1.07  --dbg_dump_prop_clauses                 false
% 1.11/1.07  --dbg_dump_prop_clauses_file            -
% 1.11/1.07  --dbg_out_stat                          false
% 1.11/1.07  ------ Parsing...
% 1.11/1.07  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.11/1.07  
% 1.11/1.07  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 1.11/1.07  
% 1.11/1.07  ------ Preprocessing... gs_s  sp: 6 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.11/1.07  
% 1.11/1.07  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.11/1.07  ------ Proving...
% 1.11/1.07  ------ Problem Properties 
% 1.11/1.07  
% 1.11/1.07  
% 1.11/1.07  clauses                                 22
% 1.11/1.07  conjectures                             2
% 1.11/1.07  EPR                                     2
% 1.11/1.07  Horn                                    17
% 1.11/1.07  unary                                   9
% 1.11/1.07  binary                                  6
% 1.11/1.07  lits                                    43
% 1.11/1.07  lits eq                                 18
% 1.11/1.07  fd_pure                                 0
% 1.11/1.07  fd_pseudo                               0
% 1.11/1.07  fd_cond                                 3
% 1.11/1.07  fd_pseudo_cond                          0
% 1.11/1.07  AC symbols                              0
% 1.11/1.07  
% 1.11/1.07  ------ Schedule dynamic 5 is on 
% 1.11/1.07  
% 1.11/1.07  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.11/1.07  
% 1.11/1.07  
% 1.11/1.07  ------ 
% 1.11/1.07  Current options:
% 1.11/1.07  ------ 
% 1.11/1.07  
% 1.11/1.07  ------ Input Options
% 1.11/1.07  
% 1.11/1.07  --out_options                           all
% 1.11/1.07  --tptp_safe_out                         true
% 1.11/1.07  --problem_path                          ""
% 1.11/1.07  --include_path                          ""
% 1.11/1.07  --clausifier                            res/vclausify_rel
% 1.11/1.07  --clausifier_options                    --mode clausify
% 1.11/1.07  --stdin                                 false
% 1.11/1.07  --stats_out                             all
% 1.11/1.07  
% 1.11/1.07  ------ General Options
% 1.11/1.07  
% 1.11/1.07  --fof                                   false
% 1.11/1.07  --time_out_real                         305.
% 1.11/1.07  --time_out_virtual                      -1.
% 1.11/1.07  --symbol_type_check                     false
% 1.11/1.07  --clausify_out                          false
% 1.11/1.07  --sig_cnt_out                           false
% 1.11/1.07  --trig_cnt_out                          false
% 1.11/1.07  --trig_cnt_out_tolerance                1.
% 1.11/1.07  --trig_cnt_out_sk_spl                   false
% 1.11/1.07  --abstr_cl_out                          false
% 1.11/1.07  
% 1.11/1.07  ------ Global Options
% 1.11/1.07  
% 1.11/1.07  --schedule                              default
% 1.11/1.07  --add_important_lit                     false
% 1.11/1.07  --prop_solver_per_cl                    1000
% 1.11/1.07  --min_unsat_core                        false
% 1.11/1.07  --soft_assumptions                      false
% 1.11/1.07  --soft_lemma_size                       3
% 1.11/1.07  --prop_impl_unit_size                   0
% 1.11/1.07  --prop_impl_unit                        []
% 1.11/1.07  --share_sel_clauses                     true
% 1.11/1.07  --reset_solvers                         false
% 1.11/1.07  --bc_imp_inh                            [conj_cone]
% 1.11/1.07  --conj_cone_tolerance                   3.
% 1.11/1.07  --extra_neg_conj                        none
% 1.11/1.07  --large_theory_mode                     true
% 1.11/1.07  --prolific_symb_bound                   200
% 1.11/1.07  --lt_threshold                          2000
% 1.11/1.07  --clause_weak_htbl                      true
% 1.11/1.07  --gc_record_bc_elim                     false
% 1.11/1.07  
% 1.11/1.07  ------ Preprocessing Options
% 1.11/1.07  
% 1.11/1.07  --preprocessing_flag                    true
% 1.11/1.07  --time_out_prep_mult                    0.1
% 1.11/1.07  --splitting_mode                        input
% 1.11/1.07  --splitting_grd                         true
% 1.11/1.07  --splitting_cvd                         false
% 1.11/1.07  --splitting_cvd_svl                     false
% 1.11/1.07  --splitting_nvd                         32
% 1.11/1.07  --sub_typing                            true
% 1.11/1.07  --prep_gs_sim                           true
% 1.11/1.07  --prep_unflatten                        true
% 1.11/1.07  --prep_res_sim                          true
% 1.11/1.07  --prep_upred                            true
% 1.11/1.07  --prep_sem_filter                       exhaustive
% 1.11/1.07  --prep_sem_filter_out                   false
% 1.11/1.07  --pred_elim                             true
% 1.11/1.07  --res_sim_input                         true
% 1.11/1.07  --eq_ax_congr_red                       true
% 1.11/1.07  --pure_diseq_elim                       true
% 1.11/1.07  --brand_transform                       false
% 1.11/1.07  --non_eq_to_eq                          false
% 1.11/1.07  --prep_def_merge                        true
% 1.11/1.07  --prep_def_merge_prop_impl              false
% 1.11/1.07  --prep_def_merge_mbd                    true
% 1.11/1.07  --prep_def_merge_tr_red                 false
% 1.11/1.07  --prep_def_merge_tr_cl                  false
% 1.11/1.07  --smt_preprocessing                     true
% 1.11/1.07  --smt_ac_axioms                         fast
% 1.11/1.07  --preprocessed_out                      false
% 1.11/1.07  --preprocessed_stats                    false
% 1.11/1.07  
% 1.11/1.07  ------ Abstraction refinement Options
% 1.11/1.07  
% 1.11/1.07  --abstr_ref                             []
% 1.11/1.07  --abstr_ref_prep                        false
% 1.11/1.07  --abstr_ref_until_sat                   false
% 1.11/1.07  --abstr_ref_sig_restrict                funpre
% 1.11/1.07  --abstr_ref_af_restrict_to_split_sk     false
% 1.11/1.07  --abstr_ref_under                       []
% 1.11/1.07  
% 1.11/1.07  ------ SAT Options
% 1.11/1.07  
% 1.11/1.07  --sat_mode                              false
% 1.11/1.07  --sat_fm_restart_options                ""
% 1.11/1.07  --sat_gr_def                            false
% 1.11/1.07  --sat_epr_types                         true
% 1.11/1.07  --sat_non_cyclic_types                  false
% 1.11/1.07  --sat_finite_models                     false
% 1.11/1.07  --sat_fm_lemmas                         false
% 1.11/1.07  --sat_fm_prep                           false
% 1.11/1.07  --sat_fm_uc_incr                        true
% 1.11/1.07  --sat_out_model                         small
% 1.11/1.07  --sat_out_clauses                       false
% 1.11/1.07  
% 1.11/1.07  ------ QBF Options
% 1.11/1.07  
% 1.11/1.07  --qbf_mode                              false
% 1.11/1.07  --qbf_elim_univ                         false
% 1.11/1.07  --qbf_dom_inst                          none
% 1.11/1.07  --qbf_dom_pre_inst                      false
% 1.11/1.07  --qbf_sk_in                             false
% 1.11/1.07  --qbf_pred_elim                         true
% 1.11/1.07  --qbf_split                             512
% 1.11/1.07  
% 1.11/1.07  ------ BMC1 Options
% 1.11/1.07  
% 1.11/1.07  --bmc1_incremental                      false
% 1.11/1.07  --bmc1_axioms                           reachable_all
% 1.11/1.07  --bmc1_min_bound                        0
% 1.11/1.07  --bmc1_max_bound                        -1
% 1.11/1.07  --bmc1_max_bound_default                -1
% 1.11/1.07  --bmc1_symbol_reachability              true
% 1.11/1.07  --bmc1_property_lemmas                  false
% 1.11/1.07  --bmc1_k_induction                      false
% 1.11/1.07  --bmc1_non_equiv_states                 false
% 1.11/1.07  --bmc1_deadlock                         false
% 1.11/1.07  --bmc1_ucm                              false
% 1.11/1.07  --bmc1_add_unsat_core                   none
% 1.11/1.07  --bmc1_unsat_core_children              false
% 1.11/1.07  --bmc1_unsat_core_extrapolate_axioms    false
% 1.11/1.07  --bmc1_out_stat                         full
% 1.11/1.07  --bmc1_ground_init                      false
% 1.11/1.07  --bmc1_pre_inst_next_state              false
% 1.11/1.07  --bmc1_pre_inst_state                   false
% 1.11/1.07  --bmc1_pre_inst_reach_state             false
% 1.11/1.07  --bmc1_out_unsat_core                   false
% 1.11/1.07  --bmc1_aig_witness_out                  false
% 1.11/1.07  --bmc1_verbose                          false
% 1.11/1.07  --bmc1_dump_clauses_tptp                false
% 1.11/1.07  --bmc1_dump_unsat_core_tptp             false
% 1.11/1.07  --bmc1_dump_file                        -
% 1.11/1.07  --bmc1_ucm_expand_uc_limit              128
% 1.11/1.07  --bmc1_ucm_n_expand_iterations          6
% 1.11/1.07  --bmc1_ucm_extend_mode                  1
% 1.11/1.07  --bmc1_ucm_init_mode                    2
% 1.11/1.07  --bmc1_ucm_cone_mode                    none
% 1.11/1.07  --bmc1_ucm_reduced_relation_type        0
% 1.11/1.07  --bmc1_ucm_relax_model                  4
% 1.11/1.07  --bmc1_ucm_full_tr_after_sat            true
% 1.11/1.07  --bmc1_ucm_expand_neg_assumptions       false
% 1.11/1.07  --bmc1_ucm_layered_model                none
% 1.11/1.07  --bmc1_ucm_max_lemma_size               10
% 1.11/1.07  
% 1.11/1.07  ------ AIG Options
% 1.11/1.07  
% 1.11/1.07  --aig_mode                              false
% 1.11/1.07  
% 1.11/1.07  ------ Instantiation Options
% 1.11/1.07  
% 1.11/1.07  --instantiation_flag                    true
% 1.11/1.07  --inst_sos_flag                         false
% 1.11/1.07  --inst_sos_phase                        true
% 1.11/1.07  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.11/1.07  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.11/1.07  --inst_lit_sel_side                     none
% 1.11/1.07  --inst_solver_per_active                1400
% 1.11/1.07  --inst_solver_calls_frac                1.
% 1.11/1.07  --inst_passive_queue_type               priority_queues
% 1.11/1.07  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.11/1.07  --inst_passive_queues_freq              [25;2]
% 1.11/1.07  --inst_dismatching                      true
% 1.11/1.07  --inst_eager_unprocessed_to_passive     true
% 1.11/1.07  --inst_prop_sim_given                   true
% 1.11/1.07  --inst_prop_sim_new                     false
% 1.11/1.07  --inst_subs_new                         false
% 1.11/1.07  --inst_eq_res_simp                      false
% 1.11/1.07  --inst_subs_given                       false
% 1.11/1.07  --inst_orphan_elimination               true
% 1.11/1.07  --inst_learning_loop_flag               true
% 1.11/1.07  --inst_learning_start                   3000
% 1.11/1.07  --inst_learning_factor                  2
% 1.11/1.07  --inst_start_prop_sim_after_learn       3
% 1.11/1.07  --inst_sel_renew                        solver
% 1.11/1.07  --inst_lit_activity_flag                true
% 1.11/1.07  --inst_restr_to_given                   false
% 1.11/1.07  --inst_activity_threshold               500
% 1.11/1.07  --inst_out_proof                        true
% 1.11/1.07  
% 1.11/1.07  ------ Resolution Options
% 1.11/1.07  
% 1.11/1.07  --resolution_flag                       false
% 1.11/1.07  --res_lit_sel                           adaptive
% 1.11/1.07  --res_lit_sel_side                      none
% 1.11/1.07  --res_ordering                          kbo
% 1.11/1.07  --res_to_prop_solver                    active
% 1.11/1.07  --res_prop_simpl_new                    false
% 1.11/1.07  --res_prop_simpl_given                  true
% 1.11/1.07  --res_passive_queue_type                priority_queues
% 1.11/1.07  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.11/1.07  --res_passive_queues_freq               [15;5]
% 1.11/1.07  --res_forward_subs                      full
% 1.11/1.07  --res_backward_subs                     full
% 1.11/1.07  --res_forward_subs_resolution           true
% 1.11/1.07  --res_backward_subs_resolution          true
% 1.11/1.07  --res_orphan_elimination                true
% 1.11/1.07  --res_time_limit                        2.
% 1.11/1.07  --res_out_proof                         true
% 1.11/1.07  
% 1.11/1.07  ------ Superposition Options
% 1.11/1.07  
% 1.11/1.07  --superposition_flag                    true
% 1.11/1.07  --sup_passive_queue_type                priority_queues
% 1.11/1.07  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.11/1.07  --sup_passive_queues_freq               [8;1;4]
% 1.11/1.07  --demod_completeness_check              fast
% 1.11/1.07  --demod_use_ground                      true
% 1.11/1.07  --sup_to_prop_solver                    passive
% 1.11/1.07  --sup_prop_simpl_new                    true
% 1.11/1.07  --sup_prop_simpl_given                  true
% 1.11/1.07  --sup_fun_splitting                     false
% 1.11/1.07  --sup_smt_interval                      50000
% 1.11/1.07  
% 1.11/1.07  ------ Superposition Simplification Setup
% 1.11/1.07  
% 1.11/1.07  --sup_indices_passive                   []
% 1.11/1.07  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.11/1.07  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.11/1.07  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.11/1.07  --sup_full_triv                         [TrivRules;PropSubs]
% 1.11/1.07  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.11/1.07  --sup_full_bw                           [BwDemod]
% 1.11/1.07  --sup_immed_triv                        [TrivRules]
% 1.11/1.07  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.11/1.07  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.11/1.07  --sup_immed_bw_main                     []
% 1.11/1.07  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.11/1.07  --sup_input_triv                        [Unflattening;TrivRules]
% 1.11/1.07  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.11/1.07  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.11/1.07  
% 1.11/1.07  ------ Combination Options
% 1.11/1.07  
% 1.11/1.07  --comb_res_mult                         3
% 1.11/1.07  --comb_sup_mult                         2
% 1.11/1.07  --comb_inst_mult                        10
% 1.11/1.07  
% 1.11/1.07  ------ Debug Options
% 1.11/1.07  
% 1.11/1.07  --dbg_backtrace                         false
% 1.11/1.07  --dbg_dump_prop_clauses                 false
% 1.11/1.07  --dbg_dump_prop_clauses_file            -
% 1.11/1.07  --dbg_out_stat                          false
% 1.11/1.07  
% 1.11/1.07  
% 1.11/1.07  
% 1.11/1.07  
% 1.11/1.07  ------ Proving...
% 1.11/1.07  
% 1.11/1.07  
% 1.11/1.07  % SZS status Theorem for theBenchmark.p
% 1.11/1.07  
% 1.11/1.07  % SZS output start CNFRefutation for theBenchmark.p
% 1.11/1.07  
% 1.11/1.07  fof(f13,conjecture,(
% 1.11/1.07    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 1.11/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.11/1.07  
% 1.11/1.07  fof(f14,negated_conjecture,(
% 1.11/1.07    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 1.11/1.07    inference(negated_conjecture,[],[f13])).
% 1.11/1.07  
% 1.11/1.07  fof(f24,plain,(
% 1.11/1.07    ? [X0,X1,X2] : (k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)))),
% 1.11/1.07    inference(ennf_transformation,[],[f14])).
% 1.11/1.07  
% 1.11/1.07  fof(f25,plain,(
% 1.11/1.07    ? [X0,X1,X2] : (k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2))),
% 1.11/1.07    inference(flattening,[],[f24])).
% 1.11/1.07  
% 1.11/1.07  fof(f28,plain,(
% 1.11/1.07    ? [X0,X1,X2] : (k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => (k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) & v1_funct_2(sK2,k1_xboole_0,sK0) & v1_funct_1(sK2))),
% 1.11/1.07    introduced(choice_axiom,[])).
% 1.11/1.07  
% 1.11/1.07  fof(f29,plain,(
% 1.11/1.07    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) & v1_funct_2(sK2,k1_xboole_0,sK0) & v1_funct_1(sK2)),
% 1.11/1.07    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f28])).
% 1.11/1.07  
% 1.11/1.07  fof(f49,plain,(
% 1.11/1.07    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 1.11/1.07    inference(cnf_transformation,[],[f29])).
% 1.11/1.07  
% 1.11/1.07  fof(f4,axiom,(
% 1.11/1.07    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.11/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.11/1.07  
% 1.11/1.07  fof(f26,plain,(
% 1.11/1.07    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.11/1.07    inference(nnf_transformation,[],[f4])).
% 1.11/1.07  
% 1.11/1.07  fof(f27,plain,(
% 1.11/1.07    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.11/1.07    inference(flattening,[],[f26])).
% 1.11/1.07  
% 1.11/1.07  fof(f34,plain,(
% 1.11/1.07    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 1.11/1.07    inference(cnf_transformation,[],[f27])).
% 1.11/1.07  
% 1.11/1.07  fof(f52,plain,(
% 1.11/1.07    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.11/1.07    inference(equality_resolution,[],[f34])).
% 1.11/1.07  
% 1.11/1.07  fof(f10,axiom,(
% 1.11/1.07    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 1.11/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.11/1.07  
% 1.11/1.07  fof(f19,plain,(
% 1.11/1.07    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.11/1.07    inference(ennf_transformation,[],[f10])).
% 1.11/1.07  
% 1.11/1.07  fof(f41,plain,(
% 1.11/1.07    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.11/1.07    inference(cnf_transformation,[],[f19])).
% 1.11/1.07  
% 1.11/1.07  fof(f8,axiom,(
% 1.11/1.07    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.11/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.11/1.07  
% 1.11/1.07  fof(f17,plain,(
% 1.11/1.07    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.11/1.07    inference(ennf_transformation,[],[f8])).
% 1.11/1.07  
% 1.11/1.07  fof(f39,plain,(
% 1.11/1.07    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.11/1.07    inference(cnf_transformation,[],[f17])).
% 1.11/1.07  
% 1.11/1.07  fof(f3,axiom,(
% 1.11/1.07    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.11/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.11/1.07  
% 1.11/1.07  fof(f32,plain,(
% 1.11/1.07    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.11/1.07    inference(cnf_transformation,[],[f3])).
% 1.11/1.07  
% 1.11/1.07  fof(f12,axiom,(
% 1.11/1.07    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 1.11/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.11/1.07  
% 1.11/1.07  fof(f22,plain,(
% 1.11/1.07    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.11/1.07    inference(ennf_transformation,[],[f12])).
% 1.11/1.07  
% 1.11/1.07  fof(f23,plain,(
% 1.11/1.07    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.11/1.07    inference(flattening,[],[f22])).
% 1.11/1.07  
% 1.11/1.07  fof(f45,plain,(
% 1.11/1.07    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.11/1.07    inference(cnf_transformation,[],[f23])).
% 1.11/1.07  
% 1.11/1.07  fof(f47,plain,(
% 1.11/1.07    v1_funct_1(sK2)),
% 1.11/1.07    inference(cnf_transformation,[],[f29])).
% 1.11/1.07  
% 1.11/1.07  fof(f11,axiom,(
% 1.11/1.07    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k8_relset_1(X0,X1,X2,X1) = X0))),
% 1.11/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.11/1.07  
% 1.11/1.07  fof(f20,plain,(
% 1.11/1.07    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.11/1.07    inference(ennf_transformation,[],[f11])).
% 1.11/1.07  
% 1.11/1.07  fof(f21,plain,(
% 1.11/1.07    ! [X0,X1,X2] : (k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.11/1.07    inference(flattening,[],[f20])).
% 1.11/1.07  
% 1.11/1.07  fof(f43,plain,(
% 1.11/1.07    ( ! [X2,X0,X1] : (k8_relset_1(X0,X1,X2,X1) = X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.11/1.07    inference(cnf_transformation,[],[f21])).
% 1.11/1.07  
% 1.11/1.07  fof(f53,plain,(
% 1.11/1.07    ( ! [X2,X1] : (k1_xboole_0 = k8_relset_1(k1_xboole_0,X1,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~v1_funct_1(X2)) )),
% 1.11/1.07    inference(equality_resolution,[],[f43])).
% 1.11/1.07  
% 1.11/1.07  fof(f7,axiom,(
% 1.11/1.07    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.11/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.11/1.07  
% 1.11/1.07  fof(f37,plain,(
% 1.11/1.07    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.11/1.07    inference(cnf_transformation,[],[f7])).
% 1.11/1.07  
% 1.11/1.07  fof(f38,plain,(
% 1.11/1.07    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.11/1.07    inference(cnf_transformation,[],[f7])).
% 1.11/1.07  
% 1.11/1.07  fof(f33,plain,(
% 1.11/1.07    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 1.11/1.07    inference(cnf_transformation,[],[f27])).
% 1.11/1.07  
% 1.11/1.07  fof(f1,axiom,(
% 1.11/1.07    v1_xboole_0(k1_xboole_0)),
% 1.11/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.11/1.07  
% 1.11/1.07  fof(f30,plain,(
% 1.11/1.07    v1_xboole_0(k1_xboole_0)),
% 1.11/1.07    inference(cnf_transformation,[],[f1])).
% 1.11/1.07  
% 1.11/1.07  fof(f2,axiom,(
% 1.11/1.07    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.11/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.11/1.07  
% 1.11/1.07  fof(f16,plain,(
% 1.11/1.07    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.11/1.07    inference(ennf_transformation,[],[f2])).
% 1.11/1.07  
% 1.11/1.07  fof(f31,plain,(
% 1.11/1.07    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 1.11/1.07    inference(cnf_transformation,[],[f16])).
% 1.11/1.07  
% 1.11/1.07  fof(f35,plain,(
% 1.11/1.07    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.11/1.07    inference(cnf_transformation,[],[f27])).
% 1.11/1.07  
% 1.11/1.07  fof(f51,plain,(
% 1.11/1.07    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.11/1.07    inference(equality_resolution,[],[f35])).
% 1.11/1.07  
% 1.11/1.07  fof(f9,axiom,(
% 1.11/1.07    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 1.11/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.11/1.07  
% 1.11/1.07  fof(f18,plain,(
% 1.11/1.07    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 1.11/1.07    inference(ennf_transformation,[],[f9])).
% 1.11/1.07  
% 1.11/1.07  fof(f40,plain,(
% 1.11/1.07    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 1.11/1.07    inference(cnf_transformation,[],[f18])).
% 1.11/1.07  
% 1.11/1.07  fof(f42,plain,(
% 1.11/1.07    ( ! [X2,X0,X1] : (k8_relset_1(X0,X1,X2,X1) = X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.11/1.07    inference(cnf_transformation,[],[f21])).
% 1.11/1.07  
% 1.11/1.07  fof(f46,plain,(
% 1.11/1.07    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.11/1.07    inference(cnf_transformation,[],[f23])).
% 1.11/1.07  
% 1.11/1.07  fof(f5,axiom,(
% 1.11/1.07    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.11/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.11/1.07  
% 1.11/1.07  fof(f36,plain,(
% 1.11/1.07    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.11/1.07    inference(cnf_transformation,[],[f5])).
% 1.11/1.07  
% 1.11/1.07  fof(f50,plain,(
% 1.11/1.07    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)),
% 1.11/1.07    inference(cnf_transformation,[],[f29])).
% 1.11/1.07  
% 1.11/1.07  cnf(c_18,negated_conjecture,
% 1.11/1.07      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
% 1.11/1.07      inference(cnf_transformation,[],[f49]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_783,plain,
% 1.11/1.07      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) = iProver_top ),
% 1.11/1.07      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_4,plain,
% 1.11/1.07      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 1.11/1.07      inference(cnf_transformation,[],[f52]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_803,plain,
% 1.11/1.07      ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 1.11/1.07      inference(demodulation,[status(thm)],[c_783,c_4]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_11,plain,
% 1.11/1.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.11/1.07      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 1.11/1.07      inference(cnf_transformation,[],[f41]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_784,plain,
% 1.11/1.07      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 1.11/1.07      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 1.11/1.07      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_1369,plain,
% 1.11/1.07      ( k8_relset_1(k1_xboole_0,X0,X1,X2) = k10_relat_1(X1,X2)
% 1.11/1.07      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 1.11/1.07      inference(superposition,[status(thm)],[c_4,c_784]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_1597,plain,
% 1.11/1.07      ( k8_relset_1(k1_xboole_0,X0,sK2,X1) = k10_relat_1(sK2,X1) ),
% 1.11/1.07      inference(superposition,[status(thm)],[c_803,c_1369]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_9,plain,
% 1.11/1.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.11/1.07      | v1_relat_1(X0) ),
% 1.11/1.07      inference(cnf_transformation,[],[f39]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_2,plain,
% 1.11/1.07      ( r1_tarski(k1_xboole_0,X0) ),
% 1.11/1.07      inference(cnf_transformation,[],[f32]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_15,plain,
% 1.11/1.07      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 1.11/1.07      | ~ r1_tarski(k2_relat_1(X0),X1)
% 1.11/1.07      | ~ v1_funct_1(X0)
% 1.11/1.07      | ~ v1_relat_1(X0) ),
% 1.11/1.07      inference(cnf_transformation,[],[f45]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_172,plain,
% 1.11/1.07      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 1.11/1.07      | ~ v1_funct_1(X0)
% 1.11/1.07      | ~ v1_relat_1(X0)
% 1.11/1.07      | X1 != X2
% 1.11/1.07      | k2_relat_1(X0) != k1_xboole_0 ),
% 1.11/1.07      inference(resolution_lifted,[status(thm)],[c_2,c_15]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_173,plain,
% 1.11/1.07      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 1.11/1.07      | ~ v1_funct_1(X0)
% 1.11/1.07      | ~ v1_relat_1(X0)
% 1.11/1.07      | k2_relat_1(X0) != k1_xboole_0 ),
% 1.11/1.07      inference(unflattening,[status(thm)],[c_172]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_20,negated_conjecture,
% 1.11/1.07      ( v1_funct_1(sK2) ),
% 1.11/1.07      inference(cnf_transformation,[],[f47]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_275,plain,
% 1.11/1.07      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 1.11/1.07      | ~ v1_relat_1(X0)
% 1.11/1.07      | k2_relat_1(X0) != k1_xboole_0
% 1.11/1.07      | sK2 != X0 ),
% 1.11/1.07      inference(resolution_lifted,[status(thm)],[c_173,c_20]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_276,plain,
% 1.11/1.07      ( v1_funct_2(sK2,k1_relat_1(sK2),X0)
% 1.11/1.07      | ~ v1_relat_1(sK2)
% 1.11/1.07      | k2_relat_1(sK2) != k1_xboole_0 ),
% 1.11/1.07      inference(unflattening,[status(thm)],[c_275]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_340,plain,
% 1.11/1.07      ( v1_funct_2(sK2,k1_relat_1(sK2),X0)
% 1.11/1.07      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 1.11/1.07      | k2_relat_1(sK2) != k1_xboole_0
% 1.11/1.07      | sK2 != X1 ),
% 1.11/1.07      inference(resolution_lifted,[status(thm)],[c_9,c_276]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_341,plain,
% 1.11/1.07      ( v1_funct_2(sK2,k1_relat_1(sK2),X0)
% 1.11/1.07      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.11/1.07      | k2_relat_1(sK2) != k1_xboole_0 ),
% 1.11/1.07      inference(unflattening,[status(thm)],[c_340]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_12,plain,
% 1.11/1.07      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 1.11/1.07      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 1.11/1.07      | ~ v1_funct_1(X0)
% 1.11/1.07      | k8_relset_1(k1_xboole_0,X1,X0,X1) = k1_xboole_0 ),
% 1.11/1.07      inference(cnf_transformation,[],[f53]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_308,plain,
% 1.11/1.07      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 1.11/1.07      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 1.11/1.07      | k8_relset_1(k1_xboole_0,X1,X0,X1) = k1_xboole_0
% 1.11/1.07      | sK2 != X0 ),
% 1.11/1.07      inference(resolution_lifted,[status(thm)],[c_12,c_20]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_309,plain,
% 1.11/1.07      ( ~ v1_funct_2(sK2,k1_xboole_0,X0)
% 1.11/1.07      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
% 1.11/1.07      | k8_relset_1(k1_xboole_0,X0,sK2,X0) = k1_xboole_0 ),
% 1.11/1.07      inference(unflattening,[status(thm)],[c_308]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_421,plain,
% 1.11/1.07      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.11/1.07      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
% 1.11/1.07      | X2 != X3
% 1.11/1.07      | k8_relset_1(k1_xboole_0,X2,sK2,X2) = k1_xboole_0
% 1.11/1.07      | k1_relat_1(sK2) != k1_xboole_0
% 1.11/1.07      | k2_relat_1(sK2) != k1_xboole_0
% 1.11/1.07      | sK2 != sK2 ),
% 1.11/1.07      inference(resolution_lifted,[status(thm)],[c_341,c_309]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_422,plain,
% 1.11/1.07      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.11/1.07      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
% 1.11/1.07      | k8_relset_1(k1_xboole_0,X2,sK2,X2) = k1_xboole_0
% 1.11/1.07      | k1_relat_1(sK2) != k1_xboole_0
% 1.11/1.07      | k2_relat_1(sK2) != k1_xboole_0 ),
% 1.11/1.07      inference(unflattening,[status(thm)],[c_421]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_520,plain,
% 1.11/1.07      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
% 1.11/1.07      | k8_relset_1(k1_xboole_0,X0,sK2,X0) = k1_xboole_0
% 1.11/1.07      | ~ sP0_iProver_split ),
% 1.11/1.07      inference(splitting,
% 1.11/1.07                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 1.11/1.07                [c_422]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_776,plain,
% 1.11/1.07      ( k8_relset_1(k1_xboole_0,X0,sK2,X0) = k1_xboole_0
% 1.11/1.07      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
% 1.11/1.07      | sP0_iProver_split != iProver_top ),
% 1.11/1.07      inference(predicate_to_equality,[status(thm)],[c_520]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_862,plain,
% 1.11/1.07      ( k8_relset_1(k1_xboole_0,X0,sK2,X0) = k1_xboole_0
% 1.11/1.07      | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 1.11/1.07      | sP0_iProver_split != iProver_top ),
% 1.11/1.07      inference(light_normalisation,[status(thm)],[c_776,c_4]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_866,plain,
% 1.11/1.07      ( k8_relset_1(k1_xboole_0,X0,sK2,X0) = k1_xboole_0
% 1.11/1.07      | sP0_iProver_split != iProver_top ),
% 1.11/1.07      inference(forward_subsumption_resolution,
% 1.11/1.07                [status(thm)],
% 1.11/1.07                [c_862,c_803]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_1718,plain,
% 1.11/1.07      ( k10_relat_1(sK2,X0) = k1_xboole_0
% 1.11/1.07      | sP0_iProver_split != iProver_top ),
% 1.11/1.07      inference(demodulation,[status(thm)],[c_1597,c_866]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_8,plain,
% 1.11/1.07      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 1.11/1.07      inference(cnf_transformation,[],[f37]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_7,plain,
% 1.11/1.07      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 1.11/1.07      inference(cnf_transformation,[],[f38]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_5,plain,
% 1.11/1.07      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 1.11/1.07      | k1_xboole_0 = X0
% 1.11/1.07      | k1_xboole_0 = X1 ),
% 1.11/1.07      inference(cnf_transformation,[],[f33]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_47,plain,
% 1.11/1.07      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 1.11/1.07      | k1_xboole_0 = k1_xboole_0 ),
% 1.11/1.07      inference(instantiation,[status(thm)],[c_5]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_48,plain,
% 1.11/1.07      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 1.11/1.07      inference(instantiation,[status(thm)],[c_4]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_0,plain,
% 1.11/1.07      ( v1_xboole_0(k1_xboole_0) ),
% 1.11/1.07      inference(cnf_transformation,[],[f30]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_522,plain,
% 1.11/1.07      ( sP1_iProver_split
% 1.11/1.07      | sP0_iProver_split
% 1.11/1.07      | k1_relat_1(sK2) != k1_xboole_0
% 1.11/1.07      | k2_relat_1(sK2) != k1_xboole_0 ),
% 1.11/1.07      inference(splitting,
% 1.11/1.07                [splitting(split),new_symbols(definition,[])],
% 1.11/1.07                [c_422]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_546,plain,
% 1.11/1.07      ( k1_relat_1(sK2) != k1_xboole_0
% 1.11/1.07      | k2_relat_1(sK2) != k1_xboole_0
% 1.11/1.07      | sP1_iProver_split = iProver_top
% 1.11/1.07      | sP0_iProver_split = iProver_top ),
% 1.11/1.07      inference(predicate_to_equality,[status(thm)],[c_522]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_1,plain,
% 1.11/1.07      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 1.11/1.07      inference(cnf_transformation,[],[f31]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_969,plain,
% 1.11/1.07      ( ~ v1_xboole_0(sK2) | k1_xboole_0 = sK2 ),
% 1.11/1.07      inference(instantiation,[status(thm)],[c_1]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_528,plain,( X0 = X0 ),theory(equality) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_975,plain,
% 1.11/1.07      ( sK2 = sK2 ),
% 1.11/1.07      inference(instantiation,[status(thm)],[c_528]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_529,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_912,plain,
% 1.11/1.07      ( k2_relat_1(sK2) != X0
% 1.11/1.07      | k2_relat_1(sK2) = k1_xboole_0
% 1.11/1.07      | k1_xboole_0 != X0 ),
% 1.11/1.07      inference(instantiation,[status(thm)],[c_529]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_985,plain,
% 1.11/1.07      ( k2_relat_1(sK2) != k2_relat_1(X0)
% 1.11/1.07      | k2_relat_1(sK2) = k1_xboole_0
% 1.11/1.07      | k1_xboole_0 != k2_relat_1(X0) ),
% 1.11/1.07      inference(instantiation,[status(thm)],[c_912]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_987,plain,
% 1.11/1.07      ( k2_relat_1(sK2) != k2_relat_1(k1_xboole_0)
% 1.11/1.07      | k2_relat_1(sK2) = k1_xboole_0
% 1.11/1.07      | k1_xboole_0 != k2_relat_1(k1_xboole_0) ),
% 1.11/1.07      inference(instantiation,[status(thm)],[c_985]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_534,plain,
% 1.11/1.07      ( X0 != X1 | k2_relat_1(X0) = k2_relat_1(X1) ),
% 1.11/1.07      theory(equality) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_986,plain,
% 1.11/1.07      ( k2_relat_1(sK2) = k2_relat_1(X0) | sK2 != X0 ),
% 1.11/1.07      inference(instantiation,[status(thm)],[c_534]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_988,plain,
% 1.11/1.07      ( k2_relat_1(sK2) = k2_relat_1(k1_xboole_0) | sK2 != k1_xboole_0 ),
% 1.11/1.07      inference(instantiation,[status(thm)],[c_986]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_913,plain,
% 1.11/1.07      ( k1_relat_1(sK2) != X0
% 1.11/1.07      | k1_relat_1(sK2) = k1_xboole_0
% 1.11/1.07      | k1_xboole_0 != X0 ),
% 1.11/1.07      inference(instantiation,[status(thm)],[c_529]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_992,plain,
% 1.11/1.07      ( k1_relat_1(sK2) != k1_relat_1(X0)
% 1.11/1.07      | k1_relat_1(sK2) = k1_xboole_0
% 1.11/1.07      | k1_xboole_0 != k1_relat_1(X0) ),
% 1.11/1.07      inference(instantiation,[status(thm)],[c_913]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_994,plain,
% 1.11/1.07      ( k1_relat_1(sK2) != k1_relat_1(k1_xboole_0)
% 1.11/1.07      | k1_relat_1(sK2) = k1_xboole_0
% 1.11/1.07      | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
% 1.11/1.07      inference(instantiation,[status(thm)],[c_992]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_535,plain,
% 1.11/1.07      ( X0 != X1 | k1_relat_1(X0) = k1_relat_1(X1) ),
% 1.11/1.07      theory(equality) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_993,plain,
% 1.11/1.07      ( k1_relat_1(sK2) = k1_relat_1(X0) | sK2 != X0 ),
% 1.11/1.07      inference(instantiation,[status(thm)],[c_535]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_995,plain,
% 1.11/1.07      ( k1_relat_1(sK2) = k1_relat_1(k1_xboole_0) | sK2 != k1_xboole_0 ),
% 1.11/1.07      inference(instantiation,[status(thm)],[c_993]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_1131,plain,
% 1.11/1.07      ( k2_relat_1(X0) != X1
% 1.11/1.07      | k1_xboole_0 != X1
% 1.11/1.07      | k1_xboole_0 = k2_relat_1(X0) ),
% 1.11/1.07      inference(instantiation,[status(thm)],[c_529]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_1132,plain,
% 1.11/1.07      ( k2_relat_1(k1_xboole_0) != k1_xboole_0
% 1.11/1.07      | k1_xboole_0 = k2_relat_1(k1_xboole_0)
% 1.11/1.07      | k1_xboole_0 != k1_xboole_0 ),
% 1.11/1.07      inference(instantiation,[status(thm)],[c_1131]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_3,plain,
% 1.11/1.07      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 1.11/1.07      inference(cnf_transformation,[],[f51]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_521,plain,
% 1.11/1.07      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.11/1.07      | ~ sP1_iProver_split ),
% 1.11/1.07      inference(splitting,
% 1.11/1.07                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 1.11/1.07                [c_422]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_775,plain,
% 1.11/1.07      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 1.11/1.07      | sP1_iProver_split != iProver_top ),
% 1.11/1.07      inference(predicate_to_equality,[status(thm)],[c_521]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_1138,plain,
% 1.11/1.07      ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 1.11/1.07      | sP1_iProver_split != iProver_top ),
% 1.11/1.07      inference(superposition,[status(thm)],[c_3,c_775]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_1155,plain,
% 1.11/1.07      ( k1_relat_1(X0) != X1
% 1.11/1.07      | k1_xboole_0 != X1
% 1.11/1.07      | k1_xboole_0 = k1_relat_1(X0) ),
% 1.11/1.07      inference(instantiation,[status(thm)],[c_529]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_1156,plain,
% 1.11/1.07      ( k1_relat_1(k1_xboole_0) != k1_xboole_0
% 1.11/1.07      | k1_xboole_0 = k1_relat_1(k1_xboole_0)
% 1.11/1.07      | k1_xboole_0 != k1_xboole_0 ),
% 1.11/1.07      inference(instantiation,[status(thm)],[c_1155]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_10,plain,
% 1.11/1.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.11/1.07      | ~ v1_xboole_0(X1)
% 1.11/1.07      | v1_xboole_0(X0) ),
% 1.11/1.07      inference(cnf_transformation,[],[f40]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_1020,plain,
% 1.11/1.07      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.11/1.07      | ~ v1_xboole_0(X0)
% 1.11/1.07      | v1_xboole_0(sK2) ),
% 1.11/1.07      inference(instantiation,[status(thm)],[c_10]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_1453,plain,
% 1.11/1.07      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
% 1.11/1.07      | v1_xboole_0(sK2)
% 1.11/1.07      | ~ v1_xboole_0(k1_xboole_0) ),
% 1.11/1.07      inference(instantiation,[status(thm)],[c_1020]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_1076,plain,
% 1.11/1.07      ( X0 != X1 | sK2 != X1 | sK2 = X0 ),
% 1.11/1.07      inference(instantiation,[status(thm)],[c_529]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_1516,plain,
% 1.11/1.07      ( X0 != sK2 | sK2 = X0 | sK2 != sK2 ),
% 1.11/1.07      inference(instantiation,[status(thm)],[c_1076]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_1517,plain,
% 1.11/1.07      ( sK2 != sK2 | sK2 = k1_xboole_0 | k1_xboole_0 != sK2 ),
% 1.11/1.07      inference(instantiation,[status(thm)],[c_1516]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_2259,plain,
% 1.11/1.07      ( k10_relat_1(sK2,X0) = k1_xboole_0 ),
% 1.11/1.07      inference(global_propositional_subsumption,
% 1.11/1.07                [status(thm)],
% 1.11/1.07                [c_1718,c_18,c_8,c_7,c_47,c_48,c_0,c_546,c_803,c_969,
% 1.11/1.07                 c_975,c_987,c_988,c_994,c_995,c_1132,c_1138,c_1156,
% 1.11/1.07                 c_1453,c_1517]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_785,plain,
% 1.11/1.07      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 1.11/1.07      | v1_xboole_0(X1) != iProver_top
% 1.11/1.07      | v1_xboole_0(X0) = iProver_top ),
% 1.11/1.07      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_1396,plain,
% 1.11/1.07      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 1.11/1.07      | v1_xboole_0(X1) != iProver_top
% 1.11/1.07      | v1_xboole_0(X0) = iProver_top ),
% 1.11/1.07      inference(superposition,[status(thm)],[c_3,c_785]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_1607,plain,
% 1.11/1.07      ( v1_xboole_0(X0) != iProver_top | v1_xboole_0(sK2) = iProver_top ),
% 1.11/1.07      inference(superposition,[status(thm)],[c_803,c_1396]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_23,plain,
% 1.11/1.07      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) = iProver_top ),
% 1.11/1.07      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_55,plain,
% 1.11/1.07      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 1.11/1.07      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_1454,plain,
% 1.11/1.07      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
% 1.11/1.07      | v1_xboole_0(sK2) = iProver_top
% 1.11/1.07      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 1.11/1.07      inference(predicate_to_equality,[status(thm)],[c_1453]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_1830,plain,
% 1.11/1.07      ( v1_xboole_0(sK2) = iProver_top ),
% 1.11/1.07      inference(global_propositional_subsumption,
% 1.11/1.07                [status(thm)],
% 1.11/1.07                [c_1607,c_23,c_55,c_1454]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_787,plain,
% 1.11/1.07      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 1.11/1.07      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_1835,plain,
% 1.11/1.07      ( sK2 = k1_xboole_0 ),
% 1.11/1.07      inference(superposition,[status(thm)],[c_1830,c_787]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_2262,plain,
% 1.11/1.07      ( k10_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 1.11/1.07      inference(light_normalisation,[status(thm)],[c_2259,c_1835]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_2264,plain,
% 1.11/1.07      ( k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 1.11/1.07      inference(instantiation,[status(thm)],[c_2262]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_13,plain,
% 1.11/1.07      ( ~ v1_funct_2(X0,X1,X2)
% 1.11/1.07      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.11/1.07      | ~ v1_funct_1(X0)
% 1.11/1.07      | k8_relset_1(X1,X2,X0,X2) = X1
% 1.11/1.07      | k1_xboole_0 = X2 ),
% 1.11/1.07      inference(cnf_transformation,[],[f42]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_290,plain,
% 1.11/1.07      ( ~ v1_funct_2(X0,X1,X2)
% 1.11/1.07      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.11/1.07      | k8_relset_1(X1,X2,X0,X2) = X1
% 1.11/1.07      | sK2 != X0
% 1.11/1.07      | k1_xboole_0 = X2 ),
% 1.11/1.07      inference(resolution_lifted,[status(thm)],[c_13,c_20]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_291,plain,
% 1.11/1.07      ( ~ v1_funct_2(sK2,X0,X1)
% 1.11/1.07      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.11/1.07      | k8_relset_1(X0,X1,sK2,X1) = X0
% 1.11/1.07      | k1_xboole_0 = X1 ),
% 1.11/1.07      inference(unflattening,[status(thm)],[c_290]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_397,plain,
% 1.11/1.07      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.11/1.07      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 1.11/1.07      | X3 != X4
% 1.11/1.07      | k8_relset_1(X2,X3,sK2,X3) = X2
% 1.11/1.07      | k1_relat_1(sK2) != X2
% 1.11/1.07      | k2_relat_1(sK2) != k1_xboole_0
% 1.11/1.07      | sK2 != sK2
% 1.11/1.07      | k1_xboole_0 = X3 ),
% 1.11/1.07      inference(resolution_lifted,[status(thm)],[c_341,c_291]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_398,plain,
% 1.11/1.07      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.11/1.07      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X2)))
% 1.11/1.07      | k8_relset_1(k1_relat_1(sK2),X2,sK2,X2) = k1_relat_1(sK2)
% 1.11/1.07      | k2_relat_1(sK2) != k1_xboole_0
% 1.11/1.07      | k1_xboole_0 = X2 ),
% 1.11/1.07      inference(unflattening,[status(thm)],[c_397]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_14,plain,
% 1.11/1.07      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 1.11/1.07      | ~ r1_tarski(k2_relat_1(X0),X1)
% 1.11/1.07      | ~ v1_funct_1(X0)
% 1.11/1.07      | ~ v1_relat_1(X0) ),
% 1.11/1.07      inference(cnf_transformation,[],[f46]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_190,plain,
% 1.11/1.07      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 1.11/1.07      | ~ v1_funct_1(X0)
% 1.11/1.07      | ~ v1_relat_1(X0)
% 1.11/1.07      | X1 != X2
% 1.11/1.07      | k2_relat_1(X0) != k1_xboole_0 ),
% 1.11/1.07      inference(resolution_lifted,[status(thm)],[c_2,c_14]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_191,plain,
% 1.11/1.07      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 1.11/1.07      | ~ v1_funct_1(X0)
% 1.11/1.07      | ~ v1_relat_1(X0)
% 1.11/1.07      | k2_relat_1(X0) != k1_xboole_0 ),
% 1.11/1.07      inference(unflattening,[status(thm)],[c_190]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_260,plain,
% 1.11/1.07      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 1.11/1.07      | ~ v1_relat_1(X0)
% 1.11/1.07      | k2_relat_1(X0) != k1_xboole_0
% 1.11/1.07      | sK2 != X0 ),
% 1.11/1.07      inference(resolution_lifted,[status(thm)],[c_191,c_20]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_261,plain,
% 1.11/1.07      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X0)))
% 1.11/1.07      | ~ v1_relat_1(sK2)
% 1.11/1.07      | k2_relat_1(sK2) != k1_xboole_0 ),
% 1.11/1.07      inference(unflattening,[status(thm)],[c_260]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_355,plain,
% 1.11/1.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.11/1.07      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X3)))
% 1.11/1.07      | k2_relat_1(sK2) != k1_xboole_0
% 1.11/1.07      | sK2 != X0 ),
% 1.11/1.07      inference(resolution_lifted,[status(thm)],[c_9,c_261]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_356,plain,
% 1.11/1.07      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.11/1.07      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X2)))
% 1.11/1.07      | k2_relat_1(sK2) != k1_xboole_0 ),
% 1.11/1.07      inference(unflattening,[status(thm)],[c_355]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_402,plain,
% 1.11/1.07      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.11/1.07      | k8_relset_1(k1_relat_1(sK2),X2,sK2,X2) = k1_relat_1(sK2)
% 1.11/1.07      | k2_relat_1(sK2) != k1_xboole_0
% 1.11/1.07      | k1_xboole_0 = X2 ),
% 1.11/1.07      inference(global_propositional_subsumption,
% 1.11/1.07                [status(thm)],
% 1.11/1.07                [c_398,c_356]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_523,plain,
% 1.11/1.07      ( k8_relset_1(k1_relat_1(sK2),X0,sK2,X0) = k1_relat_1(sK2)
% 1.11/1.07      | k1_xboole_0 = X0
% 1.11/1.07      | ~ sP2_iProver_split ),
% 1.11/1.07      inference(splitting,
% 1.11/1.07                [splitting(split),new_symbols(definition,[sP2_iProver_split])],
% 1.11/1.07                [c_402]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_779,plain,
% 1.11/1.07      ( k8_relset_1(k1_relat_1(sK2),X0,sK2,X0) = k1_relat_1(sK2)
% 1.11/1.07      | k1_xboole_0 = X0
% 1.11/1.07      | sP2_iProver_split != iProver_top ),
% 1.11/1.07      inference(predicate_to_equality,[status(thm)],[c_523]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_1842,plain,
% 1.11/1.07      ( k8_relset_1(k1_relat_1(k1_xboole_0),X0,k1_xboole_0,X0) = k1_relat_1(k1_xboole_0)
% 1.11/1.07      | k1_xboole_0 = X0
% 1.11/1.07      | sP2_iProver_split != iProver_top ),
% 1.11/1.07      inference(demodulation,[status(thm)],[c_1835,c_779]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_1881,plain,
% 1.11/1.07      ( k8_relset_1(k1_xboole_0,X0,k1_xboole_0,X0) = k1_xboole_0
% 1.11/1.07      | k1_xboole_0 = X0
% 1.11/1.07      | sP2_iProver_split != iProver_top ),
% 1.11/1.07      inference(light_normalisation,[status(thm)],[c_1842,c_8]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_524,plain,
% 1.11/1.07      ( sP2_iProver_split
% 1.11/1.07      | sP1_iProver_split
% 1.11/1.07      | k2_relat_1(sK2) != k1_xboole_0 ),
% 1.11/1.07      inference(splitting,
% 1.11/1.07                [splitting(split),new_symbols(definition,[])],
% 1.11/1.07                [c_402]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_553,plain,
% 1.11/1.07      ( k2_relat_1(sK2) != k1_xboole_0
% 1.11/1.07      | sP2_iProver_split = iProver_top
% 1.11/1.07      | sP1_iProver_split = iProver_top ),
% 1.11/1.07      inference(predicate_to_equality,[status(thm)],[c_524]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_2004,plain,
% 1.11/1.07      ( k1_xboole_0 = X0
% 1.11/1.07      | k8_relset_1(k1_xboole_0,X0,k1_xboole_0,X0) = k1_xboole_0 ),
% 1.11/1.07      inference(global_propositional_subsumption,
% 1.11/1.07                [status(thm)],
% 1.11/1.07                [c_1881,c_18,c_7,c_47,c_48,c_0,c_553,c_803,c_969,c_975,
% 1.11/1.07                 c_987,c_988,c_1132,c_1138,c_1453,c_1517]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_2005,plain,
% 1.11/1.07      ( k8_relset_1(k1_xboole_0,X0,k1_xboole_0,X0) = k1_xboole_0
% 1.11/1.07      | k1_xboole_0 = X0 ),
% 1.11/1.07      inference(renaming,[status(thm)],[c_2004]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_6,plain,
% 1.11/1.07      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 1.11/1.07      inference(cnf_transformation,[],[f36]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_786,plain,
% 1.11/1.07      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 1.11/1.07      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_1366,plain,
% 1.11/1.07      ( k8_relset_1(X0,X1,k1_xboole_0,X2) = k10_relat_1(k1_xboole_0,X2) ),
% 1.11/1.07      inference(superposition,[status(thm)],[c_786,c_784]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_2006,plain,
% 1.11/1.07      ( k10_relat_1(k1_xboole_0,X0) = k1_xboole_0 | k1_xboole_0 = X0 ),
% 1.11/1.07      inference(demodulation,[status(thm)],[c_2005,c_1366]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_17,negated_conjecture,
% 1.11/1.07      ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
% 1.11/1.07      inference(cnf_transformation,[],[f50]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_1717,plain,
% 1.11/1.07      ( k10_relat_1(sK2,sK1) != k1_xboole_0 ),
% 1.11/1.07      inference(demodulation,[status(thm)],[c_1597,c_17]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_1839,plain,
% 1.11/1.07      ( k10_relat_1(k1_xboole_0,sK1) != k1_xboole_0 ),
% 1.11/1.07      inference(demodulation,[status(thm)],[c_1835,c_1717]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_2009,plain,
% 1.11/1.07      ( sK1 = k1_xboole_0 ),
% 1.11/1.07      inference(superposition,[status(thm)],[c_2006,c_1839]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(c_2198,plain,
% 1.11/1.07      ( k10_relat_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
% 1.11/1.07      inference(demodulation,[status(thm)],[c_2009,c_1839]) ).
% 1.11/1.07  
% 1.11/1.07  cnf(contradiction,plain,
% 1.11/1.07      ( $false ),
% 1.11/1.07      inference(minisat,[status(thm)],[c_2264,c_2198]) ).
% 1.11/1.07  
% 1.11/1.07  
% 1.11/1.07  % SZS output end CNFRefutation for theBenchmark.p
% 1.11/1.07  
% 1.11/1.07  ------                               Statistics
% 1.11/1.07  
% 1.11/1.07  ------ General
% 1.11/1.07  
% 1.11/1.07  abstr_ref_over_cycles:                  0
% 1.11/1.07  abstr_ref_under_cycles:                 0
% 1.11/1.07  gc_basic_clause_elim:                   0
% 1.11/1.07  forced_gc_time:                         0
% 1.11/1.07  parsing_time:                           0.007
% 1.11/1.07  unif_index_cands_time:                  0.
% 1.11/1.07  unif_index_add_time:                    0.
% 1.11/1.07  orderings_time:                         0.
% 1.11/1.07  out_proof_time:                         0.025
% 1.11/1.07  total_time:                             0.141
% 1.11/1.07  num_of_symbols:                         51
% 1.11/1.07  num_of_terms:                           2202
% 1.11/1.07  
% 1.11/1.07  ------ Preprocessing
% 1.11/1.07  
% 1.11/1.07  num_of_splits:                          6
% 1.11/1.07  num_of_split_atoms:                     4
% 1.11/1.07  num_of_reused_defs:                     2
% 1.11/1.07  num_eq_ax_congr_red:                    8
% 1.11/1.07  num_of_sem_filtered_clauses:            1
% 1.11/1.07  num_of_subtypes:                        0
% 1.11/1.07  monotx_restored_types:                  0
% 1.11/1.07  sat_num_of_epr_types:                   0
% 1.11/1.07  sat_num_of_non_cyclic_types:            0
% 1.11/1.07  sat_guarded_non_collapsed_types:        0
% 1.11/1.07  num_pure_diseq_elim:                    0
% 1.11/1.07  simp_replaced_by:                       0
% 1.11/1.07  res_preprocessed:                       95
% 1.11/1.07  prep_upred:                             0
% 1.11/1.07  prep_unflattend:                        14
% 1.11/1.07  smt_new_axioms:                         0
% 1.11/1.07  pred_elim_cands:                        2
% 1.11/1.07  pred_elim:                              4
% 1.11/1.07  pred_elim_cl:                           4
% 1.11/1.07  pred_elim_cycles:                       7
% 1.11/1.07  merged_defs:                            0
% 1.11/1.07  merged_defs_ncl:                        0
% 1.11/1.07  bin_hyper_res:                          0
% 1.11/1.07  prep_cycles:                            4
% 1.11/1.07  pred_elim_time:                         0.006
% 1.11/1.07  splitting_time:                         0.
% 1.11/1.07  sem_filter_time:                        0.
% 1.11/1.07  monotx_time:                            0.
% 1.11/1.07  subtype_inf_time:                       0.
% 1.11/1.07  
% 1.11/1.07  ------ Problem properties
% 1.11/1.07  
% 1.11/1.07  clauses:                                22
% 1.11/1.07  conjectures:                            2
% 1.11/1.07  epr:                                    2
% 1.11/1.07  horn:                                   17
% 1.11/1.07  ground:                                 9
% 1.11/1.07  unary:                                  9
% 1.11/1.07  binary:                                 6
% 1.11/1.07  lits:                                   43
% 1.11/1.07  lits_eq:                                18
% 1.11/1.07  fd_pure:                                0
% 1.11/1.07  fd_pseudo:                              0
% 1.11/1.07  fd_cond:                                3
% 1.11/1.07  fd_pseudo_cond:                         0
% 1.11/1.07  ac_symbols:                             0
% 1.11/1.07  
% 1.11/1.07  ------ Propositional Solver
% 1.11/1.07  
% 1.11/1.07  prop_solver_calls:                      27
% 1.11/1.07  prop_fast_solver_calls:                 545
% 1.11/1.07  smt_solver_calls:                       0
% 1.11/1.07  smt_fast_solver_calls:                  0
% 1.11/1.07  prop_num_of_clauses:                    885
% 1.11/1.07  prop_preprocess_simplified:             3306
% 1.11/1.07  prop_fo_subsumed:                       11
% 1.11/1.07  prop_solver_time:                       0.
% 1.11/1.07  smt_solver_time:                        0.
% 1.11/1.07  smt_fast_solver_time:                   0.
% 1.11/1.07  prop_fast_solver_time:                  0.
% 1.11/1.07  prop_unsat_core_time:                   0.
% 1.11/1.07  
% 1.11/1.07  ------ QBF
% 1.11/1.07  
% 1.11/1.07  qbf_q_res:                              0
% 1.11/1.07  qbf_num_tautologies:                    0
% 1.11/1.07  qbf_prep_cycles:                        0
% 1.11/1.07  
% 1.11/1.07  ------ BMC1
% 1.11/1.07  
% 1.11/1.07  bmc1_current_bound:                     -1
% 1.11/1.07  bmc1_last_solved_bound:                 -1
% 1.11/1.07  bmc1_unsat_core_size:                   -1
% 1.11/1.07  bmc1_unsat_core_parents_size:           -1
% 1.11/1.07  bmc1_merge_next_fun:                    0
% 1.11/1.07  bmc1_unsat_core_clauses_time:           0.
% 1.11/1.07  
% 1.11/1.07  ------ Instantiation
% 1.11/1.07  
% 1.11/1.07  inst_num_of_clauses:                    417
% 1.11/1.07  inst_num_in_passive:                    84
% 1.11/1.07  inst_num_in_active:                     180
% 1.11/1.07  inst_num_in_unprocessed:                153
% 1.11/1.07  inst_num_of_loops:                      210
% 1.11/1.07  inst_num_of_learning_restarts:          0
% 1.11/1.07  inst_num_moves_active_passive:          28
% 1.11/1.07  inst_lit_activity:                      0
% 1.11/1.07  inst_lit_activity_moves:                0
% 1.11/1.07  inst_num_tautologies:                   0
% 1.11/1.07  inst_num_prop_implied:                  0
% 1.11/1.07  inst_num_existing_simplified:           0
% 1.11/1.07  inst_num_eq_res_simplified:             0
% 1.11/1.07  inst_num_child_elim:                    0
% 1.11/1.07  inst_num_of_dismatching_blockings:      28
% 1.11/1.07  inst_num_of_non_proper_insts:           259
% 1.11/1.07  inst_num_of_duplicates:                 0
% 1.11/1.07  inst_inst_num_from_inst_to_res:         0
% 1.11/1.07  inst_dismatching_checking_time:         0.
% 1.11/1.07  
% 1.11/1.07  ------ Resolution
% 1.11/1.07  
% 1.11/1.07  res_num_of_clauses:                     0
% 1.11/1.07  res_num_in_passive:                     0
% 1.11/1.07  res_num_in_active:                      0
% 1.11/1.07  res_num_of_loops:                       99
% 1.11/1.07  res_forward_subset_subsumed:            19
% 1.11/1.07  res_backward_subset_subsumed:           1
% 1.11/1.07  res_forward_subsumed:                   0
% 1.11/1.07  res_backward_subsumed:                  0
% 1.11/1.07  res_forward_subsumption_resolution:     0
% 1.11/1.07  res_backward_subsumption_resolution:    0
% 1.11/1.07  res_clause_to_clause_subsumption:       66
% 1.11/1.07  res_orphan_elimination:                 0
% 1.11/1.07  res_tautology_del:                      20
% 1.11/1.07  res_num_eq_res_simplified:              0
% 1.11/1.07  res_num_sel_changes:                    0
% 1.11/1.07  res_moves_from_active_to_pass:          0
% 1.11/1.07  
% 1.11/1.07  ------ Superposition
% 1.11/1.07  
% 1.11/1.07  sup_time_total:                         0.
% 1.11/1.07  sup_time_generating:                    0.
% 1.11/1.07  sup_time_sim_full:                      0.
% 1.11/1.07  sup_time_sim_immed:                     0.
% 1.11/1.07  
% 1.11/1.07  sup_num_of_clauses:                     29
% 1.11/1.07  sup_num_in_active:                      24
% 1.11/1.07  sup_num_in_passive:                     5
% 1.11/1.07  sup_num_of_loops:                       40
% 1.11/1.07  sup_fw_superposition:                   20
% 1.11/1.07  sup_bw_superposition:                   8
% 1.11/1.07  sup_immediate_simplified:               11
% 1.11/1.07  sup_given_eliminated:                   0
% 1.11/1.07  comparisons_done:                       0
% 1.11/1.07  comparisons_avoided:                    1
% 1.11/1.07  
% 1.11/1.07  ------ Simplifications
% 1.11/1.07  
% 1.11/1.07  
% 1.11/1.07  sim_fw_subset_subsumed:                 4
% 1.11/1.07  sim_bw_subset_subsumed:                 0
% 1.11/1.07  sim_fw_subsumed:                        2
% 1.11/1.07  sim_bw_subsumed:                        1
% 1.11/1.07  sim_fw_subsumption_res:                 1
% 1.11/1.07  sim_bw_subsumption_res:                 0
% 1.11/1.07  sim_tautology_del:                      0
% 1.11/1.07  sim_eq_tautology_del:                   1
% 1.11/1.07  sim_eq_res_simp:                        3
% 1.11/1.07  sim_fw_demodulated:                     2
% 1.11/1.07  sim_bw_demodulated:                     16
% 1.11/1.07  sim_light_normalised:                   7
% 1.11/1.07  sim_joinable_taut:                      0
% 1.11/1.07  sim_joinable_simp:                      0
% 1.11/1.07  sim_ac_normalised:                      0
% 1.11/1.07  sim_smt_subsumption:                    0
% 1.11/1.07  
%------------------------------------------------------------------------------
