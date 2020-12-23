%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:54:57 EST 2020

% Result     : Theorem 7.06s
% Output     : CNFRefutation 7.06s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 290 expanded)
%              Number of clauses        :   63 ( 123 expanded)
%              Number of leaves         :   15 (  57 expanded)
%              Depth                    :   19
%              Number of atoms          :  250 ( 619 expanded)
%              Number of equality atoms :   80 ( 123 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f35,f37])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f53,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(definition_unfolding,[],[f33,f37,f37])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1))
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f31,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ~ r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1))
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ~ r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f31])).

fof(f51,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f32])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f11,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f45,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f58,plain,(
    ! [X0] :
      ( k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f45,f37])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f36,f37])).

fof(f52,plain,(
    ~ r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f32])).

fof(f59,plain,(
    ~ r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1))) ),
    inference(definition_unfolding,[],[f52,f37])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k4_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_937,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k4_xboole_0(X0,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2,plain,
    ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_936,plain,
    ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) = iProver_top
    | r1_tarski(k4_xboole_0(X0,X1),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_0,plain,
    ( k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_3238,plain,
    ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) = iProver_top
    | r1_tarski(k4_xboole_0(X0,X2),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_936])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_928,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_933,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1099,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_928,c_933])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_6,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_138,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_6])).

cnf(c_139,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_138])).

cnf(c_171,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_8,c_139])).

cnf(c_927,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_171])).

cnf(c_2819,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1099,c_927])).

cnf(c_19,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1027,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1028,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1027])).

cnf(c_1040,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_171])).

cnf(c_1123,plain,
    ( ~ r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1040])).

cnf(c_1124,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1123])).

cnf(c_12,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1153,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1154,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1153])).

cnf(c_5867,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2819,c_19,c_1028,c_1124,c_1154])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_932,plain,
    ( k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_5872,plain,
    ( k3_tarski(k2_tarski(k1_relat_1(sK2),k2_relat_1(sK2))) = k3_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_5867,c_932])).

cnf(c_6429,plain,
    ( k3_tarski(k2_tarski(k2_relat_1(sK2),k1_relat_1(sK2))) = k3_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_5872,c_0])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_935,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_10689,plain,
    ( r1_tarski(k3_relat_1(sK2),X0) = iProver_top
    | r1_tarski(k1_relat_1(sK2),X0) != iProver_top
    | r1_tarski(k2_relat_1(sK2),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6429,c_935])).

cnf(c_12705,plain,
    ( r1_tarski(k4_xboole_0(k1_relat_1(sK2),X0),X1) != iProver_top
    | r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(X1,X0))) = iProver_top
    | r1_tarski(k2_relat_1(sK2),k3_tarski(k2_tarski(X1,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3238,c_10689])).

cnf(c_15122,plain,
    ( r1_tarski(k4_xboole_0(k1_relat_1(sK2),X0),X1) != iProver_top
    | r1_tarski(k4_xboole_0(k2_relat_1(sK2),X1),X0) != iProver_top
    | r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(X1,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_936,c_12705])).

cnf(c_17,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_929,plain,
    ( r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_21155,plain,
    ( r1_tarski(k4_xboole_0(k1_relat_1(sK2),sK1),sK0) != iProver_top
    | r1_tarski(k4_xboole_0(k2_relat_1(sK2),sK0),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_15122,c_929])).

cnf(c_15,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_10,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_250,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_15,c_10])).

cnf(c_1242,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | r1_tarski(k2_relat_1(sK2),X1)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_250])).

cnf(c_1911,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | r1_tarski(k2_relat_1(sK2),sK1)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1242])).

cnf(c_1912,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | r1_tarski(k2_relat_1(sK2),sK1) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1911])).

cnf(c_2653,plain,
    ( r1_tarski(k4_xboole_0(k2_relat_1(sK2),X0),sK1)
    | ~ r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2657,plain,
    ( r1_tarski(k4_xboole_0(k2_relat_1(sK2),X0),sK1) = iProver_top
    | r1_tarski(k2_relat_1(sK2),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2653])).

cnf(c_2659,plain,
    ( r1_tarski(k4_xboole_0(k2_relat_1(sK2),sK0),sK1) = iProver_top
    | r1_tarski(k2_relat_1(sK2),sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2657])).

cnf(c_21437,plain,
    ( r1_tarski(k4_xboole_0(k1_relat_1(sK2),sK1),sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_21155,c_19,c_1028,c_1124,c_1154,c_1912,c_2659])).

cnf(c_21442,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_937,c_21437])).

cnf(c_16,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_13,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_232,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_16,c_13])).

cnf(c_926,plain,
    ( k7_relat_1(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_232])).

cnf(c_6923,plain,
    ( k7_relat_1(sK2,sK0) = sK2
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_928,c_926])).

cnf(c_1241,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_relat_1(sK2)
    | k7_relat_1(sK2,X0) = sK2 ),
    inference(instantiation,[status(thm)],[c_232])).

cnf(c_1908,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_relat_1(sK2)
    | k7_relat_1(sK2,sK0) = sK2 ),
    inference(instantiation,[status(thm)],[c_1241])).

cnf(c_9316,plain,
    ( k7_relat_1(sK2,sK0) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6923,c_18,c_1027,c_1123,c_1153,c_1908])).

cnf(c_14,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_930,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_9319,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_9316,c_930])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_21442,c_9319,c_1154,c_1124,c_1028,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:49:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.06/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.06/1.49  
% 7.06/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.06/1.49  
% 7.06/1.49  ------  iProver source info
% 7.06/1.49  
% 7.06/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.06/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.06/1.49  git: non_committed_changes: false
% 7.06/1.49  git: last_make_outside_of_git: false
% 7.06/1.49  
% 7.06/1.49  ------ 
% 7.06/1.49  
% 7.06/1.49  ------ Input Options
% 7.06/1.49  
% 7.06/1.49  --out_options                           all
% 7.06/1.49  --tptp_safe_out                         true
% 7.06/1.49  --problem_path                          ""
% 7.06/1.49  --include_path                          ""
% 7.06/1.49  --clausifier                            res/vclausify_rel
% 7.06/1.49  --clausifier_options                    --mode clausify
% 7.06/1.49  --stdin                                 false
% 7.06/1.49  --stats_out                             all
% 7.06/1.49  
% 7.06/1.49  ------ General Options
% 7.06/1.49  
% 7.06/1.49  --fof                                   false
% 7.06/1.49  --time_out_real                         305.
% 7.06/1.49  --time_out_virtual                      -1.
% 7.06/1.49  --symbol_type_check                     false
% 7.06/1.49  --clausify_out                          false
% 7.06/1.49  --sig_cnt_out                           false
% 7.06/1.49  --trig_cnt_out                          false
% 7.06/1.49  --trig_cnt_out_tolerance                1.
% 7.06/1.49  --trig_cnt_out_sk_spl                   false
% 7.06/1.49  --abstr_cl_out                          false
% 7.06/1.49  
% 7.06/1.49  ------ Global Options
% 7.06/1.49  
% 7.06/1.49  --schedule                              default
% 7.06/1.49  --add_important_lit                     false
% 7.06/1.49  --prop_solver_per_cl                    1000
% 7.06/1.49  --min_unsat_core                        false
% 7.06/1.49  --soft_assumptions                      false
% 7.06/1.49  --soft_lemma_size                       3
% 7.06/1.49  --prop_impl_unit_size                   0
% 7.06/1.49  --prop_impl_unit                        []
% 7.06/1.49  --share_sel_clauses                     true
% 7.06/1.49  --reset_solvers                         false
% 7.06/1.49  --bc_imp_inh                            [conj_cone]
% 7.06/1.49  --conj_cone_tolerance                   3.
% 7.06/1.49  --extra_neg_conj                        none
% 7.06/1.49  --large_theory_mode                     true
% 7.06/1.49  --prolific_symb_bound                   200
% 7.06/1.49  --lt_threshold                          2000
% 7.06/1.49  --clause_weak_htbl                      true
% 7.06/1.49  --gc_record_bc_elim                     false
% 7.06/1.49  
% 7.06/1.49  ------ Preprocessing Options
% 7.06/1.49  
% 7.06/1.49  --preprocessing_flag                    true
% 7.06/1.49  --time_out_prep_mult                    0.1
% 7.06/1.49  --splitting_mode                        input
% 7.06/1.49  --splitting_grd                         true
% 7.06/1.49  --splitting_cvd                         false
% 7.06/1.49  --splitting_cvd_svl                     false
% 7.06/1.49  --splitting_nvd                         32
% 7.06/1.49  --sub_typing                            true
% 7.06/1.49  --prep_gs_sim                           true
% 7.06/1.49  --prep_unflatten                        true
% 7.06/1.49  --prep_res_sim                          true
% 7.06/1.49  --prep_upred                            true
% 7.06/1.49  --prep_sem_filter                       exhaustive
% 7.06/1.49  --prep_sem_filter_out                   false
% 7.06/1.49  --pred_elim                             true
% 7.06/1.49  --res_sim_input                         true
% 7.06/1.49  --eq_ax_congr_red                       true
% 7.06/1.49  --pure_diseq_elim                       true
% 7.06/1.49  --brand_transform                       false
% 7.06/1.49  --non_eq_to_eq                          false
% 7.06/1.49  --prep_def_merge                        true
% 7.06/1.49  --prep_def_merge_prop_impl              false
% 7.06/1.49  --prep_def_merge_mbd                    true
% 7.06/1.49  --prep_def_merge_tr_red                 false
% 7.06/1.49  --prep_def_merge_tr_cl                  false
% 7.06/1.49  --smt_preprocessing                     true
% 7.06/1.49  --smt_ac_axioms                         fast
% 7.06/1.49  --preprocessed_out                      false
% 7.06/1.49  --preprocessed_stats                    false
% 7.06/1.49  
% 7.06/1.49  ------ Abstraction refinement Options
% 7.06/1.49  
% 7.06/1.49  --abstr_ref                             []
% 7.06/1.49  --abstr_ref_prep                        false
% 7.06/1.49  --abstr_ref_until_sat                   false
% 7.06/1.49  --abstr_ref_sig_restrict                funpre
% 7.06/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.06/1.49  --abstr_ref_under                       []
% 7.06/1.49  
% 7.06/1.49  ------ SAT Options
% 7.06/1.49  
% 7.06/1.49  --sat_mode                              false
% 7.06/1.49  --sat_fm_restart_options                ""
% 7.06/1.49  --sat_gr_def                            false
% 7.06/1.49  --sat_epr_types                         true
% 7.06/1.49  --sat_non_cyclic_types                  false
% 7.06/1.49  --sat_finite_models                     false
% 7.06/1.49  --sat_fm_lemmas                         false
% 7.06/1.49  --sat_fm_prep                           false
% 7.06/1.49  --sat_fm_uc_incr                        true
% 7.06/1.49  --sat_out_model                         small
% 7.06/1.49  --sat_out_clauses                       false
% 7.06/1.49  
% 7.06/1.49  ------ QBF Options
% 7.06/1.49  
% 7.06/1.49  --qbf_mode                              false
% 7.06/1.49  --qbf_elim_univ                         false
% 7.06/1.49  --qbf_dom_inst                          none
% 7.06/1.49  --qbf_dom_pre_inst                      false
% 7.06/1.49  --qbf_sk_in                             false
% 7.06/1.49  --qbf_pred_elim                         true
% 7.06/1.49  --qbf_split                             512
% 7.06/1.49  
% 7.06/1.49  ------ BMC1 Options
% 7.06/1.49  
% 7.06/1.49  --bmc1_incremental                      false
% 7.06/1.49  --bmc1_axioms                           reachable_all
% 7.06/1.49  --bmc1_min_bound                        0
% 7.06/1.49  --bmc1_max_bound                        -1
% 7.06/1.49  --bmc1_max_bound_default                -1
% 7.06/1.49  --bmc1_symbol_reachability              true
% 7.06/1.49  --bmc1_property_lemmas                  false
% 7.06/1.49  --bmc1_k_induction                      false
% 7.06/1.49  --bmc1_non_equiv_states                 false
% 7.06/1.49  --bmc1_deadlock                         false
% 7.06/1.49  --bmc1_ucm                              false
% 7.06/1.49  --bmc1_add_unsat_core                   none
% 7.06/1.49  --bmc1_unsat_core_children              false
% 7.06/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.06/1.49  --bmc1_out_stat                         full
% 7.06/1.49  --bmc1_ground_init                      false
% 7.06/1.49  --bmc1_pre_inst_next_state              false
% 7.06/1.49  --bmc1_pre_inst_state                   false
% 7.06/1.49  --bmc1_pre_inst_reach_state             false
% 7.06/1.49  --bmc1_out_unsat_core                   false
% 7.06/1.49  --bmc1_aig_witness_out                  false
% 7.06/1.49  --bmc1_verbose                          false
% 7.06/1.49  --bmc1_dump_clauses_tptp                false
% 7.06/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.06/1.49  --bmc1_dump_file                        -
% 7.06/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.06/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.06/1.49  --bmc1_ucm_extend_mode                  1
% 7.06/1.49  --bmc1_ucm_init_mode                    2
% 7.06/1.49  --bmc1_ucm_cone_mode                    none
% 7.06/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.06/1.49  --bmc1_ucm_relax_model                  4
% 7.06/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.06/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.06/1.49  --bmc1_ucm_layered_model                none
% 7.06/1.49  --bmc1_ucm_max_lemma_size               10
% 7.06/1.49  
% 7.06/1.49  ------ AIG Options
% 7.06/1.49  
% 7.06/1.49  --aig_mode                              false
% 7.06/1.49  
% 7.06/1.49  ------ Instantiation Options
% 7.06/1.49  
% 7.06/1.49  --instantiation_flag                    true
% 7.06/1.49  --inst_sos_flag                         false
% 7.06/1.49  --inst_sos_phase                        true
% 7.06/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.06/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.06/1.49  --inst_lit_sel_side                     num_symb
% 7.06/1.49  --inst_solver_per_active                1400
% 7.06/1.49  --inst_solver_calls_frac                1.
% 7.06/1.49  --inst_passive_queue_type               priority_queues
% 7.06/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.06/1.49  --inst_passive_queues_freq              [25;2]
% 7.06/1.49  --inst_dismatching                      true
% 7.06/1.49  --inst_eager_unprocessed_to_passive     true
% 7.06/1.49  --inst_prop_sim_given                   true
% 7.06/1.49  --inst_prop_sim_new                     false
% 7.06/1.49  --inst_subs_new                         false
% 7.06/1.49  --inst_eq_res_simp                      false
% 7.06/1.49  --inst_subs_given                       false
% 7.06/1.49  --inst_orphan_elimination               true
% 7.06/1.49  --inst_learning_loop_flag               true
% 7.06/1.49  --inst_learning_start                   3000
% 7.06/1.49  --inst_learning_factor                  2
% 7.06/1.49  --inst_start_prop_sim_after_learn       3
% 7.06/1.49  --inst_sel_renew                        solver
% 7.06/1.49  --inst_lit_activity_flag                true
% 7.06/1.49  --inst_restr_to_given                   false
% 7.06/1.49  --inst_activity_threshold               500
% 7.06/1.49  --inst_out_proof                        true
% 7.06/1.49  
% 7.06/1.49  ------ Resolution Options
% 7.06/1.49  
% 7.06/1.49  --resolution_flag                       true
% 7.06/1.49  --res_lit_sel                           adaptive
% 7.06/1.49  --res_lit_sel_side                      none
% 7.06/1.49  --res_ordering                          kbo
% 7.06/1.49  --res_to_prop_solver                    active
% 7.06/1.49  --res_prop_simpl_new                    false
% 7.06/1.49  --res_prop_simpl_given                  true
% 7.06/1.49  --res_passive_queue_type                priority_queues
% 7.06/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.06/1.49  --res_passive_queues_freq               [15;5]
% 7.06/1.49  --res_forward_subs                      full
% 7.06/1.49  --res_backward_subs                     full
% 7.06/1.49  --res_forward_subs_resolution           true
% 7.06/1.49  --res_backward_subs_resolution          true
% 7.06/1.49  --res_orphan_elimination                true
% 7.06/1.49  --res_time_limit                        2.
% 7.06/1.49  --res_out_proof                         true
% 7.06/1.49  
% 7.06/1.49  ------ Superposition Options
% 7.06/1.49  
% 7.06/1.49  --superposition_flag                    true
% 7.06/1.49  --sup_passive_queue_type                priority_queues
% 7.06/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.06/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.06/1.49  --demod_completeness_check              fast
% 7.06/1.49  --demod_use_ground                      true
% 7.06/1.49  --sup_to_prop_solver                    passive
% 7.06/1.49  --sup_prop_simpl_new                    true
% 7.06/1.49  --sup_prop_simpl_given                  true
% 7.06/1.49  --sup_fun_splitting                     false
% 7.06/1.49  --sup_smt_interval                      50000
% 7.06/1.49  
% 7.06/1.49  ------ Superposition Simplification Setup
% 7.06/1.49  
% 7.06/1.49  --sup_indices_passive                   []
% 7.06/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.06/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.06/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.06/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.06/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.06/1.49  --sup_full_bw                           [BwDemod]
% 7.06/1.49  --sup_immed_triv                        [TrivRules]
% 7.06/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.06/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.06/1.49  --sup_immed_bw_main                     []
% 7.06/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.06/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.06/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.06/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.06/1.49  
% 7.06/1.49  ------ Combination Options
% 7.06/1.49  
% 7.06/1.49  --comb_res_mult                         3
% 7.06/1.49  --comb_sup_mult                         2
% 7.06/1.49  --comb_inst_mult                        10
% 7.06/1.49  
% 7.06/1.49  ------ Debug Options
% 7.06/1.49  
% 7.06/1.49  --dbg_backtrace                         false
% 7.06/1.49  --dbg_dump_prop_clauses                 false
% 7.06/1.49  --dbg_dump_prop_clauses_file            -
% 7.06/1.49  --dbg_out_stat                          false
% 7.06/1.49  ------ Parsing...
% 7.06/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.06/1.49  
% 7.06/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.06/1.49  
% 7.06/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.06/1.49  
% 7.06/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.06/1.49  ------ Proving...
% 7.06/1.49  ------ Problem Properties 
% 7.06/1.49  
% 7.06/1.49  
% 7.06/1.49  clauses                                 16
% 7.06/1.49  conjectures                             2
% 7.06/1.49  EPR                                     1
% 7.06/1.49  Horn                                    16
% 7.06/1.49  unary                                   6
% 7.06/1.49  binary                                  6
% 7.06/1.49  lits                                    30
% 7.06/1.49  lits eq                                 5
% 7.06/1.49  fd_pure                                 0
% 7.06/1.49  fd_pseudo                               0
% 7.06/1.49  fd_cond                                 0
% 7.06/1.49  fd_pseudo_cond                          0
% 7.06/1.49  AC symbols                              0
% 7.06/1.49  
% 7.06/1.49  ------ Schedule dynamic 5 is on 
% 7.06/1.49  
% 7.06/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.06/1.49  
% 7.06/1.49  
% 7.06/1.49  ------ 
% 7.06/1.49  Current options:
% 7.06/1.49  ------ 
% 7.06/1.49  
% 7.06/1.49  ------ Input Options
% 7.06/1.49  
% 7.06/1.49  --out_options                           all
% 7.06/1.49  --tptp_safe_out                         true
% 7.06/1.49  --problem_path                          ""
% 7.06/1.49  --include_path                          ""
% 7.06/1.49  --clausifier                            res/vclausify_rel
% 7.06/1.49  --clausifier_options                    --mode clausify
% 7.06/1.49  --stdin                                 false
% 7.06/1.49  --stats_out                             all
% 7.06/1.49  
% 7.06/1.49  ------ General Options
% 7.06/1.49  
% 7.06/1.49  --fof                                   false
% 7.06/1.49  --time_out_real                         305.
% 7.06/1.49  --time_out_virtual                      -1.
% 7.06/1.49  --symbol_type_check                     false
% 7.06/1.49  --clausify_out                          false
% 7.06/1.49  --sig_cnt_out                           false
% 7.06/1.49  --trig_cnt_out                          false
% 7.06/1.49  --trig_cnt_out_tolerance                1.
% 7.06/1.49  --trig_cnt_out_sk_spl                   false
% 7.06/1.49  --abstr_cl_out                          false
% 7.06/1.49  
% 7.06/1.49  ------ Global Options
% 7.06/1.49  
% 7.06/1.49  --schedule                              default
% 7.06/1.49  --add_important_lit                     false
% 7.06/1.49  --prop_solver_per_cl                    1000
% 7.06/1.49  --min_unsat_core                        false
% 7.06/1.49  --soft_assumptions                      false
% 7.06/1.49  --soft_lemma_size                       3
% 7.06/1.49  --prop_impl_unit_size                   0
% 7.06/1.49  --prop_impl_unit                        []
% 7.06/1.49  --share_sel_clauses                     true
% 7.06/1.49  --reset_solvers                         false
% 7.06/1.49  --bc_imp_inh                            [conj_cone]
% 7.06/1.49  --conj_cone_tolerance                   3.
% 7.06/1.49  --extra_neg_conj                        none
% 7.06/1.49  --large_theory_mode                     true
% 7.06/1.49  --prolific_symb_bound                   200
% 7.06/1.49  --lt_threshold                          2000
% 7.06/1.49  --clause_weak_htbl                      true
% 7.06/1.49  --gc_record_bc_elim                     false
% 7.06/1.49  
% 7.06/1.49  ------ Preprocessing Options
% 7.06/1.49  
% 7.06/1.49  --preprocessing_flag                    true
% 7.06/1.49  --time_out_prep_mult                    0.1
% 7.06/1.49  --splitting_mode                        input
% 7.06/1.49  --splitting_grd                         true
% 7.06/1.49  --splitting_cvd                         false
% 7.06/1.49  --splitting_cvd_svl                     false
% 7.06/1.49  --splitting_nvd                         32
% 7.06/1.49  --sub_typing                            true
% 7.06/1.49  --prep_gs_sim                           true
% 7.06/1.49  --prep_unflatten                        true
% 7.06/1.49  --prep_res_sim                          true
% 7.06/1.49  --prep_upred                            true
% 7.06/1.49  --prep_sem_filter                       exhaustive
% 7.06/1.49  --prep_sem_filter_out                   false
% 7.06/1.49  --pred_elim                             true
% 7.06/1.49  --res_sim_input                         true
% 7.06/1.49  --eq_ax_congr_red                       true
% 7.06/1.49  --pure_diseq_elim                       true
% 7.06/1.49  --brand_transform                       false
% 7.06/1.49  --non_eq_to_eq                          false
% 7.06/1.49  --prep_def_merge                        true
% 7.06/1.49  --prep_def_merge_prop_impl              false
% 7.06/1.49  --prep_def_merge_mbd                    true
% 7.06/1.49  --prep_def_merge_tr_red                 false
% 7.06/1.49  --prep_def_merge_tr_cl                  false
% 7.06/1.49  --smt_preprocessing                     true
% 7.06/1.49  --smt_ac_axioms                         fast
% 7.06/1.49  --preprocessed_out                      false
% 7.06/1.49  --preprocessed_stats                    false
% 7.06/1.49  
% 7.06/1.49  ------ Abstraction refinement Options
% 7.06/1.49  
% 7.06/1.49  --abstr_ref                             []
% 7.06/1.49  --abstr_ref_prep                        false
% 7.06/1.49  --abstr_ref_until_sat                   false
% 7.06/1.49  --abstr_ref_sig_restrict                funpre
% 7.06/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.06/1.49  --abstr_ref_under                       []
% 7.06/1.49  
% 7.06/1.49  ------ SAT Options
% 7.06/1.49  
% 7.06/1.49  --sat_mode                              false
% 7.06/1.49  --sat_fm_restart_options                ""
% 7.06/1.49  --sat_gr_def                            false
% 7.06/1.49  --sat_epr_types                         true
% 7.06/1.49  --sat_non_cyclic_types                  false
% 7.06/1.49  --sat_finite_models                     false
% 7.06/1.49  --sat_fm_lemmas                         false
% 7.06/1.49  --sat_fm_prep                           false
% 7.06/1.49  --sat_fm_uc_incr                        true
% 7.06/1.49  --sat_out_model                         small
% 7.06/1.49  --sat_out_clauses                       false
% 7.06/1.49  
% 7.06/1.49  ------ QBF Options
% 7.06/1.49  
% 7.06/1.49  --qbf_mode                              false
% 7.06/1.49  --qbf_elim_univ                         false
% 7.06/1.49  --qbf_dom_inst                          none
% 7.06/1.49  --qbf_dom_pre_inst                      false
% 7.06/1.49  --qbf_sk_in                             false
% 7.06/1.49  --qbf_pred_elim                         true
% 7.06/1.49  --qbf_split                             512
% 7.06/1.49  
% 7.06/1.49  ------ BMC1 Options
% 7.06/1.49  
% 7.06/1.49  --bmc1_incremental                      false
% 7.06/1.49  --bmc1_axioms                           reachable_all
% 7.06/1.49  --bmc1_min_bound                        0
% 7.06/1.49  --bmc1_max_bound                        -1
% 7.06/1.49  --bmc1_max_bound_default                -1
% 7.06/1.49  --bmc1_symbol_reachability              true
% 7.06/1.49  --bmc1_property_lemmas                  false
% 7.06/1.49  --bmc1_k_induction                      false
% 7.06/1.49  --bmc1_non_equiv_states                 false
% 7.06/1.49  --bmc1_deadlock                         false
% 7.06/1.49  --bmc1_ucm                              false
% 7.06/1.49  --bmc1_add_unsat_core                   none
% 7.06/1.49  --bmc1_unsat_core_children              false
% 7.06/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.06/1.49  --bmc1_out_stat                         full
% 7.06/1.49  --bmc1_ground_init                      false
% 7.06/1.49  --bmc1_pre_inst_next_state              false
% 7.06/1.49  --bmc1_pre_inst_state                   false
% 7.06/1.49  --bmc1_pre_inst_reach_state             false
% 7.06/1.49  --bmc1_out_unsat_core                   false
% 7.06/1.49  --bmc1_aig_witness_out                  false
% 7.06/1.49  --bmc1_verbose                          false
% 7.06/1.49  --bmc1_dump_clauses_tptp                false
% 7.06/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.06/1.49  --bmc1_dump_file                        -
% 7.06/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.06/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.06/1.49  --bmc1_ucm_extend_mode                  1
% 7.06/1.49  --bmc1_ucm_init_mode                    2
% 7.06/1.49  --bmc1_ucm_cone_mode                    none
% 7.06/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.06/1.49  --bmc1_ucm_relax_model                  4
% 7.06/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.06/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.06/1.49  --bmc1_ucm_layered_model                none
% 7.06/1.49  --bmc1_ucm_max_lemma_size               10
% 7.06/1.49  
% 7.06/1.49  ------ AIG Options
% 7.06/1.49  
% 7.06/1.49  --aig_mode                              false
% 7.06/1.49  
% 7.06/1.49  ------ Instantiation Options
% 7.06/1.49  
% 7.06/1.49  --instantiation_flag                    true
% 7.06/1.49  --inst_sos_flag                         false
% 7.06/1.49  --inst_sos_phase                        true
% 7.06/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.06/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.06/1.49  --inst_lit_sel_side                     none
% 7.06/1.49  --inst_solver_per_active                1400
% 7.06/1.49  --inst_solver_calls_frac                1.
% 7.06/1.49  --inst_passive_queue_type               priority_queues
% 7.06/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.06/1.49  --inst_passive_queues_freq              [25;2]
% 7.06/1.49  --inst_dismatching                      true
% 7.06/1.49  --inst_eager_unprocessed_to_passive     true
% 7.06/1.49  --inst_prop_sim_given                   true
% 7.06/1.49  --inst_prop_sim_new                     false
% 7.06/1.49  --inst_subs_new                         false
% 7.06/1.49  --inst_eq_res_simp                      false
% 7.06/1.49  --inst_subs_given                       false
% 7.06/1.49  --inst_orphan_elimination               true
% 7.06/1.49  --inst_learning_loop_flag               true
% 7.06/1.49  --inst_learning_start                   3000
% 7.06/1.49  --inst_learning_factor                  2
% 7.06/1.49  --inst_start_prop_sim_after_learn       3
% 7.06/1.49  --inst_sel_renew                        solver
% 7.06/1.49  --inst_lit_activity_flag                true
% 7.06/1.49  --inst_restr_to_given                   false
% 7.06/1.49  --inst_activity_threshold               500
% 7.06/1.49  --inst_out_proof                        true
% 7.06/1.49  
% 7.06/1.49  ------ Resolution Options
% 7.06/1.49  
% 7.06/1.49  --resolution_flag                       false
% 7.06/1.49  --res_lit_sel                           adaptive
% 7.06/1.49  --res_lit_sel_side                      none
% 7.06/1.49  --res_ordering                          kbo
% 7.06/1.49  --res_to_prop_solver                    active
% 7.06/1.49  --res_prop_simpl_new                    false
% 7.06/1.49  --res_prop_simpl_given                  true
% 7.06/1.49  --res_passive_queue_type                priority_queues
% 7.06/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.06/1.49  --res_passive_queues_freq               [15;5]
% 7.06/1.49  --res_forward_subs                      full
% 7.06/1.49  --res_backward_subs                     full
% 7.06/1.49  --res_forward_subs_resolution           true
% 7.06/1.49  --res_backward_subs_resolution          true
% 7.06/1.49  --res_orphan_elimination                true
% 7.06/1.49  --res_time_limit                        2.
% 7.06/1.49  --res_out_proof                         true
% 7.06/1.49  
% 7.06/1.49  ------ Superposition Options
% 7.06/1.49  
% 7.06/1.49  --superposition_flag                    true
% 7.06/1.49  --sup_passive_queue_type                priority_queues
% 7.06/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.06/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.06/1.49  --demod_completeness_check              fast
% 7.06/1.49  --demod_use_ground                      true
% 7.06/1.49  --sup_to_prop_solver                    passive
% 7.06/1.49  --sup_prop_simpl_new                    true
% 7.06/1.49  --sup_prop_simpl_given                  true
% 7.06/1.49  --sup_fun_splitting                     false
% 7.06/1.49  --sup_smt_interval                      50000
% 7.06/1.49  
% 7.06/1.49  ------ Superposition Simplification Setup
% 7.06/1.49  
% 7.06/1.49  --sup_indices_passive                   []
% 7.06/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.06/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.06/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.06/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.06/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.06/1.49  --sup_full_bw                           [BwDemod]
% 7.06/1.49  --sup_immed_triv                        [TrivRules]
% 7.06/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.06/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.06/1.49  --sup_immed_bw_main                     []
% 7.06/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.06/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.06/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.06/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.06/1.49  
% 7.06/1.49  ------ Combination Options
% 7.06/1.49  
% 7.06/1.49  --comb_res_mult                         3
% 7.06/1.49  --comb_sup_mult                         2
% 7.06/1.49  --comb_inst_mult                        10
% 7.06/1.49  
% 7.06/1.49  ------ Debug Options
% 7.06/1.49  
% 7.06/1.49  --dbg_backtrace                         false
% 7.06/1.49  --dbg_dump_prop_clauses                 false
% 7.06/1.49  --dbg_dump_prop_clauses_file            -
% 7.06/1.49  --dbg_out_stat                          false
% 7.06/1.49  
% 7.06/1.49  
% 7.06/1.49  
% 7.06/1.49  
% 7.06/1.49  ------ Proving...
% 7.06/1.49  
% 7.06/1.49  
% 7.06/1.49  % SZS status Theorem for theBenchmark.p
% 7.06/1.49  
% 7.06/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.06/1.49  
% 7.06/1.49  fof(f2,axiom,(
% 7.06/1.49    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X0,X2),X1))),
% 7.06/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.06/1.49  
% 7.06/1.49  fof(f17,plain,(
% 7.06/1.49    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 7.06/1.49    inference(ennf_transformation,[],[f2])).
% 7.06/1.49  
% 7.06/1.49  fof(f34,plain,(
% 7.06/1.49    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 7.06/1.49    inference(cnf_transformation,[],[f17])).
% 7.06/1.49  
% 7.06/1.49  fof(f3,axiom,(
% 7.06/1.49    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 7.06/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.06/1.49  
% 7.06/1.49  fof(f18,plain,(
% 7.06/1.49    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 7.06/1.49    inference(ennf_transformation,[],[f3])).
% 7.06/1.49  
% 7.06/1.49  fof(f35,plain,(
% 7.06/1.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 7.06/1.49    inference(cnf_transformation,[],[f18])).
% 7.06/1.49  
% 7.06/1.49  fof(f5,axiom,(
% 7.06/1.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 7.06/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.06/1.49  
% 7.06/1.49  fof(f37,plain,(
% 7.06/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 7.06/1.49    inference(cnf_transformation,[],[f5])).
% 7.06/1.49  
% 7.06/1.49  fof(f54,plain,(
% 7.06/1.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 7.06/1.49    inference(definition_unfolding,[],[f35,f37])).
% 7.06/1.49  
% 7.06/1.49  fof(f1,axiom,(
% 7.06/1.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 7.06/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.06/1.49  
% 7.06/1.49  fof(f33,plain,(
% 7.06/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 7.06/1.49    inference(cnf_transformation,[],[f1])).
% 7.06/1.49  
% 7.06/1.49  fof(f53,plain,(
% 7.06/1.49    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0))) )),
% 7.06/1.49    inference(definition_unfolding,[],[f33,f37,f37])).
% 7.06/1.49  
% 7.06/1.49  fof(f15,conjecture,(
% 7.06/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)))),
% 7.06/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.06/1.49  
% 7.06/1.49  fof(f16,negated_conjecture,(
% 7.06/1.49    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)))),
% 7.06/1.49    inference(negated_conjecture,[],[f15])).
% 7.06/1.49  
% 7.06/1.49  fof(f28,plain,(
% 7.06/1.49    ? [X0,X1,X2] : (~r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.06/1.49    inference(ennf_transformation,[],[f16])).
% 7.06/1.49  
% 7.06/1.49  fof(f31,plain,(
% 7.06/1.49    ? [X0,X1,X2] : (~r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (~r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 7.06/1.49    introduced(choice_axiom,[])).
% 7.06/1.49  
% 7.06/1.49  fof(f32,plain,(
% 7.06/1.49    ~r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 7.06/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f31])).
% 7.06/1.49  
% 7.06/1.49  fof(f51,plain,(
% 7.06/1.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 7.06/1.49    inference(cnf_transformation,[],[f32])).
% 7.06/1.49  
% 7.06/1.49  fof(f7,axiom,(
% 7.06/1.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.06/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.06/1.49  
% 7.06/1.49  fof(f29,plain,(
% 7.06/1.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.06/1.49    inference(nnf_transformation,[],[f7])).
% 7.06/1.49  
% 7.06/1.49  fof(f40,plain,(
% 7.06/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.06/1.49    inference(cnf_transformation,[],[f29])).
% 7.06/1.49  
% 7.06/1.49  fof(f8,axiom,(
% 7.06/1.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 7.06/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.06/1.49  
% 7.06/1.49  fof(f21,plain,(
% 7.06/1.49    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 7.06/1.49    inference(ennf_transformation,[],[f8])).
% 7.06/1.49  
% 7.06/1.49  fof(f42,plain,(
% 7.06/1.49    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 7.06/1.49    inference(cnf_transformation,[],[f21])).
% 7.06/1.49  
% 7.06/1.49  fof(f41,plain,(
% 7.06/1.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.06/1.49    inference(cnf_transformation,[],[f29])).
% 7.06/1.49  
% 7.06/1.49  fof(f11,axiom,(
% 7.06/1.49    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 7.06/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.06/1.49  
% 7.06/1.49  fof(f46,plain,(
% 7.06/1.49    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 7.06/1.49    inference(cnf_transformation,[],[f11])).
% 7.06/1.49  
% 7.06/1.49  fof(f10,axiom,(
% 7.06/1.49    ! [X0] : (v1_relat_1(X0) => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0))),
% 7.06/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.06/1.49  
% 7.06/1.49  fof(f23,plain,(
% 7.06/1.49    ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0))),
% 7.06/1.49    inference(ennf_transformation,[],[f10])).
% 7.06/1.49  
% 7.06/1.49  fof(f45,plain,(
% 7.06/1.49    ( ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 7.06/1.49    inference(cnf_transformation,[],[f23])).
% 7.06/1.49  
% 7.06/1.49  fof(f58,plain,(
% 7.06/1.49    ( ! [X0] : (k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 7.06/1.49    inference(definition_unfolding,[],[f45,f37])).
% 7.06/1.49  
% 7.06/1.49  fof(f4,axiom,(
% 7.06/1.49    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 7.06/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.06/1.49  
% 7.06/1.49  fof(f19,plain,(
% 7.06/1.49    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 7.06/1.49    inference(ennf_transformation,[],[f4])).
% 7.06/1.49  
% 7.06/1.49  fof(f20,plain,(
% 7.06/1.49    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 7.06/1.49    inference(flattening,[],[f19])).
% 7.06/1.49  
% 7.06/1.49  fof(f36,plain,(
% 7.06/1.49    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 7.06/1.49    inference(cnf_transformation,[],[f20])).
% 7.06/1.49  
% 7.06/1.49  fof(f55,plain,(
% 7.06/1.49    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 7.06/1.49    inference(definition_unfolding,[],[f36,f37])).
% 7.06/1.49  
% 7.06/1.49  fof(f52,plain,(
% 7.06/1.49    ~r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1))),
% 7.06/1.49    inference(cnf_transformation,[],[f32])).
% 7.06/1.49  
% 7.06/1.49  fof(f59,plain,(
% 7.06/1.49    ~r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1)))),
% 7.06/1.49    inference(definition_unfolding,[],[f52,f37])).
% 7.06/1.49  
% 7.06/1.49  fof(f14,axiom,(
% 7.06/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.06/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.06/1.49  
% 7.06/1.49  fof(f27,plain,(
% 7.06/1.49    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.06/1.49    inference(ennf_transformation,[],[f14])).
% 7.06/1.49  
% 7.06/1.49  fof(f50,plain,(
% 7.06/1.49    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.06/1.49    inference(cnf_transformation,[],[f27])).
% 7.06/1.49  
% 7.06/1.49  fof(f9,axiom,(
% 7.06/1.49    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 7.06/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.06/1.49  
% 7.06/1.49  fof(f22,plain,(
% 7.06/1.49    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.06/1.49    inference(ennf_transformation,[],[f9])).
% 7.06/1.49  
% 7.06/1.49  fof(f30,plain,(
% 7.06/1.49    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.06/1.49    inference(nnf_transformation,[],[f22])).
% 7.06/1.49  
% 7.06/1.49  fof(f43,plain,(
% 7.06/1.49    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.06/1.49    inference(cnf_transformation,[],[f30])).
% 7.06/1.49  
% 7.06/1.49  fof(f49,plain,(
% 7.06/1.49    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.06/1.49    inference(cnf_transformation,[],[f27])).
% 7.06/1.49  
% 7.06/1.49  fof(f12,axiom,(
% 7.06/1.49    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 7.06/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.06/1.49  
% 7.06/1.49  fof(f24,plain,(
% 7.06/1.49    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 7.06/1.49    inference(ennf_transformation,[],[f12])).
% 7.06/1.49  
% 7.06/1.49  fof(f25,plain,(
% 7.06/1.49    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.06/1.49    inference(flattening,[],[f24])).
% 7.06/1.49  
% 7.06/1.49  fof(f47,plain,(
% 7.06/1.49    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.06/1.49    inference(cnf_transformation,[],[f25])).
% 7.06/1.49  
% 7.06/1.49  fof(f13,axiom,(
% 7.06/1.49    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 7.06/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.06/1.49  
% 7.06/1.49  fof(f26,plain,(
% 7.06/1.49    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 7.06/1.49    inference(ennf_transformation,[],[f13])).
% 7.06/1.49  
% 7.06/1.49  fof(f48,plain,(
% 7.06/1.49    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 7.06/1.49    inference(cnf_transformation,[],[f26])).
% 7.06/1.49  
% 7.06/1.49  cnf(c_1,plain,
% 7.06/1.49      ( ~ r1_tarski(X0,X1) | r1_tarski(k4_xboole_0(X0,X2),X1) ),
% 7.06/1.49      inference(cnf_transformation,[],[f34]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_937,plain,
% 7.06/1.49      ( r1_tarski(X0,X1) != iProver_top
% 7.06/1.49      | r1_tarski(k4_xboole_0(X0,X2),X1) = iProver_top ),
% 7.06/1.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_2,plain,
% 7.06/1.49      ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))
% 7.06/1.49      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ),
% 7.06/1.49      inference(cnf_transformation,[],[f54]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_936,plain,
% 7.06/1.49      ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) = iProver_top
% 7.06/1.49      | r1_tarski(k4_xboole_0(X0,X1),X2) != iProver_top ),
% 7.06/1.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_0,plain,
% 7.06/1.49      ( k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0)) ),
% 7.06/1.49      inference(cnf_transformation,[],[f53]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_3238,plain,
% 7.06/1.49      ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) = iProver_top
% 7.06/1.49      | r1_tarski(k4_xboole_0(X0,X2),X1) != iProver_top ),
% 7.06/1.49      inference(superposition,[status(thm)],[c_0,c_936]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_18,negated_conjecture,
% 7.06/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 7.06/1.49      inference(cnf_transformation,[],[f51]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_928,plain,
% 7.06/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.06/1.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_7,plain,
% 7.06/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.06/1.49      inference(cnf_transformation,[],[f40]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_933,plain,
% 7.06/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.06/1.49      | r1_tarski(X0,X1) = iProver_top ),
% 7.06/1.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_1099,plain,
% 7.06/1.49      ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 7.06/1.49      inference(superposition,[status(thm)],[c_928,c_933]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_8,plain,
% 7.06/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.06/1.49      | ~ v1_relat_1(X1)
% 7.06/1.49      | v1_relat_1(X0) ),
% 7.06/1.49      inference(cnf_transformation,[],[f42]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_6,plain,
% 7.06/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.06/1.49      inference(cnf_transformation,[],[f41]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_138,plain,
% 7.06/1.49      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.06/1.49      inference(prop_impl,[status(thm)],[c_6]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_139,plain,
% 7.06/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.06/1.49      inference(renaming,[status(thm)],[c_138]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_171,plain,
% 7.06/1.49      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 7.06/1.49      inference(bin_hyper_res,[status(thm)],[c_8,c_139]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_927,plain,
% 7.06/1.49      ( r1_tarski(X0,X1) != iProver_top
% 7.06/1.49      | v1_relat_1(X1) != iProver_top
% 7.06/1.49      | v1_relat_1(X0) = iProver_top ),
% 7.06/1.49      inference(predicate_to_equality,[status(thm)],[c_171]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_2819,plain,
% 7.06/1.49      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 7.06/1.49      | v1_relat_1(sK2) = iProver_top ),
% 7.06/1.49      inference(superposition,[status(thm)],[c_1099,c_927]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_19,plain,
% 7.06/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.06/1.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_1027,plain,
% 7.06/1.49      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.06/1.49      | r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
% 7.06/1.49      inference(instantiation,[status(thm)],[c_7]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_1028,plain,
% 7.06/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.06/1.49      | r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 7.06/1.49      inference(predicate_to_equality,[status(thm)],[c_1027]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_1040,plain,
% 7.06/1.49      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 7.06/1.49      | v1_relat_1(X0)
% 7.06/1.49      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 7.06/1.49      inference(instantiation,[status(thm)],[c_171]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_1123,plain,
% 7.06/1.49      ( ~ r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
% 7.06/1.49      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
% 7.06/1.49      | v1_relat_1(sK2) ),
% 7.06/1.49      inference(instantiation,[status(thm)],[c_1040]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_1124,plain,
% 7.06/1.49      ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) != iProver_top
% 7.06/1.49      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 7.06/1.49      | v1_relat_1(sK2) = iProver_top ),
% 7.06/1.49      inference(predicate_to_equality,[status(thm)],[c_1123]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_12,plain,
% 7.06/1.49      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 7.06/1.49      inference(cnf_transformation,[],[f46]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_1153,plain,
% 7.06/1.49      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 7.06/1.49      inference(instantiation,[status(thm)],[c_12]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_1154,plain,
% 7.06/1.49      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 7.06/1.49      inference(predicate_to_equality,[status(thm)],[c_1153]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_5867,plain,
% 7.06/1.49      ( v1_relat_1(sK2) = iProver_top ),
% 7.06/1.49      inference(global_propositional_subsumption,
% 7.06/1.49                [status(thm)],
% 7.06/1.49                [c_2819,c_19,c_1028,c_1124,c_1154]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_11,plain,
% 7.06/1.49      ( ~ v1_relat_1(X0)
% 7.06/1.49      | k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) ),
% 7.06/1.49      inference(cnf_transformation,[],[f58]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_932,plain,
% 7.06/1.49      ( k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
% 7.06/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.06/1.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_5872,plain,
% 7.06/1.49      ( k3_tarski(k2_tarski(k1_relat_1(sK2),k2_relat_1(sK2))) = k3_relat_1(sK2) ),
% 7.06/1.49      inference(superposition,[status(thm)],[c_5867,c_932]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_6429,plain,
% 7.06/1.49      ( k3_tarski(k2_tarski(k2_relat_1(sK2),k1_relat_1(sK2))) = k3_relat_1(sK2) ),
% 7.06/1.49      inference(superposition,[status(thm)],[c_5872,c_0]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_3,plain,
% 7.06/1.49      ( ~ r1_tarski(X0,X1)
% 7.06/1.49      | ~ r1_tarski(X2,X1)
% 7.06/1.49      | r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) ),
% 7.06/1.49      inference(cnf_transformation,[],[f55]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_935,plain,
% 7.06/1.49      ( r1_tarski(X0,X1) != iProver_top
% 7.06/1.49      | r1_tarski(X2,X1) != iProver_top
% 7.06/1.49      | r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) = iProver_top ),
% 7.06/1.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_10689,plain,
% 7.06/1.49      ( r1_tarski(k3_relat_1(sK2),X0) = iProver_top
% 7.06/1.49      | r1_tarski(k1_relat_1(sK2),X0) != iProver_top
% 7.06/1.49      | r1_tarski(k2_relat_1(sK2),X0) != iProver_top ),
% 7.06/1.49      inference(superposition,[status(thm)],[c_6429,c_935]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_12705,plain,
% 7.06/1.49      ( r1_tarski(k4_xboole_0(k1_relat_1(sK2),X0),X1) != iProver_top
% 7.06/1.49      | r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(X1,X0))) = iProver_top
% 7.06/1.49      | r1_tarski(k2_relat_1(sK2),k3_tarski(k2_tarski(X1,X0))) != iProver_top ),
% 7.06/1.49      inference(superposition,[status(thm)],[c_3238,c_10689]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_15122,plain,
% 7.06/1.49      ( r1_tarski(k4_xboole_0(k1_relat_1(sK2),X0),X1) != iProver_top
% 7.06/1.49      | r1_tarski(k4_xboole_0(k2_relat_1(sK2),X1),X0) != iProver_top
% 7.06/1.49      | r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(X1,X0))) = iProver_top ),
% 7.06/1.49      inference(superposition,[status(thm)],[c_936,c_12705]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_17,negated_conjecture,
% 7.06/1.49      ( ~ r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1))) ),
% 7.06/1.49      inference(cnf_transformation,[],[f59]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_929,plain,
% 7.06/1.49      ( r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1))) != iProver_top ),
% 7.06/1.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_21155,plain,
% 7.06/1.49      ( r1_tarski(k4_xboole_0(k1_relat_1(sK2),sK1),sK0) != iProver_top
% 7.06/1.49      | r1_tarski(k4_xboole_0(k2_relat_1(sK2),sK0),sK1) != iProver_top ),
% 7.06/1.49      inference(superposition,[status(thm)],[c_15122,c_929]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_15,plain,
% 7.06/1.49      ( v5_relat_1(X0,X1)
% 7.06/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 7.06/1.49      inference(cnf_transformation,[],[f50]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_10,plain,
% 7.06/1.49      ( ~ v5_relat_1(X0,X1)
% 7.06/1.49      | r1_tarski(k2_relat_1(X0),X1)
% 7.06/1.49      | ~ v1_relat_1(X0) ),
% 7.06/1.49      inference(cnf_transformation,[],[f43]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_250,plain,
% 7.06/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.06/1.49      | r1_tarski(k2_relat_1(X0),X2)
% 7.06/1.49      | ~ v1_relat_1(X0) ),
% 7.06/1.49      inference(resolution,[status(thm)],[c_15,c_10]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_1242,plain,
% 7.06/1.49      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.06/1.49      | r1_tarski(k2_relat_1(sK2),X1)
% 7.06/1.49      | ~ v1_relat_1(sK2) ),
% 7.06/1.49      inference(instantiation,[status(thm)],[c_250]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_1911,plain,
% 7.06/1.49      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.06/1.49      | r1_tarski(k2_relat_1(sK2),sK1)
% 7.06/1.49      | ~ v1_relat_1(sK2) ),
% 7.06/1.49      inference(instantiation,[status(thm)],[c_1242]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_1912,plain,
% 7.06/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.06/1.49      | r1_tarski(k2_relat_1(sK2),sK1) = iProver_top
% 7.06/1.49      | v1_relat_1(sK2) != iProver_top ),
% 7.06/1.49      inference(predicate_to_equality,[status(thm)],[c_1911]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_2653,plain,
% 7.06/1.49      ( r1_tarski(k4_xboole_0(k2_relat_1(sK2),X0),sK1)
% 7.06/1.49      | ~ r1_tarski(k2_relat_1(sK2),sK1) ),
% 7.06/1.49      inference(instantiation,[status(thm)],[c_1]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_2657,plain,
% 7.06/1.49      ( r1_tarski(k4_xboole_0(k2_relat_1(sK2),X0),sK1) = iProver_top
% 7.06/1.49      | r1_tarski(k2_relat_1(sK2),sK1) != iProver_top ),
% 7.06/1.49      inference(predicate_to_equality,[status(thm)],[c_2653]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_2659,plain,
% 7.06/1.49      ( r1_tarski(k4_xboole_0(k2_relat_1(sK2),sK0),sK1) = iProver_top
% 7.06/1.49      | r1_tarski(k2_relat_1(sK2),sK1) != iProver_top ),
% 7.06/1.49      inference(instantiation,[status(thm)],[c_2657]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_21437,plain,
% 7.06/1.49      ( r1_tarski(k4_xboole_0(k1_relat_1(sK2),sK1),sK0) != iProver_top ),
% 7.06/1.49      inference(global_propositional_subsumption,
% 7.06/1.49                [status(thm)],
% 7.06/1.49                [c_21155,c_19,c_1028,c_1124,c_1154,c_1912,c_2659]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_21442,plain,
% 7.06/1.49      ( r1_tarski(k1_relat_1(sK2),sK0) != iProver_top ),
% 7.06/1.49      inference(superposition,[status(thm)],[c_937,c_21437]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_16,plain,
% 7.06/1.49      ( v4_relat_1(X0,X1)
% 7.06/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.06/1.49      inference(cnf_transformation,[],[f49]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_13,plain,
% 7.06/1.49      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 7.06/1.49      inference(cnf_transformation,[],[f47]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_232,plain,
% 7.06/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.06/1.49      | ~ v1_relat_1(X0)
% 7.06/1.49      | k7_relat_1(X0,X1) = X0 ),
% 7.06/1.49      inference(resolution,[status(thm)],[c_16,c_13]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_926,plain,
% 7.06/1.49      ( k7_relat_1(X0,X1) = X0
% 7.06/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.06/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.06/1.49      inference(predicate_to_equality,[status(thm)],[c_232]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_6923,plain,
% 7.06/1.49      ( k7_relat_1(sK2,sK0) = sK2 | v1_relat_1(sK2) != iProver_top ),
% 7.06/1.49      inference(superposition,[status(thm)],[c_928,c_926]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_1241,plain,
% 7.06/1.49      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.06/1.49      | ~ v1_relat_1(sK2)
% 7.06/1.49      | k7_relat_1(sK2,X0) = sK2 ),
% 7.06/1.49      inference(instantiation,[status(thm)],[c_232]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_1908,plain,
% 7.06/1.49      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.06/1.49      | ~ v1_relat_1(sK2)
% 7.06/1.49      | k7_relat_1(sK2,sK0) = sK2 ),
% 7.06/1.49      inference(instantiation,[status(thm)],[c_1241]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_9316,plain,
% 7.06/1.49      ( k7_relat_1(sK2,sK0) = sK2 ),
% 7.06/1.49      inference(global_propositional_subsumption,
% 7.06/1.49                [status(thm)],
% 7.06/1.49                [c_6923,c_18,c_1027,c_1123,c_1153,c_1908]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_14,plain,
% 7.06/1.49      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) | ~ v1_relat_1(X0) ),
% 7.06/1.49      inference(cnf_transformation,[],[f48]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_930,plain,
% 7.06/1.49      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
% 7.06/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.06/1.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(c_9319,plain,
% 7.06/1.49      ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top
% 7.06/1.49      | v1_relat_1(sK2) != iProver_top ),
% 7.06/1.49      inference(superposition,[status(thm)],[c_9316,c_930]) ).
% 7.06/1.49  
% 7.06/1.49  cnf(contradiction,plain,
% 7.06/1.49      ( $false ),
% 7.06/1.49      inference(minisat,
% 7.06/1.49                [status(thm)],
% 7.06/1.49                [c_21442,c_9319,c_1154,c_1124,c_1028,c_19]) ).
% 7.06/1.49  
% 7.06/1.49  
% 7.06/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.06/1.49  
% 7.06/1.49  ------                               Statistics
% 7.06/1.49  
% 7.06/1.49  ------ General
% 7.06/1.49  
% 7.06/1.49  abstr_ref_over_cycles:                  0
% 7.06/1.49  abstr_ref_under_cycles:                 0
% 7.06/1.49  gc_basic_clause_elim:                   0
% 7.06/1.49  forced_gc_time:                         0
% 7.06/1.49  parsing_time:                           0.009
% 7.06/1.49  unif_index_cands_time:                  0.
% 7.06/1.49  unif_index_add_time:                    0.
% 7.06/1.49  orderings_time:                         0.
% 7.06/1.49  out_proof_time:                         0.01
% 7.06/1.49  total_time:                             0.687
% 7.06/1.49  num_of_symbols:                         48
% 7.06/1.49  num_of_terms:                           41330
% 7.06/1.49  
% 7.06/1.49  ------ Preprocessing
% 7.06/1.49  
% 7.06/1.49  num_of_splits:                          0
% 7.06/1.49  num_of_split_atoms:                     0
% 7.06/1.49  num_of_reused_defs:                     0
% 7.06/1.49  num_eq_ax_congr_red:                    19
% 7.06/1.49  num_of_sem_filtered_clauses:            1
% 7.06/1.49  num_of_subtypes:                        0
% 7.06/1.49  monotx_restored_types:                  0
% 7.06/1.49  sat_num_of_epr_types:                   0
% 7.06/1.49  sat_num_of_non_cyclic_types:            0
% 7.06/1.49  sat_guarded_non_collapsed_types:        0
% 7.06/1.49  num_pure_diseq_elim:                    0
% 7.06/1.49  simp_replaced_by:                       0
% 7.06/1.49  res_preprocessed:                       90
% 7.06/1.49  prep_upred:                             0
% 7.06/1.49  prep_unflattend:                        10
% 7.06/1.49  smt_new_axioms:                         0
% 7.06/1.49  pred_elim_cands:                        3
% 7.06/1.49  pred_elim:                              2
% 7.06/1.49  pred_elim_cl:                           3
% 7.06/1.49  pred_elim_cycles:                       4
% 7.06/1.49  merged_defs:                            8
% 7.06/1.49  merged_defs_ncl:                        0
% 7.06/1.49  bin_hyper_res:                          9
% 7.06/1.49  prep_cycles:                            4
% 7.06/1.49  pred_elim_time:                         0.003
% 7.06/1.49  splitting_time:                         0.
% 7.06/1.49  sem_filter_time:                        0.
% 7.06/1.49  monotx_time:                            0.001
% 7.06/1.49  subtype_inf_time:                       0.
% 7.06/1.49  
% 7.06/1.49  ------ Problem properties
% 7.06/1.49  
% 7.06/1.49  clauses:                                16
% 7.06/1.49  conjectures:                            2
% 7.06/1.49  epr:                                    1
% 7.06/1.49  horn:                                   16
% 7.06/1.49  ground:                                 2
% 7.06/1.49  unary:                                  6
% 7.06/1.49  binary:                                 6
% 7.06/1.49  lits:                                   30
% 7.06/1.49  lits_eq:                                5
% 7.06/1.49  fd_pure:                                0
% 7.06/1.49  fd_pseudo:                              0
% 7.06/1.49  fd_cond:                                0
% 7.06/1.49  fd_pseudo_cond:                         0
% 7.06/1.49  ac_symbols:                             0
% 7.06/1.49  
% 7.06/1.49  ------ Propositional Solver
% 7.06/1.49  
% 7.06/1.49  prop_solver_calls:                      31
% 7.06/1.49  prop_fast_solver_calls:                 587
% 7.06/1.49  smt_solver_calls:                       0
% 7.06/1.49  smt_fast_solver_calls:                  0
% 7.06/1.49  prop_num_of_clauses:                    10472
% 7.06/1.49  prop_preprocess_simplified:             13699
% 7.06/1.49  prop_fo_subsumed:                       7
% 7.06/1.49  prop_solver_time:                       0.
% 7.06/1.49  smt_solver_time:                        0.
% 7.06/1.49  smt_fast_solver_time:                   0.
% 7.06/1.49  prop_fast_solver_time:                  0.
% 7.06/1.49  prop_unsat_core_time:                   0.001
% 7.06/1.49  
% 7.06/1.49  ------ QBF
% 7.06/1.49  
% 7.06/1.49  qbf_q_res:                              0
% 7.06/1.49  qbf_num_tautologies:                    0
% 7.06/1.49  qbf_prep_cycles:                        0
% 7.06/1.49  
% 7.06/1.49  ------ BMC1
% 7.06/1.49  
% 7.06/1.49  bmc1_current_bound:                     -1
% 7.06/1.49  bmc1_last_solved_bound:                 -1
% 7.06/1.49  bmc1_unsat_core_size:                   -1
% 7.06/1.49  bmc1_unsat_core_parents_size:           -1
% 7.06/1.49  bmc1_merge_next_fun:                    0
% 7.06/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.06/1.49  
% 7.06/1.49  ------ Instantiation
% 7.06/1.49  
% 7.06/1.49  inst_num_of_clauses:                    1870
% 7.06/1.49  inst_num_in_passive:                    580
% 7.06/1.49  inst_num_in_active:                     460
% 7.06/1.49  inst_num_in_unprocessed:                830
% 7.06/1.49  inst_num_of_loops:                      480
% 7.06/1.49  inst_num_of_learning_restarts:          0
% 7.06/1.49  inst_num_moves_active_passive:          18
% 7.06/1.49  inst_lit_activity:                      0
% 7.06/1.49  inst_lit_activity_moves:                2
% 7.06/1.49  inst_num_tautologies:                   0
% 7.06/1.49  inst_num_prop_implied:                  0
% 7.06/1.49  inst_num_existing_simplified:           0
% 7.06/1.49  inst_num_eq_res_simplified:             0
% 7.06/1.49  inst_num_child_elim:                    0
% 7.06/1.49  inst_num_of_dismatching_blockings:      326
% 7.06/1.49  inst_num_of_non_proper_insts:           992
% 7.06/1.49  inst_num_of_duplicates:                 0
% 7.06/1.49  inst_inst_num_from_inst_to_res:         0
% 7.06/1.49  inst_dismatching_checking_time:         0.
% 7.06/1.49  
% 7.06/1.49  ------ Resolution
% 7.06/1.49  
% 7.06/1.49  res_num_of_clauses:                     0
% 7.06/1.49  res_num_in_passive:                     0
% 7.06/1.49  res_num_in_active:                      0
% 7.06/1.49  res_num_of_loops:                       94
% 7.06/1.49  res_forward_subset_subsumed:            14
% 7.06/1.49  res_backward_subset_subsumed:           0
% 7.06/1.49  res_forward_subsumed:                   0
% 7.06/1.49  res_backward_subsumed:                  0
% 7.06/1.49  res_forward_subsumption_resolution:     0
% 7.06/1.49  res_backward_subsumption_resolution:    0
% 7.06/1.49  res_clause_to_clause_subsumption:       17141
% 7.06/1.49  res_orphan_elimination:                 0
% 7.06/1.49  res_tautology_del:                      46
% 7.06/1.49  res_num_eq_res_simplified:              0
% 7.06/1.49  res_num_sel_changes:                    0
% 7.06/1.49  res_moves_from_active_to_pass:          0
% 7.06/1.49  
% 7.06/1.49  ------ Superposition
% 7.06/1.49  
% 7.06/1.49  sup_time_total:                         0.
% 7.06/1.49  sup_time_generating:                    0.
% 7.06/1.49  sup_time_sim_full:                      0.
% 7.06/1.49  sup_time_sim_immed:                     0.
% 7.06/1.49  
% 7.06/1.49  sup_num_of_clauses:                     1643
% 7.06/1.49  sup_num_in_active:                      94
% 7.06/1.49  sup_num_in_passive:                     1549
% 7.06/1.49  sup_num_of_loops:                       94
% 7.06/1.49  sup_fw_superposition:                   1738
% 7.06/1.49  sup_bw_superposition:                   1543
% 7.06/1.49  sup_immediate_simplified:               439
% 7.06/1.49  sup_given_eliminated:                   0
% 7.06/1.49  comparisons_done:                       0
% 7.06/1.49  comparisons_avoided:                    0
% 7.06/1.49  
% 7.06/1.49  ------ Simplifications
% 7.06/1.49  
% 7.06/1.49  
% 7.06/1.49  sim_fw_subset_subsumed:                 0
% 7.06/1.49  sim_bw_subset_subsumed:                 1
% 7.06/1.49  sim_fw_subsumed:                        84
% 7.06/1.49  sim_bw_subsumed:                        19
% 7.06/1.49  sim_fw_subsumption_res:                 0
% 7.06/1.49  sim_bw_subsumption_res:                 0
% 7.06/1.49  sim_tautology_del:                      1
% 7.06/1.49  sim_eq_tautology_del:                   33
% 7.06/1.49  sim_eq_res_simp:                        0
% 7.06/1.49  sim_fw_demodulated:                     290
% 7.06/1.49  sim_bw_demodulated:                     14
% 7.06/1.49  sim_light_normalised:                   73
% 7.06/1.49  sim_joinable_taut:                      0
% 7.06/1.49  sim_joinable_simp:                      0
% 7.06/1.49  sim_ac_normalised:                      0
% 7.06/1.49  sim_smt_subsumption:                    0
% 7.06/1.49  
%------------------------------------------------------------------------------
