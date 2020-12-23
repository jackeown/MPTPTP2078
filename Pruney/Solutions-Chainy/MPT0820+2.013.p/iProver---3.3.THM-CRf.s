%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:54:53 EST 2020

% Result     : Theorem 7.85s
% Output     : CNFRefutation 7.85s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 175 expanded)
%              Number of clauses        :   52 (  65 expanded)
%              Number of leaves         :   15 (  35 expanded)
%              Depth                    :   16
%              Number of atoms          :  214 ( 351 expanded)
%              Number of equality atoms :   76 (  92 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k2_tarski(X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f34,f38])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f30,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1))
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f32,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ~ r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1))
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ~ r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f32])).

fof(f48,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f33])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f41,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f53,plain,(
    ! [X0] :
      ( k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f41,f38])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f37,f38])).

fof(f49,plain,(
    ~ r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f33])).

fof(f54,plain,(
    ~ r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1))) ),
    inference(definition_unfolding,[],[f49,f38])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f51,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f36,f38])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k3_tarski(k2_tarski(X2,X1))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_536,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k3_tarski(k2_tarski(X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_522,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_10,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_526,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1081,plain,
    ( v4_relat_1(sK2,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_522,c_526])).

cnf(c_7,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_529,plain,
    ( k7_relat_1(X0,X1) = X0
    | v4_relat_1(X0,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2249,plain,
    ( k7_relat_1(sK2,sK0) = sK2
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1081,c_529])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_649,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_679,plain,
    ( v4_relat_1(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_735,plain,
    ( ~ v4_relat_1(sK2,X0)
    | ~ v1_relat_1(sK2)
    | k7_relat_1(sK2,X0) = sK2 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_745,plain,
    ( ~ v4_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2)
    | k7_relat_1(sK2,sK0) = sK2 ),
    inference(instantiation,[status(thm)],[c_735])).

cnf(c_2826,plain,
    ( k7_relat_1(sK2,sK0) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2249,c_14,c_649,c_679,c_745])).

cnf(c_8,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_528,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2829,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2826,c_528])).

cnf(c_15,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_650,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_649])).

cnf(c_3325,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2829,c_15,c_650])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_535,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3330,plain,
    ( r1_tarski(k1_relat_1(sK2),X0) = iProver_top
    | r1_tarski(sK0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3325,c_535])).

cnf(c_527,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_940,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_522,c_527])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_530,plain,
    ( k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1348,plain,
    ( k3_tarski(k2_tarski(k1_relat_1(sK2),k2_relat_1(sK2))) = k3_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_940,c_530])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_533,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2576,plain,
    ( r1_tarski(k3_relat_1(sK2),X0) = iProver_top
    | r1_tarski(k2_relat_1(sK2),X0) != iProver_top
    | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1348,c_533])).

cnf(c_4347,plain,
    ( r1_tarski(k3_relat_1(sK2),X0) = iProver_top
    | r1_tarski(k2_relat_1(sK2),X0) != iProver_top
    | r1_tarski(sK0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3330,c_2576])).

cnf(c_5818,plain,
    ( r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(X0,X1))) = iProver_top
    | r1_tarski(k2_relat_1(sK2),X1) != iProver_top
    | r1_tarski(sK0,k3_tarski(k2_tarski(X0,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_536,c_4347])).

cnf(c_13,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_523,plain,
    ( r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_29488,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1) != iProver_top
    | r1_tarski(sK0,k3_tarski(k2_tarski(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5818,c_523])).

cnf(c_2,plain,
    ( r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_3844,plain,
    ( r1_tarski(sK0,k3_tarski(k2_tarski(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_3845,plain,
    ( r1_tarski(sK0,k3_tarski(k2_tarski(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3844])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_524,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_953,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_522,c_524])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_525,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2207,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_953,c_525])).

cnf(c_3068,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2207,c_15])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_531,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3073,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3068,c_531])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_29488,c_3845,c_3073])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:56:52 EST 2020
% 0.18/0.34  % CPUTime    : 
% 0.18/0.34  % Running in FOF mode
% 7.85/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.85/1.49  
% 7.85/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.85/1.49  
% 7.85/1.49  ------  iProver source info
% 7.85/1.49  
% 7.85/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.85/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.85/1.49  git: non_committed_changes: false
% 7.85/1.49  git: last_make_outside_of_git: false
% 7.85/1.49  
% 7.85/1.49  ------ 
% 7.85/1.49  ------ Parsing...
% 7.85/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.85/1.49  
% 7.85/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 7.85/1.49  
% 7.85/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.85/1.49  
% 7.85/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.85/1.49  ------ Proving...
% 7.85/1.49  ------ Problem Properties 
% 7.85/1.49  
% 7.85/1.49  
% 7.85/1.49  clauses                                 15
% 7.85/1.49  conjectures                             2
% 7.85/1.49  EPR                                     1
% 7.85/1.49  Horn                                    15
% 7.85/1.49  unary                                   3
% 7.85/1.49  binary                                  9
% 7.85/1.49  lits                                    30
% 7.85/1.49  lits eq                                 3
% 7.85/1.49  fd_pure                                 0
% 7.85/1.49  fd_pseudo                               0
% 7.85/1.49  fd_cond                                 0
% 7.85/1.49  fd_pseudo_cond                          0
% 7.85/1.49  AC symbols                              0
% 7.85/1.49  
% 7.85/1.49  ------ Input Options Time Limit: Unbounded
% 7.85/1.49  
% 7.85/1.49  
% 7.85/1.49  ------ 
% 7.85/1.49  Current options:
% 7.85/1.49  ------ 
% 7.85/1.49  
% 7.85/1.49  
% 7.85/1.49  
% 7.85/1.49  
% 7.85/1.49  ------ Proving...
% 7.85/1.49  
% 7.85/1.49  
% 7.85/1.49  % SZS status Theorem for theBenchmark.p
% 7.85/1.49  
% 7.85/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.85/1.49  
% 7.85/1.49  fof(f1,axiom,(
% 7.85/1.49    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 7.85/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.85/1.49  
% 7.85/1.49  fof(f17,plain,(
% 7.85/1.49    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 7.85/1.49    inference(ennf_transformation,[],[f1])).
% 7.85/1.49  
% 7.85/1.49  fof(f34,plain,(
% 7.85/1.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 7.85/1.49    inference(cnf_transformation,[],[f17])).
% 7.85/1.49  
% 7.85/1.49  fof(f5,axiom,(
% 7.85/1.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 7.85/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.85/1.49  
% 7.85/1.49  fof(f38,plain,(
% 7.85/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 7.85/1.49    inference(cnf_transformation,[],[f5])).
% 7.85/1.49  
% 7.85/1.49  fof(f50,plain,(
% 7.85/1.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X2,X1))) | ~r1_tarski(X0,X1)) )),
% 7.85/1.49    inference(definition_unfolding,[],[f34,f38])).
% 7.85/1.49  
% 7.85/1.49  fof(f14,conjecture,(
% 7.85/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)))),
% 7.85/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.85/1.49  
% 7.85/1.49  fof(f15,negated_conjecture,(
% 7.85/1.49    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)))),
% 7.85/1.49    inference(negated_conjecture,[],[f14])).
% 7.85/1.49  
% 7.85/1.49  fof(f30,plain,(
% 7.85/1.49    ? [X0,X1,X2] : (~r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.85/1.49    inference(ennf_transformation,[],[f15])).
% 7.85/1.49  
% 7.85/1.49  fof(f32,plain,(
% 7.85/1.49    ? [X0,X1,X2] : (~r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (~r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 7.85/1.49    introduced(choice_axiom,[])).
% 7.85/1.49  
% 7.85/1.49  fof(f33,plain,(
% 7.85/1.49    ~r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 7.85/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f32])).
% 7.85/1.49  
% 7.85/1.49  fof(f48,plain,(
% 7.85/1.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 7.85/1.49    inference(cnf_transformation,[],[f33])).
% 7.85/1.49  
% 7.85/1.49  fof(f11,axiom,(
% 7.85/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.85/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.85/1.49  
% 7.85/1.49  fof(f16,plain,(
% 7.85/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 7.85/1.49    inference(pure_predicate_removal,[],[f11])).
% 7.85/1.49  
% 7.85/1.49  fof(f27,plain,(
% 7.85/1.49    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.85/1.49    inference(ennf_transformation,[],[f16])).
% 7.85/1.49  
% 7.85/1.49  fof(f45,plain,(
% 7.85/1.49    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.85/1.49    inference(cnf_transformation,[],[f27])).
% 7.85/1.49  
% 7.85/1.49  fof(f8,axiom,(
% 7.85/1.49    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 7.85/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.85/1.49  
% 7.85/1.49  fof(f23,plain,(
% 7.85/1.49    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 7.85/1.49    inference(ennf_transformation,[],[f8])).
% 7.85/1.49  
% 7.85/1.49  fof(f24,plain,(
% 7.85/1.49    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.85/1.49    inference(flattening,[],[f23])).
% 7.85/1.49  
% 7.85/1.49  fof(f42,plain,(
% 7.85/1.49    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.85/1.49    inference(cnf_transformation,[],[f24])).
% 7.85/1.49  
% 7.85/1.49  fof(f10,axiom,(
% 7.85/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.85/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.85/1.49  
% 7.85/1.49  fof(f26,plain,(
% 7.85/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.85/1.49    inference(ennf_transformation,[],[f10])).
% 7.85/1.49  
% 7.85/1.49  fof(f44,plain,(
% 7.85/1.49    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.85/1.49    inference(cnf_transformation,[],[f26])).
% 7.85/1.49  
% 7.85/1.49  fof(f9,axiom,(
% 7.85/1.49    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 7.85/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.85/1.49  
% 7.85/1.49  fof(f25,plain,(
% 7.85/1.49    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 7.85/1.49    inference(ennf_transformation,[],[f9])).
% 7.85/1.49  
% 7.85/1.49  fof(f43,plain,(
% 7.85/1.49    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 7.85/1.49    inference(cnf_transformation,[],[f25])).
% 7.85/1.49  
% 7.85/1.49  fof(f2,axiom,(
% 7.85/1.49    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 7.85/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.85/1.49  
% 7.85/1.49  fof(f18,plain,(
% 7.85/1.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 7.85/1.49    inference(ennf_transformation,[],[f2])).
% 7.85/1.49  
% 7.85/1.49  fof(f19,plain,(
% 7.85/1.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 7.85/1.49    inference(flattening,[],[f18])).
% 7.85/1.49  
% 7.85/1.49  fof(f35,plain,(
% 7.85/1.49    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 7.85/1.49    inference(cnf_transformation,[],[f19])).
% 7.85/1.49  
% 7.85/1.49  fof(f7,axiom,(
% 7.85/1.49    ! [X0] : (v1_relat_1(X0) => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0))),
% 7.85/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.85/1.49  
% 7.85/1.49  fof(f22,plain,(
% 7.85/1.49    ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0))),
% 7.85/1.49    inference(ennf_transformation,[],[f7])).
% 7.85/1.49  
% 7.85/1.49  fof(f41,plain,(
% 7.85/1.49    ( ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 7.85/1.49    inference(cnf_transformation,[],[f22])).
% 7.85/1.49  
% 7.85/1.49  fof(f53,plain,(
% 7.85/1.49    ( ! [X0] : (k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 7.85/1.49    inference(definition_unfolding,[],[f41,f38])).
% 7.85/1.49  
% 7.85/1.49  fof(f4,axiom,(
% 7.85/1.49    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 7.85/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.85/1.49  
% 7.85/1.49  fof(f20,plain,(
% 7.85/1.49    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 7.85/1.49    inference(ennf_transformation,[],[f4])).
% 7.85/1.49  
% 7.85/1.49  fof(f21,plain,(
% 7.85/1.49    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 7.85/1.49    inference(flattening,[],[f20])).
% 7.85/1.49  
% 7.85/1.49  fof(f37,plain,(
% 7.85/1.49    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 7.85/1.49    inference(cnf_transformation,[],[f21])).
% 7.85/1.49  
% 7.85/1.49  fof(f52,plain,(
% 7.85/1.49    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 7.85/1.49    inference(definition_unfolding,[],[f37,f38])).
% 7.85/1.49  
% 7.85/1.49  fof(f49,plain,(
% 7.85/1.49    ~r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1))),
% 7.85/1.49    inference(cnf_transformation,[],[f33])).
% 7.85/1.49  
% 7.85/1.49  fof(f54,plain,(
% 7.85/1.49    ~r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1)))),
% 7.85/1.49    inference(definition_unfolding,[],[f49,f38])).
% 7.85/1.49  
% 7.85/1.49  fof(f3,axiom,(
% 7.85/1.49    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 7.85/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.85/1.49  
% 7.85/1.49  fof(f36,plain,(
% 7.85/1.49    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 7.85/1.49    inference(cnf_transformation,[],[f3])).
% 7.85/1.49  
% 7.85/1.49  fof(f51,plain,(
% 7.85/1.49    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) )),
% 7.85/1.49    inference(definition_unfolding,[],[f36,f38])).
% 7.85/1.49  
% 7.85/1.49  fof(f13,axiom,(
% 7.85/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 7.85/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.85/1.49  
% 7.85/1.49  fof(f29,plain,(
% 7.85/1.49    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.85/1.49    inference(ennf_transformation,[],[f13])).
% 7.85/1.49  
% 7.85/1.49  fof(f47,plain,(
% 7.85/1.49    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.85/1.49    inference(cnf_transformation,[],[f29])).
% 7.85/1.49  
% 7.85/1.49  fof(f12,axiom,(
% 7.85/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 7.85/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.85/1.49  
% 7.85/1.49  fof(f28,plain,(
% 7.85/1.49    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.85/1.49    inference(ennf_transformation,[],[f12])).
% 7.85/1.49  
% 7.85/1.49  fof(f46,plain,(
% 7.85/1.49    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.85/1.49    inference(cnf_transformation,[],[f28])).
% 7.85/1.49  
% 7.85/1.49  fof(f6,axiom,(
% 7.85/1.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.85/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.85/1.49  
% 7.85/1.49  fof(f31,plain,(
% 7.85/1.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.85/1.49    inference(nnf_transformation,[],[f6])).
% 7.85/1.49  
% 7.85/1.49  fof(f39,plain,(
% 7.85/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.85/1.49    inference(cnf_transformation,[],[f31])).
% 7.85/1.49  
% 7.85/1.49  cnf(c_0,plain,
% 7.85/1.49      ( ~ r1_tarski(X0,X1) | r1_tarski(X0,k3_tarski(k2_tarski(X2,X1))) ),
% 7.85/1.49      inference(cnf_transformation,[],[f50]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_536,plain,
% 7.85/1.49      ( r1_tarski(X0,X1) != iProver_top
% 7.85/1.49      | r1_tarski(X0,k3_tarski(k2_tarski(X2,X1))) = iProver_top ),
% 7.85/1.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_14,negated_conjecture,
% 7.85/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 7.85/1.49      inference(cnf_transformation,[],[f48]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_522,plain,
% 7.85/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.85/1.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_10,plain,
% 7.85/1.49      ( v4_relat_1(X0,X1)
% 7.85/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.85/1.49      inference(cnf_transformation,[],[f45]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_526,plain,
% 7.85/1.49      ( v4_relat_1(X0,X1) = iProver_top
% 7.85/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 7.85/1.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_1081,plain,
% 7.85/1.49      ( v4_relat_1(sK2,sK0) = iProver_top ),
% 7.85/1.49      inference(superposition,[status(thm)],[c_522,c_526]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_7,plain,
% 7.85/1.49      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 7.85/1.49      inference(cnf_transformation,[],[f42]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_529,plain,
% 7.85/1.49      ( k7_relat_1(X0,X1) = X0
% 7.85/1.49      | v4_relat_1(X0,X1) != iProver_top
% 7.85/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.85/1.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_2249,plain,
% 7.85/1.49      ( k7_relat_1(sK2,sK0) = sK2 | v1_relat_1(sK2) != iProver_top ),
% 7.85/1.49      inference(superposition,[status(thm)],[c_1081,c_529]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_9,plain,
% 7.85/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.85/1.49      | v1_relat_1(X0) ),
% 7.85/1.49      inference(cnf_transformation,[],[f44]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_649,plain,
% 7.85/1.49      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.85/1.49      | v1_relat_1(sK2) ),
% 7.85/1.49      inference(instantiation,[status(thm)],[c_9]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_679,plain,
% 7.85/1.49      ( v4_relat_1(sK2,sK0)
% 7.85/1.49      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 7.85/1.49      inference(instantiation,[status(thm)],[c_10]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_735,plain,
% 7.85/1.49      ( ~ v4_relat_1(sK2,X0)
% 7.85/1.49      | ~ v1_relat_1(sK2)
% 7.85/1.49      | k7_relat_1(sK2,X0) = sK2 ),
% 7.85/1.49      inference(instantiation,[status(thm)],[c_7]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_745,plain,
% 7.85/1.49      ( ~ v4_relat_1(sK2,sK0)
% 7.85/1.49      | ~ v1_relat_1(sK2)
% 7.85/1.49      | k7_relat_1(sK2,sK0) = sK2 ),
% 7.85/1.49      inference(instantiation,[status(thm)],[c_735]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_2826,plain,
% 7.85/1.49      ( k7_relat_1(sK2,sK0) = sK2 ),
% 7.85/1.49      inference(global_propositional_subsumption,
% 7.85/1.49                [status(thm)],
% 7.85/1.49                [c_2249,c_14,c_649,c_679,c_745]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_8,plain,
% 7.85/1.49      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) | ~ v1_relat_1(X0) ),
% 7.85/1.49      inference(cnf_transformation,[],[f43]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_528,plain,
% 7.85/1.49      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
% 7.85/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.85/1.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_2829,plain,
% 7.85/1.49      ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top
% 7.85/1.49      | v1_relat_1(sK2) != iProver_top ),
% 7.85/1.49      inference(superposition,[status(thm)],[c_2826,c_528]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_15,plain,
% 7.85/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.85/1.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_650,plain,
% 7.85/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.85/1.49      | v1_relat_1(sK2) = iProver_top ),
% 7.85/1.49      inference(predicate_to_equality,[status(thm)],[c_649]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_3325,plain,
% 7.85/1.49      ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
% 7.85/1.49      inference(global_propositional_subsumption,
% 7.85/1.49                [status(thm)],
% 7.85/1.49                [c_2829,c_15,c_650]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_1,plain,
% 7.85/1.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 7.85/1.49      inference(cnf_transformation,[],[f35]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_535,plain,
% 7.85/1.49      ( r1_tarski(X0,X1) != iProver_top
% 7.85/1.49      | r1_tarski(X1,X2) != iProver_top
% 7.85/1.49      | r1_tarski(X0,X2) = iProver_top ),
% 7.85/1.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_3330,plain,
% 7.85/1.49      ( r1_tarski(k1_relat_1(sK2),X0) = iProver_top
% 7.85/1.49      | r1_tarski(sK0,X0) != iProver_top ),
% 7.85/1.49      inference(superposition,[status(thm)],[c_3325,c_535]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_527,plain,
% 7.85/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.85/1.49      | v1_relat_1(X0) = iProver_top ),
% 7.85/1.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_940,plain,
% 7.85/1.49      ( v1_relat_1(sK2) = iProver_top ),
% 7.85/1.49      inference(superposition,[status(thm)],[c_522,c_527]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_6,plain,
% 7.85/1.49      ( ~ v1_relat_1(X0)
% 7.85/1.49      | k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) ),
% 7.85/1.49      inference(cnf_transformation,[],[f53]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_530,plain,
% 7.85/1.49      ( k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
% 7.85/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.85/1.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_1348,plain,
% 7.85/1.49      ( k3_tarski(k2_tarski(k1_relat_1(sK2),k2_relat_1(sK2))) = k3_relat_1(sK2) ),
% 7.85/1.49      inference(superposition,[status(thm)],[c_940,c_530]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_3,plain,
% 7.85/1.49      ( ~ r1_tarski(X0,X1)
% 7.85/1.49      | ~ r1_tarski(X2,X1)
% 7.85/1.49      | r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) ),
% 7.85/1.49      inference(cnf_transformation,[],[f52]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_533,plain,
% 7.85/1.49      ( r1_tarski(X0,X1) != iProver_top
% 7.85/1.49      | r1_tarski(X2,X1) != iProver_top
% 7.85/1.49      | r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) = iProver_top ),
% 7.85/1.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_2576,plain,
% 7.85/1.49      ( r1_tarski(k3_relat_1(sK2),X0) = iProver_top
% 7.85/1.49      | r1_tarski(k2_relat_1(sK2),X0) != iProver_top
% 7.85/1.49      | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
% 7.85/1.49      inference(superposition,[status(thm)],[c_1348,c_533]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_4347,plain,
% 7.85/1.49      ( r1_tarski(k3_relat_1(sK2),X0) = iProver_top
% 7.85/1.49      | r1_tarski(k2_relat_1(sK2),X0) != iProver_top
% 7.85/1.49      | r1_tarski(sK0,X0) != iProver_top ),
% 7.85/1.49      inference(superposition,[status(thm)],[c_3330,c_2576]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_5818,plain,
% 7.85/1.49      ( r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(X0,X1))) = iProver_top
% 7.85/1.49      | r1_tarski(k2_relat_1(sK2),X1) != iProver_top
% 7.85/1.49      | r1_tarski(sK0,k3_tarski(k2_tarski(X0,X1))) != iProver_top ),
% 7.85/1.49      inference(superposition,[status(thm)],[c_536,c_4347]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_13,negated_conjecture,
% 7.85/1.49      ( ~ r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1))) ),
% 7.85/1.49      inference(cnf_transformation,[],[f54]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_523,plain,
% 7.85/1.49      ( r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1))) != iProver_top ),
% 7.85/1.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_29488,plain,
% 7.85/1.49      ( r1_tarski(k2_relat_1(sK2),sK1) != iProver_top
% 7.85/1.49      | r1_tarski(sK0,k3_tarski(k2_tarski(sK0,sK1))) != iProver_top ),
% 7.85/1.49      inference(superposition,[status(thm)],[c_5818,c_523]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_2,plain,
% 7.85/1.49      ( r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
% 7.85/1.49      inference(cnf_transformation,[],[f51]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_3844,plain,
% 7.85/1.49      ( r1_tarski(sK0,k3_tarski(k2_tarski(sK0,sK1))) ),
% 7.85/1.49      inference(instantiation,[status(thm)],[c_2]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_3845,plain,
% 7.85/1.49      ( r1_tarski(sK0,k3_tarski(k2_tarski(sK0,sK1))) = iProver_top ),
% 7.85/1.49      inference(predicate_to_equality,[status(thm)],[c_3844]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_12,plain,
% 7.85/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.85/1.49      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 7.85/1.49      inference(cnf_transformation,[],[f47]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_524,plain,
% 7.85/1.49      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 7.85/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.85/1.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_953,plain,
% 7.85/1.49      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 7.85/1.49      inference(superposition,[status(thm)],[c_522,c_524]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_11,plain,
% 7.85/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.85/1.49      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
% 7.85/1.49      inference(cnf_transformation,[],[f46]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_525,plain,
% 7.85/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.85/1.49      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
% 7.85/1.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_2207,plain,
% 7.85/1.49      ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) = iProver_top
% 7.85/1.49      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 7.85/1.49      inference(superposition,[status(thm)],[c_953,c_525]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_3068,plain,
% 7.85/1.49      ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) = iProver_top ),
% 7.85/1.49      inference(global_propositional_subsumption,
% 7.85/1.49                [status(thm)],
% 7.85/1.49                [c_2207,c_15]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_5,plain,
% 7.85/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.85/1.49      inference(cnf_transformation,[],[f39]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_531,plain,
% 7.85/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.85/1.49      | r1_tarski(X0,X1) = iProver_top ),
% 7.85/1.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_3073,plain,
% 7.85/1.49      ( r1_tarski(k2_relat_1(sK2),sK1) = iProver_top ),
% 7.85/1.49      inference(superposition,[status(thm)],[c_3068,c_531]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(contradiction,plain,
% 7.85/1.49      ( $false ),
% 7.85/1.49      inference(minisat,[status(thm)],[c_29488,c_3845,c_3073]) ).
% 7.85/1.49  
% 7.85/1.49  
% 7.85/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.85/1.49  
% 7.85/1.49  ------                               Statistics
% 7.85/1.49  
% 7.85/1.49  ------ Selected
% 7.85/1.49  
% 7.85/1.49  total_time:                             0.883
% 7.85/1.49  
%------------------------------------------------------------------------------
