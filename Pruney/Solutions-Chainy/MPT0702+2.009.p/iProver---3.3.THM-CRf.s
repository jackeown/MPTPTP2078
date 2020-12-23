%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:52:08 EST 2020

% Result     : Theorem 4.00s
% Output     : CNFRefutation 4.00s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 127 expanded)
%              Number of clauses        :   40 (  42 expanded)
%              Number of leaves         :   11 (  26 expanded)
%              Depth                    :   13
%              Number of atoms          :  188 ( 453 expanded)
%              Number of equality atoms :   73 (  81 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_tarski(X0,k1_relat_1(X2))
          & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( v2_funct_1(X2)
            & r1_tarski(X0,k1_relat_1(X2))
            & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f22,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & v2_funct_1(X2)
        & r1_tarski(X0,k1_relat_1(X2))
        & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(sK0,sK1)
      & v2_funct_1(sK2)
      & r1_tarski(sK0,k1_relat_1(sK2))
      & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ~ r1_tarski(sK0,sK1)
    & v2_funct_1(sK2)
    & r1_tarski(sK0,k1_relat_1(sK2))
    & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f22])).

fof(f37,plain,(
    r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_subset_1(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f29,f31])).

fof(f35,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f34,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f38,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f36,plain,(
    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k6_subset_1(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f26,f31])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( k1_xboole_0 = k9_relat_1(X1,X0)
          & r1_tarski(X0,k1_relat_1(X1))
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k9_relat_1(X1,X0)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k9_relat_1(X1,X0)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k9_relat_1(X1,X0)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f39,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f25,f31])).

cnf(c_6,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_519,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_11,negated_conjecture,
    ( r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_514,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_521,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1097,plain,
    ( k2_xboole_0(sK0,k1_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_514,c_521])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_522,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2062,plain,
    ( r1_tarski(k1_relat_1(sK2),X0) != iProver_top
    | r1_tarski(sK0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1097,c_522])).

cnf(c_2811,plain,
    ( r1_tarski(sK0,k2_xboole_0(k1_relat_1(sK2),X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_519,c_2062])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
    | r1_tarski(k6_subset_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_520,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
    | r1_tarski(k6_subset_1(X0,X1),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2320,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
    | r1_tarski(k6_subset_1(X0,X2),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_520])).

cnf(c_12728,plain,
    ( r1_tarski(k6_subset_1(sK0,X0),k1_relat_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2811,c_2320])).

cnf(c_13,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_512,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_8,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k6_subset_1(X1,X2)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_517,plain,
    ( k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k6_subset_1(X1,X2))
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1002,plain,
    ( k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) = k9_relat_1(sK2,k6_subset_1(X0,X1))
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_512,c_517])).

cnf(c_14,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_15,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_10,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_19,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1417,plain,
    ( k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) = k9_relat_1(sK2,k6_subset_1(X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1002,c_15,c_19])).

cnf(c_12,negated_conjecture,
    ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_513,plain,
    ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | k6_subset_1(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_524,plain,
    ( k6_subset_1(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1208,plain,
    ( k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_513,c_524])).

cnf(c_1423,plain,
    ( k9_relat_1(sK2,k6_subset_1(sK0,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1417,c_1208])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k9_relat_1(X1,X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_518,plain,
    ( k9_relat_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1922,plain,
    ( k6_subset_1(sK0,sK1) = k1_xboole_0
    | r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1423,c_518])).

cnf(c_9,negated_conjecture,
    ( ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | k6_subset_1(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_11640,plain,
    ( r1_tarski(sK0,sK1)
    | k6_subset_1(sK0,sK1) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_11878,plain,
    ( r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1922,c_15,c_9,c_11640])).

cnf(c_16007,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_12728,c_11878])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 17:41:37 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 4.00/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.00/0.98  
% 4.00/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.00/0.98  
% 4.00/0.98  ------  iProver source info
% 4.00/0.98  
% 4.00/0.98  git: date: 2020-06-30 10:37:57 +0100
% 4.00/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.00/0.98  git: non_committed_changes: false
% 4.00/0.98  git: last_make_outside_of_git: false
% 4.00/0.98  
% 4.00/0.98  ------ 
% 4.00/0.98  ------ Parsing...
% 4.00/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.00/0.98  
% 4.00/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 4.00/0.98  
% 4.00/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.00/0.98  
% 4.00/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.00/0.98  ------ Proving...
% 4.00/0.98  ------ Problem Properties 
% 4.00/0.98  
% 4.00/0.98  
% 4.00/0.98  clauses                                 15
% 4.00/0.98  conjectures                             6
% 4.00/0.98  EPR                                     4
% 4.00/0.98  Horn                                    15
% 4.00/0.98  unary                                   8
% 4.00/0.98  binary                                  5
% 4.00/0.98  lits                                    26
% 4.00/0.98  lits eq                                 7
% 4.00/0.98  fd_pure                                 0
% 4.00/0.98  fd_pseudo                               0
% 4.00/0.98  fd_cond                                 1
% 4.00/0.98  fd_pseudo_cond                          0
% 4.00/0.98  AC symbols                              0
% 4.00/0.98  
% 4.00/0.98  ------ Input Options Time Limit: Unbounded
% 4.00/0.98  
% 4.00/0.98  
% 4.00/0.98  ------ 
% 4.00/0.98  Current options:
% 4.00/0.98  ------ 
% 4.00/0.98  
% 4.00/0.98  
% 4.00/0.98  
% 4.00/0.98  
% 4.00/0.98  ------ Proving...
% 4.00/0.98  
% 4.00/0.98  
% 4.00/0.98  % SZS status Theorem for theBenchmark.p
% 4.00/0.98  
% 4.00/0.98   Resolution empty clause
% 4.00/0.98  
% 4.00/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 4.00/0.98  
% 4.00/0.98  fof(f6,axiom,(
% 4.00/0.98    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 4.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.98  
% 4.00/0.98  fof(f30,plain,(
% 4.00/0.98    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 4.00/0.98    inference(cnf_transformation,[],[f6])).
% 4.00/0.98  
% 4.00/0.98  fof(f10,conjecture,(
% 4.00/0.98    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 4.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.98  
% 4.00/0.98  fof(f11,negated_conjecture,(
% 4.00/0.98    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 4.00/0.98    inference(negated_conjecture,[],[f10])).
% 4.00/0.98  
% 4.00/0.98  fof(f19,plain,(
% 4.00/0.98    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 4.00/0.98    inference(ennf_transformation,[],[f11])).
% 4.00/0.98  
% 4.00/0.98  fof(f20,plain,(
% 4.00/0.98    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 4.00/0.98    inference(flattening,[],[f19])).
% 4.00/0.98  
% 4.00/0.98  fof(f22,plain,(
% 4.00/0.98    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & v2_funct_1(sK2) & r1_tarski(sK0,k1_relat_1(sK2)) & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 4.00/0.98    introduced(choice_axiom,[])).
% 4.00/0.98  
% 4.00/0.98  fof(f23,plain,(
% 4.00/0.98    ~r1_tarski(sK0,sK1) & v2_funct_1(sK2) & r1_tarski(sK0,k1_relat_1(sK2)) & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 4.00/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f22])).
% 4.00/0.98  
% 4.00/0.98  fof(f37,plain,(
% 4.00/0.98    r1_tarski(sK0,k1_relat_1(sK2))),
% 4.00/0.98    inference(cnf_transformation,[],[f23])).
% 4.00/0.98  
% 4.00/0.98  fof(f4,axiom,(
% 4.00/0.98    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 4.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.98  
% 4.00/0.98  fof(f13,plain,(
% 4.00/0.98    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 4.00/0.98    inference(ennf_transformation,[],[f4])).
% 4.00/0.98  
% 4.00/0.98  fof(f28,plain,(
% 4.00/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 4.00/0.98    inference(cnf_transformation,[],[f13])).
% 4.00/0.98  
% 4.00/0.98  fof(f3,axiom,(
% 4.00/0.98    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 4.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.98  
% 4.00/0.98  fof(f12,plain,(
% 4.00/0.98    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 4.00/0.98    inference(ennf_transformation,[],[f3])).
% 4.00/0.98  
% 4.00/0.98  fof(f27,plain,(
% 4.00/0.98    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 4.00/0.98    inference(cnf_transformation,[],[f12])).
% 4.00/0.98  
% 4.00/0.98  fof(f1,axiom,(
% 4.00/0.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 4.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.98  
% 4.00/0.98  fof(f24,plain,(
% 4.00/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 4.00/0.98    inference(cnf_transformation,[],[f1])).
% 4.00/0.98  
% 4.00/0.98  fof(f5,axiom,(
% 4.00/0.98    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 4.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.98  
% 4.00/0.98  fof(f14,plain,(
% 4.00/0.98    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 4.00/0.98    inference(ennf_transformation,[],[f5])).
% 4.00/0.98  
% 4.00/0.98  fof(f29,plain,(
% 4.00/0.98    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 4.00/0.98    inference(cnf_transformation,[],[f14])).
% 4.00/0.98  
% 4.00/0.98  fof(f7,axiom,(
% 4.00/0.98    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 4.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.98  
% 4.00/0.98  fof(f31,plain,(
% 4.00/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 4.00/0.98    inference(cnf_transformation,[],[f7])).
% 4.00/0.98  
% 4.00/0.98  fof(f42,plain,(
% 4.00/0.98    ( ! [X2,X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 4.00/0.98    inference(definition_unfolding,[],[f29,f31])).
% 4.00/0.98  
% 4.00/0.98  fof(f35,plain,(
% 4.00/0.98    v1_funct_1(sK2)),
% 4.00/0.98    inference(cnf_transformation,[],[f23])).
% 4.00/0.98  
% 4.00/0.98  fof(f9,axiom,(
% 4.00/0.98    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1))))),
% 4.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.98  
% 4.00/0.98  fof(f17,plain,(
% 4.00/0.98    ! [X0,X1,X2] : ((k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1)) | ~v2_funct_1(X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 4.00/0.98    inference(ennf_transformation,[],[f9])).
% 4.00/0.98  
% 4.00/0.98  fof(f18,plain,(
% 4.00/0.98    ! [X0,X1,X2] : (k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 4.00/0.98    inference(flattening,[],[f17])).
% 4.00/0.98  
% 4.00/0.98  fof(f33,plain,(
% 4.00/0.98    ( ! [X2,X0,X1] : (k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 4.00/0.98    inference(cnf_transformation,[],[f18])).
% 4.00/0.98  
% 4.00/0.98  fof(f34,plain,(
% 4.00/0.98    v1_relat_1(sK2)),
% 4.00/0.98    inference(cnf_transformation,[],[f23])).
% 4.00/0.98  
% 4.00/0.98  fof(f38,plain,(
% 4.00/0.98    v2_funct_1(sK2)),
% 4.00/0.98    inference(cnf_transformation,[],[f23])).
% 4.00/0.98  
% 4.00/0.98  fof(f36,plain,(
% 4.00/0.98    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 4.00/0.98    inference(cnf_transformation,[],[f23])).
% 4.00/0.98  
% 4.00/0.98  fof(f2,axiom,(
% 4.00/0.98    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 4.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.98  
% 4.00/0.98  fof(f21,plain,(
% 4.00/0.98    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 4.00/0.98    inference(nnf_transformation,[],[f2])).
% 4.00/0.98  
% 4.00/0.98  fof(f26,plain,(
% 4.00/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 4.00/0.98    inference(cnf_transformation,[],[f21])).
% 4.00/0.98  
% 4.00/0.98  fof(f40,plain,(
% 4.00/0.98    ( ! [X0,X1] : (k1_xboole_0 = k6_subset_1(X0,X1) | ~r1_tarski(X0,X1)) )),
% 4.00/0.98    inference(definition_unfolding,[],[f26,f31])).
% 4.00/0.98  
% 4.00/0.98  fof(f8,axiom,(
% 4.00/0.98    ! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0))),
% 4.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.98  
% 4.00/0.98  fof(f15,plain,(
% 4.00/0.98    ! [X0,X1] : ((k1_xboole_0 != k9_relat_1(X1,X0) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_xboole_0 = X0) | ~v1_relat_1(X1))),
% 4.00/0.98    inference(ennf_transformation,[],[f8])).
% 4.00/0.98  
% 4.00/0.98  fof(f16,plain,(
% 4.00/0.98    ! [X0,X1] : (k1_xboole_0 != k9_relat_1(X1,X0) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1))),
% 4.00/0.98    inference(flattening,[],[f15])).
% 4.00/0.98  
% 4.00/0.98  fof(f32,plain,(
% 4.00/0.98    ( ! [X0,X1] : (k1_xboole_0 != k9_relat_1(X1,X0) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1)) )),
% 4.00/0.98    inference(cnf_transformation,[],[f16])).
% 4.00/0.98  
% 4.00/0.98  fof(f39,plain,(
% 4.00/0.98    ~r1_tarski(sK0,sK1)),
% 4.00/0.98    inference(cnf_transformation,[],[f23])).
% 4.00/0.98  
% 4.00/0.98  fof(f25,plain,(
% 4.00/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 4.00/0.98    inference(cnf_transformation,[],[f21])).
% 4.00/0.98  
% 4.00/0.98  fof(f41,plain,(
% 4.00/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k6_subset_1(X0,X1)) )),
% 4.00/0.98    inference(definition_unfolding,[],[f25,f31])).
% 4.00/0.98  
% 4.00/0.98  cnf(c_6,plain,
% 4.00/0.98      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 4.00/0.98      inference(cnf_transformation,[],[f30]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_519,plain,
% 4.00/0.98      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 4.00/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_11,negated_conjecture,
% 4.00/0.98      ( r1_tarski(sK0,k1_relat_1(sK2)) ),
% 4.00/0.98      inference(cnf_transformation,[],[f37]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_514,plain,
% 4.00/0.98      ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top ),
% 4.00/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_4,plain,
% 4.00/0.98      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 4.00/0.98      inference(cnf_transformation,[],[f28]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_521,plain,
% 4.00/0.98      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 4.00/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_1097,plain,
% 4.00/0.98      ( k2_xboole_0(sK0,k1_relat_1(sK2)) = k1_relat_1(sK2) ),
% 4.00/0.98      inference(superposition,[status(thm)],[c_514,c_521]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_3,plain,
% 4.00/0.98      ( r1_tarski(X0,X1) | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 4.00/0.98      inference(cnf_transformation,[],[f27]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_522,plain,
% 4.00/0.98      ( r1_tarski(X0,X1) = iProver_top
% 4.00/0.98      | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
% 4.00/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_2062,plain,
% 4.00/0.98      ( r1_tarski(k1_relat_1(sK2),X0) != iProver_top
% 4.00/0.98      | r1_tarski(sK0,X0) = iProver_top ),
% 4.00/0.98      inference(superposition,[status(thm)],[c_1097,c_522]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_2811,plain,
% 4.00/0.98      ( r1_tarski(sK0,k2_xboole_0(k1_relat_1(sK2),X0)) = iProver_top ),
% 4.00/0.98      inference(superposition,[status(thm)],[c_519,c_2062]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_0,plain,
% 4.00/0.98      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 4.00/0.98      inference(cnf_transformation,[],[f24]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_5,plain,
% 4.00/0.98      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2)) | r1_tarski(k6_subset_1(X0,X1),X2) ),
% 4.00/0.98      inference(cnf_transformation,[],[f42]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_520,plain,
% 4.00/0.98      ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
% 4.00/0.98      | r1_tarski(k6_subset_1(X0,X1),X2) = iProver_top ),
% 4.00/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_2320,plain,
% 4.00/0.98      ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
% 4.00/0.98      | r1_tarski(k6_subset_1(X0,X2),X1) = iProver_top ),
% 4.00/0.98      inference(superposition,[status(thm)],[c_0,c_520]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_12728,plain,
% 4.00/0.98      ( r1_tarski(k6_subset_1(sK0,X0),k1_relat_1(sK2)) = iProver_top ),
% 4.00/0.98      inference(superposition,[status(thm)],[c_2811,c_2320]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_13,negated_conjecture,
% 4.00/0.98      ( v1_funct_1(sK2) ),
% 4.00/0.98      inference(cnf_transformation,[],[f35]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_512,plain,
% 4.00/0.98      ( v1_funct_1(sK2) = iProver_top ),
% 4.00/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_8,plain,
% 4.00/0.98      ( ~ v1_funct_1(X0)
% 4.00/0.98      | ~ v2_funct_1(X0)
% 4.00/0.98      | ~ v1_relat_1(X0)
% 4.00/0.98      | k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k6_subset_1(X1,X2)) ),
% 4.00/0.98      inference(cnf_transformation,[],[f33]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_517,plain,
% 4.00/0.98      ( k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k6_subset_1(X1,X2))
% 4.00/0.98      | v1_funct_1(X0) != iProver_top
% 4.00/0.98      | v2_funct_1(X0) != iProver_top
% 4.00/0.98      | v1_relat_1(X0) != iProver_top ),
% 4.00/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_1002,plain,
% 4.00/0.98      ( k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) = k9_relat_1(sK2,k6_subset_1(X0,X1))
% 4.00/0.98      | v2_funct_1(sK2) != iProver_top
% 4.00/0.98      | v1_relat_1(sK2) != iProver_top ),
% 4.00/0.98      inference(superposition,[status(thm)],[c_512,c_517]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_14,negated_conjecture,
% 4.00/0.98      ( v1_relat_1(sK2) ),
% 4.00/0.98      inference(cnf_transformation,[],[f34]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_15,plain,
% 4.00/0.98      ( v1_relat_1(sK2) = iProver_top ),
% 4.00/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_10,negated_conjecture,
% 4.00/0.98      ( v2_funct_1(sK2) ),
% 4.00/0.98      inference(cnf_transformation,[],[f38]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_19,plain,
% 4.00/0.98      ( v2_funct_1(sK2) = iProver_top ),
% 4.00/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_1417,plain,
% 4.00/0.98      ( k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) = k9_relat_1(sK2,k6_subset_1(X0,X1)) ),
% 4.00/0.98      inference(global_propositional_subsumption,
% 4.00/0.98                [status(thm)],
% 4.00/0.98                [c_1002,c_15,c_19]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_12,negated_conjecture,
% 4.00/0.98      ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
% 4.00/0.98      inference(cnf_transformation,[],[f36]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_513,plain,
% 4.00/0.98      ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) = iProver_top ),
% 4.00/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_1,plain,
% 4.00/0.98      ( ~ r1_tarski(X0,X1) | k6_subset_1(X0,X1) = k1_xboole_0 ),
% 4.00/0.98      inference(cnf_transformation,[],[f40]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_524,plain,
% 4.00/0.98      ( k6_subset_1(X0,X1) = k1_xboole_0 | r1_tarski(X0,X1) != iProver_top ),
% 4.00/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_1208,plain,
% 4.00/0.98      ( k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) = k1_xboole_0 ),
% 4.00/0.98      inference(superposition,[status(thm)],[c_513,c_524]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_1423,plain,
% 4.00/0.98      ( k9_relat_1(sK2,k6_subset_1(sK0,sK1)) = k1_xboole_0 ),
% 4.00/0.98      inference(superposition,[status(thm)],[c_1417,c_1208]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_7,plain,
% 4.00/0.98      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 4.00/0.98      | ~ v1_relat_1(X1)
% 4.00/0.98      | k9_relat_1(X1,X0) != k1_xboole_0
% 4.00/0.98      | k1_xboole_0 = X0 ),
% 4.00/0.98      inference(cnf_transformation,[],[f32]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_518,plain,
% 4.00/0.98      ( k9_relat_1(X0,X1) != k1_xboole_0
% 4.00/0.98      | k1_xboole_0 = X1
% 4.00/0.98      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 4.00/0.98      | v1_relat_1(X0) != iProver_top ),
% 4.00/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_1922,plain,
% 4.00/0.98      ( k6_subset_1(sK0,sK1) = k1_xboole_0
% 4.00/0.98      | r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2)) != iProver_top
% 4.00/0.98      | v1_relat_1(sK2) != iProver_top ),
% 4.00/0.98      inference(superposition,[status(thm)],[c_1423,c_518]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_9,negated_conjecture,
% 4.00/0.98      ( ~ r1_tarski(sK0,sK1) ),
% 4.00/0.98      inference(cnf_transformation,[],[f39]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_2,plain,
% 4.00/0.98      ( r1_tarski(X0,X1) | k6_subset_1(X0,X1) != k1_xboole_0 ),
% 4.00/0.98      inference(cnf_transformation,[],[f41]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_11640,plain,
% 4.00/0.98      ( r1_tarski(sK0,sK1) | k6_subset_1(sK0,sK1) != k1_xboole_0 ),
% 4.00/0.98      inference(instantiation,[status(thm)],[c_2]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_11878,plain,
% 4.00/0.98      ( r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2)) != iProver_top ),
% 4.00/0.98      inference(global_propositional_subsumption,
% 4.00/0.98                [status(thm)],
% 4.00/0.98                [c_1922,c_15,c_9,c_11640]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_16007,plain,
% 4.00/0.98      ( $false ),
% 4.00/0.98      inference(superposition,[status(thm)],[c_12728,c_11878]) ).
% 4.00/0.98  
% 4.00/0.98  
% 4.00/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 4.00/0.98  
% 4.00/0.98  ------                               Statistics
% 4.00/0.98  
% 4.00/0.98  ------ Selected
% 4.00/0.98  
% 4.00/0.98  total_time:                             0.44
% 4.00/0.98  
%------------------------------------------------------------------------------
