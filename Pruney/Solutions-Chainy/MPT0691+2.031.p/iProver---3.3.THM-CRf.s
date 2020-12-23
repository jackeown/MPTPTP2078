%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:51:44 EST 2020

% Result     : Theorem 6.96s
% Output     : CNFRefutation 6.96s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 308 expanded)
%              Number of clauses        :   50 ( 122 expanded)
%              Number of leaves         :   11 (  58 expanded)
%              Depth                    :   18
%              Number of atoms          :  141 ( 667 expanded)
%              Number of equality atoms :   70 ( 180 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k1_relat_1(X1))
         => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f28,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f29,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f32,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f32])).

fof(f49,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f47,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f50,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f33])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f51,plain,(
    ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_17,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_574,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_581,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_578,plain,
    ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1361,plain,
    ( k10_relat_1(k7_relat_1(X0,X1),k2_relat_1(k7_relat_1(X0,X1))) = k1_relat_1(k7_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_581,c_578])).

cnf(c_5564,plain,
    ( k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(k7_relat_1(sK1,X0))) = k1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_574,c_1361])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_580,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1467,plain,
    ( k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0) ),
    inference(superposition,[status(thm)],[c_574,c_580])).

cnf(c_5565,plain,
    ( k10_relat_1(k7_relat_1(sK1,X0),k9_relat_1(sK1,X0)) = k1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_5564,c_1467])).

cnf(c_14,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(k7_relat_1(X0,X1),X2) = k3_xboole_0(X1,k10_relat_1(X0,X2)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_577,plain,
    ( k10_relat_1(k7_relat_1(X0,X1),X2) = k3_xboole_0(X1,k10_relat_1(X0,X2))
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1258,plain,
    ( k10_relat_1(k7_relat_1(sK1,X0),X1) = k3_xboole_0(X0,k10_relat_1(sK1,X1)) ),
    inference(superposition,[status(thm)],[c_574,c_577])).

cnf(c_6040,plain,
    ( k3_xboole_0(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0))) = k1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_5565,c_1258])).

cnf(c_16,negated_conjecture,
    ( r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_575,plain,
    ( r1_tarski(sK0,k1_relat_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k3_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_587,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k3_xboole_0(X0,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_583,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2091,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,X1)
    | r1_tarski(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_587,c_583])).

cnf(c_17912,plain,
    ( k3_xboole_0(k3_xboole_0(sK0,X0),k1_relat_1(sK1)) = k3_xboole_0(sK0,X0) ),
    inference(superposition,[status(thm)],[c_575,c_2091])).

cnf(c_18719,plain,
    ( k3_xboole_0(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) = k3_xboole_0(k1_relat_1(k7_relat_1(sK1,sK0)),k1_relat_1(sK1)) ),
    inference(superposition,[status(thm)],[c_6040,c_17912])).

cnf(c_1266,plain,
    ( k3_xboole_0(sK0,k1_relat_1(sK1)) = sK0 ),
    inference(superposition,[status(thm)],[c_575,c_583])).

cnf(c_1362,plain,
    ( k10_relat_1(sK1,k2_relat_1(sK1)) = k1_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_574,c_578])).

cnf(c_12,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_579,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1717,plain,
    ( r1_tarski(k3_xboole_0(X0,k10_relat_1(sK1,X1)),k1_relat_1(k7_relat_1(sK1,X0))) = iProver_top
    | v1_relat_1(k7_relat_1(sK1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1258,c_579])).

cnf(c_1724,plain,
    ( r1_tarski(k3_xboole_0(X0,k1_relat_1(sK1)),k1_relat_1(k7_relat_1(sK1,X0))) = iProver_top
    | v1_relat_1(k7_relat_1(sK1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1362,c_1717])).

cnf(c_1811,plain,
    ( r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0))) = iProver_top
    | v1_relat_1(k7_relat_1(sK1,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1266,c_1724])).

cnf(c_1821,plain,
    ( k3_xboole_0(sK0,k1_relat_1(k7_relat_1(sK1,sK0))) = sK0
    | v1_relat_1(k7_relat_1(sK1,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1811,c_583])).

cnf(c_1939,plain,
    ( k3_xboole_0(sK0,k1_relat_1(k7_relat_1(sK1,sK0))) = sK0
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_581,c_1821])).

cnf(c_18,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_15432,plain,
    ( k3_xboole_0(sK0,k1_relat_1(k7_relat_1(sK1,sK0))) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1939,c_18])).

cnf(c_6,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_585,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1265,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_585,c_583])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_4515,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1265,c_0])).

cnf(c_6769,plain,
    ( k3_xboole_0(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0))) = k3_xboole_0(X0,k1_relat_1(k7_relat_1(sK1,X0))) ),
    inference(superposition,[status(thm)],[c_6040,c_4515])).

cnf(c_6791,plain,
    ( k3_xboole_0(X0,k1_relat_1(k7_relat_1(sK1,X0))) = k1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(demodulation,[status(thm)],[c_6769,c_6040])).

cnf(c_15443,plain,
    ( k1_relat_1(k7_relat_1(sK1,sK0)) = sK0 ),
    inference(superposition,[status(thm)],[c_15432,c_6791])).

cnf(c_18767,plain,
    ( k3_xboole_0(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_18719,c_1266,c_15443])).

cnf(c_975,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_585])).

cnf(c_18968,plain,
    ( r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_18767,c_975])).

cnf(c_15,negated_conjecture,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_20,plain,
    ( r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_18968,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:33:03 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 6.96/1.51  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.96/1.51  
% 6.96/1.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.96/1.51  
% 6.96/1.51  ------  iProver source info
% 6.96/1.51  
% 6.96/1.51  git: date: 2020-06-30 10:37:57 +0100
% 6.96/1.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.96/1.51  git: non_committed_changes: false
% 6.96/1.51  git: last_make_outside_of_git: false
% 6.96/1.51  
% 6.96/1.51  ------ 
% 6.96/1.51  
% 6.96/1.51  ------ Input Options
% 6.96/1.51  
% 6.96/1.51  --out_options                           all
% 6.96/1.51  --tptp_safe_out                         true
% 6.96/1.51  --problem_path                          ""
% 6.96/1.51  --include_path                          ""
% 6.96/1.51  --clausifier                            res/vclausify_rel
% 6.96/1.51  --clausifier_options                    ""
% 6.96/1.51  --stdin                                 false
% 6.96/1.51  --stats_out                             all
% 6.96/1.51  
% 6.96/1.51  ------ General Options
% 6.96/1.51  
% 6.96/1.51  --fof                                   false
% 6.96/1.51  --time_out_real                         305.
% 6.96/1.51  --time_out_virtual                      -1.
% 6.96/1.51  --symbol_type_check                     false
% 6.96/1.51  --clausify_out                          false
% 6.96/1.51  --sig_cnt_out                           false
% 6.96/1.51  --trig_cnt_out                          false
% 6.96/1.51  --trig_cnt_out_tolerance                1.
% 6.96/1.51  --trig_cnt_out_sk_spl                   false
% 6.96/1.51  --abstr_cl_out                          false
% 6.96/1.51  
% 6.96/1.51  ------ Global Options
% 6.96/1.51  
% 6.96/1.51  --schedule                              default
% 6.96/1.51  --add_important_lit                     false
% 6.96/1.51  --prop_solver_per_cl                    1000
% 6.96/1.51  --min_unsat_core                        false
% 6.96/1.51  --soft_assumptions                      false
% 6.96/1.51  --soft_lemma_size                       3
% 6.96/1.51  --prop_impl_unit_size                   0
% 6.96/1.51  --prop_impl_unit                        []
% 6.96/1.51  --share_sel_clauses                     true
% 6.96/1.51  --reset_solvers                         false
% 6.96/1.51  --bc_imp_inh                            [conj_cone]
% 6.96/1.51  --conj_cone_tolerance                   3.
% 6.96/1.51  --extra_neg_conj                        none
% 6.96/1.51  --large_theory_mode                     true
% 6.96/1.51  --prolific_symb_bound                   200
% 6.96/1.51  --lt_threshold                          2000
% 6.96/1.51  --clause_weak_htbl                      true
% 6.96/1.51  --gc_record_bc_elim                     false
% 6.96/1.51  
% 6.96/1.51  ------ Preprocessing Options
% 6.96/1.51  
% 6.96/1.51  --preprocessing_flag                    true
% 6.96/1.51  --time_out_prep_mult                    0.1
% 6.96/1.51  --splitting_mode                        input
% 6.96/1.51  --splitting_grd                         true
% 6.96/1.51  --splitting_cvd                         false
% 6.96/1.51  --splitting_cvd_svl                     false
% 6.96/1.51  --splitting_nvd                         32
% 6.96/1.51  --sub_typing                            true
% 6.96/1.51  --prep_gs_sim                           true
% 6.96/1.51  --prep_unflatten                        true
% 6.96/1.51  --prep_res_sim                          true
% 6.96/1.51  --prep_upred                            true
% 6.96/1.51  --prep_sem_filter                       exhaustive
% 6.96/1.51  --prep_sem_filter_out                   false
% 6.96/1.51  --pred_elim                             true
% 6.96/1.51  --res_sim_input                         true
% 6.96/1.51  --eq_ax_congr_red                       true
% 6.96/1.51  --pure_diseq_elim                       true
% 6.96/1.51  --brand_transform                       false
% 6.96/1.51  --non_eq_to_eq                          false
% 6.96/1.51  --prep_def_merge                        true
% 6.96/1.51  --prep_def_merge_prop_impl              false
% 6.96/1.51  --prep_def_merge_mbd                    true
% 6.96/1.51  --prep_def_merge_tr_red                 false
% 6.96/1.51  --prep_def_merge_tr_cl                  false
% 6.96/1.51  --smt_preprocessing                     true
% 6.96/1.51  --smt_ac_axioms                         fast
% 6.96/1.51  --preprocessed_out                      false
% 6.96/1.51  --preprocessed_stats                    false
% 6.96/1.51  
% 6.96/1.51  ------ Abstraction refinement Options
% 6.96/1.51  
% 6.96/1.51  --abstr_ref                             []
% 6.96/1.51  --abstr_ref_prep                        false
% 6.96/1.51  --abstr_ref_until_sat                   false
% 6.96/1.51  --abstr_ref_sig_restrict                funpre
% 6.96/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 6.96/1.51  --abstr_ref_under                       []
% 6.96/1.51  
% 6.96/1.51  ------ SAT Options
% 6.96/1.51  
% 6.96/1.51  --sat_mode                              false
% 6.96/1.51  --sat_fm_restart_options                ""
% 6.96/1.51  --sat_gr_def                            false
% 6.96/1.51  --sat_epr_types                         true
% 6.96/1.51  --sat_non_cyclic_types                  false
% 6.96/1.51  --sat_finite_models                     false
% 6.96/1.51  --sat_fm_lemmas                         false
% 6.96/1.51  --sat_fm_prep                           false
% 6.96/1.51  --sat_fm_uc_incr                        true
% 6.96/1.51  --sat_out_model                         small
% 6.96/1.51  --sat_out_clauses                       false
% 6.96/1.51  
% 6.96/1.51  ------ QBF Options
% 6.96/1.51  
% 6.96/1.51  --qbf_mode                              false
% 6.96/1.51  --qbf_elim_univ                         false
% 6.96/1.51  --qbf_dom_inst                          none
% 6.96/1.51  --qbf_dom_pre_inst                      false
% 6.96/1.51  --qbf_sk_in                             false
% 6.96/1.51  --qbf_pred_elim                         true
% 6.96/1.51  --qbf_split                             512
% 6.96/1.51  
% 6.96/1.51  ------ BMC1 Options
% 6.96/1.51  
% 6.96/1.51  --bmc1_incremental                      false
% 6.96/1.51  --bmc1_axioms                           reachable_all
% 6.96/1.51  --bmc1_min_bound                        0
% 6.96/1.51  --bmc1_max_bound                        -1
% 6.96/1.51  --bmc1_max_bound_default                -1
% 6.96/1.51  --bmc1_symbol_reachability              true
% 6.96/1.51  --bmc1_property_lemmas                  false
% 6.96/1.51  --bmc1_k_induction                      false
% 6.96/1.51  --bmc1_non_equiv_states                 false
% 6.96/1.51  --bmc1_deadlock                         false
% 6.96/1.51  --bmc1_ucm                              false
% 6.96/1.51  --bmc1_add_unsat_core                   none
% 6.96/1.51  --bmc1_unsat_core_children              false
% 6.96/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 6.96/1.51  --bmc1_out_stat                         full
% 6.96/1.51  --bmc1_ground_init                      false
% 6.96/1.51  --bmc1_pre_inst_next_state              false
% 6.96/1.51  --bmc1_pre_inst_state                   false
% 6.96/1.51  --bmc1_pre_inst_reach_state             false
% 6.96/1.51  --bmc1_out_unsat_core                   false
% 6.96/1.51  --bmc1_aig_witness_out                  false
% 6.96/1.51  --bmc1_verbose                          false
% 6.96/1.51  --bmc1_dump_clauses_tptp                false
% 6.96/1.51  --bmc1_dump_unsat_core_tptp             false
% 6.96/1.51  --bmc1_dump_file                        -
% 6.96/1.51  --bmc1_ucm_expand_uc_limit              128
% 6.96/1.51  --bmc1_ucm_n_expand_iterations          6
% 6.96/1.51  --bmc1_ucm_extend_mode                  1
% 6.96/1.51  --bmc1_ucm_init_mode                    2
% 6.96/1.51  --bmc1_ucm_cone_mode                    none
% 6.96/1.51  --bmc1_ucm_reduced_relation_type        0
% 6.96/1.51  --bmc1_ucm_relax_model                  4
% 6.96/1.51  --bmc1_ucm_full_tr_after_sat            true
% 6.96/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 6.96/1.51  --bmc1_ucm_layered_model                none
% 6.96/1.51  --bmc1_ucm_max_lemma_size               10
% 6.96/1.51  
% 6.96/1.51  ------ AIG Options
% 6.96/1.51  
% 6.96/1.51  --aig_mode                              false
% 6.96/1.51  
% 6.96/1.51  ------ Instantiation Options
% 6.96/1.51  
% 6.96/1.51  --instantiation_flag                    true
% 6.96/1.51  --inst_sos_flag                         true
% 6.96/1.51  --inst_sos_phase                        true
% 6.96/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.96/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.96/1.51  --inst_lit_sel_side                     num_symb
% 6.96/1.51  --inst_solver_per_active                1400
% 6.96/1.51  --inst_solver_calls_frac                1.
% 6.96/1.51  --inst_passive_queue_type               priority_queues
% 6.96/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.96/1.51  --inst_passive_queues_freq              [25;2]
% 6.96/1.51  --inst_dismatching                      true
% 6.96/1.51  --inst_eager_unprocessed_to_passive     true
% 6.96/1.51  --inst_prop_sim_given                   true
% 6.96/1.51  --inst_prop_sim_new                     false
% 6.96/1.51  --inst_subs_new                         false
% 6.96/1.51  --inst_eq_res_simp                      false
% 6.96/1.51  --inst_subs_given                       false
% 6.96/1.51  --inst_orphan_elimination               true
% 6.96/1.51  --inst_learning_loop_flag               true
% 6.96/1.51  --inst_learning_start                   3000
% 6.96/1.51  --inst_learning_factor                  2
% 6.96/1.51  --inst_start_prop_sim_after_learn       3
% 6.96/1.51  --inst_sel_renew                        solver
% 6.96/1.51  --inst_lit_activity_flag                true
% 6.96/1.51  --inst_restr_to_given                   false
% 6.96/1.51  --inst_activity_threshold               500
% 6.96/1.51  --inst_out_proof                        true
% 6.96/1.51  
% 6.96/1.51  ------ Resolution Options
% 6.96/1.51  
% 6.96/1.51  --resolution_flag                       true
% 6.96/1.51  --res_lit_sel                           adaptive
% 6.96/1.51  --res_lit_sel_side                      none
% 6.96/1.51  --res_ordering                          kbo
% 6.96/1.51  --res_to_prop_solver                    active
% 6.96/1.51  --res_prop_simpl_new                    false
% 6.96/1.51  --res_prop_simpl_given                  true
% 6.96/1.51  --res_passive_queue_type                priority_queues
% 6.96/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.96/1.51  --res_passive_queues_freq               [15;5]
% 6.96/1.51  --res_forward_subs                      full
% 6.96/1.51  --res_backward_subs                     full
% 6.96/1.51  --res_forward_subs_resolution           true
% 6.96/1.51  --res_backward_subs_resolution          true
% 6.96/1.51  --res_orphan_elimination                true
% 6.96/1.51  --res_time_limit                        2.
% 6.96/1.51  --res_out_proof                         true
% 6.96/1.51  
% 6.96/1.51  ------ Superposition Options
% 6.96/1.51  
% 6.96/1.51  --superposition_flag                    true
% 6.96/1.51  --sup_passive_queue_type                priority_queues
% 6.96/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.96/1.51  --sup_passive_queues_freq               [8;1;4]
% 6.96/1.51  --demod_completeness_check              fast
% 6.96/1.51  --demod_use_ground                      true
% 6.96/1.51  --sup_to_prop_solver                    passive
% 6.96/1.51  --sup_prop_simpl_new                    true
% 6.96/1.51  --sup_prop_simpl_given                  true
% 6.96/1.51  --sup_fun_splitting                     true
% 6.96/1.51  --sup_smt_interval                      50000
% 6.96/1.51  
% 6.96/1.51  ------ Superposition Simplification Setup
% 6.96/1.51  
% 6.96/1.51  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 6.96/1.51  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 6.96/1.51  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 6.96/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 6.96/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 6.96/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 6.96/1.51  --sup_full_bw                           [BwDemod;BwSubsumption]
% 6.96/1.51  --sup_immed_triv                        [TrivRules]
% 6.96/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.96/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 6.96/1.51  --sup_immed_bw_main                     []
% 6.96/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 6.96/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 6.96/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 6.96/1.51  --sup_input_bw                          []
% 6.96/1.51  
% 6.96/1.51  ------ Combination Options
% 6.96/1.51  
% 6.96/1.51  --comb_res_mult                         3
% 6.96/1.51  --comb_sup_mult                         2
% 6.96/1.51  --comb_inst_mult                        10
% 6.96/1.51  
% 6.96/1.51  ------ Debug Options
% 6.96/1.51  
% 6.96/1.51  --dbg_backtrace                         false
% 6.96/1.51  --dbg_dump_prop_clauses                 false
% 6.96/1.51  --dbg_dump_prop_clauses_file            -
% 6.96/1.51  --dbg_out_stat                          false
% 6.96/1.51  ------ Parsing...
% 6.96/1.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.96/1.51  
% 6.96/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 6.96/1.51  
% 6.96/1.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.96/1.51  
% 6.96/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.96/1.51  ------ Proving...
% 6.96/1.51  ------ Problem Properties 
% 6.96/1.51  
% 6.96/1.51  
% 6.96/1.51  clauses                                 17
% 6.96/1.51  conjectures                             3
% 6.96/1.51  EPR                                     4
% 6.96/1.51  Horn                                    17
% 6.96/1.51  unary                                   6
% 6.96/1.51  binary                                  8
% 6.96/1.51  lits                                    31
% 6.96/1.51  lits eq                                 6
% 6.96/1.51  fd_pure                                 0
% 6.96/1.51  fd_pseudo                               0
% 6.96/1.51  fd_cond                                 0
% 6.96/1.51  fd_pseudo_cond                          1
% 6.96/1.51  AC symbols                              0
% 6.96/1.51  
% 6.96/1.51  ------ Schedule dynamic 5 is on 
% 6.96/1.51  
% 6.96/1.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 6.96/1.51  
% 6.96/1.51  
% 6.96/1.51  ------ 
% 6.96/1.51  Current options:
% 6.96/1.51  ------ 
% 6.96/1.51  
% 6.96/1.51  ------ Input Options
% 6.96/1.51  
% 6.96/1.51  --out_options                           all
% 6.96/1.51  --tptp_safe_out                         true
% 6.96/1.51  --problem_path                          ""
% 6.96/1.51  --include_path                          ""
% 6.96/1.51  --clausifier                            res/vclausify_rel
% 6.96/1.51  --clausifier_options                    ""
% 6.96/1.51  --stdin                                 false
% 6.96/1.51  --stats_out                             all
% 6.96/1.51  
% 6.96/1.51  ------ General Options
% 6.96/1.51  
% 6.96/1.51  --fof                                   false
% 6.96/1.51  --time_out_real                         305.
% 6.96/1.51  --time_out_virtual                      -1.
% 6.96/1.51  --symbol_type_check                     false
% 6.96/1.51  --clausify_out                          false
% 6.96/1.51  --sig_cnt_out                           false
% 6.96/1.51  --trig_cnt_out                          false
% 6.96/1.51  --trig_cnt_out_tolerance                1.
% 6.96/1.51  --trig_cnt_out_sk_spl                   false
% 6.96/1.51  --abstr_cl_out                          false
% 6.96/1.51  
% 6.96/1.51  ------ Global Options
% 6.96/1.51  
% 6.96/1.51  --schedule                              default
% 6.96/1.51  --add_important_lit                     false
% 6.96/1.51  --prop_solver_per_cl                    1000
% 6.96/1.51  --min_unsat_core                        false
% 6.96/1.51  --soft_assumptions                      false
% 6.96/1.51  --soft_lemma_size                       3
% 6.96/1.51  --prop_impl_unit_size                   0
% 6.96/1.51  --prop_impl_unit                        []
% 6.96/1.51  --share_sel_clauses                     true
% 6.96/1.51  --reset_solvers                         false
% 6.96/1.51  --bc_imp_inh                            [conj_cone]
% 6.96/1.51  --conj_cone_tolerance                   3.
% 6.96/1.51  --extra_neg_conj                        none
% 6.96/1.51  --large_theory_mode                     true
% 6.96/1.51  --prolific_symb_bound                   200
% 6.96/1.51  --lt_threshold                          2000
% 6.96/1.51  --clause_weak_htbl                      true
% 6.96/1.51  --gc_record_bc_elim                     false
% 6.96/1.51  
% 6.96/1.51  ------ Preprocessing Options
% 6.96/1.51  
% 6.96/1.51  --preprocessing_flag                    true
% 6.96/1.51  --time_out_prep_mult                    0.1
% 6.96/1.51  --splitting_mode                        input
% 6.96/1.51  --splitting_grd                         true
% 6.96/1.51  --splitting_cvd                         false
% 6.96/1.51  --splitting_cvd_svl                     false
% 6.96/1.51  --splitting_nvd                         32
% 6.96/1.51  --sub_typing                            true
% 6.96/1.51  --prep_gs_sim                           true
% 6.96/1.51  --prep_unflatten                        true
% 6.96/1.51  --prep_res_sim                          true
% 6.96/1.51  --prep_upred                            true
% 6.96/1.51  --prep_sem_filter                       exhaustive
% 6.96/1.51  --prep_sem_filter_out                   false
% 6.96/1.51  --pred_elim                             true
% 6.96/1.51  --res_sim_input                         true
% 6.96/1.51  --eq_ax_congr_red                       true
% 6.96/1.51  --pure_diseq_elim                       true
% 6.96/1.51  --brand_transform                       false
% 6.96/1.51  --non_eq_to_eq                          false
% 6.96/1.51  --prep_def_merge                        true
% 6.96/1.51  --prep_def_merge_prop_impl              false
% 6.96/1.51  --prep_def_merge_mbd                    true
% 6.96/1.51  --prep_def_merge_tr_red                 false
% 6.96/1.51  --prep_def_merge_tr_cl                  false
% 6.96/1.51  --smt_preprocessing                     true
% 6.96/1.51  --smt_ac_axioms                         fast
% 6.96/1.51  --preprocessed_out                      false
% 6.96/1.51  --preprocessed_stats                    false
% 6.96/1.51  
% 6.96/1.51  ------ Abstraction refinement Options
% 6.96/1.51  
% 6.96/1.51  --abstr_ref                             []
% 6.96/1.51  --abstr_ref_prep                        false
% 6.96/1.51  --abstr_ref_until_sat                   false
% 6.96/1.51  --abstr_ref_sig_restrict                funpre
% 6.96/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 6.96/1.51  --abstr_ref_under                       []
% 6.96/1.51  
% 6.96/1.51  ------ SAT Options
% 6.96/1.51  
% 6.96/1.51  --sat_mode                              false
% 6.96/1.51  --sat_fm_restart_options                ""
% 6.96/1.51  --sat_gr_def                            false
% 6.96/1.51  --sat_epr_types                         true
% 6.96/1.51  --sat_non_cyclic_types                  false
% 6.96/1.51  --sat_finite_models                     false
% 6.96/1.51  --sat_fm_lemmas                         false
% 6.96/1.51  --sat_fm_prep                           false
% 6.96/1.51  --sat_fm_uc_incr                        true
% 6.96/1.51  --sat_out_model                         small
% 6.96/1.51  --sat_out_clauses                       false
% 6.96/1.51  
% 6.96/1.51  ------ QBF Options
% 6.96/1.51  
% 6.96/1.51  --qbf_mode                              false
% 6.96/1.51  --qbf_elim_univ                         false
% 6.96/1.51  --qbf_dom_inst                          none
% 6.96/1.51  --qbf_dom_pre_inst                      false
% 6.96/1.51  --qbf_sk_in                             false
% 6.96/1.51  --qbf_pred_elim                         true
% 6.96/1.51  --qbf_split                             512
% 6.96/1.51  
% 6.96/1.51  ------ BMC1 Options
% 6.96/1.51  
% 6.96/1.51  --bmc1_incremental                      false
% 6.96/1.51  --bmc1_axioms                           reachable_all
% 6.96/1.51  --bmc1_min_bound                        0
% 6.96/1.51  --bmc1_max_bound                        -1
% 6.96/1.51  --bmc1_max_bound_default                -1
% 6.96/1.51  --bmc1_symbol_reachability              true
% 6.96/1.51  --bmc1_property_lemmas                  false
% 6.96/1.51  --bmc1_k_induction                      false
% 6.96/1.51  --bmc1_non_equiv_states                 false
% 6.96/1.51  --bmc1_deadlock                         false
% 6.96/1.51  --bmc1_ucm                              false
% 6.96/1.51  --bmc1_add_unsat_core                   none
% 6.96/1.51  --bmc1_unsat_core_children              false
% 6.96/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 6.96/1.51  --bmc1_out_stat                         full
% 6.96/1.51  --bmc1_ground_init                      false
% 6.96/1.51  --bmc1_pre_inst_next_state              false
% 6.96/1.51  --bmc1_pre_inst_state                   false
% 6.96/1.51  --bmc1_pre_inst_reach_state             false
% 6.96/1.51  --bmc1_out_unsat_core                   false
% 6.96/1.51  --bmc1_aig_witness_out                  false
% 6.96/1.51  --bmc1_verbose                          false
% 6.96/1.51  --bmc1_dump_clauses_tptp                false
% 6.96/1.51  --bmc1_dump_unsat_core_tptp             false
% 6.96/1.51  --bmc1_dump_file                        -
% 6.96/1.51  --bmc1_ucm_expand_uc_limit              128
% 6.96/1.51  --bmc1_ucm_n_expand_iterations          6
% 6.96/1.51  --bmc1_ucm_extend_mode                  1
% 6.96/1.51  --bmc1_ucm_init_mode                    2
% 6.96/1.51  --bmc1_ucm_cone_mode                    none
% 6.96/1.51  --bmc1_ucm_reduced_relation_type        0
% 6.96/1.51  --bmc1_ucm_relax_model                  4
% 6.96/1.51  --bmc1_ucm_full_tr_after_sat            true
% 6.96/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 6.96/1.51  --bmc1_ucm_layered_model                none
% 6.96/1.51  --bmc1_ucm_max_lemma_size               10
% 6.96/1.51  
% 6.96/1.51  ------ AIG Options
% 6.96/1.51  
% 6.96/1.51  --aig_mode                              false
% 6.96/1.51  
% 6.96/1.51  ------ Instantiation Options
% 6.96/1.51  
% 6.96/1.51  --instantiation_flag                    true
% 6.96/1.51  --inst_sos_flag                         true
% 6.96/1.51  --inst_sos_phase                        true
% 6.96/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.96/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.96/1.51  --inst_lit_sel_side                     none
% 6.96/1.51  --inst_solver_per_active                1400
% 6.96/1.51  --inst_solver_calls_frac                1.
% 6.96/1.51  --inst_passive_queue_type               priority_queues
% 6.96/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.96/1.51  --inst_passive_queues_freq              [25;2]
% 6.96/1.51  --inst_dismatching                      true
% 6.96/1.51  --inst_eager_unprocessed_to_passive     true
% 6.96/1.51  --inst_prop_sim_given                   true
% 6.96/1.51  --inst_prop_sim_new                     false
% 6.96/1.51  --inst_subs_new                         false
% 6.96/1.51  --inst_eq_res_simp                      false
% 6.96/1.51  --inst_subs_given                       false
% 6.96/1.51  --inst_orphan_elimination               true
% 6.96/1.51  --inst_learning_loop_flag               true
% 6.96/1.51  --inst_learning_start                   3000
% 6.96/1.51  --inst_learning_factor                  2
% 6.96/1.51  --inst_start_prop_sim_after_learn       3
% 6.96/1.51  --inst_sel_renew                        solver
% 6.96/1.51  --inst_lit_activity_flag                true
% 6.96/1.51  --inst_restr_to_given                   false
% 6.96/1.51  --inst_activity_threshold               500
% 6.96/1.51  --inst_out_proof                        true
% 6.96/1.51  
% 6.96/1.51  ------ Resolution Options
% 6.96/1.51  
% 6.96/1.51  --resolution_flag                       false
% 6.96/1.51  --res_lit_sel                           adaptive
% 6.96/1.51  --res_lit_sel_side                      none
% 6.96/1.51  --res_ordering                          kbo
% 6.96/1.51  --res_to_prop_solver                    active
% 6.96/1.51  --res_prop_simpl_new                    false
% 6.96/1.51  --res_prop_simpl_given                  true
% 6.96/1.51  --res_passive_queue_type                priority_queues
% 6.96/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.96/1.51  --res_passive_queues_freq               [15;5]
% 6.96/1.51  --res_forward_subs                      full
% 6.96/1.51  --res_backward_subs                     full
% 6.96/1.51  --res_forward_subs_resolution           true
% 6.96/1.51  --res_backward_subs_resolution          true
% 6.96/1.51  --res_orphan_elimination                true
% 6.96/1.51  --res_time_limit                        2.
% 6.96/1.51  --res_out_proof                         true
% 6.96/1.51  
% 6.96/1.51  ------ Superposition Options
% 6.96/1.51  
% 6.96/1.51  --superposition_flag                    true
% 6.96/1.51  --sup_passive_queue_type                priority_queues
% 6.96/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.96/1.51  --sup_passive_queues_freq               [8;1;4]
% 6.96/1.51  --demod_completeness_check              fast
% 6.96/1.51  --demod_use_ground                      true
% 6.96/1.51  --sup_to_prop_solver                    passive
% 6.96/1.51  --sup_prop_simpl_new                    true
% 6.96/1.51  --sup_prop_simpl_given                  true
% 6.96/1.51  --sup_fun_splitting                     true
% 6.96/1.51  --sup_smt_interval                      50000
% 6.96/1.51  
% 6.96/1.51  ------ Superposition Simplification Setup
% 6.96/1.51  
% 6.96/1.51  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 6.96/1.51  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 6.96/1.51  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 6.96/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 6.96/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 6.96/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 6.96/1.51  --sup_full_bw                           [BwDemod;BwSubsumption]
% 6.96/1.51  --sup_immed_triv                        [TrivRules]
% 6.96/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.96/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 6.96/1.51  --sup_immed_bw_main                     []
% 6.96/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 6.96/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 6.96/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 6.96/1.51  --sup_input_bw                          []
% 6.96/1.51  
% 6.96/1.51  ------ Combination Options
% 6.96/1.51  
% 6.96/1.51  --comb_res_mult                         3
% 6.96/1.51  --comb_sup_mult                         2
% 6.96/1.51  --comb_inst_mult                        10
% 6.96/1.51  
% 6.96/1.51  ------ Debug Options
% 6.96/1.51  
% 6.96/1.51  --dbg_backtrace                         false
% 6.96/1.51  --dbg_dump_prop_clauses                 false
% 6.96/1.51  --dbg_dump_prop_clauses_file            -
% 6.96/1.51  --dbg_out_stat                          false
% 6.96/1.51  
% 6.96/1.51  
% 6.96/1.51  
% 6.96/1.51  
% 6.96/1.51  ------ Proving...
% 6.96/1.51  
% 6.96/1.51  
% 6.96/1.51  % SZS status Theorem for theBenchmark.p
% 6.96/1.51  
% 6.96/1.51  % SZS output start CNFRefutation for theBenchmark.p
% 6.96/1.51  
% 6.96/1.51  fof(f14,conjecture,(
% 6.96/1.51    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 6.96/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.96/1.51  
% 6.96/1.51  fof(f15,negated_conjecture,(
% 6.96/1.51    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 6.96/1.51    inference(negated_conjecture,[],[f14])).
% 6.96/1.51  
% 6.96/1.51  fof(f28,plain,(
% 6.96/1.51    ? [X0,X1] : ((~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 6.96/1.51    inference(ennf_transformation,[],[f15])).
% 6.96/1.51  
% 6.96/1.51  fof(f29,plain,(
% 6.96/1.51    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 6.96/1.51    inference(flattening,[],[f28])).
% 6.96/1.51  
% 6.96/1.51  fof(f32,plain,(
% 6.96/1.51    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1)) => (~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 6.96/1.51    introduced(choice_axiom,[])).
% 6.96/1.51  
% 6.96/1.51  fof(f33,plain,(
% 6.96/1.51    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1)),
% 6.96/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f32])).
% 6.96/1.51  
% 6.96/1.51  fof(f49,plain,(
% 6.96/1.51    v1_relat_1(sK1)),
% 6.96/1.51    inference(cnf_transformation,[],[f33])).
% 6.96/1.51  
% 6.96/1.51  fof(f9,axiom,(
% 6.96/1.51    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 6.96/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.96/1.51  
% 6.96/1.51  fof(f23,plain,(
% 6.96/1.51    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 6.96/1.51    inference(ennf_transformation,[],[f9])).
% 6.96/1.51  
% 6.96/1.51  fof(f44,plain,(
% 6.96/1.51    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 6.96/1.51    inference(cnf_transformation,[],[f23])).
% 6.96/1.51  
% 6.96/1.51  fof(f12,axiom,(
% 6.96/1.51    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 6.96/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.96/1.51  
% 6.96/1.51  fof(f26,plain,(
% 6.96/1.51    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 6.96/1.51    inference(ennf_transformation,[],[f12])).
% 6.96/1.51  
% 6.96/1.51  fof(f47,plain,(
% 6.96/1.51    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 6.96/1.51    inference(cnf_transformation,[],[f26])).
% 6.96/1.51  
% 6.96/1.51  fof(f10,axiom,(
% 6.96/1.51    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 6.96/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.96/1.51  
% 6.96/1.51  fof(f24,plain,(
% 6.96/1.51    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 6.96/1.51    inference(ennf_transformation,[],[f10])).
% 6.96/1.51  
% 6.96/1.51  fof(f45,plain,(
% 6.96/1.51    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 6.96/1.51    inference(cnf_transformation,[],[f24])).
% 6.96/1.51  
% 6.96/1.51  fof(f13,axiom,(
% 6.96/1.51    ! [X0,X1,X2] : (v1_relat_1(X2) => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1))),
% 6.96/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.96/1.51  
% 6.96/1.51  fof(f27,plain,(
% 6.96/1.51    ! [X0,X1,X2] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 6.96/1.51    inference(ennf_transformation,[],[f13])).
% 6.96/1.51  
% 6.96/1.51  fof(f48,plain,(
% 6.96/1.51    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 6.96/1.51    inference(cnf_transformation,[],[f27])).
% 6.96/1.51  
% 6.96/1.51  fof(f50,plain,(
% 6.96/1.51    r1_tarski(sK0,k1_relat_1(sK1))),
% 6.96/1.51    inference(cnf_transformation,[],[f33])).
% 6.96/1.51  
% 6.96/1.51  fof(f3,axiom,(
% 6.96/1.51    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),X1))),
% 6.96/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.96/1.51  
% 6.96/1.51  fof(f16,plain,(
% 6.96/1.51    ! [X0,X1,X2] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 6.96/1.51    inference(ennf_transformation,[],[f3])).
% 6.96/1.51  
% 6.96/1.51  fof(f38,plain,(
% 6.96/1.51    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 6.96/1.51    inference(cnf_transformation,[],[f16])).
% 6.96/1.51  
% 6.96/1.51  fof(f7,axiom,(
% 6.96/1.51    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 6.96/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.96/1.51  
% 6.96/1.51  fof(f20,plain,(
% 6.96/1.51    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 6.96/1.51    inference(ennf_transformation,[],[f7])).
% 6.96/1.51  
% 6.96/1.51  fof(f42,plain,(
% 6.96/1.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 6.96/1.51    inference(cnf_transformation,[],[f20])).
% 6.96/1.51  
% 6.96/1.51  fof(f11,axiom,(
% 6.96/1.51    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 6.96/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.96/1.51  
% 6.96/1.51  fof(f25,plain,(
% 6.96/1.51    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 6.96/1.51    inference(ennf_transformation,[],[f11])).
% 6.96/1.51  
% 6.96/1.51  fof(f46,plain,(
% 6.96/1.51    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 6.96/1.51    inference(cnf_transformation,[],[f25])).
% 6.96/1.51  
% 6.96/1.51  fof(f5,axiom,(
% 6.96/1.51    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 6.96/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.96/1.51  
% 6.96/1.51  fof(f40,plain,(
% 6.96/1.51    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 6.96/1.51    inference(cnf_transformation,[],[f5])).
% 6.96/1.51  
% 6.96/1.51  fof(f1,axiom,(
% 6.96/1.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 6.96/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.96/1.51  
% 6.96/1.51  fof(f34,plain,(
% 6.96/1.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 6.96/1.51    inference(cnf_transformation,[],[f1])).
% 6.96/1.51  
% 6.96/1.51  fof(f51,plain,(
% 6.96/1.51    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 6.96/1.51    inference(cnf_transformation,[],[f33])).
% 6.96/1.51  
% 6.96/1.51  cnf(c_17,negated_conjecture,
% 6.96/1.51      ( v1_relat_1(sK1) ),
% 6.96/1.51      inference(cnf_transformation,[],[f49]) ).
% 6.96/1.51  
% 6.96/1.51  cnf(c_574,plain,
% 6.96/1.51      ( v1_relat_1(sK1) = iProver_top ),
% 6.96/1.51      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 6.96/1.51  
% 6.96/1.51  cnf(c_10,plain,
% 6.96/1.51      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 6.96/1.51      inference(cnf_transformation,[],[f44]) ).
% 6.96/1.51  
% 6.96/1.51  cnf(c_581,plain,
% 6.96/1.51      ( v1_relat_1(X0) != iProver_top
% 6.96/1.51      | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
% 6.96/1.51      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 6.96/1.51  
% 6.96/1.51  cnf(c_13,plain,
% 6.96/1.51      ( ~ v1_relat_1(X0)
% 6.96/1.51      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
% 6.96/1.51      inference(cnf_transformation,[],[f47]) ).
% 6.96/1.51  
% 6.96/1.51  cnf(c_578,plain,
% 6.96/1.51      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
% 6.96/1.51      | v1_relat_1(X0) != iProver_top ),
% 6.96/1.51      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 6.96/1.51  
% 6.96/1.51  cnf(c_1361,plain,
% 6.96/1.51      ( k10_relat_1(k7_relat_1(X0,X1),k2_relat_1(k7_relat_1(X0,X1))) = k1_relat_1(k7_relat_1(X0,X1))
% 6.96/1.51      | v1_relat_1(X0) != iProver_top ),
% 6.96/1.51      inference(superposition,[status(thm)],[c_581,c_578]) ).
% 6.96/1.51  
% 6.96/1.51  cnf(c_5564,plain,
% 6.96/1.51      ( k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(k7_relat_1(sK1,X0))) = k1_relat_1(k7_relat_1(sK1,X0)) ),
% 6.96/1.51      inference(superposition,[status(thm)],[c_574,c_1361]) ).
% 6.96/1.51  
% 6.96/1.51  cnf(c_11,plain,
% 6.96/1.51      ( ~ v1_relat_1(X0)
% 6.96/1.51      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 6.96/1.51      inference(cnf_transformation,[],[f45]) ).
% 6.96/1.51  
% 6.96/1.51  cnf(c_580,plain,
% 6.96/1.51      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 6.96/1.51      | v1_relat_1(X0) != iProver_top ),
% 6.96/1.51      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 6.96/1.51  
% 6.96/1.51  cnf(c_1467,plain,
% 6.96/1.51      ( k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0) ),
% 6.96/1.51      inference(superposition,[status(thm)],[c_574,c_580]) ).
% 6.96/1.51  
% 6.96/1.51  cnf(c_5565,plain,
% 6.96/1.51      ( k10_relat_1(k7_relat_1(sK1,X0),k9_relat_1(sK1,X0)) = k1_relat_1(k7_relat_1(sK1,X0)) ),
% 6.96/1.51      inference(light_normalisation,[status(thm)],[c_5564,c_1467]) ).
% 6.96/1.51  
% 6.96/1.51  cnf(c_14,plain,
% 6.96/1.51      ( ~ v1_relat_1(X0)
% 6.96/1.51      | k10_relat_1(k7_relat_1(X0,X1),X2) = k3_xboole_0(X1,k10_relat_1(X0,X2)) ),
% 6.96/1.51      inference(cnf_transformation,[],[f48]) ).
% 6.96/1.51  
% 6.96/1.51  cnf(c_577,plain,
% 6.96/1.51      ( k10_relat_1(k7_relat_1(X0,X1),X2) = k3_xboole_0(X1,k10_relat_1(X0,X2))
% 6.96/1.51      | v1_relat_1(X0) != iProver_top ),
% 6.96/1.51      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 6.96/1.51  
% 6.96/1.51  cnf(c_1258,plain,
% 6.96/1.51      ( k10_relat_1(k7_relat_1(sK1,X0),X1) = k3_xboole_0(X0,k10_relat_1(sK1,X1)) ),
% 6.96/1.51      inference(superposition,[status(thm)],[c_574,c_577]) ).
% 6.96/1.51  
% 6.96/1.51  cnf(c_6040,plain,
% 6.96/1.51      ( k3_xboole_0(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0))) = k1_relat_1(k7_relat_1(sK1,X0)) ),
% 6.96/1.51      inference(superposition,[status(thm)],[c_5565,c_1258]) ).
% 6.96/1.51  
% 6.96/1.51  cnf(c_16,negated_conjecture,
% 6.96/1.51      ( r1_tarski(sK0,k1_relat_1(sK1)) ),
% 6.96/1.51      inference(cnf_transformation,[],[f50]) ).
% 6.96/1.51  
% 6.96/1.51  cnf(c_575,plain,
% 6.96/1.51      ( r1_tarski(sK0,k1_relat_1(sK1)) = iProver_top ),
% 6.96/1.51      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 6.96/1.51  
% 6.96/1.51  cnf(c_4,plain,
% 6.96/1.51      ( ~ r1_tarski(X0,X1) | r1_tarski(k3_xboole_0(X0,X2),X1) ),
% 6.96/1.51      inference(cnf_transformation,[],[f38]) ).
% 6.96/1.51  
% 6.96/1.51  cnf(c_587,plain,
% 6.96/1.51      ( r1_tarski(X0,X1) != iProver_top
% 6.96/1.51      | r1_tarski(k3_xboole_0(X0,X2),X1) = iProver_top ),
% 6.96/1.51      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 6.96/1.51  
% 6.96/1.51  cnf(c_8,plain,
% 6.96/1.51      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 6.96/1.51      inference(cnf_transformation,[],[f42]) ).
% 6.96/1.51  
% 6.96/1.51  cnf(c_583,plain,
% 6.96/1.51      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 6.96/1.51      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 6.96/1.51  
% 6.96/1.51  cnf(c_2091,plain,
% 6.96/1.51      ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,X1)
% 6.96/1.51      | r1_tarski(X0,X2) != iProver_top ),
% 6.96/1.51      inference(superposition,[status(thm)],[c_587,c_583]) ).
% 6.96/1.51  
% 6.96/1.51  cnf(c_17912,plain,
% 6.96/1.51      ( k3_xboole_0(k3_xboole_0(sK0,X0),k1_relat_1(sK1)) = k3_xboole_0(sK0,X0) ),
% 6.96/1.51      inference(superposition,[status(thm)],[c_575,c_2091]) ).
% 6.96/1.51  
% 6.96/1.51  cnf(c_18719,plain,
% 6.96/1.51      ( k3_xboole_0(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) = k3_xboole_0(k1_relat_1(k7_relat_1(sK1,sK0)),k1_relat_1(sK1)) ),
% 6.96/1.51      inference(superposition,[status(thm)],[c_6040,c_17912]) ).
% 6.96/1.51  
% 6.96/1.51  cnf(c_1266,plain,
% 6.96/1.51      ( k3_xboole_0(sK0,k1_relat_1(sK1)) = sK0 ),
% 6.96/1.51      inference(superposition,[status(thm)],[c_575,c_583]) ).
% 6.96/1.51  
% 6.96/1.51  cnf(c_1362,plain,
% 6.96/1.51      ( k10_relat_1(sK1,k2_relat_1(sK1)) = k1_relat_1(sK1) ),
% 6.96/1.51      inference(superposition,[status(thm)],[c_574,c_578]) ).
% 6.96/1.51  
% 6.96/1.51  cnf(c_12,plain,
% 6.96/1.51      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 6.96/1.51      inference(cnf_transformation,[],[f46]) ).
% 6.96/1.51  
% 6.96/1.51  cnf(c_579,plain,
% 6.96/1.51      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) = iProver_top
% 6.96/1.51      | v1_relat_1(X0) != iProver_top ),
% 6.96/1.51      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 6.96/1.51  
% 6.96/1.51  cnf(c_1717,plain,
% 6.96/1.51      ( r1_tarski(k3_xboole_0(X0,k10_relat_1(sK1,X1)),k1_relat_1(k7_relat_1(sK1,X0))) = iProver_top
% 6.96/1.51      | v1_relat_1(k7_relat_1(sK1,X0)) != iProver_top ),
% 6.96/1.51      inference(superposition,[status(thm)],[c_1258,c_579]) ).
% 6.96/1.51  
% 6.96/1.51  cnf(c_1724,plain,
% 6.96/1.51      ( r1_tarski(k3_xboole_0(X0,k1_relat_1(sK1)),k1_relat_1(k7_relat_1(sK1,X0))) = iProver_top
% 6.96/1.51      | v1_relat_1(k7_relat_1(sK1,X0)) != iProver_top ),
% 6.96/1.51      inference(superposition,[status(thm)],[c_1362,c_1717]) ).
% 6.96/1.51  
% 6.96/1.51  cnf(c_1811,plain,
% 6.96/1.51      ( r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0))) = iProver_top
% 6.96/1.51      | v1_relat_1(k7_relat_1(sK1,sK0)) != iProver_top ),
% 6.96/1.51      inference(superposition,[status(thm)],[c_1266,c_1724]) ).
% 6.96/1.51  
% 6.96/1.51  cnf(c_1821,plain,
% 6.96/1.51      ( k3_xboole_0(sK0,k1_relat_1(k7_relat_1(sK1,sK0))) = sK0
% 6.96/1.51      | v1_relat_1(k7_relat_1(sK1,sK0)) != iProver_top ),
% 6.96/1.51      inference(superposition,[status(thm)],[c_1811,c_583]) ).
% 6.96/1.51  
% 6.96/1.51  cnf(c_1939,plain,
% 6.96/1.51      ( k3_xboole_0(sK0,k1_relat_1(k7_relat_1(sK1,sK0))) = sK0
% 6.96/1.51      | v1_relat_1(sK1) != iProver_top ),
% 6.96/1.51      inference(superposition,[status(thm)],[c_581,c_1821]) ).
% 6.96/1.51  
% 6.96/1.51  cnf(c_18,plain,
% 6.96/1.51      ( v1_relat_1(sK1) = iProver_top ),
% 6.96/1.51      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 6.96/1.51  
% 6.96/1.51  cnf(c_15432,plain,
% 6.96/1.51      ( k3_xboole_0(sK0,k1_relat_1(k7_relat_1(sK1,sK0))) = sK0 ),
% 6.96/1.51      inference(global_propositional_subsumption,
% 6.96/1.51                [status(thm)],
% 6.96/1.51                [c_1939,c_18]) ).
% 6.96/1.51  
% 6.96/1.51  cnf(c_6,plain,
% 6.96/1.51      ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
% 6.96/1.51      inference(cnf_transformation,[],[f40]) ).
% 6.96/1.51  
% 6.96/1.51  cnf(c_585,plain,
% 6.96/1.51      ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
% 6.96/1.51      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 6.96/1.51  
% 6.96/1.51  cnf(c_1265,plain,
% 6.96/1.51      ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X0,X1) ),
% 6.96/1.51      inference(superposition,[status(thm)],[c_585,c_583]) ).
% 6.96/1.51  
% 6.96/1.51  cnf(c_0,plain,
% 6.96/1.51      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 6.96/1.51      inference(cnf_transformation,[],[f34]) ).
% 6.96/1.51  
% 6.96/1.51  cnf(c_4515,plain,
% 6.96/1.51      ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
% 6.96/1.51      inference(superposition,[status(thm)],[c_1265,c_0]) ).
% 6.96/1.51  
% 6.96/1.51  cnf(c_6769,plain,
% 6.96/1.51      ( k3_xboole_0(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0))) = k3_xboole_0(X0,k1_relat_1(k7_relat_1(sK1,X0))) ),
% 6.96/1.51      inference(superposition,[status(thm)],[c_6040,c_4515]) ).
% 6.96/1.51  
% 6.96/1.51  cnf(c_6791,plain,
% 6.96/1.51      ( k3_xboole_0(X0,k1_relat_1(k7_relat_1(sK1,X0))) = k1_relat_1(k7_relat_1(sK1,X0)) ),
% 6.96/1.51      inference(demodulation,[status(thm)],[c_6769,c_6040]) ).
% 6.96/1.51  
% 6.96/1.51  cnf(c_15443,plain,
% 6.96/1.51      ( k1_relat_1(k7_relat_1(sK1,sK0)) = sK0 ),
% 6.96/1.51      inference(superposition,[status(thm)],[c_15432,c_6791]) ).
% 6.96/1.51  
% 6.96/1.51  cnf(c_18767,plain,
% 6.96/1.51      ( k3_xboole_0(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) = sK0 ),
% 6.96/1.51      inference(light_normalisation,
% 6.96/1.51                [status(thm)],
% 6.96/1.51                [c_18719,c_1266,c_15443]) ).
% 6.96/1.51  
% 6.96/1.51  cnf(c_975,plain,
% 6.96/1.51      ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
% 6.96/1.51      inference(superposition,[status(thm)],[c_0,c_585]) ).
% 6.96/1.51  
% 6.96/1.51  cnf(c_18968,plain,
% 6.96/1.51      ( r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) = iProver_top ),
% 6.96/1.51      inference(superposition,[status(thm)],[c_18767,c_975]) ).
% 6.96/1.51  
% 6.96/1.51  cnf(c_15,negated_conjecture,
% 6.96/1.51      ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
% 6.96/1.51      inference(cnf_transformation,[],[f51]) ).
% 6.96/1.51  
% 6.96/1.51  cnf(c_20,plain,
% 6.96/1.51      ( r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) != iProver_top ),
% 6.96/1.51      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 6.96/1.51  
% 6.96/1.51  cnf(contradiction,plain,
% 6.96/1.51      ( $false ),
% 6.96/1.51      inference(minisat,[status(thm)],[c_18968,c_20]) ).
% 6.96/1.51  
% 6.96/1.51  
% 6.96/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 6.96/1.51  
% 6.96/1.51  ------                               Statistics
% 6.96/1.51  
% 6.96/1.51  ------ General
% 6.96/1.51  
% 6.96/1.51  abstr_ref_over_cycles:                  0
% 6.96/1.51  abstr_ref_under_cycles:                 0
% 6.96/1.51  gc_basic_clause_elim:                   0
% 6.96/1.51  forced_gc_time:                         0
% 6.96/1.51  parsing_time:                           0.006
% 6.96/1.51  unif_index_cands_time:                  0.
% 6.96/1.51  unif_index_add_time:                    0.
% 6.96/1.51  orderings_time:                         0.
% 6.96/1.51  out_proof_time:                         0.011
% 6.96/1.51  total_time:                             0.524
% 6.96/1.51  num_of_symbols:                         42
% 6.96/1.51  num_of_terms:                           24673
% 6.96/1.51  
% 6.96/1.51  ------ Preprocessing
% 6.96/1.51  
% 6.96/1.51  num_of_splits:                          0
% 6.96/1.51  num_of_split_atoms:                     0
% 6.96/1.51  num_of_reused_defs:                     0
% 6.96/1.51  num_eq_ax_congr_red:                    15
% 6.96/1.51  num_of_sem_filtered_clauses:            1
% 6.96/1.51  num_of_subtypes:                        0
% 6.96/1.51  monotx_restored_types:                  0
% 6.96/1.51  sat_num_of_epr_types:                   0
% 6.96/1.51  sat_num_of_non_cyclic_types:            0
% 6.96/1.51  sat_guarded_non_collapsed_types:        0
% 6.96/1.51  num_pure_diseq_elim:                    0
% 6.96/1.51  simp_replaced_by:                       0
% 6.96/1.51  res_preprocessed:                       87
% 6.96/1.51  prep_upred:                             0
% 6.96/1.51  prep_unflattend:                        0
% 6.96/1.51  smt_new_axioms:                         0
% 6.96/1.51  pred_elim_cands:                        2
% 6.96/1.51  pred_elim:                              0
% 6.96/1.51  pred_elim_cl:                           0
% 6.96/1.51  pred_elim_cycles:                       2
% 6.96/1.51  merged_defs:                            0
% 6.96/1.51  merged_defs_ncl:                        0
% 6.96/1.51  bin_hyper_res:                          0
% 6.96/1.51  prep_cycles:                            4
% 6.96/1.51  pred_elim_time:                         0.
% 6.96/1.51  splitting_time:                         0.
% 6.96/1.51  sem_filter_time:                        0.
% 6.96/1.51  monotx_time:                            0.
% 6.96/1.51  subtype_inf_time:                       0.
% 6.96/1.51  
% 6.96/1.51  ------ Problem properties
% 6.96/1.51  
% 6.96/1.51  clauses:                                17
% 6.96/1.51  conjectures:                            3
% 6.96/1.51  epr:                                    4
% 6.96/1.51  horn:                                   17
% 6.96/1.51  ground:                                 3
% 6.96/1.51  unary:                                  6
% 6.96/1.51  binary:                                 8
% 6.96/1.51  lits:                                   31
% 6.96/1.51  lits_eq:                                6
% 6.96/1.51  fd_pure:                                0
% 6.96/1.51  fd_pseudo:                              0
% 6.96/1.51  fd_cond:                                0
% 6.96/1.51  fd_pseudo_cond:                         1
% 6.96/1.51  ac_symbols:                             0
% 6.96/1.51  
% 6.96/1.51  ------ Propositional Solver
% 6.96/1.51  
% 6.96/1.51  prop_solver_calls:                      33
% 6.96/1.51  prop_fast_solver_calls:                 568
% 6.96/1.51  smt_solver_calls:                       0
% 6.96/1.51  smt_fast_solver_calls:                  0
% 6.96/1.51  prop_num_of_clauses:                    9178
% 6.96/1.51  prop_preprocess_simplified:             14599
% 6.96/1.51  prop_fo_subsumed:                       1
% 6.96/1.51  prop_solver_time:                       0.
% 6.96/1.51  smt_solver_time:                        0.
% 6.96/1.51  smt_fast_solver_time:                   0.
% 6.96/1.51  prop_fast_solver_time:                  0.
% 6.96/1.51  prop_unsat_core_time:                   0.001
% 6.96/1.51  
% 6.96/1.51  ------ QBF
% 6.96/1.51  
% 6.96/1.51  qbf_q_res:                              0
% 6.96/1.51  qbf_num_tautologies:                    0
% 6.96/1.51  qbf_prep_cycles:                        0
% 6.96/1.51  
% 6.96/1.51  ------ BMC1
% 6.96/1.51  
% 6.96/1.51  bmc1_current_bound:                     -1
% 6.96/1.51  bmc1_last_solved_bound:                 -1
% 6.96/1.51  bmc1_unsat_core_size:                   -1
% 6.96/1.51  bmc1_unsat_core_parents_size:           -1
% 6.96/1.51  bmc1_merge_next_fun:                    0
% 6.96/1.51  bmc1_unsat_core_clauses_time:           0.
% 6.96/1.51  
% 6.96/1.51  ------ Instantiation
% 6.96/1.51  
% 6.96/1.51  inst_num_of_clauses:                    2195
% 6.96/1.51  inst_num_in_passive:                    949
% 6.96/1.51  inst_num_in_active:                     613
% 6.96/1.51  inst_num_in_unprocessed:                633
% 6.96/1.51  inst_num_of_loops:                      670
% 6.96/1.51  inst_num_of_learning_restarts:          0
% 6.96/1.51  inst_num_moves_active_passive:          53
% 6.96/1.51  inst_lit_activity:                      0
% 6.96/1.51  inst_lit_activity_moves:                1
% 6.96/1.51  inst_num_tautologies:                   0
% 6.96/1.51  inst_num_prop_implied:                  0
% 6.96/1.51  inst_num_existing_simplified:           0
% 6.96/1.51  inst_num_eq_res_simplified:             0
% 6.96/1.51  inst_num_child_elim:                    0
% 6.96/1.51  inst_num_of_dismatching_blockings:      2175
% 6.96/1.51  inst_num_of_non_proper_insts:           3061
% 6.96/1.51  inst_num_of_duplicates:                 0
% 6.96/1.51  inst_inst_num_from_inst_to_res:         0
% 6.96/1.51  inst_dismatching_checking_time:         0.
% 6.96/1.51  
% 6.96/1.51  ------ Resolution
% 6.96/1.51  
% 6.96/1.51  res_num_of_clauses:                     0
% 6.96/1.51  res_num_in_passive:                     0
% 6.96/1.51  res_num_in_active:                      0
% 6.96/1.51  res_num_of_loops:                       91
% 6.96/1.51  res_forward_subset_subsumed:            348
% 6.96/1.51  res_backward_subset_subsumed:           4
% 6.96/1.51  res_forward_subsumed:                   0
% 6.96/1.51  res_backward_subsumed:                  0
% 6.96/1.51  res_forward_subsumption_resolution:     0
% 6.96/1.51  res_backward_subsumption_resolution:    0
% 6.96/1.51  res_clause_to_clause_subsumption:       4561
% 6.96/1.51  res_orphan_elimination:                 0
% 6.96/1.51  res_tautology_del:                      175
% 6.96/1.51  res_num_eq_res_simplified:              0
% 6.96/1.51  res_num_sel_changes:                    0
% 6.96/1.51  res_moves_from_active_to_pass:          0
% 6.96/1.51  
% 6.96/1.51  ------ Superposition
% 6.96/1.51  
% 6.96/1.51  sup_time_total:                         0.
% 6.96/1.51  sup_time_generating:                    0.
% 6.96/1.51  sup_time_sim_full:                      0.
% 6.96/1.51  sup_time_sim_immed:                     0.
% 6.96/1.51  
% 6.96/1.51  sup_num_of_clauses:                     629
% 6.96/1.51  sup_num_in_active:                      130
% 6.96/1.51  sup_num_in_passive:                     499
% 6.96/1.51  sup_num_of_loops:                       132
% 6.96/1.51  sup_fw_superposition:                   802
% 6.96/1.51  sup_bw_superposition:                   876
% 6.96/1.51  sup_immediate_simplified:               468
% 6.96/1.51  sup_given_eliminated:                   1
% 6.96/1.51  comparisons_done:                       0
% 6.96/1.51  comparisons_avoided:                    0
% 6.96/1.51  
% 6.96/1.51  ------ Simplifications
% 6.96/1.51  
% 6.96/1.51  
% 6.96/1.51  sim_fw_subset_subsumed:                 11
% 6.96/1.51  sim_bw_subset_subsumed:                 6
% 6.96/1.51  sim_fw_subsumed:                        81
% 6.96/1.51  sim_bw_subsumed:                        1
% 6.96/1.51  sim_fw_subsumption_res:                 0
% 6.96/1.51  sim_bw_subsumption_res:                 0
% 6.96/1.51  sim_tautology_del:                      35
% 6.96/1.51  sim_eq_tautology_del:                   52
% 6.96/1.51  sim_eq_res_simp:                        0
% 6.96/1.51  sim_fw_demodulated:                     209
% 6.96/1.51  sim_bw_demodulated:                     17
% 6.96/1.51  sim_light_normalised:                   180
% 6.96/1.51  sim_joinable_taut:                      0
% 6.96/1.51  sim_joinable_simp:                      0
% 6.96/1.51  sim_ac_normalised:                      0
% 6.96/1.51  sim_smt_subsumption:                    0
% 6.96/1.51  
%------------------------------------------------------------------------------
