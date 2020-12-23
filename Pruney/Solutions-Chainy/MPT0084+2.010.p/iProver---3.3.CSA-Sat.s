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
% DateTime   : Thu Dec  3 11:24:13 EST 2020

% Result     : CounterSatisfiable 11.87s
% Output     : Saturation 11.87s
% Verified   : 
% Statistics : Number of formulae       :  306 (25929 expanded)
%              Number of clauses        :  282 (11422 expanded)
%              Number of leaves         :    8 (4955 expanded)
%              Depth                    :   28
%              Number of atoms          :  987 (66254 expanded)
%              Number of equality atoms :  913 (22816 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    7 (   3 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,X2)
          & ~ r1_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
      & r1_tarski(X0,X2)
      & ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) )
   => ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
      & r1_tarski(sK0,sK2)
      & ~ r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    & r1_tarski(sK0,sK2)
    & ~ r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f14])).

fof(f24,plain,(
    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f9,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f8])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f10])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f23,plain,(
    r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f22,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_99,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f17])).

cnf(c_64,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_2])).

cnf(c_6,negated_conjecture,
    ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_132,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | k3_xboole_0(sK1,sK2) != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_64,c_6])).

cnf(c_133,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_132])).

cnf(c_3,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_48557,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_48625,plain,
    ( r1_tarski(k1_xboole_0,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_133,c_48557])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_48623,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_48557])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X3)
    | r1_tarski(k3_xboole_0(X2,X0),k3_xboole_0(X3,X1)) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_48556,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X3) != iProver_top
    | r1_tarski(k3_xboole_0(X2,X0),k3_xboole_0(X3,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | ~ r1_xboole_0(X1,X2)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_142,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | k3_xboole_0(sK1,sK2) != X2
    | sK0 != X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_6])).

cnf(c_143,plain,
    ( ~ r1_tarski(X0,k3_xboole_0(sK1,sK2))
    | ~ r1_tarski(X0,sK0)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_142])).

cnf(c_48552,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k3_xboole_0(sK1,sK2)) != iProver_top
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_143])).

cnf(c_48693,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X1,sK2) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(k3_xboole_0(X0,X1),sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_48556,c_48552])).

cnf(c_49148,plain,
    ( k3_xboole_0(X0,sK0) = k1_xboole_0
    | r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(sK0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_48623,c_48693])).

cnf(c_7,negated_conjecture,
    ( r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_10,plain,
    ( r1_tarski(sK0,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_922,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_997,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_922])).

cnf(c_921,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X3) != iProver_top
    | r1_tarski(k3_xboole_0(X2,X0),k3_xboole_0(X3,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_917,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k3_xboole_0(sK1,sK2)) != iProver_top
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_143])).

cnf(c_1068,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X1,sK2) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(k3_xboole_0(X0,X1),sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_921,c_917])).

cnf(c_1543,plain,
    ( k3_xboole_0(X0,sK0) = k1_xboole_0
    | r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(sK0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_997,c_1068])).

cnf(c_49514,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | k3_xboole_0(X0,sK0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_49148,c_10,c_1543])).

cnf(c_49515,plain,
    ( k3_xboole_0(X0,sK0) = k1_xboole_0
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_49514])).

cnf(c_49520,plain,
    ( k3_xboole_0(k3_xboole_0(sK1,X0),sK0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_48557,c_49515])).

cnf(c_48555,plain,
    ( r1_tarski(sK0,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_48690,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X3) != iProver_top
    | r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X3,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_48556])).

cnf(c_49553,plain,
    ( r1_tarski(X0,k3_xboole_0(sK1,X1)) != iProver_top
    | r1_tarski(X2,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(X2,X0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_49520,c_48690])).

cnf(c_50179,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,sK1) != iProver_top
    | r1_tarski(X3,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(X3,k3_xboole_0(X2,X0)),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_48556,c_49553])).

cnf(c_51108,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(X1,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(X1,k3_xboole_0(X0,sK0)),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_48555,c_50179])).

cnf(c_51341,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(X1,sK1) != iProver_top
    | r1_tarski(X2,sK0) != iProver_top
    | r1_tarski(X3,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(X3,k3_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X0,sK0)))),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_51108,c_50179])).

cnf(c_51843,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(X1,sK0) != iProver_top
    | r1_tarski(X2,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(X1,k3_xboole_0(X0,k3_xboole_0(X2,k1_xboole_0))),k1_xboole_0) = iProver_top
    | r1_tarski(k3_xboole_0(sK1,X3),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_49520,c_51341])).

cnf(c_2129,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | k3_xboole_0(X0,sK0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1543,c_10])).

cnf(c_2130,plain,
    ( k3_xboole_0(X0,sK0) = k1_xboole_0
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_2129])).

cnf(c_2137,plain,
    ( k3_xboole_0(k3_xboole_0(sK1,X0),sK0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_922,c_2130])).

cnf(c_920,plain,
    ( r1_tarski(sK0,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1065,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X3) != iProver_top
    | r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X3,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_921])).

cnf(c_2203,plain,
    ( r1_tarski(X0,k3_xboole_0(sK1,X1)) != iProver_top
    | r1_tarski(X2,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(X2,X0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2137,c_1065])).

cnf(c_3365,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,sK1) != iProver_top
    | r1_tarski(X3,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(X3,k3_xboole_0(X2,X0)),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_921,c_2203])).

cnf(c_4871,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(X1,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(X1,k3_xboole_0(X0,sK0)),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_920,c_3365])).

cnf(c_5108,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(X1,sK1) != iProver_top
    | r1_tarski(X2,sK0) != iProver_top
    | r1_tarski(X3,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(X3,k3_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X0,sK0)))),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4871,c_3365])).

cnf(c_5270,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(X1,sK0) != iProver_top
    | r1_tarski(X2,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(X1,k3_xboole_0(X0,k3_xboole_0(X2,k1_xboole_0))),k1_xboole_0) = iProver_top
    | r1_tarski(k3_xboole_0(sK1,X3),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2137,c_5108])).

cnf(c_6186,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(X1,sK0) != iProver_top
    | r1_tarski(X2,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(X1,k3_xboole_0(X0,k3_xboole_0(X2,k1_xboole_0))),k1_xboole_0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5270,c_922])).

cnf(c_52403,plain,
    ( r1_tarski(k3_xboole_0(X1,k3_xboole_0(X0,k3_xboole_0(X2,k1_xboole_0))),k1_xboole_0) = iProver_top
    | r1_tarski(X2,sK0) != iProver_top
    | r1_tarski(X1,sK0) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_51843,c_6186])).

cnf(c_52404,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(X1,sK0) != iProver_top
    | r1_tarski(X2,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(X1,k3_xboole_0(X0,k3_xboole_0(X2,k1_xboole_0))),k1_xboole_0) = iProver_top ),
    inference(renaming,[status(thm)],[c_52403])).

cnf(c_50182,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,sK1) != iProver_top
    | r1_tarski(X3,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(X3,k3_xboole_0(X0,X2)),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_48690,c_49553])).

cnf(c_52419,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(X1,sK1) != iProver_top
    | r1_tarski(X2,sK0) != iProver_top
    | r1_tarski(X3,sK0) != iProver_top
    | r1_tarski(X4,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(X4,k3_xboole_0(k3_xboole_0(X2,k3_xboole_0(X0,k3_xboole_0(X3,k1_xboole_0))),X1)),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_52404,c_50182])).

cnf(c_1,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f18])).

cnf(c_62,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_1])).

cnf(c_114,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | X1 != X3
    | X2 != X4
    | k3_xboole_0(X3,X4) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_62,c_5])).

cnf(c_115,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_114])).

cnf(c_48553,plain,
    ( k3_xboole_0(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X2
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X2,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_115])).

cnf(c_49542,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k3_xboole_0(sK1,X1)) != iProver_top
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_49520,c_48553])).

cnf(c_50016,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(k3_xboole_0(X0,X1),sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_48556,c_49542])).

cnf(c_50658,plain,
    ( k3_xboole_0(sK0,X0) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_48557,c_50016])).

cnf(c_56354,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X3,k1_xboole_0))),X4))) = k1_xboole_0
    | r1_tarski(X4,sK1) != iProver_top
    | r1_tarski(X2,sK1) != iProver_top
    | r1_tarski(X1,sK0) != iProver_top
    | r1_tarski(X3,sK0) != iProver_top
    | r1_tarski(X0,sK0) != iProver_top
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_52419,c_50658])).

cnf(c_61417,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X2,k1_xboole_0))),X3))) = k1_xboole_0
    | r1_tarski(X1,sK1) != iProver_top
    | r1_tarski(X3,sK1) != iProver_top
    | r1_tarski(X0,sK0) != iProver_top
    | r1_tarski(X2,sK0) != iProver_top
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_48625,c_56354])).

cnf(c_61470,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k3_xboole_0(sK0,X0),k3_xboole_0(X1,k3_xboole_0(X2,k1_xboole_0))),X3))) = k1_xboole_0
    | r1_tarski(X1,sK1) != iProver_top
    | r1_tarski(X3,sK1) != iProver_top
    | r1_tarski(X2,sK0) != iProver_top
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_48557,c_61417])).

cnf(c_61939,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k3_xboole_0(sK0,X0),k3_xboole_0(k3_xboole_0(X1,sK1),k3_xboole_0(X2,k1_xboole_0))),X3))) = k1_xboole_0
    | r1_tarski(X3,sK1) != iProver_top
    | r1_tarski(X2,sK0) != iProver_top
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_48623,c_61470])).

cnf(c_62377,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k3_xboole_0(sK0,X0),k3_xboole_0(k3_xboole_0(X1,sK1),k3_xboole_0(k1_xboole_0,k1_xboole_0))),X2))) = k1_xboole_0
    | r1_tarski(X2,sK1) != iProver_top
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_48625,c_61939])).

cnf(c_61938,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k3_xboole_0(sK0,X0),k3_xboole_0(k3_xboole_0(sK1,X1),k3_xboole_0(X2,k1_xboole_0))),X3))) = k1_xboole_0
    | r1_tarski(X3,sK1) != iProver_top
    | r1_tarski(X2,sK0) != iProver_top
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_48557,c_61470])).

cnf(c_62280,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k3_xboole_0(sK0,X0),k3_xboole_0(k3_xboole_0(sK1,X1),k3_xboole_0(k1_xboole_0,k1_xboole_0))),X2))) = k1_xboole_0
    | r1_tarski(X2,sK1) != iProver_top
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_48625,c_61938])).

cnf(c_61472,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k3_xboole_0(X0,sK0),k3_xboole_0(X1,k3_xboole_0(X2,k1_xboole_0))),X3))) = k1_xboole_0
    | r1_tarski(X1,sK1) != iProver_top
    | r1_tarski(X3,sK1) != iProver_top
    | r1_tarski(X2,sK0) != iProver_top
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_48623,c_61417])).

cnf(c_61999,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k3_xboole_0(X0,sK0),k3_xboole_0(k3_xboole_0(sK1,X1),k3_xboole_0(X2,k1_xboole_0))),X3))) = k1_xboole_0
    | r1_tarski(X3,sK1) != iProver_top
    | r1_tarski(X2,sK0) != iProver_top
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_48557,c_61472])).

cnf(c_61471,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k1_xboole_0,k3_xboole_0(X0,k3_xboole_0(X1,k1_xboole_0))),X2))) = k1_xboole_0
    | r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(X2,sK1) != iProver_top
    | r1_tarski(X1,sK0) != iProver_top
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_48625,c_61417])).

cnf(c_61519,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k1_xboole_0,k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(X1,sK0),k1_xboole_0))),X2))) = k1_xboole_0
    | r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(X2,sK1) != iProver_top
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_48623,c_61471])).

cnf(c_61888,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(X0,sK1),k3_xboole_0(k3_xboole_0(X1,sK0),k1_xboole_0))),X2))) = k1_xboole_0
    | r1_tarski(X2,sK1) != iProver_top
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_48623,c_61519])).

cnf(c_61887,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(sK1,X0),k3_xboole_0(k3_xboole_0(X1,sK0),k1_xboole_0))),X2))) = k1_xboole_0
    | r1_tarski(X2,sK1) != iProver_top
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_48557,c_61519])).

cnf(c_61517,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k1_xboole_0,k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(sK0,X1),k1_xboole_0))),X2))) = k1_xboole_0
    | r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(X2,sK1) != iProver_top
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_48557,c_61471])).

cnf(c_61739,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(X0,sK1),k3_xboole_0(k3_xboole_0(sK0,X1),k1_xboole_0))),X2))) = k1_xboole_0
    | r1_tarski(X2,sK1) != iProver_top
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_48623,c_61517])).

cnf(c_61738,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(sK1,X0),k3_xboole_0(k3_xboole_0(sK0,X1),k1_xboole_0))),X2))) = k1_xboole_0
    | r1_tarski(X2,sK1) != iProver_top
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_48557,c_61517])).

cnf(c_49550,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(sK1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_49520,c_0])).

cnf(c_51845,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(X1,sK1) != iProver_top
    | r1_tarski(X2,sK1) != iProver_top
    | r1_tarski(X3,sK0) != iProver_top
    | r1_tarski(X4,sK0) != iProver_top
    | r1_tarski(X5,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(X5,k3_xboole_0(k3_xboole_0(X4,k3_xboole_0(X0,k3_xboole_0(X3,k3_xboole_0(X1,sK0)))),X2)),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_51341,c_50182])).

cnf(c_53073,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(X1,sK1) != iProver_top
    | r1_tarski(X2,sK1) != iProver_top
    | r1_tarski(X3,sK0) != iProver_top
    | r1_tarski(X4,sK0) != iProver_top
    | r1_tarski(X5,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(k3_xboole_0(k3_xboole_0(X3,k3_xboole_0(X0,k3_xboole_0(X4,k3_xboole_0(X2,sK0)))),X1),X5),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_51845])).

cnf(c_56075,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(X1,sK1) != iProver_top
    | r1_tarski(X2,sK0) != iProver_top
    | r1_tarski(X3,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(k3_xboole_0(k3_xboole_0(X2,k3_xboole_0(X0,k1_xboole_0)),X1),X3),k1_xboole_0) = iProver_top
    | r1_tarski(sK1,sK1) != iProver_top
    | r1_tarski(sK0,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_49550,c_53073])).

cnf(c_2192,plain,
    ( r1_tarski(k1_xboole_0,k3_xboole_0(sK1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2137,c_922])).

cnf(c_4887,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(X1,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(X1,k3_xboole_0(X0,k1_xboole_0)),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2192,c_3365])).

cnf(c_2204,plain,
    ( r1_tarski(X0,k3_xboole_0(sK1,X1)) != iProver_top
    | r1_tarski(X2,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(X0,X2),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2137,c_921])).

cnf(c_3625,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,sK1) != iProver_top
    | r1_tarski(X3,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(k3_xboole_0(X0,X2),X3),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1065,c_2204])).

cnf(c_14869,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(X1,sK1) != iProver_top
    | r1_tarski(X2,sK0) != iProver_top
    | r1_tarski(X3,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(k3_xboole_0(k3_xboole_0(X2,k3_xboole_0(X0,k1_xboole_0)),X1),X3),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4887,c_3625])).

cnf(c_61305,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(X1,sK1) != iProver_top
    | r1_tarski(X2,sK0) != iProver_top
    | r1_tarski(X3,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(k3_xboole_0(k3_xboole_0(X2,k3_xboole_0(X0,k1_xboole_0)),X1),X3),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_56075,c_14869])).

cnf(c_61306,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(X1,sK1) != iProver_top
    | r1_tarski(X2,sK0) != iProver_top
    | r1_tarski(X3,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(k3_xboole_0(k3_xboole_0(X2,k3_xboole_0(X1,k1_xboole_0)),X0),X3),k1_xboole_0) = iProver_top ),
    inference(renaming,[status(thm)],[c_61305])).

cnf(c_51831,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(X1,sK1) != iProver_top
    | r1_tarski(X2,sK0) != iProver_top
    | r1_tarski(X3,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(X2,k3_xboole_0(X1,sK0))),X3),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_51341])).

cnf(c_52174,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(X1,sK1) != iProver_top
    | r1_tarski(X2,sK0) != iProver_top
    | r1_tarski(X3,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(k3_xboole_0(k3_xboole_0(X2,k3_xboole_0(X0,sK0)),X1),X3),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_51831])).

cnf(c_55965,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,sK0)),X2),X3)) = k1_xboole_0
    | r1_tarski(X2,sK1) != iProver_top
    | r1_tarski(X1,sK1) != iProver_top
    | r1_tarski(X0,sK0) != iProver_top
    | r1_tarski(X3,sK0) != iProver_top
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_52174,c_50658])).

cnf(c_61007,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(k3_xboole_0(k1_xboole_0,k3_xboole_0(X0,sK0)),X1),X2)) = k1_xboole_0
    | r1_tarski(X1,sK1) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(X2,sK0) != iProver_top
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_48625,c_55965])).

cnf(c_61053,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(k3_xboole_0(k1_xboole_0,k3_xboole_0(X0,sK0)),k3_xboole_0(X1,sK1)),X2)) = k1_xboole_0
    | r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(X2,sK0) != iProver_top
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_48623,c_61007])).

cnf(c_61142,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(X0,sK1),sK0)),k3_xboole_0(X1,sK1)),X2)) = k1_xboole_0
    | r1_tarski(X2,sK0) != iProver_top
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_48623,c_61053])).

cnf(c_49521,plain,
    ( k3_xboole_0(k3_xboole_0(X0,sK1),sK0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_48623,c_49515])).

cnf(c_61146,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k3_xboole_0(X0,sK1)),X1)) = k1_xboole_0
    | r1_tarski(X1,sK0) != iProver_top
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_61142,c_49521])).

cnf(c_61259,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k3_xboole_0(X0,sK1)),k1_xboole_0)) = k1_xboole_0
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_48625,c_61146])).

cnf(c_61052,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(k3_xboole_0(k1_xboole_0,k3_xboole_0(X0,sK0)),k3_xboole_0(sK1,X1)),X2)) = k1_xboole_0
    | r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(X2,sK0) != iProver_top
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_48557,c_61007])).

cnf(c_61083,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(X0,sK1),sK0)),k3_xboole_0(sK1,X1)),X2)) = k1_xboole_0
    | r1_tarski(X2,sK0) != iProver_top
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_48623,c_61052])).

cnf(c_61087,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k3_xboole_0(sK1,X0)),X1)) = k1_xboole_0
    | r1_tarski(X1,sK0) != iProver_top
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_61083,c_49521])).

cnf(c_61213,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k3_xboole_0(sK1,X0)),k1_xboole_0)) = k1_xboole_0
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_48625,c_61087])).

cnf(c_51336,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(X1,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(X1,k3_xboole_0(sK0,X0)),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_51108])).

cnf(c_51443,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(X1,sK1) != iProver_top
    | r1_tarski(X2,sK0) != iProver_top
    | r1_tarski(X3,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(X3,k3_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(sK0,X0)))),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_51336,c_50179])).

cnf(c_52085,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(X1,sK1) != iProver_top
    | r1_tarski(X2,sK0) != iProver_top
    | r1_tarski(X3,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(X2,k3_xboole_0(k3_xboole_0(X3,k3_xboole_0(sK0,X0)),X1)),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_51443])).

cnf(c_55834,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(X1,k3_xboole_0(sK0,X2)),X3))) = k1_xboole_0
    | r1_tarski(X3,sK1) != iProver_top
    | r1_tarski(X2,sK1) != iProver_top
    | r1_tarski(X0,sK0) != iProver_top
    | r1_tarski(X1,sK0) != iProver_top
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_52085,c_50658])).

cnf(c_60710,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(sK0,X1)),X2))) = k1_xboole_0
    | r1_tarski(X1,sK1) != iProver_top
    | r1_tarski(X2,sK1) != iProver_top
    | r1_tarski(X0,sK0) != iProver_top
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_48625,c_55834])).

cnf(c_60757,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k3_xboole_0(X0,sK0),k3_xboole_0(sK0,X1)),X2))) = k1_xboole_0
    | r1_tarski(X1,sK1) != iProver_top
    | r1_tarski(X2,sK1) != iProver_top
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_48623,c_60710])).

cnf(c_60904,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k3_xboole_0(X0,sK0),k3_xboole_0(sK0,k3_xboole_0(X1,sK1))),X2))) = k1_xboole_0
    | r1_tarski(X2,sK1) != iProver_top
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_48623,c_60757])).

cnf(c_48736,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,sK2) != iProver_top
    | r1_tarski(X1,sK1) != iProver_top
    | r1_tarski(k3_xboole_0(X0,X1),sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_48690,c_48552])).

cnf(c_49181,plain,
    ( k3_xboole_0(sK0,X0) = k1_xboole_0
    | r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(sK0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_48557,c_48736])).

cnf(c_1115,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,sK2) != iProver_top
    | r1_tarski(X1,sK1) != iProver_top
    | r1_tarski(k3_xboole_0(X0,X1),sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1065,c_917])).

cnf(c_1580,plain,
    ( k3_xboole_0(sK0,X0) = k1_xboole_0
    | r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(sK0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_922,c_1115])).

cnf(c_49682,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | k3_xboole_0(sK0,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_49181,c_10,c_1580])).

cnf(c_49683,plain,
    ( k3_xboole_0(sK0,X0) = k1_xboole_0
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_49682])).

cnf(c_49689,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(X0,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_48623,c_49683])).

cnf(c_60908,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k3_xboole_0(X0,sK0),k1_xboole_0),X1))) = k1_xboole_0
    | r1_tarski(X1,sK1) != iProver_top
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_60904,c_49689])).

cnf(c_60755,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k3_xboole_0(sK0,X0),k3_xboole_0(sK0,X1)),X2))) = k1_xboole_0
    | r1_tarski(X1,sK1) != iProver_top
    | r1_tarski(X2,sK1) != iProver_top
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_48557,c_60710])).

cnf(c_60869,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k3_xboole_0(sK0,X0),k3_xboole_0(sK0,k3_xboole_0(X1,sK1))),X2))) = k1_xboole_0
    | r1_tarski(X2,sK1) != iProver_top
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_48623,c_60755])).

cnf(c_60873,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k3_xboole_0(sK0,X0),k1_xboole_0),X1))) = k1_xboole_0
    | r1_tarski(X1,sK1) != iProver_top
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_60869,c_49689])).

cnf(c_60756,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0)),X1))) = k1_xboole_0
    | r1_tarski(X1,sK1) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_48625,c_60710])).

cnf(c_60800,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0)),k3_xboole_0(X1,sK1)))) = k1_xboole_0
    | r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_48623,c_60756])).

cnf(c_60843,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k1_xboole_0,k3_xboole_0(sK0,k3_xboole_0(X0,sK1))),k3_xboole_0(X1,sK1)))) = k1_xboole_0
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_48623,c_60800])).

cnf(c_60846,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k3_xboole_0(X0,sK1)))) = k1_xboole_0
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_60843,c_49689])).

cnf(c_60799,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0)),k3_xboole_0(sK1,X1)))) = k1_xboole_0
    | r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_48557,c_60756])).

cnf(c_60824,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k1_xboole_0,k3_xboole_0(sK0,k3_xboole_0(X0,sK1))),k3_xboole_0(sK1,X1)))) = k1_xboole_0
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_48623,c_60799])).

cnf(c_60827,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k3_xboole_0(sK1,X0)))) = k1_xboole_0
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_60824,c_49689])).

cnf(c_61518,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k1_xboole_0,k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,k1_xboole_0))),X1))) = k1_xboole_0
    | r1_tarski(X1,sK1) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_48625,c_61471])).

cnf(c_61562,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k1_xboole_0,k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,k1_xboole_0))),k3_xboole_0(X1,sK1)))) = k1_xboole_0
    | r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_48623,c_61518])).

cnf(c_61679,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(X0,sK1),k3_xboole_0(k1_xboole_0,k1_xboole_0))),k3_xboole_0(X1,sK1)))) = k1_xboole_0
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_48623,c_61562])).

cnf(c_61678,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(sK1,X0),k3_xboole_0(k1_xboole_0,k1_xboole_0))),k3_xboole_0(X1,sK1)))) = k1_xboole_0
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_48557,c_61562])).

cnf(c_61561,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k1_xboole_0,k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,k1_xboole_0))),k3_xboole_0(sK1,X1)))) = k1_xboole_0
    | r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_48557,c_61518])).

cnf(c_61619,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(X0,sK1),k3_xboole_0(k1_xboole_0,k1_xboole_0))),k3_xboole_0(sK1,X1)))) = k1_xboole_0
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_48623,c_61561])).

cnf(c_61618,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(sK1,X0),k3_xboole_0(k1_xboole_0,k1_xboole_0))),k3_xboole_0(sK1,X1)))) = k1_xboole_0
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_48557,c_61561])).

cnf(c_56352,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(X1,sK1) != iProver_top
    | r1_tarski(X2,sK0) != iProver_top
    | r1_tarski(X3,sK0) != iProver_top
    | r1_tarski(X4,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(X2,k3_xboole_0(k3_xboole_0(X3,k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X4))),X1)),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_52419])).

cnf(c_56349,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(X1,sK1) != iProver_top
    | r1_tarski(X2,sK0) != iProver_top
    | r1_tarski(X3,sK0) != iProver_top
    | r1_tarski(X4,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(X2,k3_xboole_0(k3_xboole_0(X3,k3_xboole_0(k3_xboole_0(X4,k1_xboole_0),X1)),X0)),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_52419])).

cnf(c_56346,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(X1,sK1) != iProver_top
    | r1_tarski(X2,sK0) != iProver_top
    | r1_tarski(X3,sK0) != iProver_top
    | r1_tarski(X4,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(X2,k3_xboole_0(k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(X3,k1_xboole_0)),X4),X1)),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_52419])).

cnf(c_52420,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(X1,sK1) != iProver_top
    | r1_tarski(X2,sK0) != iProver_top
    | r1_tarski(X3,sK0) != iProver_top
    | r1_tarski(X4,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(X4,k3_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X0,k3_xboole_0(X3,k1_xboole_0))))),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_52404,c_50179])).

cnf(c_56513,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(X1,sK1) != iProver_top
    | r1_tarski(X2,sK0) != iProver_top
    | r1_tarski(X3,sK0) != iProver_top
    | r1_tarski(X4,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(X2,k3_xboole_0(X1,k3_xboole_0(X3,k1_xboole_0)))),X4),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_52420])).

cnf(c_58963,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(X1,sK1) != iProver_top
    | r1_tarski(X2,sK0) != iProver_top
    | r1_tarski(X3,sK0) != iProver_top
    | r1_tarski(X4,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(X2,k3_xboole_0(k3_xboole_0(X3,k1_xboole_0),X1))),X4),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_56513])).

cnf(c_48689,plain,
    ( r1_tarski(k3_xboole_0(sK1,sK2),X0) != iProver_top
    | r1_tarski(sK0,X1) != iProver_top
    | r1_tarski(k1_xboole_0,k3_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_133,c_48556])).

cnf(c_48777,plain,
    ( r1_tarski(sK0,X0) != iProver_top
    | r1_tarski(k1_xboole_0,k3_xboole_0(X0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_48557,c_48689])).

cnf(c_2138,plain,
    ( k3_xboole_0(k3_xboole_0(X0,sK1),sK0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_997,c_2130])).

cnf(c_2460,plain,
    ( r1_tarski(k1_xboole_0,k3_xboole_0(X0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2138,c_922])).

cnf(c_48936,plain,
    ( r1_tarski(k1_xboole_0,k3_xboole_0(X0,sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_48777,c_2460])).

cnf(c_48941,plain,
    ( r1_tarski(k1_xboole_0,k3_xboole_0(sK1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_48936])).

cnf(c_50019,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X1,sK1) != iProver_top
    | r1_tarski(k3_xboole_0(X0,X1),sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_48690,c_49542])).

cnf(c_50958,plain,
    ( k3_xboole_0(X0,sK0) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_48623,c_50019])).

cnf(c_56701,plain,
    ( k3_xboole_0(k1_xboole_0,sK0) = k1_xboole_0
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_48941,c_50958])).

cnf(c_56689,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),sK0) = k1_xboole_0
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_48623,c_50958])).

cnf(c_56076,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(X1,sK1) != iProver_top
    | r1_tarski(X2,sK1) != iProver_top
    | r1_tarski(X3,sK0) != iProver_top
    | r1_tarski(X4,sK0) != iProver_top
    | r1_tarski(X5,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(k3_xboole_0(k3_xboole_0(X3,k3_xboole_0(X0,k3_xboole_0(X4,k3_xboole_0(sK0,X2)))),X1),X5),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_53073])).

cnf(c_56073,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(X1,sK1) != iProver_top
    | r1_tarski(X2,sK1) != iProver_top
    | r1_tarski(X3,sK0) != iProver_top
    | r1_tarski(X4,sK0) != iProver_top
    | r1_tarski(X5,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(k3_xboole_0(k3_xboole_0(X3,k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(X1,sK0),X4))),X2),X5),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_53073])).

cnf(c_56070,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(X1,sK1) != iProver_top
    | r1_tarski(X2,sK1) != iProver_top
    | r1_tarski(X3,sK0) != iProver_top
    | r1_tarski(X4,sK0) != iProver_top
    | r1_tarski(X5,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(k3_xboole_0(k3_xboole_0(X3,k3_xboole_0(k3_xboole_0(X4,k3_xboole_0(X0,sK0)),X2)),X1),X5),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_53073])).

cnf(c_55220,plain,
    ( k3_xboole_0(sK0,k1_xboole_0) = k1_xboole_0
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_48941,c_50658])).

cnf(c_55208,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(X0,X1)) = k1_xboole_0
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_48623,c_50658])).

cnf(c_56067,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(X1,sK1) != iProver_top
    | r1_tarski(X2,sK1) != iProver_top
    | r1_tarski(X3,sK0) != iProver_top
    | r1_tarski(X4,sK0) != iProver_top
    | r1_tarski(X5,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(X3,k3_xboole_0(X1,sK0))),X4),X2),X5),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_53073])).

cnf(c_53087,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(X1,sK1) != iProver_top
    | r1_tarski(X2,sK0) != iProver_top
    | r1_tarski(X3,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(X2,k3_xboole_0(k3_xboole_0(X3,k3_xboole_0(X0,k1_xboole_0)),X1)),k1_xboole_0) = iProver_top
    | r1_tarski(sK1,sK1) != iProver_top
    | r1_tarski(sK0,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_49550,c_51845])).

cnf(c_51481,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(X1,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(X1,k3_xboole_0(k1_xboole_0,X0)),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_48941,c_50182])).

cnf(c_53657,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(X1,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(k3_xboole_0(k1_xboole_0,X0),X1),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_51481])).

cnf(c_49554,plain,
    ( r1_tarski(X0,k3_xboole_0(sK1,X1)) != iProver_top
    | r1_tarski(X2,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(X0,X2),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_49520,c_48556])).

cnf(c_50287,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,sK1) != iProver_top
    | r1_tarski(X3,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(k3_xboole_0(X0,X2),X3),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_48690,c_49554])).

cnf(c_53944,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(X1,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(k3_xboole_0(k3_xboole_0(X2,X3),X0),X1),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_48623,c_50287])).

cnf(c_52411,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(X1,sK0) != iProver_top
    | r1_tarski(X2,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,k1_xboole_0)),X2),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_52404])).

cnf(c_52894,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(X1,sK0) != iProver_top
    | r1_tarski(X2,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(k3_xboole_0(k3_xboole_0(X1,k1_xboole_0),X0),X2),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_52411])).

cnf(c_54434,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(X1,sK0) != iProver_top
    | r1_tarski(X2,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(k3_xboole_0(k3_xboole_0(k1_xboole_0,X1),X0),X2),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_52894])).

cnf(c_52414,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(X1,sK0) != iProver_top
    | r1_tarski(X2,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(X1,k3_xboole_0(k3_xboole_0(X2,k1_xboole_0),X0)),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_52404])).

cnf(c_52994,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(X1,sK0) != iProver_top
    | r1_tarski(X2,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(X1,k3_xboole_0(k3_xboole_0(k1_xboole_0,X2),X0)),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_52414])).

cnf(c_52897,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(X1,sK0) != iProver_top
    | r1_tarski(X2,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X1)),X2),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_52411])).

cnf(c_50284,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,sK1) != iProver_top
    | r1_tarski(X3,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(k3_xboole_0(X2,X0),X3),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_48556,c_49554])).

cnf(c_52510,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(X1,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(k3_xboole_0(X0,k1_xboole_0),X1),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_48941,c_50284])).

cnf(c_52498,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(X1,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(X2,X3)),X1),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_48623,c_50284])).

cnf(c_51846,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(X1,sK1) != iProver_top
    | r1_tarski(X2,sK1) != iProver_top
    | r1_tarski(X3,sK0) != iProver_top
    | r1_tarski(X4,sK0) != iProver_top
    | r1_tarski(X5,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(X5,k3_xboole_0(X2,k3_xboole_0(X4,k3_xboole_0(X0,k3_xboole_0(X3,k3_xboole_0(X1,sK0)))))),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_51341,c_50179])).

cnf(c_53357,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(X1,sK1) != iProver_top
    | r1_tarski(X2,sK0) != iProver_top
    | r1_tarski(X3,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(X2,k3_xboole_0(X0,k3_xboole_0(X3,k3_xboole_0(X1,k1_xboole_0)))),k1_xboole_0) = iProver_top
    | r1_tarski(sK1,sK1) != iProver_top
    | r1_tarski(sK0,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_49550,c_51846])).

cnf(c_53343,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(X1,sK1) != iProver_top
    | r1_tarski(X2,sK1) != iProver_top
    | r1_tarski(X3,sK0) != iProver_top
    | r1_tarski(X4,sK0) != iProver_top
    | r1_tarski(X5,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(X3,k3_xboole_0(X1,k3_xboole_0(X4,k3_xboole_0(X2,sK0))))),X5),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_51846])).

cnf(c_52417,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(X1,sK0) != iProver_top
    | r1_tarski(X2,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(X1,k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X2))),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_52404])).

cnf(c_52097,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(X1,sK1) != iProver_top
    | r1_tarski(X2,sK1) != iProver_top
    | r1_tarski(X3,sK0) != iProver_top
    | r1_tarski(X4,sK0) != iProver_top
    | r1_tarski(X5,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(X5,k3_xboole_0(X2,k3_xboole_0(X4,k3_xboole_0(X0,k3_xboole_0(X3,k3_xboole_0(sK0,X1)))))),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_51443,c_50179])).

cnf(c_52096,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(X1,sK1) != iProver_top
    | r1_tarski(X2,sK1) != iProver_top
    | r1_tarski(X3,sK0) != iProver_top
    | r1_tarski(X4,sK0) != iProver_top
    | r1_tarski(X5,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(X5,k3_xboole_0(k3_xboole_0(X4,k3_xboole_0(X0,k3_xboole_0(X3,k3_xboole_0(sK0,X1)))),X2)),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_51443,c_50182])).

cnf(c_51333,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(X1,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(k3_xboole_0(X0,sK0),X1),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_51108])).

cnf(c_51392,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(X1,sK1) != iProver_top
    | r1_tarski(X2,sK0) != iProver_top
    | r1_tarski(X3,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(X3,k3_xboole_0(X1,k3_xboole_0(k3_xboole_0(X0,sK0),X2))),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_51333,c_50179])).

cnf(c_51978,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(X1,sK1) != iProver_top
    | r1_tarski(X2,sK1) != iProver_top
    | r1_tarski(X3,sK0) != iProver_top
    | r1_tarski(X4,sK0) != iProver_top
    | r1_tarski(X5,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(X5,k3_xboole_0(X2,k3_xboole_0(X4,k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(X1,sK0),X3))))),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_51392,c_50179])).

cnf(c_51977,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(X1,sK1) != iProver_top
    | r1_tarski(X2,sK1) != iProver_top
    | r1_tarski(X3,sK0) != iProver_top
    | r1_tarski(X4,sK0) != iProver_top
    | r1_tarski(X5,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(X5,k3_xboole_0(k3_xboole_0(X4,k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(X1,sK0),X3))),X2)),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_51392,c_50182])).

cnf(c_51834,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(X1,sK1) != iProver_top
    | r1_tarski(X2,sK0) != iProver_top
    | r1_tarski(X3,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(X2,k3_xboole_0(k3_xboole_0(X3,k3_xboole_0(X0,sK0)),X1)),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_51341])).

cnf(c_52325,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(X1,sK1) != iProver_top
    | r1_tarski(X2,sK1) != iProver_top
    | r1_tarski(X3,sK0) != iProver_top
    | r1_tarski(X4,sK0) != iProver_top
    | r1_tarski(X5,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(X5,k3_xboole_0(k3_xboole_0(X3,k3_xboole_0(k3_xboole_0(X4,k3_xboole_0(X1,sK0)),X0)),X2)),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_51834,c_50182])).

cnf(c_51966,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(X1,sK1) != iProver_top
    | r1_tarski(X2,sK0) != iProver_top
    | r1_tarski(X3,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(X2,k3_xboole_0(k3_xboole_0(k3_xboole_0(X0,sK0),X3),X1)),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_51392])).

cnf(c_52185,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(X1,sK1) != iProver_top
    | r1_tarski(X2,sK1) != iProver_top
    | r1_tarski(X3,sK0) != iProver_top
    | r1_tarski(X4,sK0) != iProver_top
    | r1_tarski(X5,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(X5,k3_xboole_0(k3_xboole_0(k3_xboole_0(X1,k3_xboole_0(X3,k3_xboole_0(X0,sK0))),X4),X2)),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_51831,c_50182])).

cnf(c_52082,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(X1,sK1) != iProver_top
    | r1_tarski(X2,sK0) != iProver_top
    | r1_tarski(X3,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(X2,k3_xboole_0(sK0,X1))),X3),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_51443])).

cnf(c_51963,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(X1,sK1) != iProver_top
    | r1_tarski(X2,sK0) != iProver_top
    | r1_tarski(X3,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(k3_xboole_0(X1,k3_xboole_0(k3_xboole_0(X0,sK0),X2)),X3),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_51392])).

cnf(c_51387,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(X1,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(k3_xboole_0(sK0,X0),X1),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_51333])).

cnf(c_51784,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(X1,sK1) != iProver_top
    | r1_tarski(X2,sK0) != iProver_top
    | r1_tarski(X3,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(X3,k3_xboole_0(k3_xboole_0(k3_xboole_0(sK0,X0),X2),X1)),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_51387,c_50182])).

cnf(c_51469,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(X1,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(X1,k3_xboole_0(k3_xboole_0(X2,X3),X0)),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_48623,c_50182])).

cnf(c_51785,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(X1,sK1) != iProver_top
    | r1_tarski(X2,sK0) != iProver_top
    | r1_tarski(X3,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(X3,k3_xboole_0(X1,k3_xboole_0(k3_xboole_0(sK0,X0),X2))),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_51387,c_50179])).

cnf(c_51123,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(X1,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(X1,k3_xboole_0(X0,k1_xboole_0)),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_48941,c_50179])).

cnf(c_51111,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(X1,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(X1,k3_xboole_0(X0,k3_xboole_0(X2,X3))),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_48623,c_50179])).

cnf(c_49832,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k3_xboole_0(X1,sK1)) != iProver_top
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_49521,c_48553])).

cnf(c_50066,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,sK1)) = k1_xboole_0
    | r1_tarski(k3_xboole_0(X0,k3_xboole_0(X1,sK1)),sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_48623,c_49832])).

cnf(c_50632,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,sK1)) = k1_xboole_0
    | r1_tarski(k3_xboole_0(k3_xboole_0(X1,sK1),X0),sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_50066])).

cnf(c_51058,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,sK1)) = k1_xboole_0
    | r1_tarski(k3_xboole_0(k3_xboole_0(sK1,X1),X0),sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_50632])).

cnf(c_50959,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X1,sK1) != iProver_top
    | r1_tarski(k3_xboole_0(X1,X0),sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_50019])).

cnf(c_50064,plain,
    ( k3_xboole_0(k3_xboole_0(X0,sK1),X1) = k1_xboole_0
    | r1_tarski(k3_xboole_0(k3_xboole_0(X0,sK1),X1),sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_48557,c_49832])).

cnf(c_50604,plain,
    ( k3_xboole_0(k3_xboole_0(X0,sK1),X1) = k1_xboole_0
    | r1_tarski(k3_xboole_0(X1,k3_xboole_0(X0,sK1)),sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_50064])).

cnf(c_51015,plain,
    ( k3_xboole_0(k3_xboole_0(X0,sK1),X1) = k1_xboole_0
    | r1_tarski(k3_xboole_0(X1,k3_xboole_0(sK1,X0)),sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_50604])).

cnf(c_50660,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(k3_xboole_0(X1,X0),sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_50016])).

cnf(c_50636,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,sK1)) = k1_xboole_0
    | r1_tarski(k3_xboole_0(X0,k3_xboole_0(sK1,X1)),sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_50066])).

cnf(c_50608,plain,
    ( k3_xboole_0(k3_xboole_0(X0,sK1),X1) = k1_xboole_0
    | r1_tarski(k3_xboole_0(k3_xboole_0(sK1,X0),X1),sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_50064])).

cnf(c_49845,plain,
    ( r1_tarski(X0,k3_xboole_0(X1,sK1)) != iProver_top
    | r1_tarski(X2,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(X0,X2),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_49521,c_48556])).

cnf(c_50540,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(k3_xboole_0(X1,k3_xboole_0(X2,sK1)),X0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_48623,c_49845])).

cnf(c_50538,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(k3_xboole_0(k3_xboole_0(X1,sK1),X2),X0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_48557,c_49845])).

cnf(c_49844,plain,
    ( r1_tarski(X0,k3_xboole_0(X1,sK1)) != iProver_top
    | r1_tarski(X2,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(X2,X0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_49521,c_48690])).

cnf(c_50505,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X2,sK1))),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_48623,c_49844])).

cnf(c_50503,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(X1,sK1),X2)),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_48557,c_49844])).

cnf(c_50018,plain,
    ( k3_xboole_0(X0,k3_xboole_0(sK1,X1)) = k1_xboole_0
    | r1_tarski(k3_xboole_0(X0,k3_xboole_0(sK1,X1)),sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_48623,c_49542])).

cnf(c_50575,plain,
    ( k3_xboole_0(X0,k3_xboole_0(sK1,X1)) = k1_xboole_0
    | r1_tarski(k3_xboole_0(k3_xboole_0(sK1,X1),X0),sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_50018])).

cnf(c_50731,plain,
    ( k3_xboole_0(X0,k3_xboole_0(sK1,X1)) = k1_xboole_0
    | r1_tarski(k3_xboole_0(k3_xboole_0(X1,sK1),X0),sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_50575])).

cnf(c_50580,plain,
    ( k3_xboole_0(X0,k3_xboole_0(sK1,X1)) = k1_xboole_0
    | r1_tarski(k3_xboole_0(X0,k3_xboole_0(X1,sK1)),sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_50018])).

cnf(c_49551,plain,
    ( r1_tarski(k3_xboole_0(sK1,X0),X1) != iProver_top
    | r1_tarski(sK0,X2) != iProver_top
    | r1_tarski(k1_xboole_0,k3_xboole_0(X2,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_49520,c_48690])).

cnf(c_50098,plain,
    ( r1_tarski(sK0,X0) != iProver_top
    | r1_tarski(k1_xboole_0,k3_xboole_0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_48623,c_49551])).

cnf(c_50364,plain,
    ( r1_tarski(sK0,k3_xboole_0(X0,sK1)) != iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_49521,c_50098])).

cnf(c_50363,plain,
    ( r1_tarski(sK0,k3_xboole_0(sK1,X0)) != iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_49520,c_50098])).

cnf(c_50286,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(k3_xboole_0(X1,k3_xboole_0(sK1,X2)),X0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_48623,c_49554])).

cnf(c_50283,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(k3_xboole_0(k3_xboole_0(sK1,X1),X2),X0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_48557,c_49554])).

cnf(c_50181,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(sK1,X2))),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_48623,c_49553])).

cnf(c_50178,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(sK1,X1),X2)),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_48557,c_49553])).

cnf(c_48778,plain,
    ( r1_tarski(sK2,X0) != iProver_top
    | r1_tarski(sK1,X1) != iProver_top
    | r1_tarski(sK0,X2) != iProver_top
    | r1_tarski(k1_xboole_0,k3_xboole_0(X2,k3_xboole_0(X1,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_48556,c_48689])).

cnf(c_49230,plain,
    ( r1_tarski(sK2,k3_xboole_0(sK1,sK2)) != iProver_top
    | r1_tarski(sK1,sK0) != iProver_top
    | r1_tarski(sK0,X0) != iProver_top
    | r1_tarski(k1_xboole_0,k3_xboole_0(X0,k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_133,c_48778])).

cnf(c_1067,plain,
    ( r1_tarski(X0,k3_xboole_0(sK1,sK2)) != iProver_top
    | r1_tarski(X1,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(X1,X0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_133,c_921])).

cnf(c_1200,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(sK1,sK2))),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_997,c_1067])).

cnf(c_2201,plain,
    ( r1_tarski(k3_xboole_0(sK1,X0),X1) != iProver_top
    | r1_tarski(sK0,X2) != iProver_top
    | r1_tarski(k1_xboole_0,k3_xboole_0(X2,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2137,c_1065])).

cnf(c_3188,plain,
    ( r1_tarski(sK1,sK0) != iProver_top
    | r1_tarski(sK0,X0) != iProver_top
    | r1_tarski(k1_xboole_0,k3_xboole_0(X0,k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1200,c_2201])).

cnf(c_49384,plain,
    ( r1_tarski(sK1,sK0) != iProver_top
    | r1_tarski(sK0,X0) != iProver_top
    | r1_tarski(k1_xboole_0,k3_xboole_0(X0,k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_49230,c_3188])).

cnf(c_49391,plain,
    ( r1_tarski(sK1,sK0) != iProver_top
    | r1_tarski(sK0,X0) != iProver_top
    | r1_tarski(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_49384])).

cnf(c_49552,plain,
    ( r1_tarski(k3_xboole_0(sK1,X0),X1) != iProver_top
    | r1_tarski(sK0,X2) != iProver_top
    | r1_tarski(k1_xboole_0,k3_xboole_0(X1,X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_49520,c_48556])).

cnf(c_50138,plain,
    ( r1_tarski(sK0,X0) != iProver_top
    | r1_tarski(k1_xboole_0,k3_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_48623,c_49552])).

cnf(c_50015,plain,
    ( k3_xboole_0(k3_xboole_0(sK1,X0),X1) = k1_xboole_0
    | r1_tarski(k3_xboole_0(k3_xboole_0(sK1,X0),X1),sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_48557,c_49542])).

cnf(c_50428,plain,
    ( k3_xboole_0(k3_xboole_0(sK1,X0),X1) = k1_xboole_0
    | r1_tarski(k3_xboole_0(X1,k3_xboole_0(sK1,X0)),sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_50015])).

cnf(c_50466,plain,
    ( k3_xboole_0(k3_xboole_0(sK1,X0),X1) = k1_xboole_0
    | r1_tarski(k3_xboole_0(X1,k3_xboole_0(X0,sK1)),sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_50428])).

cnf(c_50433,plain,
    ( k3_xboole_0(k3_xboole_0(sK1,X0),X1) = k1_xboole_0
    | r1_tarski(k3_xboole_0(k3_xboole_0(X0,sK1),X1),sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_50015])).

cnf(c_49842,plain,
    ( r1_tarski(k3_xboole_0(X0,sK1),X1) != iProver_top
    | r1_tarski(sK0,X2) != iProver_top
    | r1_tarski(k1_xboole_0,k3_xboole_0(X2,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_49521,c_48690])).

cnf(c_49549,plain,
    ( r1_tarski(sK2,sK0) != iProver_top
    | r1_tarski(sK1,k3_xboole_0(sK1,X0)) != iProver_top
    | r1_tarski(sK0,X1) != iProver_top
    | r1_tarski(k1_xboole_0,k3_xboole_0(X1,k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_49520,c_48778])).

cnf(c_49799,plain,
    ( r1_tarski(sK2,sK0) != iProver_top
    | r1_tarski(sK1,k3_xboole_0(X0,sK1)) != iProver_top
    | r1_tarski(sK0,X1) != iProver_top
    | r1_tarski(k1_xboole_0,k3_xboole_0(X1,k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_49549])).

cnf(c_48732,plain,
    ( r1_tarski(k3_xboole_0(sK1,sK2),X0) != iProver_top
    | r1_tarski(sK0,X1) != iProver_top
    | r1_tarski(k1_xboole_0,k3_xboole_0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_133,c_48690])).

cnf(c_48857,plain,
    ( r1_tarski(sK2,X0) != iProver_top
    | r1_tarski(sK1,X1) != iProver_top
    | r1_tarski(sK0,X2) != iProver_top
    | r1_tarski(k1_xboole_0,k3_xboole_0(k3_xboole_0(X1,X0),X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_48556,c_48732])).

cnf(c_49545,plain,
    ( r1_tarski(sK2,sK0) != iProver_top
    | r1_tarski(sK1,k3_xboole_0(sK1,X0)) != iProver_top
    | r1_tarski(sK0,X1) != iProver_top
    | r1_tarski(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_49520,c_48857])).

cnf(c_49773,plain,
    ( r1_tarski(sK2,sK0) != iProver_top
    | r1_tarski(sK1,k3_xboole_0(X0,sK1)) != iProver_top
    | r1_tarski(sK0,X1) != iProver_top
    | r1_tarski(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_49545])).

cnf(c_49182,plain,
    ( k3_xboole_0(X0,sK0) = k1_xboole_0
    | r1_tarski(X0,sK2) != iProver_top
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_48623,c_48736])).

cnf(c_49707,plain,
    ( k3_xboole_0(k3_xboole_0(X0,sK2),sK0) = k1_xboole_0
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_48623,c_49182])).

cnf(c_49705,plain,
    ( k3_xboole_0(k3_xboole_0(sK2,X0),sK0) = k1_xboole_0
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_48557,c_49182])).

cnf(c_49227,plain,
    ( r1_tarski(sK2,sK2) != iProver_top
    | r1_tarski(sK1,sK1) != iProver_top
    | r1_tarski(sK0,sK0) != iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_133,c_48778])).

cnf(c_1114,plain,
    ( r1_tarski(X0,k3_xboole_0(sK1,sK2)) != iProver_top
    | r1_tarski(X1,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(X0,X1),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_133,c_1065])).

cnf(c_1288,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(k3_xboole_0(X1,k3_xboole_0(sK1,sK2)),X0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_997,c_1114])).

cnf(c_2212,plain,
    ( r1_tarski(sK0,sK0) != iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2137,c_1288])).

cnf(c_49367,plain,
    ( r1_tarski(sK0,sK0) != iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_49227,c_2212])).

cnf(c_48626,plain,
    ( k3_xboole_0(k3_xboole_0(sK1,sK2),X0) = k1_xboole_0
    | r1_tarski(k3_xboole_0(k3_xboole_0(sK1,sK2),X0),sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_48557,c_48552])).

cnf(c_48981,plain,
    ( k3_xboole_0(k3_xboole_0(sK1,sK2),sK0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_48623,c_48626])).

cnf(c_49468,plain,
    ( r1_tarski(sK2,sK0) != iProver_top
    | r1_tarski(sK1,k3_xboole_0(sK1,sK2)) != iProver_top
    | r1_tarski(sK0,X0) != iProver_top
    | r1_tarski(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_48981,c_48857])).

cnf(c_49147,plain,
    ( k3_xboole_0(sK0,X0) = k1_xboole_0
    | r1_tarski(X0,sK2) != iProver_top
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_48557,c_48693])).

cnf(c_49338,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(X0,sK2)) = k1_xboole_0
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_48623,c_49147])).

cnf(c_49337,plain,
    ( k3_xboole_0(sK0,sK0) = k1_xboole_0
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_48555,c_49147])).

cnf(c_49336,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(sK2,X0)) = k1_xboole_0
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_48557,c_49147])).

cnf(c_49231,plain,
    ( r1_tarski(sK2,sK0) != iProver_top
    | r1_tarski(sK1,k3_xboole_0(sK1,sK2)) != iProver_top
    | r1_tarski(sK0,X0) != iProver_top
    | r1_tarski(k1_xboole_0,k3_xboole_0(X0,k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_48981,c_48778])).

cnf(c_49183,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,sK2) != iProver_top
    | r1_tarski(X1,sK1) != iProver_top
    | r1_tarski(k3_xboole_0(X1,X0),sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_48736])).

cnf(c_49149,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X1,sK2) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(k3_xboole_0(X1,X0),sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_48693])).

cnf(c_48672,plain,
    ( k3_xboole_0(X0,k3_xboole_0(sK1,sK2)) = k1_xboole_0
    | r1_tarski(k3_xboole_0(X0,k3_xboole_0(sK1,sK2)),sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_48623,c_48552])).

cnf(c_49057,plain,
    ( k3_xboole_0(X0,k3_xboole_0(sK1,sK2)) = k1_xboole_0
    | r1_tarski(k3_xboole_0(k3_xboole_0(sK1,sK2),X0),sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_48672])).

cnf(c_48982,plain,
    ( k3_xboole_0(k3_xboole_0(sK1,sK2),X0) = k1_xboole_0
    | r1_tarski(k3_xboole_0(X0,k3_xboole_0(sK1,sK2)),sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_48626])).

cnf(c_48735,plain,
    ( r1_tarski(X0,k3_xboole_0(sK1,sK2)) != iProver_top
    | r1_tarski(X1,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(X0,X1),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_133,c_48690])).

cnf(c_48902,plain,
    ( r1_tarski(X0,sK2) != iProver_top
    | r1_tarski(X1,sK1) != iProver_top
    | r1_tarski(X2,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(k3_xboole_0(X0,X1),X2),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_48690,c_48735])).

cnf(c_48901,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(k3_xboole_0(X1,k3_xboole_0(sK1,sK2)),X0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_48623,c_48735])).

cnf(c_48899,plain,
    ( r1_tarski(X0,sK2) != iProver_top
    | r1_tarski(X1,sK1) != iProver_top
    | r1_tarski(X2,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(k3_xboole_0(X1,X0),X2),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_48556,c_48735])).

cnf(c_48898,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(k3_xboole_0(k3_xboole_0(sK1,sK2),X1),X0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_48557,c_48735])).

cnf(c_48859,plain,
    ( r1_tarski(sK2,X0) != iProver_top
    | r1_tarski(sK1,X1) != iProver_top
    | r1_tarski(sK0,X2) != iProver_top
    | r1_tarski(k1_xboole_0,k3_xboole_0(k3_xboole_0(X0,X1),X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_48690,c_48732])).

cnf(c_48858,plain,
    ( r1_tarski(sK0,X0) != iProver_top
    | r1_tarski(k1_xboole_0,k3_xboole_0(sK2,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_48623,c_48732])).

cnf(c_48692,plain,
    ( r1_tarski(X0,k3_xboole_0(sK1,sK2)) != iProver_top
    | r1_tarski(X1,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(X1,X0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_133,c_48556])).

cnf(c_48817,plain,
    ( r1_tarski(X0,sK2) != iProver_top
    | r1_tarski(X1,sK1) != iProver_top
    | r1_tarski(X2,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(X2,k3_xboole_0(X0,X1)),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_48690,c_48692])).

cnf(c_48816,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(sK1,sK2))),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_48623,c_48692])).

cnf(c_48814,plain,
    ( r1_tarski(X0,sK2) != iProver_top
    | r1_tarski(X1,sK1) != iProver_top
    | r1_tarski(X2,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(X2,k3_xboole_0(X1,X0)),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_48556,c_48692])).

cnf(c_48813,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | r1_tarski(k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(sK1,sK2),X1)),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_48557,c_48692])).

cnf(c_48780,plain,
    ( r1_tarski(sK2,X0) != iProver_top
    | r1_tarski(sK1,X1) != iProver_top
    | r1_tarski(sK0,X2) != iProver_top
    | r1_tarski(k1_xboole_0,k3_xboole_0(X2,k3_xboole_0(X0,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_48690,c_48689])).

cnf(c_48779,plain,
    ( r1_tarski(sK0,X0) != iProver_top
    | r1_tarski(k1_xboole_0,k3_xboole_0(X0,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_48623,c_48689])).

cnf(c_48671,plain,
    ( r1_tarski(k1_xboole_0,k3_xboole_0(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_133,c_48623])).

cnf(c_8,negated_conjecture,
    ( ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_157,plain,
    ( k3_xboole_0(sK1,sK2) != sK1
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_8])).

cnf(c_197,plain,
    ( k3_xboole_0(sK1,sK2) != sK1 ),
    inference(equality_resolution_simp,[status(thm)],[c_157])).

cnf(c_137,plain,
    ( k3_xboole_0(X0,X1) != k1_xboole_0
    | sK1 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_62,c_8])).

cnf(c_138,plain,
    ( k3_xboole_0(sK0,sK1) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_137])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:01:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 11.87/2.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.87/2.00  
% 11.87/2.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.87/2.00  
% 11.87/2.00  ------  iProver source info
% 11.87/2.00  
% 11.87/2.00  git: date: 2020-06-30 10:37:57 +0100
% 11.87/2.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.87/2.00  git: non_committed_changes: false
% 11.87/2.00  git: last_make_outside_of_git: false
% 11.87/2.00  
% 11.87/2.00  ------ 
% 11.87/2.00  ------ Parsing...
% 11.87/2.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.87/2.00  
% 11.87/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e 
% 11.87/2.00  
% 11.87/2.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.87/2.00  
% 11.87/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.87/2.00  ------ Proving...
% 11.87/2.00  ------ Problem Properties 
% 11.87/2.00  
% 11.87/2.00  
% 11.87/2.00  clauses                                 9
% 11.87/2.00  conjectures                             1
% 11.87/2.00  EPR                                     1
% 11.87/2.00  Horn                                    9
% 11.87/2.00  unary                                   5
% 11.87/2.00  binary                                  1
% 11.87/2.00  lits                                    17
% 11.87/2.00  lits eq                                 8
% 11.87/2.00  fd_pure                                 0
% 11.87/2.00  fd_pseudo                               0
% 11.87/2.00  fd_cond                                 2
% 11.87/2.00  fd_pseudo_cond                          0
% 11.87/2.00  AC symbols                              0
% 11.87/2.00  
% 11.87/2.00  ------ Input Options Time Limit: Unbounded
% 11.87/2.00  
% 11.87/2.00  
% 11.87/2.00  
% 11.87/2.00  
% 11.87/2.00  ------ Preprocessing...
% 11.87/2.00  
% 11.87/2.00  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 11.87/2.00  Current options:
% 11.87/2.00  ------ 
% 11.87/2.00  
% 11.87/2.00  
% 11.87/2.00  
% 11.87/2.00  
% 11.87/2.00  ------ Proving...
% 11.87/2.00  
% 11.87/2.00  
% 11.87/2.00  ------ Preprocessing...
% 11.87/2.00  
% 11.87/2.00  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.87/2.00  
% 11.87/2.00  ------ Proving...
% 11.87/2.00  
% 11.87/2.00  
% 11.87/2.00  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.87/2.00  
% 11.87/2.00  ------ Proving...
% 11.87/2.00  
% 11.87/2.00  
% 11.87/2.00  ------ Preprocessing...
% 11.87/2.00  
% 11.87/2.00  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.87/2.00  
% 11.87/2.00  ------ Proving...
% 11.87/2.00  
% 11.87/2.00  
% 11.87/2.00  ------ Preprocessing...
% 11.87/2.00  
% 11.87/2.00  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.87/2.00  
% 11.87/2.00  ------ Proving...
% 11.87/2.00  
% 11.87/2.00  
% 11.87/2.00  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.87/2.00  
% 11.87/2.00  ------ Proving...
% 11.87/2.00  
% 11.87/2.00  
% 11.87/2.00  ------ Preprocessing...
% 11.87/2.00  
% 11.87/2.00  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.87/2.00  
% 11.87/2.00  ------ Proving...
% 11.87/2.00  
% 11.87/2.00  
% 11.87/2.00  ------ Preprocessing...
% 11.87/2.00  
% 11.87/2.00  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.87/2.00  
% 11.87/2.00  ------ Proving...
% 11.87/2.00  
% 11.87/2.00  
% 11.87/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.87/2.00  
% 11.87/2.00  ------ Proving...
% 11.87/2.00  
% 11.87/2.00  
% 11.87/2.00  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.87/2.00  
% 11.87/2.00  ------ Proving...
% 11.87/2.00  
% 11.87/2.00  
% 11.87/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.87/2.00  
% 11.87/2.00  ------ Proving...
% 11.87/2.00  
% 11.87/2.00  
% 11.87/2.00  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.87/2.00  
% 11.87/2.00  ------ Proving...
% 11.87/2.00  
% 11.87/2.00  
% 11.87/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.87/2.00  
% 11.87/2.00  ------ Proving...
% 11.87/2.00  
% 11.87/2.00  
% 11.87/2.00  ------ Preprocessing...
% 11.87/2.00  
% 11.87/2.00  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.87/2.00  
% 11.87/2.00  ------ Proving...
% 11.87/2.00  
% 11.87/2.00  
% 11.87/2.00  ------ Preprocessing...
% 11.87/2.00  
% 11.87/2.00  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.87/2.00  
% 11.87/2.00  ------ Proving...
% 11.87/2.00  
% 11.87/2.00  
% 11.87/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.87/2.00  
% 11.87/2.00  ------ Proving...
% 11.87/2.00  
% 11.87/2.00  
% 11.87/2.00  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.87/2.00  
% 11.87/2.00  ------ Proving...
% 11.87/2.00  
% 11.87/2.00  
% 11.87/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.87/2.00  
% 11.87/2.00  ------ Proving...
% 11.87/2.00  
% 11.87/2.00  
% 11.87/2.00  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.87/2.00  
% 11.87/2.00  ------ Proving...
% 11.87/2.00  
% 11.87/2.00  
% 11.87/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.87/2.00  
% 11.87/2.00  ------ Proving...
% 11.87/2.00  
% 11.87/2.00  
% 11.87/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.87/2.00  
% 11.87/2.00  ------ Proving...
% 11.87/2.00  
% 11.87/2.00  
% 11.87/2.00  % SZS status CounterSatisfiable for theBenchmark.p
% 11.87/2.00  
% 11.87/2.00  % SZS output start Saturation for theBenchmark.p
% 11.87/2.00  
% 11.87/2.00  fof(f2,axiom,(
% 11.87/2.00    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 11.87/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.87/2.00  
% 11.87/2.00  fof(f13,plain,(
% 11.87/2.00    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 11.87/2.00    inference(nnf_transformation,[],[f2])).
% 11.87/2.00  
% 11.87/2.00  fof(f17,plain,(
% 11.87/2.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 11.87/2.00    inference(cnf_transformation,[],[f13])).
% 11.87/2.00  
% 11.87/2.00  fof(f6,conjecture,(
% 11.87/2.00    ! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 11.87/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.87/2.00  
% 11.87/2.00  fof(f7,negated_conjecture,(
% 11.87/2.00    ~! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 11.87/2.00    inference(negated_conjecture,[],[f6])).
% 11.87/2.00  
% 11.87/2.00  fof(f12,plain,(
% 11.87/2.00    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 11.87/2.00    inference(ennf_transformation,[],[f7])).
% 11.87/2.00  
% 11.87/2.00  fof(f14,plain,(
% 11.87/2.00    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1)) => (r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,sK2) & ~r1_xboole_0(sK0,sK1))),
% 11.87/2.00    introduced(choice_axiom,[])).
% 11.87/2.00  
% 11.87/2.00  fof(f15,plain,(
% 11.87/2.00    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,sK2) & ~r1_xboole_0(sK0,sK1)),
% 11.87/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f14])).
% 11.87/2.00  
% 11.87/2.00  fof(f24,plain,(
% 11.87/2.00    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 11.87/2.00    inference(cnf_transformation,[],[f15])).
% 11.87/2.00  
% 11.87/2.00  fof(f3,axiom,(
% 11.87/2.00    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 11.87/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.87/2.00  
% 11.87/2.00  fof(f19,plain,(
% 11.87/2.00    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 11.87/2.00    inference(cnf_transformation,[],[f3])).
% 11.87/2.00  
% 11.87/2.00  fof(f1,axiom,(
% 11.87/2.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 11.87/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.87/2.00  
% 11.87/2.00  fof(f16,plain,(
% 11.87/2.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 11.87/2.00    inference(cnf_transformation,[],[f1])).
% 11.87/2.00  
% 11.87/2.00  fof(f4,axiom,(
% 11.87/2.00    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)))),
% 11.87/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.87/2.00  
% 11.87/2.00  fof(f8,plain,(
% 11.87/2.00    ! [X0,X1,X2,X3] : (r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) | (~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)))),
% 11.87/2.00    inference(ennf_transformation,[],[f4])).
% 11.87/2.00  
% 11.87/2.00  fof(f9,plain,(
% 11.87/2.00    ! [X0,X1,X2,X3] : (r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 11.87/2.00    inference(flattening,[],[f8])).
% 11.87/2.00  
% 11.87/2.00  fof(f20,plain,(
% 11.87/2.00    ( ! [X2,X0,X3,X1] : (r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 11.87/2.00    inference(cnf_transformation,[],[f9])).
% 11.87/2.00  
% 11.87/2.00  fof(f5,axiom,(
% 11.87/2.00    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k1_xboole_0 = X0)),
% 11.87/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.87/2.00  
% 11.87/2.00  fof(f10,plain,(
% 11.87/2.00    ! [X0,X1,X2] : (k1_xboole_0 = X0 | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 11.87/2.00    inference(ennf_transformation,[],[f5])).
% 11.87/2.00  
% 11.87/2.00  fof(f11,plain,(
% 11.87/2.00    ! [X0,X1,X2] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 11.87/2.00    inference(flattening,[],[f10])).
% 11.87/2.00  
% 11.87/2.00  fof(f21,plain,(
% 11.87/2.00    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 11.87/2.00    inference(cnf_transformation,[],[f11])).
% 11.87/2.00  
% 11.87/2.00  fof(f23,plain,(
% 11.87/2.00    r1_tarski(sK0,sK2)),
% 11.87/2.00    inference(cnf_transformation,[],[f15])).
% 11.87/2.00  
% 11.87/2.00  fof(f18,plain,(
% 11.87/2.00    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 11.87/2.00    inference(cnf_transformation,[],[f13])).
% 11.87/2.00  
% 11.87/2.00  fof(f22,plain,(
% 11.87/2.00    ~r1_xboole_0(sK0,sK1)),
% 11.87/2.00    inference(cnf_transformation,[],[f15])).
% 11.87/2.00  
% 11.87/2.00  cnf(c_99,plain,( X0_2 = X0_2 ),theory(equality) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_2,plain,
% 11.87/2.00      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 11.87/2.00      inference(cnf_transformation,[],[f17]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_64,plain,
% 11.87/2.00      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 11.87/2.00      inference(prop_impl,[status(thm)],[c_2]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_6,negated_conjecture,
% 11.87/2.00      ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
% 11.87/2.00      inference(cnf_transformation,[],[f24]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_132,plain,
% 11.87/2.00      ( k3_xboole_0(X0,X1) = k1_xboole_0
% 11.87/2.00      | k3_xboole_0(sK1,sK2) != X1
% 11.87/2.00      | sK0 != X0 ),
% 11.87/2.00      inference(resolution_lifted,[status(thm)],[c_64,c_6]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_133,plain,
% 11.87/2.00      ( k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)) = k1_xboole_0 ),
% 11.87/2.00      inference(unflattening,[status(thm)],[c_132]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_3,plain,
% 11.87/2.00      ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
% 11.87/2.00      inference(cnf_transformation,[],[f19]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_48557,plain,
% 11.87/2.00      ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
% 11.87/2.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_48625,plain,
% 11.87/2.00      ( r1_tarski(k1_xboole_0,sK0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_133,c_48557]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_0,plain,
% 11.87/2.00      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 11.87/2.00      inference(cnf_transformation,[],[f16]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_48623,plain,
% 11.87/2.00      ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_0,c_48557]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_4,plain,
% 11.87/2.00      ( ~ r1_tarski(X0,X1)
% 11.87/2.00      | ~ r1_tarski(X2,X3)
% 11.87/2.00      | r1_tarski(k3_xboole_0(X2,X0),k3_xboole_0(X3,X1)) ),
% 11.87/2.00      inference(cnf_transformation,[],[f20]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_48556,plain,
% 11.87/2.00      ( r1_tarski(X0,X1) != iProver_top
% 11.87/2.00      | r1_tarski(X2,X3) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(X2,X0),k3_xboole_0(X3,X1)) = iProver_top ),
% 11.87/2.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_5,plain,
% 11.87/2.00      ( ~ r1_tarski(X0,X1)
% 11.87/2.00      | ~ r1_tarski(X0,X2)
% 11.87/2.00      | ~ r1_xboole_0(X1,X2)
% 11.87/2.00      | k1_xboole_0 = X0 ),
% 11.87/2.00      inference(cnf_transformation,[],[f21]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_142,plain,
% 11.87/2.00      ( ~ r1_tarski(X0,X1)
% 11.87/2.00      | ~ r1_tarski(X0,X2)
% 11.87/2.00      | k3_xboole_0(sK1,sK2) != X2
% 11.87/2.00      | sK0 != X1
% 11.87/2.00      | k1_xboole_0 = X0 ),
% 11.87/2.00      inference(resolution_lifted,[status(thm)],[c_5,c_6]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_143,plain,
% 11.87/2.00      ( ~ r1_tarski(X0,k3_xboole_0(sK1,sK2))
% 11.87/2.00      | ~ r1_tarski(X0,sK0)
% 11.87/2.00      | k1_xboole_0 = X0 ),
% 11.87/2.00      inference(unflattening,[status(thm)],[c_142]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_48552,plain,
% 11.87/2.00      ( k1_xboole_0 = X0
% 11.87/2.00      | r1_tarski(X0,k3_xboole_0(sK1,sK2)) != iProver_top
% 11.87/2.00      | r1_tarski(X0,sK0) != iProver_top ),
% 11.87/2.00      inference(predicate_to_equality,[status(thm)],[c_143]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_48693,plain,
% 11.87/2.00      ( k3_xboole_0(X0,X1) = k1_xboole_0
% 11.87/2.00      | r1_tarski(X1,sK2) != iProver_top
% 11.87/2.00      | r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(X0,X1),sK0) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48556,c_48552]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_49148,plain,
% 11.87/2.00      ( k3_xboole_0(X0,sK0) = k1_xboole_0
% 11.87/2.00      | r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(sK0,sK2) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48623,c_48693]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_7,negated_conjecture,
% 11.87/2.00      ( r1_tarski(sK0,sK2) ),
% 11.87/2.00      inference(cnf_transformation,[],[f23]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_10,plain,
% 11.87/2.00      ( r1_tarski(sK0,sK2) = iProver_top ),
% 11.87/2.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_922,plain,
% 11.87/2.00      ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
% 11.87/2.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_997,plain,
% 11.87/2.00      ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_0,c_922]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_921,plain,
% 11.87/2.00      ( r1_tarski(X0,X1) != iProver_top
% 11.87/2.00      | r1_tarski(X2,X3) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(X2,X0),k3_xboole_0(X3,X1)) = iProver_top ),
% 11.87/2.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_917,plain,
% 11.87/2.00      ( k1_xboole_0 = X0
% 11.87/2.00      | r1_tarski(X0,k3_xboole_0(sK1,sK2)) != iProver_top
% 11.87/2.00      | r1_tarski(X0,sK0) != iProver_top ),
% 11.87/2.00      inference(predicate_to_equality,[status(thm)],[c_143]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_1068,plain,
% 11.87/2.00      ( k3_xboole_0(X0,X1) = k1_xboole_0
% 11.87/2.00      | r1_tarski(X1,sK2) != iProver_top
% 11.87/2.00      | r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(X0,X1),sK0) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_921,c_917]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_1543,plain,
% 11.87/2.00      ( k3_xboole_0(X0,sK0) = k1_xboole_0
% 11.87/2.00      | r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(sK0,sK2) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_997,c_1068]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_49514,plain,
% 11.87/2.00      ( r1_tarski(X0,sK1) != iProver_top | k3_xboole_0(X0,sK0) = k1_xboole_0 ),
% 11.87/2.00      inference(global_propositional_subsumption,
% 11.87/2.00                [status(thm)],
% 11.87/2.00                [c_49148,c_10,c_1543]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_49515,plain,
% 11.87/2.00      ( k3_xboole_0(X0,sK0) = k1_xboole_0 | r1_tarski(X0,sK1) != iProver_top ),
% 11.87/2.00      inference(renaming,[status(thm)],[c_49514]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_49520,plain,
% 11.87/2.00      ( k3_xboole_0(k3_xboole_0(sK1,X0),sK0) = k1_xboole_0 ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48557,c_49515]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_48555,plain,
% 11.87/2.00      ( r1_tarski(sK0,sK2) = iProver_top ),
% 11.87/2.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_48690,plain,
% 11.87/2.00      ( r1_tarski(X0,X1) != iProver_top
% 11.87/2.00      | r1_tarski(X2,X3) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X3,X1)) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_0,c_48556]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_49553,plain,
% 11.87/2.00      ( r1_tarski(X0,k3_xboole_0(sK1,X1)) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(X2,X0),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_49520,c_48690]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_50179,plain,
% 11.87/2.00      ( r1_tarski(X0,X1) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X3,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(X3,k3_xboole_0(X2,X0)),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48556,c_49553]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_51108,plain,
% 11.87/2.00      ( r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(X1,k3_xboole_0(X0,sK0)),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48555,c_50179]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_51341,plain,
% 11.87/2.00      ( r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(X3,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(X3,k3_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X0,sK0)))),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_51108,c_50179]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_51843,plain,
% 11.87/2.00      ( r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(X1,k3_xboole_0(X0,k3_xboole_0(X2,k1_xboole_0))),k1_xboole_0) = iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(sK1,X3),sK1) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_49520,c_51341]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_2129,plain,
% 11.87/2.00      ( r1_tarski(X0,sK1) != iProver_top | k3_xboole_0(X0,sK0) = k1_xboole_0 ),
% 11.87/2.00      inference(global_propositional_subsumption,[status(thm)],[c_1543,c_10]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_2130,plain,
% 11.87/2.00      ( k3_xboole_0(X0,sK0) = k1_xboole_0 | r1_tarski(X0,sK1) != iProver_top ),
% 11.87/2.00      inference(renaming,[status(thm)],[c_2129]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_2137,plain,
% 11.87/2.00      ( k3_xboole_0(k3_xboole_0(sK1,X0),sK0) = k1_xboole_0 ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_922,c_2130]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_920,plain,
% 11.87/2.00      ( r1_tarski(sK0,sK2) = iProver_top ),
% 11.87/2.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_1065,plain,
% 11.87/2.00      ( r1_tarski(X0,X1) != iProver_top
% 11.87/2.00      | r1_tarski(X2,X3) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X3,X1)) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_0,c_921]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_2203,plain,
% 11.87/2.00      ( r1_tarski(X0,k3_xboole_0(sK1,X1)) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(X2,X0),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_2137,c_1065]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_3365,plain,
% 11.87/2.00      ( r1_tarski(X0,X1) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X3,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(X3,k3_xboole_0(X2,X0)),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_921,c_2203]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_4871,plain,
% 11.87/2.00      ( r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(X1,k3_xboole_0(X0,sK0)),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_920,c_3365]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_5108,plain,
% 11.87/2.00      ( r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(X3,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(X3,k3_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X0,sK0)))),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_4871,c_3365]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_5270,plain,
% 11.87/2.00      ( r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(X1,k3_xboole_0(X0,k3_xboole_0(X2,k1_xboole_0))),k1_xboole_0) = iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(sK1,X3),sK1) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_2137,c_5108]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_6186,plain,
% 11.87/2.00      ( r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(X1,k3_xboole_0(X0,k3_xboole_0(X2,k1_xboole_0))),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(forward_subsumption_resolution,[status(thm)],[c_5270,c_922]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_52403,plain,
% 11.87/2.00      ( r1_tarski(k3_xboole_0(X1,k3_xboole_0(X0,k3_xboole_0(X2,k1_xboole_0))),k1_xboole_0) = iProver_top
% 11.87/2.00      | r1_tarski(X2,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(X0,sK1) != iProver_top ),
% 11.87/2.00      inference(global_propositional_subsumption,
% 11.87/2.00                [status(thm)],
% 11.87/2.00                [c_51843,c_6186]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_52404,plain,
% 11.87/2.00      ( r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(X1,k3_xboole_0(X0,k3_xboole_0(X2,k1_xboole_0))),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(renaming,[status(thm)],[c_52403]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_50182,plain,
% 11.87/2.00      ( r1_tarski(X0,X1) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X3,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(X3,k3_xboole_0(X0,X2)),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48690,c_49553]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_52419,plain,
% 11.87/2.00      ( r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(X3,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(X4,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(X4,k3_xboole_0(k3_xboole_0(X2,k3_xboole_0(X0,k3_xboole_0(X3,k1_xboole_0))),X1)),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_52404,c_50182]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_1,plain,
% 11.87/2.00      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 11.87/2.00      inference(cnf_transformation,[],[f18]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_62,plain,
% 11.87/2.00      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 11.87/2.00      inference(prop_impl,[status(thm)],[c_1]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_114,plain,
% 11.87/2.00      ( ~ r1_tarski(X0,X1)
% 11.87/2.00      | ~ r1_tarski(X0,X2)
% 11.87/2.00      | X1 != X3
% 11.87/2.00      | X2 != X4
% 11.87/2.00      | k3_xboole_0(X3,X4) != k1_xboole_0
% 11.87/2.00      | k1_xboole_0 = X0 ),
% 11.87/2.00      inference(resolution_lifted,[status(thm)],[c_62,c_5]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_115,plain,
% 11.87/2.00      ( ~ r1_tarski(X0,X1)
% 11.87/2.00      | ~ r1_tarski(X0,X2)
% 11.87/2.00      | k3_xboole_0(X1,X2) != k1_xboole_0
% 11.87/2.00      | k1_xboole_0 = X0 ),
% 11.87/2.00      inference(unflattening,[status(thm)],[c_114]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_48553,plain,
% 11.87/2.00      ( k3_xboole_0(X0,X1) != k1_xboole_0
% 11.87/2.00      | k1_xboole_0 = X2
% 11.87/2.00      | r1_tarski(X2,X0) != iProver_top
% 11.87/2.00      | r1_tarski(X2,X1) != iProver_top ),
% 11.87/2.00      inference(predicate_to_equality,[status(thm)],[c_115]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_49542,plain,
% 11.87/2.00      ( k1_xboole_0 = X0
% 11.87/2.00      | r1_tarski(X0,k3_xboole_0(sK1,X1)) != iProver_top
% 11.87/2.00      | r1_tarski(X0,sK0) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_49520,c_48553]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_50016,plain,
% 11.87/2.00      ( k3_xboole_0(X0,X1) = k1_xboole_0
% 11.87/2.00      | r1_tarski(X1,X2) != iProver_top
% 11.87/2.00      | r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(X0,X1),sK0) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48556,c_49542]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_50658,plain,
% 11.87/2.00      ( k3_xboole_0(sK0,X0) = k1_xboole_0
% 11.87/2.00      | r1_tarski(X0,X1) != iProver_top
% 11.87/2.00      | r1_tarski(sK0,sK1) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48557,c_50016]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_56354,plain,
% 11.87/2.00      ( k3_xboole_0(sK0,k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X3,k1_xboole_0))),X4))) = k1_xboole_0
% 11.87/2.00      | r1_tarski(X4,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(X3,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(X0,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(sK0,sK1) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_52419,c_50658]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_61417,plain,
% 11.87/2.00      ( k3_xboole_0(sK0,k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X2,k1_xboole_0))),X3))) = k1_xboole_0
% 11.87/2.00      | r1_tarski(X1,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X3,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X0,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(sK0,sK1) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48625,c_56354]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_61470,plain,
% 11.87/2.00      ( k3_xboole_0(sK0,k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k3_xboole_0(sK0,X0),k3_xboole_0(X1,k3_xboole_0(X2,k1_xboole_0))),X3))) = k1_xboole_0
% 11.87/2.00      | r1_tarski(X1,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X3,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(sK0,sK1) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48557,c_61417]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_61939,plain,
% 11.87/2.00      ( k3_xboole_0(sK0,k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k3_xboole_0(sK0,X0),k3_xboole_0(k3_xboole_0(X1,sK1),k3_xboole_0(X2,k1_xboole_0))),X3))) = k1_xboole_0
% 11.87/2.00      | r1_tarski(X3,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(sK0,sK1) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48623,c_61470]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_62377,plain,
% 11.87/2.00      ( k3_xboole_0(sK0,k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k3_xboole_0(sK0,X0),k3_xboole_0(k3_xboole_0(X1,sK1),k3_xboole_0(k1_xboole_0,k1_xboole_0))),X2))) = k1_xboole_0
% 11.87/2.00      | r1_tarski(X2,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(sK0,sK1) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48625,c_61939]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_61938,plain,
% 11.87/2.00      ( k3_xboole_0(sK0,k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k3_xboole_0(sK0,X0),k3_xboole_0(k3_xboole_0(sK1,X1),k3_xboole_0(X2,k1_xboole_0))),X3))) = k1_xboole_0
% 11.87/2.00      | r1_tarski(X3,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(sK0,sK1) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48557,c_61470]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_62280,plain,
% 11.87/2.00      ( k3_xboole_0(sK0,k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k3_xboole_0(sK0,X0),k3_xboole_0(k3_xboole_0(sK1,X1),k3_xboole_0(k1_xboole_0,k1_xboole_0))),X2))) = k1_xboole_0
% 11.87/2.00      | r1_tarski(X2,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(sK0,sK1) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48625,c_61938]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_61472,plain,
% 11.87/2.00      ( k3_xboole_0(sK0,k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k3_xboole_0(X0,sK0),k3_xboole_0(X1,k3_xboole_0(X2,k1_xboole_0))),X3))) = k1_xboole_0
% 11.87/2.00      | r1_tarski(X1,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X3,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(sK0,sK1) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48623,c_61417]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_61999,plain,
% 11.87/2.00      ( k3_xboole_0(sK0,k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k3_xboole_0(X0,sK0),k3_xboole_0(k3_xboole_0(sK1,X1),k3_xboole_0(X2,k1_xboole_0))),X3))) = k1_xboole_0
% 11.87/2.00      | r1_tarski(X3,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(sK0,sK1) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48557,c_61472]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_61471,plain,
% 11.87/2.00      ( k3_xboole_0(sK0,k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k1_xboole_0,k3_xboole_0(X0,k3_xboole_0(X1,k1_xboole_0))),X2))) = k1_xboole_0
% 11.87/2.00      | r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(sK0,sK1) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48625,c_61417]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_61519,plain,
% 11.87/2.00      ( k3_xboole_0(sK0,k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k1_xboole_0,k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(X1,sK0),k1_xboole_0))),X2))) = k1_xboole_0
% 11.87/2.00      | r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(sK0,sK1) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48623,c_61471]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_61888,plain,
% 11.87/2.00      ( k3_xboole_0(sK0,k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(X0,sK1),k3_xboole_0(k3_xboole_0(X1,sK0),k1_xboole_0))),X2))) = k1_xboole_0
% 11.87/2.00      | r1_tarski(X2,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(sK0,sK1) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48623,c_61519]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_61887,plain,
% 11.87/2.00      ( k3_xboole_0(sK0,k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(sK1,X0),k3_xboole_0(k3_xboole_0(X1,sK0),k1_xboole_0))),X2))) = k1_xboole_0
% 11.87/2.00      | r1_tarski(X2,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(sK0,sK1) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48557,c_61519]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_61517,plain,
% 11.87/2.00      ( k3_xboole_0(sK0,k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k1_xboole_0,k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(sK0,X1),k1_xboole_0))),X2))) = k1_xboole_0
% 11.87/2.00      | r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(sK0,sK1) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48557,c_61471]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_61739,plain,
% 11.87/2.00      ( k3_xboole_0(sK0,k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(X0,sK1),k3_xboole_0(k3_xboole_0(sK0,X1),k1_xboole_0))),X2))) = k1_xboole_0
% 11.87/2.00      | r1_tarski(X2,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(sK0,sK1) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48623,c_61517]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_61738,plain,
% 11.87/2.00      ( k3_xboole_0(sK0,k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(sK1,X0),k3_xboole_0(k3_xboole_0(sK0,X1),k1_xboole_0))),X2))) = k1_xboole_0
% 11.87/2.00      | r1_tarski(X2,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(sK0,sK1) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48557,c_61517]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_49550,plain,
% 11.87/2.00      ( k3_xboole_0(sK0,k3_xboole_0(sK1,X0)) = k1_xboole_0 ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_49520,c_0]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_51845,plain,
% 11.87/2.00      ( r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X3,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(X4,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(X5,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(X5,k3_xboole_0(k3_xboole_0(X4,k3_xboole_0(X0,k3_xboole_0(X3,k3_xboole_0(X1,sK0)))),X2)),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_51341,c_50182]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_53073,plain,
% 11.87/2.00      ( r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X3,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(X4,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(X5,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(k3_xboole_0(k3_xboole_0(X3,k3_xboole_0(X0,k3_xboole_0(X4,k3_xboole_0(X2,sK0)))),X1),X5),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_0,c_51845]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_56075,plain,
% 11.87/2.00      ( r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(X3,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(k3_xboole_0(k3_xboole_0(X2,k3_xboole_0(X0,k1_xboole_0)),X1),X3),k1_xboole_0) = iProver_top
% 11.87/2.00      | r1_tarski(sK1,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(sK0,sK0) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_49550,c_53073]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_2192,plain,
% 11.87/2.00      ( r1_tarski(k1_xboole_0,k3_xboole_0(sK1,X0)) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_2137,c_922]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_4887,plain,
% 11.87/2.00      ( r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(X1,k3_xboole_0(X0,k1_xboole_0)),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_2192,c_3365]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_2204,plain,
% 11.87/2.00      ( r1_tarski(X0,k3_xboole_0(sK1,X1)) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(X0,X2),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_2137,c_921]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_3625,plain,
% 11.87/2.00      ( r1_tarski(X0,X1) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X3,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(k3_xboole_0(X0,X2),X3),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_1065,c_2204]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_14869,plain,
% 11.87/2.00      ( r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(X3,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(k3_xboole_0(k3_xboole_0(X2,k3_xboole_0(X0,k1_xboole_0)),X1),X3),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_4887,c_3625]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_61305,plain,
% 11.87/2.00      ( r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(X3,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(k3_xboole_0(k3_xboole_0(X2,k3_xboole_0(X0,k1_xboole_0)),X1),X3),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(global_propositional_subsumption,
% 11.87/2.00                [status(thm)],
% 11.87/2.00                [c_56075,c_14869]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_61306,plain,
% 11.87/2.00      ( r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(X3,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(k3_xboole_0(k3_xboole_0(X2,k3_xboole_0(X1,k1_xboole_0)),X0),X3),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(renaming,[status(thm)],[c_61305]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_51831,plain,
% 11.87/2.00      ( r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(X3,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(X2,k3_xboole_0(X1,sK0))),X3),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_0,c_51341]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_52174,plain,
% 11.87/2.00      ( r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(X3,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(k3_xboole_0(k3_xboole_0(X2,k3_xboole_0(X0,sK0)),X1),X3),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_0,c_51831]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_55965,plain,
% 11.87/2.00      ( k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,sK0)),X2),X3)) = k1_xboole_0
% 11.87/2.00      | r1_tarski(X2,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X0,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(X3,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(sK0,sK1) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_52174,c_50658]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_61007,plain,
% 11.87/2.00      ( k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(k3_xboole_0(k1_xboole_0,k3_xboole_0(X0,sK0)),X1),X2)) = k1_xboole_0
% 11.87/2.00      | r1_tarski(X1,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(sK0,sK1) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48625,c_55965]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_61053,plain,
% 11.87/2.00      ( k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(k3_xboole_0(k1_xboole_0,k3_xboole_0(X0,sK0)),k3_xboole_0(X1,sK1)),X2)) = k1_xboole_0
% 11.87/2.00      | r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(sK0,sK1) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48623,c_61007]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_61142,plain,
% 11.87/2.00      ( k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(X0,sK1),sK0)),k3_xboole_0(X1,sK1)),X2)) = k1_xboole_0
% 11.87/2.00      | r1_tarski(X2,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(sK0,sK1) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48623,c_61053]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_49521,plain,
% 11.87/2.00      ( k3_xboole_0(k3_xboole_0(X0,sK1),sK0) = k1_xboole_0 ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48623,c_49515]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_61146,plain,
% 11.87/2.00      ( k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k3_xboole_0(X0,sK1)),X1)) = k1_xboole_0
% 11.87/2.00      | r1_tarski(X1,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(sK0,sK1) != iProver_top ),
% 11.87/2.00      inference(light_normalisation,[status(thm)],[c_61142,c_49521]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_61259,plain,
% 11.87/2.00      ( k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k3_xboole_0(X0,sK1)),k1_xboole_0)) = k1_xboole_0
% 11.87/2.00      | r1_tarski(sK0,sK1) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48625,c_61146]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_61052,plain,
% 11.87/2.00      ( k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(k3_xboole_0(k1_xboole_0,k3_xboole_0(X0,sK0)),k3_xboole_0(sK1,X1)),X2)) = k1_xboole_0
% 11.87/2.00      | r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(sK0,sK1) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48557,c_61007]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_61083,plain,
% 11.87/2.00      ( k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(X0,sK1),sK0)),k3_xboole_0(sK1,X1)),X2)) = k1_xboole_0
% 11.87/2.00      | r1_tarski(X2,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(sK0,sK1) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48623,c_61052]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_61087,plain,
% 11.87/2.00      ( k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k3_xboole_0(sK1,X0)),X1)) = k1_xboole_0
% 11.87/2.00      | r1_tarski(X1,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(sK0,sK1) != iProver_top ),
% 11.87/2.00      inference(light_normalisation,[status(thm)],[c_61083,c_49521]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_61213,plain,
% 11.87/2.00      ( k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k3_xboole_0(sK1,X0)),k1_xboole_0)) = k1_xboole_0
% 11.87/2.00      | r1_tarski(sK0,sK1) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48625,c_61087]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_51336,plain,
% 11.87/2.00      ( r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(X1,k3_xboole_0(sK0,X0)),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_0,c_51108]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_51443,plain,
% 11.87/2.00      ( r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(X3,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(X3,k3_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(sK0,X0)))),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_51336,c_50179]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_52085,plain,
% 11.87/2.00      ( r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(X3,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(X2,k3_xboole_0(k3_xboole_0(X3,k3_xboole_0(sK0,X0)),X1)),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_0,c_51443]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_55834,plain,
% 11.87/2.00      ( k3_xboole_0(sK0,k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(X1,k3_xboole_0(sK0,X2)),X3))) = k1_xboole_0
% 11.87/2.00      | r1_tarski(X3,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X0,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(sK0,sK1) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_52085,c_50658]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_60710,plain,
% 11.87/2.00      ( k3_xboole_0(sK0,k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(sK0,X1)),X2))) = k1_xboole_0
% 11.87/2.00      | r1_tarski(X1,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X0,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(sK0,sK1) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48625,c_55834]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_60757,plain,
% 11.87/2.00      ( k3_xboole_0(sK0,k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k3_xboole_0(X0,sK0),k3_xboole_0(sK0,X1)),X2))) = k1_xboole_0
% 11.87/2.00      | r1_tarski(X1,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(sK0,sK1) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48623,c_60710]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_60904,plain,
% 11.87/2.00      ( k3_xboole_0(sK0,k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k3_xboole_0(X0,sK0),k3_xboole_0(sK0,k3_xboole_0(X1,sK1))),X2))) = k1_xboole_0
% 11.87/2.00      | r1_tarski(X2,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(sK0,sK1) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48623,c_60757]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_48736,plain,
% 11.87/2.00      ( k3_xboole_0(X0,X1) = k1_xboole_0
% 11.87/2.00      | r1_tarski(X0,sK2) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(X0,X1),sK0) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48690,c_48552]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_49181,plain,
% 11.87/2.00      ( k3_xboole_0(sK0,X0) = k1_xboole_0
% 11.87/2.00      | r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(sK0,sK2) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48557,c_48736]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_1115,plain,
% 11.87/2.00      ( k3_xboole_0(X0,X1) = k1_xboole_0
% 11.87/2.00      | r1_tarski(X0,sK2) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(X0,X1),sK0) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_1065,c_917]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_1580,plain,
% 11.87/2.00      ( k3_xboole_0(sK0,X0) = k1_xboole_0
% 11.87/2.00      | r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(sK0,sK2) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_922,c_1115]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_49682,plain,
% 11.87/2.00      ( r1_tarski(X0,sK1) != iProver_top | k3_xboole_0(sK0,X0) = k1_xboole_0 ),
% 11.87/2.00      inference(global_propositional_subsumption,
% 11.87/2.00                [status(thm)],
% 11.87/2.00                [c_49181,c_10,c_1580]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_49683,plain,
% 11.87/2.00      ( k3_xboole_0(sK0,X0) = k1_xboole_0 | r1_tarski(X0,sK1) != iProver_top ),
% 11.87/2.00      inference(renaming,[status(thm)],[c_49682]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_49689,plain,
% 11.87/2.00      ( k3_xboole_0(sK0,k3_xboole_0(X0,sK1)) = k1_xboole_0 ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48623,c_49683]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_60908,plain,
% 11.87/2.00      ( k3_xboole_0(sK0,k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k3_xboole_0(X0,sK0),k1_xboole_0),X1))) = k1_xboole_0
% 11.87/2.00      | r1_tarski(X1,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(sK0,sK1) != iProver_top ),
% 11.87/2.00      inference(demodulation,[status(thm)],[c_60904,c_49689]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_60755,plain,
% 11.87/2.00      ( k3_xboole_0(sK0,k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k3_xboole_0(sK0,X0),k3_xboole_0(sK0,X1)),X2))) = k1_xboole_0
% 11.87/2.00      | r1_tarski(X1,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(sK0,sK1) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48557,c_60710]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_60869,plain,
% 11.87/2.00      ( k3_xboole_0(sK0,k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k3_xboole_0(sK0,X0),k3_xboole_0(sK0,k3_xboole_0(X1,sK1))),X2))) = k1_xboole_0
% 11.87/2.00      | r1_tarski(X2,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(sK0,sK1) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48623,c_60755]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_60873,plain,
% 11.87/2.00      ( k3_xboole_0(sK0,k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k3_xboole_0(sK0,X0),k1_xboole_0),X1))) = k1_xboole_0
% 11.87/2.00      | r1_tarski(X1,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(sK0,sK1) != iProver_top ),
% 11.87/2.00      inference(demodulation,[status(thm)],[c_60869,c_49689]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_60756,plain,
% 11.87/2.00      ( k3_xboole_0(sK0,k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0)),X1))) = k1_xboole_0
% 11.87/2.00      | r1_tarski(X1,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(sK0,sK1) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48625,c_60710]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_60800,plain,
% 11.87/2.00      ( k3_xboole_0(sK0,k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0)),k3_xboole_0(X1,sK1)))) = k1_xboole_0
% 11.87/2.00      | r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(sK0,sK1) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48623,c_60756]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_60843,plain,
% 11.87/2.00      ( k3_xboole_0(sK0,k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k1_xboole_0,k3_xboole_0(sK0,k3_xboole_0(X0,sK1))),k3_xboole_0(X1,sK1)))) = k1_xboole_0
% 11.87/2.00      | r1_tarski(sK0,sK1) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48623,c_60800]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_60846,plain,
% 11.87/2.00      ( k3_xboole_0(sK0,k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k3_xboole_0(X0,sK1)))) = k1_xboole_0
% 11.87/2.00      | r1_tarski(sK0,sK1) != iProver_top ),
% 11.87/2.00      inference(light_normalisation,[status(thm)],[c_60843,c_49689]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_60799,plain,
% 11.87/2.00      ( k3_xboole_0(sK0,k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0)),k3_xboole_0(sK1,X1)))) = k1_xboole_0
% 11.87/2.00      | r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(sK0,sK1) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48557,c_60756]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_60824,plain,
% 11.87/2.00      ( k3_xboole_0(sK0,k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k1_xboole_0,k3_xboole_0(sK0,k3_xboole_0(X0,sK1))),k3_xboole_0(sK1,X1)))) = k1_xboole_0
% 11.87/2.00      | r1_tarski(sK0,sK1) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48623,c_60799]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_60827,plain,
% 11.87/2.00      ( k3_xboole_0(sK0,k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k3_xboole_0(sK1,X0)))) = k1_xboole_0
% 11.87/2.00      | r1_tarski(sK0,sK1) != iProver_top ),
% 11.87/2.00      inference(light_normalisation,[status(thm)],[c_60824,c_49689]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_61518,plain,
% 11.87/2.00      ( k3_xboole_0(sK0,k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k1_xboole_0,k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,k1_xboole_0))),X1))) = k1_xboole_0
% 11.87/2.00      | r1_tarski(X1,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(sK0,sK1) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48625,c_61471]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_61562,plain,
% 11.87/2.00      ( k3_xboole_0(sK0,k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k1_xboole_0,k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,k1_xboole_0))),k3_xboole_0(X1,sK1)))) = k1_xboole_0
% 11.87/2.00      | r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(sK0,sK1) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48623,c_61518]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_61679,plain,
% 11.87/2.00      ( k3_xboole_0(sK0,k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(X0,sK1),k3_xboole_0(k1_xboole_0,k1_xboole_0))),k3_xboole_0(X1,sK1)))) = k1_xboole_0
% 11.87/2.00      | r1_tarski(sK0,sK1) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48623,c_61562]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_61678,plain,
% 11.87/2.00      ( k3_xboole_0(sK0,k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(sK1,X0),k3_xboole_0(k1_xboole_0,k1_xboole_0))),k3_xboole_0(X1,sK1)))) = k1_xboole_0
% 11.87/2.00      | r1_tarski(sK0,sK1) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48557,c_61562]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_61561,plain,
% 11.87/2.00      ( k3_xboole_0(sK0,k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k1_xboole_0,k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,k1_xboole_0))),k3_xboole_0(sK1,X1)))) = k1_xboole_0
% 11.87/2.00      | r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(sK0,sK1) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48557,c_61518]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_61619,plain,
% 11.87/2.00      ( k3_xboole_0(sK0,k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(X0,sK1),k3_xboole_0(k1_xboole_0,k1_xboole_0))),k3_xboole_0(sK1,X1)))) = k1_xboole_0
% 11.87/2.00      | r1_tarski(sK0,sK1) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48623,c_61561]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_61618,plain,
% 11.87/2.00      ( k3_xboole_0(sK0,k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(sK1,X0),k3_xboole_0(k1_xboole_0,k1_xboole_0))),k3_xboole_0(sK1,X1)))) = k1_xboole_0
% 11.87/2.00      | r1_tarski(sK0,sK1) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48557,c_61561]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_56352,plain,
% 11.87/2.00      ( r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(X3,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(X4,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(X2,k3_xboole_0(k3_xboole_0(X3,k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X4))),X1)),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_0,c_52419]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_56349,plain,
% 11.87/2.00      ( r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(X3,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(X4,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(X2,k3_xboole_0(k3_xboole_0(X3,k3_xboole_0(k3_xboole_0(X4,k1_xboole_0),X1)),X0)),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_0,c_52419]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_56346,plain,
% 11.87/2.00      ( r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(X3,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(X4,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(X2,k3_xboole_0(k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(X3,k1_xboole_0)),X4),X1)),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_0,c_52419]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_52420,plain,
% 11.87/2.00      ( r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(X3,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(X4,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(X4,k3_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X0,k3_xboole_0(X3,k1_xboole_0))))),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_52404,c_50179]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_56513,plain,
% 11.87/2.00      ( r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(X3,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(X4,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(X2,k3_xboole_0(X1,k3_xboole_0(X3,k1_xboole_0)))),X4),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_0,c_52420]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_58963,plain,
% 11.87/2.00      ( r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(X3,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(X4,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(X2,k3_xboole_0(k3_xboole_0(X3,k1_xboole_0),X1))),X4),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_0,c_56513]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_48689,plain,
% 11.87/2.00      ( r1_tarski(k3_xboole_0(sK1,sK2),X0) != iProver_top
% 11.87/2.00      | r1_tarski(sK0,X1) != iProver_top
% 11.87/2.00      | r1_tarski(k1_xboole_0,k3_xboole_0(X1,X0)) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_133,c_48556]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_48777,plain,
% 11.87/2.00      ( r1_tarski(sK0,X0) != iProver_top
% 11.87/2.00      | r1_tarski(k1_xboole_0,k3_xboole_0(X0,sK1)) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48557,c_48689]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_2138,plain,
% 11.87/2.00      ( k3_xboole_0(k3_xboole_0(X0,sK1),sK0) = k1_xboole_0 ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_997,c_2130]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_2460,plain,
% 11.87/2.00      ( r1_tarski(k1_xboole_0,k3_xboole_0(X0,sK1)) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_2138,c_922]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_48936,plain,
% 11.87/2.00      ( r1_tarski(k1_xboole_0,k3_xboole_0(X0,sK1)) = iProver_top ),
% 11.87/2.00      inference(global_propositional_subsumption,
% 11.87/2.00                [status(thm)],
% 11.87/2.00                [c_48777,c_2460]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_48941,plain,
% 11.87/2.00      ( r1_tarski(k1_xboole_0,k3_xboole_0(sK1,X0)) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_0,c_48936]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_50019,plain,
% 11.87/2.00      ( k3_xboole_0(X0,X1) = k1_xboole_0
% 11.87/2.00      | r1_tarski(X0,X2) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(X0,X1),sK0) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48690,c_49542]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_50958,plain,
% 11.87/2.00      ( k3_xboole_0(X0,sK0) = k1_xboole_0
% 11.87/2.00      | r1_tarski(X0,X1) != iProver_top
% 11.87/2.00      | r1_tarski(sK0,sK1) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48623,c_50019]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_56701,plain,
% 11.87/2.00      ( k3_xboole_0(k1_xboole_0,sK0) = k1_xboole_0
% 11.87/2.00      | r1_tarski(sK0,sK1) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48941,c_50958]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_56689,plain,
% 11.87/2.00      ( k3_xboole_0(k3_xboole_0(X0,X1),sK0) = k1_xboole_0
% 11.87/2.00      | r1_tarski(sK0,sK1) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48623,c_50958]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_56076,plain,
% 11.87/2.00      ( r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X3,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(X4,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(X5,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(k3_xboole_0(k3_xboole_0(X3,k3_xboole_0(X0,k3_xboole_0(X4,k3_xboole_0(sK0,X2)))),X1),X5),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_0,c_53073]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_56073,plain,
% 11.87/2.00      ( r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X3,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(X4,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(X5,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(k3_xboole_0(k3_xboole_0(X3,k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(X1,sK0),X4))),X2),X5),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_0,c_53073]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_56070,plain,
% 11.87/2.00      ( r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X3,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(X4,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(X5,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(k3_xboole_0(k3_xboole_0(X3,k3_xboole_0(k3_xboole_0(X4,k3_xboole_0(X0,sK0)),X2)),X1),X5),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_0,c_53073]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_55220,plain,
% 11.87/2.00      ( k3_xboole_0(sK0,k1_xboole_0) = k1_xboole_0
% 11.87/2.00      | r1_tarski(sK0,sK1) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48941,c_50658]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_55208,plain,
% 11.87/2.00      ( k3_xboole_0(sK0,k3_xboole_0(X0,X1)) = k1_xboole_0
% 11.87/2.00      | r1_tarski(sK0,sK1) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48623,c_50658]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_56067,plain,
% 11.87/2.00      ( r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X3,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(X4,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(X5,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(X3,k3_xboole_0(X1,sK0))),X4),X2),X5),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_0,c_53073]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_53087,plain,
% 11.87/2.00      ( r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(X3,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(X2,k3_xboole_0(k3_xboole_0(X3,k3_xboole_0(X0,k1_xboole_0)),X1)),k1_xboole_0) = iProver_top
% 11.87/2.00      | r1_tarski(sK1,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(sK0,sK0) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_49550,c_51845]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_51481,plain,
% 11.87/2.00      ( r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(X1,k3_xboole_0(k1_xboole_0,X0)),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48941,c_50182]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_53657,plain,
% 11.87/2.00      ( r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(k3_xboole_0(k1_xboole_0,X0),X1),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_0,c_51481]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_49554,plain,
% 11.87/2.00      ( r1_tarski(X0,k3_xboole_0(sK1,X1)) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(X0,X2),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_49520,c_48556]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_50287,plain,
% 11.87/2.00      ( r1_tarski(X0,X1) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X3,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(k3_xboole_0(X0,X2),X3),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48690,c_49554]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_53944,plain,
% 11.87/2.00      ( r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(k3_xboole_0(k3_xboole_0(X2,X3),X0),X1),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48623,c_50287]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_52411,plain,
% 11.87/2.00      ( r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,k1_xboole_0)),X2),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_0,c_52404]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_52894,plain,
% 11.87/2.00      ( r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(k3_xboole_0(k3_xboole_0(X1,k1_xboole_0),X0),X2),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_0,c_52411]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_54434,plain,
% 11.87/2.00      ( r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(k3_xboole_0(k3_xboole_0(k1_xboole_0,X1),X0),X2),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_0,c_52894]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_52414,plain,
% 11.87/2.00      ( r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(X1,k3_xboole_0(k3_xboole_0(X2,k1_xboole_0),X0)),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_0,c_52404]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_52994,plain,
% 11.87/2.00      ( r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(X1,k3_xboole_0(k3_xboole_0(k1_xboole_0,X2),X0)),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_0,c_52414]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_52897,plain,
% 11.87/2.00      ( r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X1)),X2),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_0,c_52411]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_50284,plain,
% 11.87/2.00      ( r1_tarski(X0,X1) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X3,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(k3_xboole_0(X2,X0),X3),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48556,c_49554]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_52510,plain,
% 11.87/2.00      ( r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(k3_xboole_0(X0,k1_xboole_0),X1),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48941,c_50284]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_52498,plain,
% 11.87/2.00      ( r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(X2,X3)),X1),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48623,c_50284]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_51846,plain,
% 11.87/2.00      ( r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X3,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(X4,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(X5,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(X5,k3_xboole_0(X2,k3_xboole_0(X4,k3_xboole_0(X0,k3_xboole_0(X3,k3_xboole_0(X1,sK0)))))),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_51341,c_50179]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_53357,plain,
% 11.87/2.00      ( r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(X3,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(X2,k3_xboole_0(X0,k3_xboole_0(X3,k3_xboole_0(X1,k1_xboole_0)))),k1_xboole_0) = iProver_top
% 11.87/2.00      | r1_tarski(sK1,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(sK0,sK0) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_49550,c_51846]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_53343,plain,
% 11.87/2.00      ( r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X3,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(X4,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(X5,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(X3,k3_xboole_0(X1,k3_xboole_0(X4,k3_xboole_0(X2,sK0))))),X5),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_0,c_51846]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_52417,plain,
% 11.87/2.00      ( r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(X1,k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X2))),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_0,c_52404]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_52097,plain,
% 11.87/2.00      ( r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X3,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(X4,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(X5,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(X5,k3_xboole_0(X2,k3_xboole_0(X4,k3_xboole_0(X0,k3_xboole_0(X3,k3_xboole_0(sK0,X1)))))),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_51443,c_50179]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_52096,plain,
% 11.87/2.00      ( r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X3,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(X4,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(X5,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(X5,k3_xboole_0(k3_xboole_0(X4,k3_xboole_0(X0,k3_xboole_0(X3,k3_xboole_0(sK0,X1)))),X2)),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_51443,c_50182]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_51333,plain,
% 11.87/2.00      ( r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(k3_xboole_0(X0,sK0),X1),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_0,c_51108]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_51392,plain,
% 11.87/2.00      ( r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(X3,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(X3,k3_xboole_0(X1,k3_xboole_0(k3_xboole_0(X0,sK0),X2))),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_51333,c_50179]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_51978,plain,
% 11.87/2.00      ( r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X3,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(X4,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(X5,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(X5,k3_xboole_0(X2,k3_xboole_0(X4,k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(X1,sK0),X3))))),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_51392,c_50179]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_51977,plain,
% 11.87/2.00      ( r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X3,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(X4,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(X5,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(X5,k3_xboole_0(k3_xboole_0(X4,k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(X1,sK0),X3))),X2)),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_51392,c_50182]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_51834,plain,
% 11.87/2.00      ( r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(X3,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(X2,k3_xboole_0(k3_xboole_0(X3,k3_xboole_0(X0,sK0)),X1)),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_0,c_51341]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_52325,plain,
% 11.87/2.00      ( r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X3,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(X4,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(X5,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(X5,k3_xboole_0(k3_xboole_0(X3,k3_xboole_0(k3_xboole_0(X4,k3_xboole_0(X1,sK0)),X0)),X2)),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_51834,c_50182]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_51966,plain,
% 11.87/2.00      ( r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(X3,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(X2,k3_xboole_0(k3_xboole_0(k3_xboole_0(X0,sK0),X3),X1)),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_0,c_51392]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_52185,plain,
% 11.87/2.00      ( r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X3,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(X4,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(X5,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(X5,k3_xboole_0(k3_xboole_0(k3_xboole_0(X1,k3_xboole_0(X3,k3_xboole_0(X0,sK0))),X4),X2)),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_51831,c_50182]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_52082,plain,
% 11.87/2.00      ( r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(X3,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(X2,k3_xboole_0(sK0,X1))),X3),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_0,c_51443]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_51963,plain,
% 11.87/2.00      ( r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(X3,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(k3_xboole_0(X1,k3_xboole_0(k3_xboole_0(X0,sK0),X2)),X3),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_0,c_51392]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_51387,plain,
% 11.87/2.00      ( r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(k3_xboole_0(sK0,X0),X1),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_0,c_51333]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_51784,plain,
% 11.87/2.00      ( r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(X3,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(X3,k3_xboole_0(k3_xboole_0(k3_xboole_0(sK0,X0),X2),X1)),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_51387,c_50182]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_51469,plain,
% 11.87/2.00      ( r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(X1,k3_xboole_0(k3_xboole_0(X2,X3),X0)),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48623,c_50182]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_51785,plain,
% 11.87/2.00      ( r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(X3,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(X3,k3_xboole_0(X1,k3_xboole_0(k3_xboole_0(sK0,X0),X2))),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_51387,c_50179]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_51123,plain,
% 11.87/2.00      ( r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(X1,k3_xboole_0(X0,k1_xboole_0)),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48941,c_50179]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_51111,plain,
% 11.87/2.00      ( r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(X1,k3_xboole_0(X0,k3_xboole_0(X2,X3))),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48623,c_50179]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_49832,plain,
% 11.87/2.00      ( k1_xboole_0 = X0
% 11.87/2.00      | r1_tarski(X0,k3_xboole_0(X1,sK1)) != iProver_top
% 11.87/2.00      | r1_tarski(X0,sK0) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_49521,c_48553]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_50066,plain,
% 11.87/2.00      ( k3_xboole_0(X0,k3_xboole_0(X1,sK1)) = k1_xboole_0
% 11.87/2.00      | r1_tarski(k3_xboole_0(X0,k3_xboole_0(X1,sK1)),sK0) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48623,c_49832]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_50632,plain,
% 11.87/2.00      ( k3_xboole_0(X0,k3_xboole_0(X1,sK1)) = k1_xboole_0
% 11.87/2.00      | r1_tarski(k3_xboole_0(k3_xboole_0(X1,sK1),X0),sK0) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_0,c_50066]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_51058,plain,
% 11.87/2.00      ( k3_xboole_0(X0,k3_xboole_0(X1,sK1)) = k1_xboole_0
% 11.87/2.00      | r1_tarski(k3_xboole_0(k3_xboole_0(sK1,X1),X0),sK0) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_0,c_50632]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_50959,plain,
% 11.87/2.00      ( k3_xboole_0(X0,X1) = k1_xboole_0
% 11.87/2.00      | r1_tarski(X0,X2) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(X1,X0),sK0) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_0,c_50019]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_50064,plain,
% 11.87/2.00      ( k3_xboole_0(k3_xboole_0(X0,sK1),X1) = k1_xboole_0
% 11.87/2.00      | r1_tarski(k3_xboole_0(k3_xboole_0(X0,sK1),X1),sK0) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48557,c_49832]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_50604,plain,
% 11.87/2.00      ( k3_xboole_0(k3_xboole_0(X0,sK1),X1) = k1_xboole_0
% 11.87/2.00      | r1_tarski(k3_xboole_0(X1,k3_xboole_0(X0,sK1)),sK0) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_0,c_50064]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_51015,plain,
% 11.87/2.00      ( k3_xboole_0(k3_xboole_0(X0,sK1),X1) = k1_xboole_0
% 11.87/2.00      | r1_tarski(k3_xboole_0(X1,k3_xboole_0(sK1,X0)),sK0) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_0,c_50604]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_50660,plain,
% 11.87/2.00      ( k3_xboole_0(X0,X1) = k1_xboole_0
% 11.87/2.00      | r1_tarski(X1,X2) != iProver_top
% 11.87/2.00      | r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(X1,X0),sK0) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_0,c_50016]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_50636,plain,
% 11.87/2.00      ( k3_xboole_0(X0,k3_xboole_0(X1,sK1)) = k1_xboole_0
% 11.87/2.00      | r1_tarski(k3_xboole_0(X0,k3_xboole_0(sK1,X1)),sK0) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_0,c_50066]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_50608,plain,
% 11.87/2.00      ( k3_xboole_0(k3_xboole_0(X0,sK1),X1) = k1_xboole_0
% 11.87/2.00      | r1_tarski(k3_xboole_0(k3_xboole_0(sK1,X0),X1),sK0) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_0,c_50064]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_49845,plain,
% 11.87/2.00      ( r1_tarski(X0,k3_xboole_0(X1,sK1)) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(X0,X2),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_49521,c_48556]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_50540,plain,
% 11.87/2.00      ( r1_tarski(X0,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(k3_xboole_0(X1,k3_xboole_0(X2,sK1)),X0),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48623,c_49845]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_50538,plain,
% 11.87/2.00      ( r1_tarski(X0,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(k3_xboole_0(k3_xboole_0(X1,sK1),X2),X0),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48557,c_49845]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_49844,plain,
% 11.87/2.00      ( r1_tarski(X0,k3_xboole_0(X1,sK1)) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(X2,X0),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_49521,c_48690]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_50505,plain,
% 11.87/2.00      ( r1_tarski(X0,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X2,sK1))),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48623,c_49844]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_50503,plain,
% 11.87/2.00      ( r1_tarski(X0,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(X1,sK1),X2)),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48557,c_49844]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_50018,plain,
% 11.87/2.00      ( k3_xboole_0(X0,k3_xboole_0(sK1,X1)) = k1_xboole_0
% 11.87/2.00      | r1_tarski(k3_xboole_0(X0,k3_xboole_0(sK1,X1)),sK0) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48623,c_49542]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_50575,plain,
% 11.87/2.00      ( k3_xboole_0(X0,k3_xboole_0(sK1,X1)) = k1_xboole_0
% 11.87/2.00      | r1_tarski(k3_xboole_0(k3_xboole_0(sK1,X1),X0),sK0) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_0,c_50018]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_50731,plain,
% 11.87/2.00      ( k3_xboole_0(X0,k3_xboole_0(sK1,X1)) = k1_xboole_0
% 11.87/2.00      | r1_tarski(k3_xboole_0(k3_xboole_0(X1,sK1),X0),sK0) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_0,c_50575]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_50580,plain,
% 11.87/2.00      ( k3_xboole_0(X0,k3_xboole_0(sK1,X1)) = k1_xboole_0
% 11.87/2.00      | r1_tarski(k3_xboole_0(X0,k3_xboole_0(X1,sK1)),sK0) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_0,c_50018]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_49551,plain,
% 11.87/2.00      ( r1_tarski(k3_xboole_0(sK1,X0),X1) != iProver_top
% 11.87/2.00      | r1_tarski(sK0,X2) != iProver_top
% 11.87/2.00      | r1_tarski(k1_xboole_0,k3_xboole_0(X2,X1)) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_49520,c_48690]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_50098,plain,
% 11.87/2.00      ( r1_tarski(sK0,X0) != iProver_top
% 11.87/2.00      | r1_tarski(k1_xboole_0,k3_xboole_0(X0,X1)) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48623,c_49551]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_50364,plain,
% 11.87/2.00      ( r1_tarski(sK0,k3_xboole_0(X0,sK1)) != iProver_top
% 11.87/2.00      | r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_49521,c_50098]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_50363,plain,
% 11.87/2.00      ( r1_tarski(sK0,k3_xboole_0(sK1,X0)) != iProver_top
% 11.87/2.00      | r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_49520,c_50098]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_50286,plain,
% 11.87/2.00      ( r1_tarski(X0,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(k3_xboole_0(X1,k3_xboole_0(sK1,X2)),X0),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48623,c_49554]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_50283,plain,
% 11.87/2.00      ( r1_tarski(X0,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(k3_xboole_0(k3_xboole_0(sK1,X1),X2),X0),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48557,c_49554]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_50181,plain,
% 11.87/2.00      ( r1_tarski(X0,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(sK1,X2))),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48623,c_49553]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_50178,plain,
% 11.87/2.00      ( r1_tarski(X0,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(sK1,X1),X2)),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48557,c_49553]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_48778,plain,
% 11.87/2.00      ( r1_tarski(sK2,X0) != iProver_top
% 11.87/2.00      | r1_tarski(sK1,X1) != iProver_top
% 11.87/2.00      | r1_tarski(sK0,X2) != iProver_top
% 11.87/2.00      | r1_tarski(k1_xboole_0,k3_xboole_0(X2,k3_xboole_0(X1,X0))) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48556,c_48689]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_49230,plain,
% 11.87/2.00      ( r1_tarski(sK2,k3_xboole_0(sK1,sK2)) != iProver_top
% 11.87/2.00      | r1_tarski(sK1,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(sK0,X0) != iProver_top
% 11.87/2.00      | r1_tarski(k1_xboole_0,k3_xboole_0(X0,k1_xboole_0)) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_133,c_48778]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_1067,plain,
% 11.87/2.00      ( r1_tarski(X0,k3_xboole_0(sK1,sK2)) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(X1,X0),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_133,c_921]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_1200,plain,
% 11.87/2.00      ( r1_tarski(X0,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(sK1,sK2))),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_997,c_1067]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_2201,plain,
% 11.87/2.00      ( r1_tarski(k3_xboole_0(sK1,X0),X1) != iProver_top
% 11.87/2.00      | r1_tarski(sK0,X2) != iProver_top
% 11.87/2.00      | r1_tarski(k1_xboole_0,k3_xboole_0(X2,X1)) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_2137,c_1065]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_3188,plain,
% 11.87/2.00      ( r1_tarski(sK1,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(sK0,X0) != iProver_top
% 11.87/2.00      | r1_tarski(k1_xboole_0,k3_xboole_0(X0,k1_xboole_0)) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_1200,c_2201]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_49384,plain,
% 11.87/2.00      ( r1_tarski(sK1,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(sK0,X0) != iProver_top
% 11.87/2.00      | r1_tarski(k1_xboole_0,k3_xboole_0(X0,k1_xboole_0)) = iProver_top ),
% 11.87/2.00      inference(global_propositional_subsumption,
% 11.87/2.00                [status(thm)],
% 11.87/2.00                [c_49230,c_3188]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_49391,plain,
% 11.87/2.00      ( r1_tarski(sK1,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(sK0,X0) != iProver_top
% 11.87/2.00      | r1_tarski(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_0,c_49384]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_49552,plain,
% 11.87/2.00      ( r1_tarski(k3_xboole_0(sK1,X0),X1) != iProver_top
% 11.87/2.00      | r1_tarski(sK0,X2) != iProver_top
% 11.87/2.00      | r1_tarski(k1_xboole_0,k3_xboole_0(X1,X2)) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_49520,c_48556]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_50138,plain,
% 11.87/2.00      ( r1_tarski(sK0,X0) != iProver_top
% 11.87/2.00      | r1_tarski(k1_xboole_0,k3_xboole_0(X1,X0)) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48623,c_49552]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_50015,plain,
% 11.87/2.00      ( k3_xboole_0(k3_xboole_0(sK1,X0),X1) = k1_xboole_0
% 11.87/2.00      | r1_tarski(k3_xboole_0(k3_xboole_0(sK1,X0),X1),sK0) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48557,c_49542]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_50428,plain,
% 11.87/2.00      ( k3_xboole_0(k3_xboole_0(sK1,X0),X1) = k1_xboole_0
% 11.87/2.00      | r1_tarski(k3_xboole_0(X1,k3_xboole_0(sK1,X0)),sK0) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_0,c_50015]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_50466,plain,
% 11.87/2.00      ( k3_xboole_0(k3_xboole_0(sK1,X0),X1) = k1_xboole_0
% 11.87/2.00      | r1_tarski(k3_xboole_0(X1,k3_xboole_0(X0,sK1)),sK0) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_0,c_50428]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_50433,plain,
% 11.87/2.00      ( k3_xboole_0(k3_xboole_0(sK1,X0),X1) = k1_xboole_0
% 11.87/2.00      | r1_tarski(k3_xboole_0(k3_xboole_0(X0,sK1),X1),sK0) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_0,c_50015]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_49842,plain,
% 11.87/2.00      ( r1_tarski(k3_xboole_0(X0,sK1),X1) != iProver_top
% 11.87/2.00      | r1_tarski(sK0,X2) != iProver_top
% 11.87/2.00      | r1_tarski(k1_xboole_0,k3_xboole_0(X2,X1)) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_49521,c_48690]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_49549,plain,
% 11.87/2.00      ( r1_tarski(sK2,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(sK1,k3_xboole_0(sK1,X0)) != iProver_top
% 11.87/2.00      | r1_tarski(sK0,X1) != iProver_top
% 11.87/2.00      | r1_tarski(k1_xboole_0,k3_xboole_0(X1,k1_xboole_0)) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_49520,c_48778]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_49799,plain,
% 11.87/2.00      ( r1_tarski(sK2,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(sK1,k3_xboole_0(X0,sK1)) != iProver_top
% 11.87/2.00      | r1_tarski(sK0,X1) != iProver_top
% 11.87/2.00      | r1_tarski(k1_xboole_0,k3_xboole_0(X1,k1_xboole_0)) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_0,c_49549]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_48732,plain,
% 11.87/2.00      ( r1_tarski(k3_xboole_0(sK1,sK2),X0) != iProver_top
% 11.87/2.00      | r1_tarski(sK0,X1) != iProver_top
% 11.87/2.00      | r1_tarski(k1_xboole_0,k3_xboole_0(X0,X1)) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_133,c_48690]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_48857,plain,
% 11.87/2.00      ( r1_tarski(sK2,X0) != iProver_top
% 11.87/2.00      | r1_tarski(sK1,X1) != iProver_top
% 11.87/2.00      | r1_tarski(sK0,X2) != iProver_top
% 11.87/2.00      | r1_tarski(k1_xboole_0,k3_xboole_0(k3_xboole_0(X1,X0),X2)) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48556,c_48732]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_49545,plain,
% 11.87/2.00      ( r1_tarski(sK2,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(sK1,k3_xboole_0(sK1,X0)) != iProver_top
% 11.87/2.00      | r1_tarski(sK0,X1) != iProver_top
% 11.87/2.00      | r1_tarski(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_49520,c_48857]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_49773,plain,
% 11.87/2.00      ( r1_tarski(sK2,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(sK1,k3_xboole_0(X0,sK1)) != iProver_top
% 11.87/2.00      | r1_tarski(sK0,X1) != iProver_top
% 11.87/2.00      | r1_tarski(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_0,c_49545]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_49182,plain,
% 11.87/2.00      ( k3_xboole_0(X0,sK0) = k1_xboole_0
% 11.87/2.00      | r1_tarski(X0,sK2) != iProver_top
% 11.87/2.00      | r1_tarski(sK0,sK1) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48623,c_48736]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_49707,plain,
% 11.87/2.00      ( k3_xboole_0(k3_xboole_0(X0,sK2),sK0) = k1_xboole_0
% 11.87/2.00      | r1_tarski(sK0,sK1) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48623,c_49182]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_49705,plain,
% 11.87/2.00      ( k3_xboole_0(k3_xboole_0(sK2,X0),sK0) = k1_xboole_0
% 11.87/2.00      | r1_tarski(sK0,sK1) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48557,c_49182]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_49227,plain,
% 11.87/2.00      ( r1_tarski(sK2,sK2) != iProver_top
% 11.87/2.00      | r1_tarski(sK1,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(sK0,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_133,c_48778]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_1114,plain,
% 11.87/2.00      ( r1_tarski(X0,k3_xboole_0(sK1,sK2)) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(X0,X1),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_133,c_1065]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_1288,plain,
% 11.87/2.00      ( r1_tarski(X0,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(k3_xboole_0(X1,k3_xboole_0(sK1,sK2)),X0),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_997,c_1114]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_2212,plain,
% 11.87/2.00      ( r1_tarski(sK0,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_2137,c_1288]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_49367,plain,
% 11.87/2.00      ( r1_tarski(sK0,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(global_propositional_subsumption,
% 11.87/2.00                [status(thm)],
% 11.87/2.00                [c_49227,c_2212]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_48626,plain,
% 11.87/2.00      ( k3_xboole_0(k3_xboole_0(sK1,sK2),X0) = k1_xboole_0
% 11.87/2.00      | r1_tarski(k3_xboole_0(k3_xboole_0(sK1,sK2),X0),sK0) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48557,c_48552]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_48981,plain,
% 11.87/2.00      ( k3_xboole_0(k3_xboole_0(sK1,sK2),sK0) = k1_xboole_0 ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48623,c_48626]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_49468,plain,
% 11.87/2.00      ( r1_tarski(sK2,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(sK1,k3_xboole_0(sK1,sK2)) != iProver_top
% 11.87/2.00      | r1_tarski(sK0,X0) != iProver_top
% 11.87/2.00      | r1_tarski(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48981,c_48857]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_49147,plain,
% 11.87/2.00      ( k3_xboole_0(sK0,X0) = k1_xboole_0
% 11.87/2.00      | r1_tarski(X0,sK2) != iProver_top
% 11.87/2.00      | r1_tarski(sK0,sK1) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48557,c_48693]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_49338,plain,
% 11.87/2.00      ( k3_xboole_0(sK0,k3_xboole_0(X0,sK2)) = k1_xboole_0
% 11.87/2.00      | r1_tarski(sK0,sK1) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48623,c_49147]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_49337,plain,
% 11.87/2.00      ( k3_xboole_0(sK0,sK0) = k1_xboole_0
% 11.87/2.00      | r1_tarski(sK0,sK1) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48555,c_49147]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_49336,plain,
% 11.87/2.00      ( k3_xboole_0(sK0,k3_xboole_0(sK2,X0)) = k1_xboole_0
% 11.87/2.00      | r1_tarski(sK0,sK1) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48557,c_49147]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_49231,plain,
% 11.87/2.00      ( r1_tarski(sK2,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(sK1,k3_xboole_0(sK1,sK2)) != iProver_top
% 11.87/2.00      | r1_tarski(sK0,X0) != iProver_top
% 11.87/2.00      | r1_tarski(k1_xboole_0,k3_xboole_0(X0,k1_xboole_0)) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48981,c_48778]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_49183,plain,
% 11.87/2.00      ( k3_xboole_0(X0,X1) = k1_xboole_0
% 11.87/2.00      | r1_tarski(X0,sK2) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(X1,X0),sK0) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_0,c_48736]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_49149,plain,
% 11.87/2.00      ( k3_xboole_0(X0,X1) = k1_xboole_0
% 11.87/2.00      | r1_tarski(X1,sK2) != iProver_top
% 11.87/2.00      | r1_tarski(X0,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(X1,X0),sK0) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_0,c_48693]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_48672,plain,
% 11.87/2.00      ( k3_xboole_0(X0,k3_xboole_0(sK1,sK2)) = k1_xboole_0
% 11.87/2.00      | r1_tarski(k3_xboole_0(X0,k3_xboole_0(sK1,sK2)),sK0) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48623,c_48552]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_49057,plain,
% 11.87/2.00      ( k3_xboole_0(X0,k3_xboole_0(sK1,sK2)) = k1_xboole_0
% 11.87/2.00      | r1_tarski(k3_xboole_0(k3_xboole_0(sK1,sK2),X0),sK0) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_0,c_48672]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_48982,plain,
% 11.87/2.00      ( k3_xboole_0(k3_xboole_0(sK1,sK2),X0) = k1_xboole_0
% 11.87/2.00      | r1_tarski(k3_xboole_0(X0,k3_xboole_0(sK1,sK2)),sK0) != iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_0,c_48626]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_48735,plain,
% 11.87/2.00      ( r1_tarski(X0,k3_xboole_0(sK1,sK2)) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(X0,X1),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_133,c_48690]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_48902,plain,
% 11.87/2.00      ( r1_tarski(X0,sK2) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(k3_xboole_0(X0,X1),X2),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48690,c_48735]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_48901,plain,
% 11.87/2.00      ( r1_tarski(X0,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(k3_xboole_0(X1,k3_xboole_0(sK1,sK2)),X0),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48623,c_48735]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_48899,plain,
% 11.87/2.00      ( r1_tarski(X0,sK2) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(k3_xboole_0(X1,X0),X2),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48556,c_48735]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_48898,plain,
% 11.87/2.00      ( r1_tarski(X0,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(k3_xboole_0(k3_xboole_0(sK1,sK2),X1),X0),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48557,c_48735]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_48859,plain,
% 11.87/2.00      ( r1_tarski(sK2,X0) != iProver_top
% 11.87/2.00      | r1_tarski(sK1,X1) != iProver_top
% 11.87/2.00      | r1_tarski(sK0,X2) != iProver_top
% 11.87/2.00      | r1_tarski(k1_xboole_0,k3_xboole_0(k3_xboole_0(X0,X1),X2)) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48690,c_48732]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_48858,plain,
% 11.87/2.00      ( r1_tarski(sK0,X0) != iProver_top
% 11.87/2.00      | r1_tarski(k1_xboole_0,k3_xboole_0(sK2,X0)) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48623,c_48732]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_48692,plain,
% 11.87/2.00      ( r1_tarski(X0,k3_xboole_0(sK1,sK2)) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(X1,X0),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_133,c_48556]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_48817,plain,
% 11.87/2.00      ( r1_tarski(X0,sK2) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(X2,k3_xboole_0(X0,X1)),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48690,c_48692]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_48816,plain,
% 11.87/2.00      ( r1_tarski(X0,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(sK1,sK2))),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48623,c_48692]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_48814,plain,
% 11.87/2.00      ( r1_tarski(X0,sK2) != iProver_top
% 11.87/2.00      | r1_tarski(X1,sK1) != iProver_top
% 11.87/2.00      | r1_tarski(X2,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(X2,k3_xboole_0(X1,X0)),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48556,c_48692]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_48813,plain,
% 11.87/2.00      ( r1_tarski(X0,sK0) != iProver_top
% 11.87/2.00      | r1_tarski(k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(sK1,sK2),X1)),k1_xboole_0) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48557,c_48692]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_48780,plain,
% 11.87/2.00      ( r1_tarski(sK2,X0) != iProver_top
% 11.87/2.00      | r1_tarski(sK1,X1) != iProver_top
% 11.87/2.00      | r1_tarski(sK0,X2) != iProver_top
% 11.87/2.00      | r1_tarski(k1_xboole_0,k3_xboole_0(X2,k3_xboole_0(X0,X1))) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48690,c_48689]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_48779,plain,
% 11.87/2.00      ( r1_tarski(sK0,X0) != iProver_top
% 11.87/2.00      | r1_tarski(k1_xboole_0,k3_xboole_0(X0,sK2)) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_48623,c_48689]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_48671,plain,
% 11.87/2.00      ( r1_tarski(k1_xboole_0,k3_xboole_0(sK1,sK2)) = iProver_top ),
% 11.87/2.00      inference(superposition,[status(thm)],[c_133,c_48623]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_8,negated_conjecture,
% 11.87/2.00      ( ~ r1_xboole_0(sK0,sK1) ),
% 11.87/2.00      inference(cnf_transformation,[],[f22]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_157,plain,
% 11.87/2.00      ( k3_xboole_0(sK1,sK2) != sK1 | sK0 != sK0 ),
% 11.87/2.00      inference(resolution_lifted,[status(thm)],[c_6,c_8]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_197,plain,
% 11.87/2.00      ( k3_xboole_0(sK1,sK2) != sK1 ),
% 11.87/2.00      inference(equality_resolution_simp,[status(thm)],[c_157]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_137,plain,
% 11.87/2.00      ( k3_xboole_0(X0,X1) != k1_xboole_0 | sK1 != X1 | sK0 != X0 ),
% 11.87/2.00      inference(resolution_lifted,[status(thm)],[c_62,c_8]) ).
% 11.87/2.00  
% 11.87/2.00  cnf(c_138,plain,
% 11.87/2.00      ( k3_xboole_0(sK0,sK1) != k1_xboole_0 ),
% 11.87/2.00      inference(unflattening,[status(thm)],[c_137]) ).
% 11.87/2.00  
% 11.87/2.00  
% 11.87/2.00  % SZS output end Saturation for theBenchmark.p
% 11.87/2.00  
% 11.87/2.00  ------                               Statistics
% 11.87/2.00  
% 11.87/2.00  ------ Selected
% 11.87/2.00  
% 11.87/2.00  total_time:                             1.478
% 11.87/2.00  
%------------------------------------------------------------------------------
