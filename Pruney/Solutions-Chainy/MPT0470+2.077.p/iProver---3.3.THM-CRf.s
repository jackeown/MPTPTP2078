%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:44:08 EST 2020

% Result     : Theorem 1.29s
% Output     : CNFRefutation 1.29s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 225 expanded)
%              Number of clauses        :   58 ( 106 expanded)
%              Number of leaves         :   14 (  43 expanded)
%              Depth                    :   17
%              Number of atoms          :  224 ( 492 expanded)
%              Number of equality atoms :  117 ( 246 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f18,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f12,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f25,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f26,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).

fof(f40,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f11,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f32,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f34,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f39,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f41,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_367,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_13,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_362,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_11,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_8,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_364,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1410,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_364])).

cnf(c_4,plain,
    ( v1_relat_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_30,plain,
    ( v1_relat_1(X0) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_32,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_38,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1537,plain,
    ( v1_relat_1(X0) != iProver_top
    | r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1410,c_32,c_38])).

cnf(c_1538,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1537])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_369,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1543,plain,
    ( k3_xboole_0(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1538,c_369])).

cnf(c_3,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_1544,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1543,c_3])).

cnf(c_1552,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_362,c_1544])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_366,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(k1_relat_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1627,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) != iProver_top
    | v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1552,c_366])).

cnf(c_1715,plain,
    ( v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) = iProver_top
    | v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1627,c_38])).

cnf(c_1716,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) != iProver_top
    | v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_1715])).

cnf(c_1721,plain,
    ( v1_relat_1(sK0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top
    | v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_367,c_1716])).

cnf(c_14,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1762,plain,
    ( v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1721,c_14,c_32,c_38])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_370,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1768,plain,
    ( k5_relat_1(k1_xboole_0,sK0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1762,c_370])).

cnf(c_10,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_9,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_363,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_619,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10,c_363])).

cnf(c_1060,plain,
    ( v1_relat_1(X0) != iProver_top
    | r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_619,c_32,c_38])).

cnf(c_1061,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1060])).

cnf(c_1066,plain,
    ( k3_xboole_0(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) = k2_relat_1(k5_relat_1(X0,k1_xboole_0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1061,c_369])).

cnf(c_1067,plain,
    ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1066,c_3])).

cnf(c_1075,plain,
    ( k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_362,c_1067])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_365,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(k2_relat_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1161,plain,
    ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) != iProver_top
    | v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1075,c_365])).

cnf(c_472,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))
    | ~ v1_xboole_0(k2_relat_1(k5_relat_1(sK0,k1_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_476,plain,
    ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) != iProver_top
    | v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) = iProver_top
    | v1_xboole_0(k2_relat_1(k5_relat_1(sK0,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_472])).

cnf(c_572,plain,
    ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_573,plain,
    ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) = iProver_top
    | v1_relat_1(sK0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_572])).

cnf(c_161,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_875,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_relat_1(k5_relat_1(sK0,k1_xboole_0)))
    | k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) != X0 ),
    inference(instantiation,[status(thm)],[c_161])).

cnf(c_876,plain,
    ( k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) != X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_relat_1(k5_relat_1(sK0,k1_xboole_0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_875])).

cnf(c_878,plain,
    ( k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) != k1_xboole_0
    | v1_xboole_0(k2_relat_1(k5_relat_1(sK0,k1_xboole_0))) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_876])).

cnf(c_1266,plain,
    ( v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1161,c_14,c_32,c_38,c_476,c_573,c_878,c_1075])).

cnf(c_1272,plain,
    ( k5_relat_1(sK0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1266,c_370])).

cnf(c_12,negated_conjecture,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1602,plain,
    ( k5_relat_1(k1_xboole_0,sK0) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1272,c_12])).

cnf(c_1603,plain,
    ( k5_relat_1(k1_xboole_0,sK0) != k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_1602])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1768,c_1603])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:11:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 1.29/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.29/1.00  
% 1.29/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.29/1.00  
% 1.29/1.00  ------  iProver source info
% 1.29/1.00  
% 1.29/1.00  git: date: 2020-06-30 10:37:57 +0100
% 1.29/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.29/1.00  git: non_committed_changes: false
% 1.29/1.00  git: last_make_outside_of_git: false
% 1.29/1.00  
% 1.29/1.00  ------ 
% 1.29/1.00  
% 1.29/1.00  ------ Input Options
% 1.29/1.00  
% 1.29/1.00  --out_options                           all
% 1.29/1.00  --tptp_safe_out                         true
% 1.29/1.00  --problem_path                          ""
% 1.29/1.00  --include_path                          ""
% 1.29/1.00  --clausifier                            res/vclausify_rel
% 1.29/1.00  --clausifier_options                    --mode clausify
% 1.29/1.00  --stdin                                 false
% 1.29/1.00  --stats_out                             all
% 1.29/1.00  
% 1.29/1.00  ------ General Options
% 1.29/1.00  
% 1.29/1.00  --fof                                   false
% 1.29/1.00  --time_out_real                         305.
% 1.29/1.00  --time_out_virtual                      -1.
% 1.29/1.00  --symbol_type_check                     false
% 1.29/1.00  --clausify_out                          false
% 1.29/1.00  --sig_cnt_out                           false
% 1.29/1.00  --trig_cnt_out                          false
% 1.29/1.00  --trig_cnt_out_tolerance                1.
% 1.29/1.00  --trig_cnt_out_sk_spl                   false
% 1.29/1.00  --abstr_cl_out                          false
% 1.29/1.00  
% 1.29/1.00  ------ Global Options
% 1.29/1.00  
% 1.29/1.00  --schedule                              default
% 1.29/1.00  --add_important_lit                     false
% 1.29/1.00  --prop_solver_per_cl                    1000
% 1.29/1.00  --min_unsat_core                        false
% 1.29/1.00  --soft_assumptions                      false
% 1.29/1.00  --soft_lemma_size                       3
% 1.29/1.00  --prop_impl_unit_size                   0
% 1.29/1.00  --prop_impl_unit                        []
% 1.29/1.00  --share_sel_clauses                     true
% 1.29/1.00  --reset_solvers                         false
% 1.29/1.00  --bc_imp_inh                            [conj_cone]
% 1.29/1.00  --conj_cone_tolerance                   3.
% 1.29/1.00  --extra_neg_conj                        none
% 1.29/1.00  --large_theory_mode                     true
% 1.29/1.00  --prolific_symb_bound                   200
% 1.29/1.00  --lt_threshold                          2000
% 1.29/1.00  --clause_weak_htbl                      true
% 1.29/1.00  --gc_record_bc_elim                     false
% 1.29/1.00  
% 1.29/1.00  ------ Preprocessing Options
% 1.29/1.00  
% 1.29/1.00  --preprocessing_flag                    true
% 1.29/1.00  --time_out_prep_mult                    0.1
% 1.29/1.00  --splitting_mode                        input
% 1.29/1.00  --splitting_grd                         true
% 1.29/1.00  --splitting_cvd                         false
% 1.29/1.00  --splitting_cvd_svl                     false
% 1.29/1.00  --splitting_nvd                         32
% 1.29/1.00  --sub_typing                            true
% 1.29/1.00  --prep_gs_sim                           true
% 1.29/1.00  --prep_unflatten                        true
% 1.29/1.00  --prep_res_sim                          true
% 1.29/1.00  --prep_upred                            true
% 1.29/1.00  --prep_sem_filter                       exhaustive
% 1.29/1.00  --prep_sem_filter_out                   false
% 1.29/1.00  --pred_elim                             true
% 1.29/1.00  --res_sim_input                         true
% 1.29/1.00  --eq_ax_congr_red                       true
% 1.29/1.00  --pure_diseq_elim                       true
% 1.29/1.00  --brand_transform                       false
% 1.29/1.00  --non_eq_to_eq                          false
% 1.29/1.00  --prep_def_merge                        true
% 1.29/1.00  --prep_def_merge_prop_impl              false
% 1.29/1.00  --prep_def_merge_mbd                    true
% 1.29/1.00  --prep_def_merge_tr_red                 false
% 1.29/1.00  --prep_def_merge_tr_cl                  false
% 1.29/1.00  --smt_preprocessing                     true
% 1.29/1.00  --smt_ac_axioms                         fast
% 1.29/1.00  --preprocessed_out                      false
% 1.29/1.00  --preprocessed_stats                    false
% 1.29/1.00  
% 1.29/1.00  ------ Abstraction refinement Options
% 1.29/1.00  
% 1.29/1.00  --abstr_ref                             []
% 1.29/1.00  --abstr_ref_prep                        false
% 1.29/1.00  --abstr_ref_until_sat                   false
% 1.29/1.00  --abstr_ref_sig_restrict                funpre
% 1.29/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.29/1.00  --abstr_ref_under                       []
% 1.29/1.00  
% 1.29/1.00  ------ SAT Options
% 1.29/1.00  
% 1.29/1.00  --sat_mode                              false
% 1.29/1.00  --sat_fm_restart_options                ""
% 1.29/1.00  --sat_gr_def                            false
% 1.29/1.00  --sat_epr_types                         true
% 1.29/1.00  --sat_non_cyclic_types                  false
% 1.29/1.00  --sat_finite_models                     false
% 1.29/1.00  --sat_fm_lemmas                         false
% 1.29/1.00  --sat_fm_prep                           false
% 1.29/1.00  --sat_fm_uc_incr                        true
% 1.29/1.00  --sat_out_model                         small
% 1.29/1.00  --sat_out_clauses                       false
% 1.29/1.00  
% 1.29/1.00  ------ QBF Options
% 1.29/1.00  
% 1.29/1.00  --qbf_mode                              false
% 1.29/1.00  --qbf_elim_univ                         false
% 1.29/1.00  --qbf_dom_inst                          none
% 1.29/1.00  --qbf_dom_pre_inst                      false
% 1.29/1.00  --qbf_sk_in                             false
% 1.29/1.00  --qbf_pred_elim                         true
% 1.29/1.00  --qbf_split                             512
% 1.29/1.00  
% 1.29/1.00  ------ BMC1 Options
% 1.29/1.00  
% 1.29/1.00  --bmc1_incremental                      false
% 1.29/1.00  --bmc1_axioms                           reachable_all
% 1.29/1.00  --bmc1_min_bound                        0
% 1.29/1.00  --bmc1_max_bound                        -1
% 1.29/1.00  --bmc1_max_bound_default                -1
% 1.29/1.00  --bmc1_symbol_reachability              true
% 1.29/1.00  --bmc1_property_lemmas                  false
% 1.29/1.00  --bmc1_k_induction                      false
% 1.29/1.00  --bmc1_non_equiv_states                 false
% 1.29/1.00  --bmc1_deadlock                         false
% 1.29/1.00  --bmc1_ucm                              false
% 1.29/1.00  --bmc1_add_unsat_core                   none
% 1.29/1.00  --bmc1_unsat_core_children              false
% 1.29/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.29/1.00  --bmc1_out_stat                         full
% 1.29/1.00  --bmc1_ground_init                      false
% 1.29/1.00  --bmc1_pre_inst_next_state              false
% 1.29/1.00  --bmc1_pre_inst_state                   false
% 1.29/1.00  --bmc1_pre_inst_reach_state             false
% 1.29/1.00  --bmc1_out_unsat_core                   false
% 1.29/1.00  --bmc1_aig_witness_out                  false
% 1.29/1.00  --bmc1_verbose                          false
% 1.29/1.00  --bmc1_dump_clauses_tptp                false
% 1.29/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.29/1.00  --bmc1_dump_file                        -
% 1.29/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.29/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.29/1.00  --bmc1_ucm_extend_mode                  1
% 1.29/1.00  --bmc1_ucm_init_mode                    2
% 1.29/1.00  --bmc1_ucm_cone_mode                    none
% 1.29/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.29/1.00  --bmc1_ucm_relax_model                  4
% 1.29/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.29/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.29/1.00  --bmc1_ucm_layered_model                none
% 1.29/1.00  --bmc1_ucm_max_lemma_size               10
% 1.29/1.00  
% 1.29/1.00  ------ AIG Options
% 1.29/1.00  
% 1.29/1.00  --aig_mode                              false
% 1.29/1.00  
% 1.29/1.00  ------ Instantiation Options
% 1.29/1.00  
% 1.29/1.00  --instantiation_flag                    true
% 1.29/1.00  --inst_sos_flag                         false
% 1.29/1.00  --inst_sos_phase                        true
% 1.29/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.29/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.29/1.00  --inst_lit_sel_side                     num_symb
% 1.29/1.00  --inst_solver_per_active                1400
% 1.29/1.00  --inst_solver_calls_frac                1.
% 1.29/1.00  --inst_passive_queue_type               priority_queues
% 1.29/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.29/1.00  --inst_passive_queues_freq              [25;2]
% 1.29/1.00  --inst_dismatching                      true
% 1.29/1.00  --inst_eager_unprocessed_to_passive     true
% 1.29/1.00  --inst_prop_sim_given                   true
% 1.29/1.00  --inst_prop_sim_new                     false
% 1.29/1.00  --inst_subs_new                         false
% 1.29/1.00  --inst_eq_res_simp                      false
% 1.29/1.00  --inst_subs_given                       false
% 1.29/1.00  --inst_orphan_elimination               true
% 1.29/1.00  --inst_learning_loop_flag               true
% 1.29/1.00  --inst_learning_start                   3000
% 1.29/1.00  --inst_learning_factor                  2
% 1.29/1.00  --inst_start_prop_sim_after_learn       3
% 1.29/1.00  --inst_sel_renew                        solver
% 1.29/1.00  --inst_lit_activity_flag                true
% 1.29/1.00  --inst_restr_to_given                   false
% 1.29/1.00  --inst_activity_threshold               500
% 1.29/1.00  --inst_out_proof                        true
% 1.29/1.00  
% 1.29/1.00  ------ Resolution Options
% 1.29/1.00  
% 1.29/1.00  --resolution_flag                       true
% 1.29/1.00  --res_lit_sel                           adaptive
% 1.29/1.00  --res_lit_sel_side                      none
% 1.29/1.00  --res_ordering                          kbo
% 1.29/1.00  --res_to_prop_solver                    active
% 1.29/1.00  --res_prop_simpl_new                    false
% 1.29/1.00  --res_prop_simpl_given                  true
% 1.29/1.00  --res_passive_queue_type                priority_queues
% 1.29/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.29/1.00  --res_passive_queues_freq               [15;5]
% 1.29/1.00  --res_forward_subs                      full
% 1.29/1.00  --res_backward_subs                     full
% 1.29/1.00  --res_forward_subs_resolution           true
% 1.29/1.00  --res_backward_subs_resolution          true
% 1.29/1.00  --res_orphan_elimination                true
% 1.29/1.00  --res_time_limit                        2.
% 1.29/1.00  --res_out_proof                         true
% 1.29/1.00  
% 1.29/1.00  ------ Superposition Options
% 1.29/1.00  
% 1.29/1.00  --superposition_flag                    true
% 1.29/1.00  --sup_passive_queue_type                priority_queues
% 1.29/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.29/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.29/1.00  --demod_completeness_check              fast
% 1.29/1.00  --demod_use_ground                      true
% 1.29/1.00  --sup_to_prop_solver                    passive
% 1.29/1.00  --sup_prop_simpl_new                    true
% 1.29/1.00  --sup_prop_simpl_given                  true
% 1.29/1.00  --sup_fun_splitting                     false
% 1.29/1.00  --sup_smt_interval                      50000
% 1.29/1.00  
% 1.29/1.00  ------ Superposition Simplification Setup
% 1.29/1.00  
% 1.29/1.00  --sup_indices_passive                   []
% 1.29/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.29/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.29/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.29/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.29/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.29/1.00  --sup_full_bw                           [BwDemod]
% 1.29/1.00  --sup_immed_triv                        [TrivRules]
% 1.29/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.29/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.29/1.00  --sup_immed_bw_main                     []
% 1.29/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.29/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.29/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.29/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.29/1.00  
% 1.29/1.00  ------ Combination Options
% 1.29/1.00  
% 1.29/1.00  --comb_res_mult                         3
% 1.29/1.00  --comb_sup_mult                         2
% 1.29/1.00  --comb_inst_mult                        10
% 1.29/1.00  
% 1.29/1.00  ------ Debug Options
% 1.29/1.00  
% 1.29/1.00  --dbg_backtrace                         false
% 1.29/1.00  --dbg_dump_prop_clauses                 false
% 1.29/1.00  --dbg_dump_prop_clauses_file            -
% 1.29/1.00  --dbg_out_stat                          false
% 1.29/1.00  ------ Parsing...
% 1.29/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.29/1.00  
% 1.29/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 1.29/1.00  
% 1.29/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.29/1.00  
% 1.29/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.29/1.00  ------ Proving...
% 1.29/1.00  ------ Problem Properties 
% 1.29/1.00  
% 1.29/1.00  
% 1.29/1.00  clauses                                 14
% 1.29/1.00  conjectures                             2
% 1.29/1.00  EPR                                     4
% 1.29/1.00  Horn                                    14
% 1.29/1.00  unary                                   5
% 1.29/1.00  binary                                  4
% 1.29/1.00  lits                                    28
% 1.29/1.00  lits eq                                 7
% 1.29/1.00  fd_pure                                 0
% 1.29/1.00  fd_pseudo                               0
% 1.29/1.00  fd_cond                                 1
% 1.29/1.00  fd_pseudo_cond                          0
% 1.29/1.00  AC symbols                              0
% 1.29/1.00  
% 1.29/1.00  ------ Schedule dynamic 5 is on 
% 1.29/1.00  
% 1.29/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.29/1.00  
% 1.29/1.00  
% 1.29/1.00  ------ 
% 1.29/1.00  Current options:
% 1.29/1.00  ------ 
% 1.29/1.00  
% 1.29/1.00  ------ Input Options
% 1.29/1.00  
% 1.29/1.00  --out_options                           all
% 1.29/1.00  --tptp_safe_out                         true
% 1.29/1.00  --problem_path                          ""
% 1.29/1.00  --include_path                          ""
% 1.29/1.00  --clausifier                            res/vclausify_rel
% 1.29/1.00  --clausifier_options                    --mode clausify
% 1.29/1.00  --stdin                                 false
% 1.29/1.00  --stats_out                             all
% 1.29/1.00  
% 1.29/1.00  ------ General Options
% 1.29/1.00  
% 1.29/1.00  --fof                                   false
% 1.29/1.00  --time_out_real                         305.
% 1.29/1.00  --time_out_virtual                      -1.
% 1.29/1.00  --symbol_type_check                     false
% 1.29/1.00  --clausify_out                          false
% 1.29/1.00  --sig_cnt_out                           false
% 1.29/1.00  --trig_cnt_out                          false
% 1.29/1.00  --trig_cnt_out_tolerance                1.
% 1.29/1.00  --trig_cnt_out_sk_spl                   false
% 1.29/1.00  --abstr_cl_out                          false
% 1.29/1.00  
% 1.29/1.00  ------ Global Options
% 1.29/1.00  
% 1.29/1.00  --schedule                              default
% 1.29/1.00  --add_important_lit                     false
% 1.29/1.00  --prop_solver_per_cl                    1000
% 1.29/1.00  --min_unsat_core                        false
% 1.29/1.00  --soft_assumptions                      false
% 1.29/1.00  --soft_lemma_size                       3
% 1.29/1.00  --prop_impl_unit_size                   0
% 1.29/1.00  --prop_impl_unit                        []
% 1.29/1.00  --share_sel_clauses                     true
% 1.29/1.00  --reset_solvers                         false
% 1.29/1.00  --bc_imp_inh                            [conj_cone]
% 1.29/1.00  --conj_cone_tolerance                   3.
% 1.29/1.00  --extra_neg_conj                        none
% 1.29/1.00  --large_theory_mode                     true
% 1.29/1.00  --prolific_symb_bound                   200
% 1.29/1.00  --lt_threshold                          2000
% 1.29/1.00  --clause_weak_htbl                      true
% 1.29/1.00  --gc_record_bc_elim                     false
% 1.29/1.00  
% 1.29/1.00  ------ Preprocessing Options
% 1.29/1.00  
% 1.29/1.00  --preprocessing_flag                    true
% 1.29/1.00  --time_out_prep_mult                    0.1
% 1.29/1.00  --splitting_mode                        input
% 1.29/1.00  --splitting_grd                         true
% 1.29/1.00  --splitting_cvd                         false
% 1.29/1.00  --splitting_cvd_svl                     false
% 1.29/1.00  --splitting_nvd                         32
% 1.29/1.00  --sub_typing                            true
% 1.29/1.00  --prep_gs_sim                           true
% 1.29/1.00  --prep_unflatten                        true
% 1.29/1.00  --prep_res_sim                          true
% 1.29/1.00  --prep_upred                            true
% 1.29/1.00  --prep_sem_filter                       exhaustive
% 1.29/1.00  --prep_sem_filter_out                   false
% 1.29/1.00  --pred_elim                             true
% 1.29/1.00  --res_sim_input                         true
% 1.29/1.00  --eq_ax_congr_red                       true
% 1.29/1.00  --pure_diseq_elim                       true
% 1.29/1.00  --brand_transform                       false
% 1.29/1.00  --non_eq_to_eq                          false
% 1.29/1.00  --prep_def_merge                        true
% 1.29/1.00  --prep_def_merge_prop_impl              false
% 1.29/1.00  --prep_def_merge_mbd                    true
% 1.29/1.00  --prep_def_merge_tr_red                 false
% 1.29/1.00  --prep_def_merge_tr_cl                  false
% 1.29/1.00  --smt_preprocessing                     true
% 1.29/1.00  --smt_ac_axioms                         fast
% 1.29/1.00  --preprocessed_out                      false
% 1.29/1.00  --preprocessed_stats                    false
% 1.29/1.00  
% 1.29/1.00  ------ Abstraction refinement Options
% 1.29/1.00  
% 1.29/1.00  --abstr_ref                             []
% 1.29/1.00  --abstr_ref_prep                        false
% 1.29/1.00  --abstr_ref_until_sat                   false
% 1.29/1.00  --abstr_ref_sig_restrict                funpre
% 1.29/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.29/1.00  --abstr_ref_under                       []
% 1.29/1.00  
% 1.29/1.00  ------ SAT Options
% 1.29/1.00  
% 1.29/1.00  --sat_mode                              false
% 1.29/1.00  --sat_fm_restart_options                ""
% 1.29/1.00  --sat_gr_def                            false
% 1.29/1.00  --sat_epr_types                         true
% 1.29/1.00  --sat_non_cyclic_types                  false
% 1.29/1.00  --sat_finite_models                     false
% 1.29/1.00  --sat_fm_lemmas                         false
% 1.29/1.00  --sat_fm_prep                           false
% 1.29/1.00  --sat_fm_uc_incr                        true
% 1.29/1.00  --sat_out_model                         small
% 1.29/1.00  --sat_out_clauses                       false
% 1.29/1.00  
% 1.29/1.00  ------ QBF Options
% 1.29/1.00  
% 1.29/1.00  --qbf_mode                              false
% 1.29/1.00  --qbf_elim_univ                         false
% 1.29/1.00  --qbf_dom_inst                          none
% 1.29/1.00  --qbf_dom_pre_inst                      false
% 1.29/1.00  --qbf_sk_in                             false
% 1.29/1.00  --qbf_pred_elim                         true
% 1.29/1.00  --qbf_split                             512
% 1.29/1.00  
% 1.29/1.00  ------ BMC1 Options
% 1.29/1.00  
% 1.29/1.00  --bmc1_incremental                      false
% 1.29/1.00  --bmc1_axioms                           reachable_all
% 1.29/1.00  --bmc1_min_bound                        0
% 1.29/1.00  --bmc1_max_bound                        -1
% 1.29/1.00  --bmc1_max_bound_default                -1
% 1.29/1.00  --bmc1_symbol_reachability              true
% 1.29/1.00  --bmc1_property_lemmas                  false
% 1.29/1.00  --bmc1_k_induction                      false
% 1.29/1.00  --bmc1_non_equiv_states                 false
% 1.29/1.00  --bmc1_deadlock                         false
% 1.29/1.00  --bmc1_ucm                              false
% 1.29/1.00  --bmc1_add_unsat_core                   none
% 1.29/1.00  --bmc1_unsat_core_children              false
% 1.29/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.29/1.00  --bmc1_out_stat                         full
% 1.29/1.00  --bmc1_ground_init                      false
% 1.29/1.00  --bmc1_pre_inst_next_state              false
% 1.29/1.00  --bmc1_pre_inst_state                   false
% 1.29/1.00  --bmc1_pre_inst_reach_state             false
% 1.29/1.00  --bmc1_out_unsat_core                   false
% 1.29/1.00  --bmc1_aig_witness_out                  false
% 1.29/1.00  --bmc1_verbose                          false
% 1.29/1.00  --bmc1_dump_clauses_tptp                false
% 1.29/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.29/1.00  --bmc1_dump_file                        -
% 1.29/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.29/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.29/1.00  --bmc1_ucm_extend_mode                  1
% 1.29/1.00  --bmc1_ucm_init_mode                    2
% 1.29/1.00  --bmc1_ucm_cone_mode                    none
% 1.29/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.29/1.00  --bmc1_ucm_relax_model                  4
% 1.29/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.29/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.29/1.00  --bmc1_ucm_layered_model                none
% 1.29/1.00  --bmc1_ucm_max_lemma_size               10
% 1.29/1.00  
% 1.29/1.00  ------ AIG Options
% 1.29/1.00  
% 1.29/1.00  --aig_mode                              false
% 1.29/1.00  
% 1.29/1.00  ------ Instantiation Options
% 1.29/1.00  
% 1.29/1.00  --instantiation_flag                    true
% 1.29/1.00  --inst_sos_flag                         false
% 1.29/1.00  --inst_sos_phase                        true
% 1.29/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.29/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.29/1.00  --inst_lit_sel_side                     none
% 1.29/1.00  --inst_solver_per_active                1400
% 1.29/1.00  --inst_solver_calls_frac                1.
% 1.29/1.00  --inst_passive_queue_type               priority_queues
% 1.29/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.29/1.00  --inst_passive_queues_freq              [25;2]
% 1.29/1.00  --inst_dismatching                      true
% 1.29/1.00  --inst_eager_unprocessed_to_passive     true
% 1.29/1.00  --inst_prop_sim_given                   true
% 1.29/1.00  --inst_prop_sim_new                     false
% 1.29/1.00  --inst_subs_new                         false
% 1.29/1.00  --inst_eq_res_simp                      false
% 1.29/1.00  --inst_subs_given                       false
% 1.29/1.00  --inst_orphan_elimination               true
% 1.29/1.00  --inst_learning_loop_flag               true
% 1.29/1.00  --inst_learning_start                   3000
% 1.29/1.00  --inst_learning_factor                  2
% 1.29/1.00  --inst_start_prop_sim_after_learn       3
% 1.29/1.00  --inst_sel_renew                        solver
% 1.29/1.00  --inst_lit_activity_flag                true
% 1.29/1.00  --inst_restr_to_given                   false
% 1.29/1.00  --inst_activity_threshold               500
% 1.29/1.00  --inst_out_proof                        true
% 1.29/1.00  
% 1.29/1.00  ------ Resolution Options
% 1.29/1.00  
% 1.29/1.00  --resolution_flag                       false
% 1.29/1.00  --res_lit_sel                           adaptive
% 1.29/1.00  --res_lit_sel_side                      none
% 1.29/1.00  --res_ordering                          kbo
% 1.29/1.00  --res_to_prop_solver                    active
% 1.29/1.00  --res_prop_simpl_new                    false
% 1.29/1.00  --res_prop_simpl_given                  true
% 1.29/1.00  --res_passive_queue_type                priority_queues
% 1.29/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.29/1.00  --res_passive_queues_freq               [15;5]
% 1.29/1.00  --res_forward_subs                      full
% 1.29/1.00  --res_backward_subs                     full
% 1.29/1.00  --res_forward_subs_resolution           true
% 1.29/1.00  --res_backward_subs_resolution          true
% 1.29/1.00  --res_orphan_elimination                true
% 1.29/1.00  --res_time_limit                        2.
% 1.29/1.00  --res_out_proof                         true
% 1.29/1.00  
% 1.29/1.00  ------ Superposition Options
% 1.29/1.00  
% 1.29/1.00  --superposition_flag                    true
% 1.29/1.00  --sup_passive_queue_type                priority_queues
% 1.29/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.29/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.29/1.00  --demod_completeness_check              fast
% 1.29/1.00  --demod_use_ground                      true
% 1.29/1.00  --sup_to_prop_solver                    passive
% 1.29/1.00  --sup_prop_simpl_new                    true
% 1.29/1.00  --sup_prop_simpl_given                  true
% 1.29/1.00  --sup_fun_splitting                     false
% 1.29/1.00  --sup_smt_interval                      50000
% 1.29/1.00  
% 1.29/1.00  ------ Superposition Simplification Setup
% 1.29/1.00  
% 1.29/1.00  --sup_indices_passive                   []
% 1.29/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.29/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.29/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.29/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.29/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.29/1.00  --sup_full_bw                           [BwDemod]
% 1.29/1.00  --sup_immed_triv                        [TrivRules]
% 1.29/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.29/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.29/1.00  --sup_immed_bw_main                     []
% 1.29/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.29/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.29/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.29/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.29/1.00  
% 1.29/1.00  ------ Combination Options
% 1.29/1.00  
% 1.29/1.00  --comb_res_mult                         3
% 1.29/1.00  --comb_sup_mult                         2
% 1.29/1.00  --comb_inst_mult                        10
% 1.29/1.00  
% 1.29/1.00  ------ Debug Options
% 1.29/1.00  
% 1.29/1.00  --dbg_backtrace                         false
% 1.29/1.00  --dbg_dump_prop_clauses                 false
% 1.29/1.00  --dbg_dump_prop_clauses_file            -
% 1.29/1.00  --dbg_out_stat                          false
% 1.29/1.00  
% 1.29/1.00  
% 1.29/1.00  
% 1.29/1.00  
% 1.29/1.00  ------ Proving...
% 1.29/1.00  
% 1.29/1.00  
% 1.29/1.00  % SZS status Theorem for theBenchmark.p
% 1.29/1.00  
% 1.29/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 1.29/1.00  
% 1.29/1.00  fof(f6,axiom,(
% 1.29/1.00    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 1.29/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.29/1.00  
% 1.29/1.00  fof(f17,plain,(
% 1.29/1.00    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 1.29/1.00    inference(ennf_transformation,[],[f6])).
% 1.29/1.00  
% 1.29/1.00  fof(f18,plain,(
% 1.29/1.00    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 1.29/1.00    inference(flattening,[],[f17])).
% 1.29/1.00  
% 1.29/1.00  fof(f33,plain,(
% 1.29/1.00    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.29/1.00    inference(cnf_transformation,[],[f18])).
% 1.29/1.00  
% 1.29/1.00  fof(f12,conjecture,(
% 1.29/1.00    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 1.29/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.29/1.00  
% 1.29/1.00  fof(f13,negated_conjecture,(
% 1.29/1.00    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 1.29/1.00    inference(negated_conjecture,[],[f12])).
% 1.29/1.00  
% 1.29/1.00  fof(f25,plain,(
% 1.29/1.00    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 1.29/1.00    inference(ennf_transformation,[],[f13])).
% 1.29/1.00  
% 1.29/1.00  fof(f26,plain,(
% 1.29/1.00    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 1.29/1.00    introduced(choice_axiom,[])).
% 1.29/1.00  
% 1.29/1.00  fof(f27,plain,(
% 1.29/1.00    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 1.29/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).
% 1.29/1.00  
% 1.29/1.00  fof(f40,plain,(
% 1.29/1.00    v1_relat_1(sK0)),
% 1.29/1.00    inference(cnf_transformation,[],[f27])).
% 1.29/1.00  
% 1.29/1.00  fof(f11,axiom,(
% 1.29/1.00    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.29/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.29/1.00  
% 1.29/1.00  fof(f38,plain,(
% 1.29/1.00    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.29/1.00    inference(cnf_transformation,[],[f11])).
% 1.29/1.00  
% 1.29/1.00  fof(f9,axiom,(
% 1.29/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 1.29/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.29/1.00  
% 1.29/1.00  fof(f23,plain,(
% 1.29/1.00    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.29/1.00    inference(ennf_transformation,[],[f9])).
% 1.29/1.00  
% 1.29/1.00  fof(f36,plain,(
% 1.29/1.00    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.29/1.00    inference(cnf_transformation,[],[f23])).
% 1.29/1.00  
% 1.29/1.00  fof(f5,axiom,(
% 1.29/1.00    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 1.29/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.29/1.00  
% 1.29/1.00  fof(f16,plain,(
% 1.29/1.00    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 1.29/1.00    inference(ennf_transformation,[],[f5])).
% 1.29/1.00  
% 1.29/1.00  fof(f32,plain,(
% 1.29/1.00    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 1.29/1.00    inference(cnf_transformation,[],[f16])).
% 1.29/1.00  
% 1.29/1.00  fof(f1,axiom,(
% 1.29/1.00    v1_xboole_0(k1_xboole_0)),
% 1.29/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.29/1.00  
% 1.29/1.00  fof(f28,plain,(
% 1.29/1.00    v1_xboole_0(k1_xboole_0)),
% 1.29/1.00    inference(cnf_transformation,[],[f1])).
% 1.29/1.00  
% 1.29/1.00  fof(f3,axiom,(
% 1.29/1.00    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.29/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.29/1.00  
% 1.29/1.00  fof(f15,plain,(
% 1.29/1.00    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.29/1.00    inference(ennf_transformation,[],[f3])).
% 1.29/1.00  
% 1.29/1.00  fof(f30,plain,(
% 1.29/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.29/1.00    inference(cnf_transformation,[],[f15])).
% 1.29/1.00  
% 1.29/1.00  fof(f4,axiom,(
% 1.29/1.00    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.29/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.29/1.00  
% 1.29/1.00  fof(f31,plain,(
% 1.29/1.00    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.29/1.00    inference(cnf_transformation,[],[f4])).
% 1.29/1.00  
% 1.29/1.00  fof(f7,axiom,(
% 1.29/1.00    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k1_relat_1(X0)))),
% 1.29/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.29/1.00  
% 1.29/1.00  fof(f19,plain,(
% 1.29/1.00    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 1.29/1.00    inference(ennf_transformation,[],[f7])).
% 1.29/1.00  
% 1.29/1.00  fof(f20,plain,(
% 1.29/1.00    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 1.29/1.00    inference(flattening,[],[f19])).
% 1.29/1.00  
% 1.29/1.00  fof(f34,plain,(
% 1.29/1.00    ( ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 1.29/1.00    inference(cnf_transformation,[],[f20])).
% 1.29/1.00  
% 1.29/1.00  fof(f2,axiom,(
% 1.29/1.00    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.29/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.29/1.00  
% 1.29/1.00  fof(f14,plain,(
% 1.29/1.00    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.29/1.00    inference(ennf_transformation,[],[f2])).
% 1.29/1.00  
% 1.29/1.00  fof(f29,plain,(
% 1.29/1.00    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 1.29/1.00    inference(cnf_transformation,[],[f14])).
% 1.29/1.00  
% 1.29/1.00  fof(f39,plain,(
% 1.29/1.00    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.29/1.00    inference(cnf_transformation,[],[f11])).
% 1.29/1.00  
% 1.29/1.00  fof(f10,axiom,(
% 1.29/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 1.29/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.29/1.00  
% 1.29/1.00  fof(f24,plain,(
% 1.29/1.00    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.29/1.00    inference(ennf_transformation,[],[f10])).
% 1.29/1.00  
% 1.29/1.00  fof(f37,plain,(
% 1.29/1.00    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.29/1.00    inference(cnf_transformation,[],[f24])).
% 1.29/1.00  
% 1.29/1.00  fof(f8,axiom,(
% 1.29/1.00    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k2_relat_1(X0)))),
% 1.29/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.29/1.00  
% 1.29/1.00  fof(f21,plain,(
% 1.29/1.00    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 1.29/1.00    inference(ennf_transformation,[],[f8])).
% 1.29/1.00  
% 1.29/1.00  fof(f22,plain,(
% 1.29/1.00    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 1.29/1.00    inference(flattening,[],[f21])).
% 1.29/1.00  
% 1.29/1.00  fof(f35,plain,(
% 1.29/1.00    ( ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 1.29/1.00    inference(cnf_transformation,[],[f22])).
% 1.29/1.00  
% 1.29/1.00  fof(f41,plain,(
% 1.29/1.00    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 1.29/1.00    inference(cnf_transformation,[],[f27])).
% 1.29/1.00  
% 1.29/1.00  cnf(c_5,plain,
% 1.29/1.00      ( ~ v1_relat_1(X0)
% 1.29/1.00      | ~ v1_relat_1(X1)
% 1.29/1.00      | v1_relat_1(k5_relat_1(X1,X0)) ),
% 1.29/1.00      inference(cnf_transformation,[],[f33]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_367,plain,
% 1.29/1.00      ( v1_relat_1(X0) != iProver_top
% 1.29/1.00      | v1_relat_1(X1) != iProver_top
% 1.29/1.00      | v1_relat_1(k5_relat_1(X0,X1)) = iProver_top ),
% 1.29/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_13,negated_conjecture,
% 1.29/1.00      ( v1_relat_1(sK0) ),
% 1.29/1.00      inference(cnf_transformation,[],[f40]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_362,plain,
% 1.29/1.00      ( v1_relat_1(sK0) = iProver_top ),
% 1.29/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_11,plain,
% 1.29/1.00      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 1.29/1.00      inference(cnf_transformation,[],[f38]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_8,plain,
% 1.29/1.00      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
% 1.29/1.00      | ~ v1_relat_1(X1)
% 1.29/1.00      | ~ v1_relat_1(X0) ),
% 1.29/1.00      inference(cnf_transformation,[],[f36]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_364,plain,
% 1.29/1.00      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) = iProver_top
% 1.29/1.00      | v1_relat_1(X1) != iProver_top
% 1.29/1.00      | v1_relat_1(X0) != iProver_top ),
% 1.29/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_1410,plain,
% 1.29/1.00      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0) = iProver_top
% 1.29/1.00      | v1_relat_1(X0) != iProver_top
% 1.29/1.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 1.29/1.00      inference(superposition,[status(thm)],[c_11,c_364]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_4,plain,
% 1.29/1.00      ( v1_relat_1(X0) | ~ v1_xboole_0(X0) ),
% 1.29/1.00      inference(cnf_transformation,[],[f32]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_30,plain,
% 1.29/1.00      ( v1_relat_1(X0) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 1.29/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_32,plain,
% 1.29/1.00      ( v1_relat_1(k1_xboole_0) = iProver_top
% 1.29/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 1.29/1.00      inference(instantiation,[status(thm)],[c_30]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_0,plain,
% 1.29/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 1.29/1.00      inference(cnf_transformation,[],[f28]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_38,plain,
% 1.29/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 1.29/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_1537,plain,
% 1.29/1.00      ( v1_relat_1(X0) != iProver_top
% 1.29/1.00      | r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0) = iProver_top ),
% 1.29/1.00      inference(global_propositional_subsumption,
% 1.29/1.00                [status(thm)],
% 1.29/1.00                [c_1410,c_32,c_38]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_1538,plain,
% 1.29/1.00      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0) = iProver_top
% 1.29/1.00      | v1_relat_1(X0) != iProver_top ),
% 1.29/1.00      inference(renaming,[status(thm)],[c_1537]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_2,plain,
% 1.29/1.00      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 1.29/1.00      inference(cnf_transformation,[],[f30]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_369,plain,
% 1.29/1.00      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 1.29/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_1543,plain,
% 1.29/1.00      ( k3_xboole_0(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,X0))
% 1.29/1.00      | v1_relat_1(X0) != iProver_top ),
% 1.29/1.00      inference(superposition,[status(thm)],[c_1538,c_369]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_3,plain,
% 1.29/1.00      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 1.29/1.00      inference(cnf_transformation,[],[f31]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_1544,plain,
% 1.29/1.00      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
% 1.29/1.00      | v1_relat_1(X0) != iProver_top ),
% 1.29/1.00      inference(demodulation,[status(thm)],[c_1543,c_3]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_1552,plain,
% 1.29/1.00      ( k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k1_xboole_0 ),
% 1.29/1.00      inference(superposition,[status(thm)],[c_362,c_1544]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_6,plain,
% 1.29/1.00      ( ~ v1_relat_1(X0)
% 1.29/1.00      | v1_xboole_0(X0)
% 1.29/1.00      | ~ v1_xboole_0(k1_relat_1(X0)) ),
% 1.29/1.00      inference(cnf_transformation,[],[f34]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_366,plain,
% 1.29/1.00      ( v1_relat_1(X0) != iProver_top
% 1.29/1.00      | v1_xboole_0(X0) = iProver_top
% 1.29/1.00      | v1_xboole_0(k1_relat_1(X0)) != iProver_top ),
% 1.29/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_1627,plain,
% 1.29/1.00      ( v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) != iProver_top
% 1.29/1.00      | v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) = iProver_top
% 1.29/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 1.29/1.00      inference(superposition,[status(thm)],[c_1552,c_366]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_1715,plain,
% 1.29/1.00      ( v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) = iProver_top
% 1.29/1.00      | v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) != iProver_top ),
% 1.29/1.00      inference(global_propositional_subsumption,
% 1.29/1.00                [status(thm)],
% 1.29/1.00                [c_1627,c_38]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_1716,plain,
% 1.29/1.00      ( v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) != iProver_top
% 1.29/1.00      | v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) = iProver_top ),
% 1.29/1.00      inference(renaming,[status(thm)],[c_1715]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_1721,plain,
% 1.29/1.00      ( v1_relat_1(sK0) != iProver_top
% 1.29/1.00      | v1_relat_1(k1_xboole_0) != iProver_top
% 1.29/1.00      | v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) = iProver_top ),
% 1.29/1.00      inference(superposition,[status(thm)],[c_367,c_1716]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_14,plain,
% 1.29/1.00      ( v1_relat_1(sK0) = iProver_top ),
% 1.29/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_1762,plain,
% 1.29/1.00      ( v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) = iProver_top ),
% 1.29/1.00      inference(global_propositional_subsumption,
% 1.29/1.00                [status(thm)],
% 1.29/1.00                [c_1721,c_14,c_32,c_38]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_1,plain,
% 1.29/1.00      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 1.29/1.00      inference(cnf_transformation,[],[f29]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_370,plain,
% 1.29/1.00      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 1.29/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_1768,plain,
% 1.29/1.00      ( k5_relat_1(k1_xboole_0,sK0) = k1_xboole_0 ),
% 1.29/1.00      inference(superposition,[status(thm)],[c_1762,c_370]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_10,plain,
% 1.29/1.00      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 1.29/1.00      inference(cnf_transformation,[],[f39]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_9,plain,
% 1.29/1.00      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
% 1.29/1.00      | ~ v1_relat_1(X1)
% 1.29/1.00      | ~ v1_relat_1(X0) ),
% 1.29/1.00      inference(cnf_transformation,[],[f37]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_363,plain,
% 1.29/1.00      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
% 1.29/1.00      | v1_relat_1(X1) != iProver_top
% 1.29/1.00      | v1_relat_1(X0) != iProver_top ),
% 1.29/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_619,plain,
% 1.29/1.00      ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) = iProver_top
% 1.29/1.00      | v1_relat_1(X0) != iProver_top
% 1.29/1.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 1.29/1.00      inference(superposition,[status(thm)],[c_10,c_363]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_1060,plain,
% 1.29/1.00      ( v1_relat_1(X0) != iProver_top
% 1.29/1.00      | r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) = iProver_top ),
% 1.29/1.00      inference(global_propositional_subsumption,
% 1.29/1.00                [status(thm)],
% 1.29/1.00                [c_619,c_32,c_38]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_1061,plain,
% 1.29/1.00      ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) = iProver_top
% 1.29/1.00      | v1_relat_1(X0) != iProver_top ),
% 1.29/1.00      inference(renaming,[status(thm)],[c_1060]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_1066,plain,
% 1.29/1.00      ( k3_xboole_0(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) = k2_relat_1(k5_relat_1(X0,k1_xboole_0))
% 1.29/1.00      | v1_relat_1(X0) != iProver_top ),
% 1.29/1.00      inference(superposition,[status(thm)],[c_1061,c_369]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_1067,plain,
% 1.29/1.00      ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
% 1.29/1.00      | v1_relat_1(X0) != iProver_top ),
% 1.29/1.00      inference(demodulation,[status(thm)],[c_1066,c_3]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_1075,plain,
% 1.29/1.00      ( k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k1_xboole_0 ),
% 1.29/1.00      inference(superposition,[status(thm)],[c_362,c_1067]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_7,plain,
% 1.29/1.00      ( ~ v1_relat_1(X0)
% 1.29/1.00      | v1_xboole_0(X0)
% 1.29/1.00      | ~ v1_xboole_0(k2_relat_1(X0)) ),
% 1.29/1.00      inference(cnf_transformation,[],[f35]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_365,plain,
% 1.29/1.00      ( v1_relat_1(X0) != iProver_top
% 1.29/1.00      | v1_xboole_0(X0) = iProver_top
% 1.29/1.00      | v1_xboole_0(k2_relat_1(X0)) != iProver_top ),
% 1.29/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_1161,plain,
% 1.29/1.00      ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) != iProver_top
% 1.29/1.00      | v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) = iProver_top
% 1.29/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 1.29/1.00      inference(superposition,[status(thm)],[c_1075,c_365]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_472,plain,
% 1.29/1.00      ( ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
% 1.29/1.00      | v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))
% 1.29/1.00      | ~ v1_xboole_0(k2_relat_1(k5_relat_1(sK0,k1_xboole_0))) ),
% 1.29/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_476,plain,
% 1.29/1.00      ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) != iProver_top
% 1.29/1.00      | v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) = iProver_top
% 1.29/1.00      | v1_xboole_0(k2_relat_1(k5_relat_1(sK0,k1_xboole_0))) != iProver_top ),
% 1.29/1.00      inference(predicate_to_equality,[status(thm)],[c_472]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_572,plain,
% 1.29/1.00      ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
% 1.29/1.00      | ~ v1_relat_1(sK0)
% 1.29/1.00      | ~ v1_relat_1(k1_xboole_0) ),
% 1.29/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_573,plain,
% 1.29/1.00      ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) = iProver_top
% 1.29/1.00      | v1_relat_1(sK0) != iProver_top
% 1.29/1.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 1.29/1.00      inference(predicate_to_equality,[status(thm)],[c_572]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_161,plain,
% 1.29/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 1.29/1.00      theory(equality) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_875,plain,
% 1.29/1.00      ( ~ v1_xboole_0(X0)
% 1.29/1.00      | v1_xboole_0(k2_relat_1(k5_relat_1(sK0,k1_xboole_0)))
% 1.29/1.00      | k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) != X0 ),
% 1.29/1.00      inference(instantiation,[status(thm)],[c_161]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_876,plain,
% 1.29/1.00      ( k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) != X0
% 1.29/1.00      | v1_xboole_0(X0) != iProver_top
% 1.29/1.00      | v1_xboole_0(k2_relat_1(k5_relat_1(sK0,k1_xboole_0))) = iProver_top ),
% 1.29/1.00      inference(predicate_to_equality,[status(thm)],[c_875]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_878,plain,
% 1.29/1.00      ( k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) != k1_xboole_0
% 1.29/1.00      | v1_xboole_0(k2_relat_1(k5_relat_1(sK0,k1_xboole_0))) = iProver_top
% 1.29/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 1.29/1.00      inference(instantiation,[status(thm)],[c_876]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_1266,plain,
% 1.29/1.00      ( v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) = iProver_top ),
% 1.29/1.00      inference(global_propositional_subsumption,
% 1.29/1.00                [status(thm)],
% 1.29/1.00                [c_1161,c_14,c_32,c_38,c_476,c_573,c_878,c_1075]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_1272,plain,
% 1.29/1.00      ( k5_relat_1(sK0,k1_xboole_0) = k1_xboole_0 ),
% 1.29/1.00      inference(superposition,[status(thm)],[c_1266,c_370]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_12,negated_conjecture,
% 1.29/1.00      ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
% 1.29/1.00      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
% 1.29/1.00      inference(cnf_transformation,[],[f41]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_1602,plain,
% 1.29/1.00      ( k5_relat_1(k1_xboole_0,sK0) != k1_xboole_0
% 1.29/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 1.29/1.00      inference(demodulation,[status(thm)],[c_1272,c_12]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(c_1603,plain,
% 1.29/1.00      ( k5_relat_1(k1_xboole_0,sK0) != k1_xboole_0 ),
% 1.29/1.00      inference(equality_resolution_simp,[status(thm)],[c_1602]) ).
% 1.29/1.00  
% 1.29/1.00  cnf(contradiction,plain,
% 1.29/1.00      ( $false ),
% 1.29/1.00      inference(minisat,[status(thm)],[c_1768,c_1603]) ).
% 1.29/1.00  
% 1.29/1.00  
% 1.29/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 1.29/1.00  
% 1.29/1.00  ------                               Statistics
% 1.29/1.00  
% 1.29/1.00  ------ General
% 1.29/1.00  
% 1.29/1.00  abstr_ref_over_cycles:                  0
% 1.29/1.00  abstr_ref_under_cycles:                 0
% 1.29/1.00  gc_basic_clause_elim:                   0
% 1.29/1.00  forced_gc_time:                         0
% 1.29/1.00  parsing_time:                           0.01
% 1.29/1.00  unif_index_cands_time:                  0.
% 1.29/1.00  unif_index_add_time:                    0.
% 1.29/1.00  orderings_time:                         0.
% 1.29/1.00  out_proof_time:                         0.009
% 1.29/1.00  total_time:                             0.088
% 1.29/1.00  num_of_symbols:                         40
% 1.29/1.00  num_of_terms:                           1610
% 1.29/1.00  
% 1.29/1.00  ------ Preprocessing
% 1.29/1.00  
% 1.29/1.00  num_of_splits:                          0
% 1.29/1.00  num_of_split_atoms:                     0
% 1.29/1.00  num_of_reused_defs:                     0
% 1.29/1.00  num_eq_ax_congr_red:                    2
% 1.29/1.00  num_of_sem_filtered_clauses:            1
% 1.29/1.00  num_of_subtypes:                        1
% 1.29/1.00  monotx_restored_types:                  1
% 1.29/1.00  sat_num_of_epr_types:                   0
% 1.29/1.00  sat_num_of_non_cyclic_types:            0
% 1.29/1.00  sat_guarded_non_collapsed_types:        1
% 1.29/1.01  num_pure_diseq_elim:                    0
% 1.29/1.01  simp_replaced_by:                       0
% 1.29/1.01  res_preprocessed:                       61
% 1.29/1.01  prep_upred:                             0
% 1.29/1.01  prep_unflattend:                        4
% 1.29/1.01  smt_new_axioms:                         0
% 1.29/1.01  pred_elim_cands:                        3
% 1.29/1.01  pred_elim:                              0
% 1.29/1.01  pred_elim_cl:                           0
% 1.29/1.01  pred_elim_cycles:                       1
% 1.29/1.01  merged_defs:                            0
% 1.29/1.01  merged_defs_ncl:                        0
% 1.29/1.01  bin_hyper_res:                          0
% 1.29/1.01  prep_cycles:                            3
% 1.29/1.01  pred_elim_time:                         0.001
% 1.29/1.01  splitting_time:                         0.
% 1.29/1.01  sem_filter_time:                        0.
% 1.29/1.01  monotx_time:                            0.001
% 1.29/1.01  subtype_inf_time:                       0.
% 1.29/1.01  
% 1.29/1.01  ------ Problem properties
% 1.29/1.01  
% 1.29/1.01  clauses:                                14
% 1.29/1.01  conjectures:                            2
% 1.29/1.01  epr:                                    4
% 1.29/1.01  horn:                                   14
% 1.29/1.01  ground:                                 5
% 1.29/1.01  unary:                                  5
% 1.29/1.01  binary:                                 4
% 1.29/1.01  lits:                                   28
% 1.29/1.01  lits_eq:                                7
% 1.29/1.01  fd_pure:                                0
% 1.29/1.01  fd_pseudo:                              0
% 1.29/1.01  fd_cond:                                1
% 1.29/1.01  fd_pseudo_cond:                         0
% 1.29/1.01  ac_symbols:                             0
% 1.29/1.01  
% 1.29/1.01  ------ Propositional Solver
% 1.29/1.01  
% 1.29/1.01  prop_solver_calls:                      24
% 1.29/1.01  prop_fast_solver_calls:                 343
% 1.29/1.01  smt_solver_calls:                       0
% 1.29/1.01  smt_fast_solver_calls:                  0
% 1.29/1.01  prop_num_of_clauses:                    633
% 1.29/1.01  prop_preprocess_simplified:             2264
% 1.29/1.01  prop_fo_subsumed:                       9
% 1.29/1.01  prop_solver_time:                       0.
% 1.29/1.01  smt_solver_time:                        0.
% 1.29/1.01  smt_fast_solver_time:                   0.
% 1.29/1.01  prop_fast_solver_time:                  0.
% 1.29/1.01  prop_unsat_core_time:                   0.
% 1.29/1.01  
% 1.29/1.01  ------ QBF
% 1.29/1.01  
% 1.29/1.01  qbf_q_res:                              0
% 1.29/1.01  qbf_num_tautologies:                    0
% 1.29/1.01  qbf_prep_cycles:                        0
% 1.29/1.01  
% 1.29/1.01  ------ BMC1
% 1.29/1.01  
% 1.29/1.01  bmc1_current_bound:                     -1
% 1.29/1.01  bmc1_last_solved_bound:                 -1
% 1.29/1.01  bmc1_unsat_core_size:                   -1
% 1.29/1.01  bmc1_unsat_core_parents_size:           -1
% 1.29/1.01  bmc1_merge_next_fun:                    0
% 1.29/1.01  bmc1_unsat_core_clauses_time:           0.
% 1.29/1.01  
% 1.29/1.01  ------ Instantiation
% 1.29/1.01  
% 1.29/1.01  inst_num_of_clauses:                    215
% 1.29/1.01  inst_num_in_passive:                    99
% 1.29/1.01  inst_num_in_active:                     107
% 1.29/1.01  inst_num_in_unprocessed:                9
% 1.29/1.01  inst_num_of_loops:                      150
% 1.29/1.01  inst_num_of_learning_restarts:          0
% 1.29/1.01  inst_num_moves_active_passive:          40
% 1.29/1.01  inst_lit_activity:                      0
% 1.29/1.01  inst_lit_activity_moves:                0
% 1.29/1.01  inst_num_tautologies:                   0
% 1.29/1.01  inst_num_prop_implied:                  0
% 1.29/1.01  inst_num_existing_simplified:           0
% 1.29/1.01  inst_num_eq_res_simplified:             0
% 1.29/1.01  inst_num_child_elim:                    0
% 1.29/1.01  inst_num_of_dismatching_blockings:      56
% 1.29/1.01  inst_num_of_non_proper_insts:           210
% 1.29/1.01  inst_num_of_duplicates:                 0
% 1.29/1.01  inst_inst_num_from_inst_to_res:         0
% 1.29/1.01  inst_dismatching_checking_time:         0.
% 1.29/1.01  
% 1.29/1.01  ------ Resolution
% 1.29/1.01  
% 1.29/1.01  res_num_of_clauses:                     0
% 1.29/1.01  res_num_in_passive:                     0
% 1.29/1.01  res_num_in_active:                      0
% 1.29/1.01  res_num_of_loops:                       64
% 1.29/1.01  res_forward_subset_subsumed:            15
% 1.29/1.01  res_backward_subset_subsumed:           0
% 1.29/1.01  res_forward_subsumed:                   0
% 1.29/1.01  res_backward_subsumed:                  0
% 1.29/1.01  res_forward_subsumption_resolution:     0
% 1.29/1.01  res_backward_subsumption_resolution:    0
% 1.29/1.01  res_clause_to_clause_subsumption:       64
% 1.29/1.01  res_orphan_elimination:                 0
% 1.29/1.01  res_tautology_del:                      39
% 1.29/1.01  res_num_eq_res_simplified:              0
% 1.29/1.01  res_num_sel_changes:                    0
% 1.29/1.01  res_moves_from_active_to_pass:          0
% 1.29/1.01  
% 1.29/1.01  ------ Superposition
% 1.29/1.01  
% 1.29/1.01  sup_time_total:                         0.
% 1.29/1.01  sup_time_generating:                    0.
% 1.29/1.01  sup_time_sim_full:                      0.
% 1.29/1.01  sup_time_sim_immed:                     0.
% 1.29/1.01  
% 1.29/1.01  sup_num_of_clauses:                     39
% 1.29/1.01  sup_num_in_active:                      25
% 1.29/1.01  sup_num_in_passive:                     14
% 1.29/1.01  sup_num_of_loops:                       29
% 1.29/1.01  sup_fw_superposition:                   17
% 1.29/1.01  sup_bw_superposition:                   22
% 1.29/1.01  sup_immediate_simplified:               12
% 1.29/1.01  sup_given_eliminated:                   2
% 1.29/1.01  comparisons_done:                       0
% 1.29/1.01  comparisons_avoided:                    0
% 1.29/1.01  
% 1.29/1.01  ------ Simplifications
% 1.29/1.01  
% 1.29/1.01  
% 1.29/1.01  sim_fw_subset_subsumed:                 2
% 1.29/1.01  sim_bw_subset_subsumed:                 0
% 1.29/1.01  sim_fw_subsumed:                        1
% 1.29/1.01  sim_bw_subsumed:                        0
% 1.29/1.01  sim_fw_subsumption_res:                 0
% 1.29/1.01  sim_bw_subsumption_res:                 0
% 1.29/1.01  sim_tautology_del:                      1
% 1.29/1.01  sim_eq_tautology_del:                   2
% 1.29/1.01  sim_eq_res_simp:                        1
% 1.29/1.01  sim_fw_demodulated:                     4
% 1.29/1.01  sim_bw_demodulated:                     6
% 1.29/1.01  sim_light_normalised:                   7
% 1.29/1.01  sim_joinable_taut:                      0
% 1.29/1.01  sim_joinable_simp:                      0
% 1.29/1.01  sim_ac_normalised:                      0
% 1.29/1.01  sim_smt_subsumption:                    0
% 1.29/1.01  
%------------------------------------------------------------------------------
