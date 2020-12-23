%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:22:27 EST 2020

% Result     : Theorem 12.03s
% Output     : CNFRefutation 12.03s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 297 expanded)
%              Number of clauses        :   61 ( 131 expanded)
%              Number of leaves         :   13 (  58 expanded)
%              Depth                    :   26
%              Number of atoms          :  224 ( 861 expanded)
%              Number of equality atoms :   85 ( 254 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ( r1_tarski(X3,X2)
              & r1_tarski(X3,X1) )
           => r1_tarski(X3,X0) )
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k3_xboole_0(X1,X2) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = X0
      | ? [X3] :
          ( ~ r1_tarski(X3,X0)
          & r1_tarski(X3,X2)
          & r1_tarski(X3,X1) )
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = X0
      | ? [X3] :
          ( ~ r1_tarski(X3,X0)
          & r1_tarski(X3,X2)
          & r1_tarski(X3,X1) )
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tarski(X3,X0)
          & r1_tarski(X3,X2)
          & r1_tarski(X3,X1) )
     => ( ~ r1_tarski(sK0(X0,X1,X2),X0)
        & r1_tarski(sK0(X0,X1,X2),X2)
        & r1_tarski(sK0(X0,X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = X0
      | ( ~ r1_tarski(sK0(X0,X1,X2),X0)
        & r1_tarski(sK0(X0,X1,X2),X2)
        & r1_tarski(sK0(X0,X1,X2),X1) )
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f25])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = X0
      | r1_tarski(sK0(X0,X1,X2),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = X0
      | ~ r1_tarski(sK0(X0,X1,X2),X0)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_tarski(X2,X3)
          & r1_tarski(X0,X1) )
       => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f27,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3))
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(k3_xboole_0(sK1,sK3),k3_xboole_0(sK2,sK4))
      & r1_tarski(sK3,sK4)
      & r1_tarski(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ~ r1_tarski(k3_xboole_0(sK1,sK3),k3_xboole_0(sK2,sK4))
    & r1_tarski(sK3,sK4)
    & r1_tarski(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f24,f27])).

fof(f42,plain,(
    r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f28])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f43,plain,(
    ~ r1_tarski(k3_xboole_0(sK1,sK3),k3_xboole_0(sK2,sK4)) ),
    inference(cnf_transformation,[],[f28])).

fof(f41,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_9,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_363,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(sK0(X0,X1,X2),X2)
    | k3_xboole_0(X1,X2) = X0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_366,plain,
    ( k3_xboole_0(X0,X1) = X2
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(sK0(X2,X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | ~ r1_tarski(sK0(X0,X1,X2),X0)
    | k3_xboole_0(X1,X2) = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_367,plain,
    ( k3_xboole_0(X0,X1) = X2
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(sK0(X2,X0,X1),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2637,plain,
    ( k3_xboole_0(X0,X1) = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X1,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_366,c_367])).

cnf(c_4811,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X0)
    | k3_xboole_0(X1,X0) = X0 ),
    inference(resolution,[status(thm)],[c_5,c_6])).

cnf(c_2664,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X0)
    | k3_xboole_0(X1,X0) = X0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2637])).

cnf(c_2,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_370,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_371,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1137,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0 ),
    inference(superposition,[status(thm)],[c_370,c_371])).

cnf(c_1138,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_363,c_371])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_361,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2923,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X0)) = iProver_top
    | r1_tarski(k1_xboole_0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1138,c_361])).

cnf(c_8944,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X0)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2923,c_363])).

cnf(c_8946,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1137,c_8944])).

cnf(c_9004,plain,
    ( r1_tarski(X0,X0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_8946])).

cnf(c_9139,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X1,X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4811,c_2664,c_9004])).

cnf(c_9141,plain,
    ( k3_xboole_0(X0,X1) = X1
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9139])).

cnf(c_22231,plain,
    ( r1_tarski(X1,X0) != iProver_top
    | k3_xboole_0(X0,X1) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2637,c_9141])).

cnf(c_22232,plain,
    ( k3_xboole_0(X0,X1) = X1
    | r1_tarski(X1,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_22231])).

cnf(c_22240,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_363,c_22232])).

cnf(c_13,negated_conjecture,
    ( r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_359,plain,
    ( r1_tarski(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_10,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_362,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_22241,plain,
    ( k3_xboole_0(k2_xboole_0(X0,X1),X0) = X0 ),
    inference(superposition,[status(thm)],[c_362,c_22232])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_364,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_23354,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
    | r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_22241,c_364])).

cnf(c_30511,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k3_xboole_0(k2_xboole_0(X0,X2),X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_361,c_23354])).

cnf(c_34639,plain,
    ( k2_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),X2),X2) = X2
    | r1_tarski(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_30511,c_371])).

cnf(c_35185,plain,
    ( k2_xboole_0(k3_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),X2),X0),X0) = X0 ),
    inference(superposition,[status(thm)],[c_370,c_34639])).

cnf(c_0,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_372,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_37857,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k3_xboole_0(k2_xboole_0(k3_xboole_0(X0,X2),X3),X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_35185,c_372])).

cnf(c_51378,plain,
    ( k2_xboole_0(k3_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),X2),X0),X3) = X3
    | r1_tarski(X0,X3) != iProver_top ),
    inference(superposition,[status(thm)],[c_37857,c_371])).

cnf(c_55514,plain,
    ( k2_xboole_0(k3_xboole_0(k2_xboole_0(k3_xboole_0(sK3,X0),X1),sK3),sK4) = sK4 ),
    inference(superposition,[status(thm)],[c_359,c_51378])).

cnf(c_56554,plain,
    ( r1_tarski(k3_xboole_0(k2_xboole_0(k3_xboole_0(sK3,X0),X1),sK3),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_55514,c_362])).

cnf(c_58678,plain,
    ( r1_tarski(k3_xboole_0(k2_xboole_0(k1_xboole_0,X0),sK3),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_22240,c_56554])).

cnf(c_58745,plain,
    ( r1_tarski(k3_xboole_0(X0,sK3),sK4) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_58678,c_1138])).

cnf(c_58750,plain,
    ( r1_tarski(k3_xboole_0(sK1,sK3),sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_58745])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_369,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,k3_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_12,negated_conjecture,
    ( ~ r1_tarski(k3_xboole_0(sK1,sK3),k3_xboole_0(sK2,sK4)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_360,plain,
    ( r1_tarski(k3_xboole_0(sK1,sK3),k3_xboole_0(sK2,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2254,plain,
    ( r1_tarski(k3_xboole_0(sK1,sK3),sK4) != iProver_top
    | r1_tarski(k3_xboole_0(sK1,sK3),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_369,c_360])).

cnf(c_14,negated_conjecture,
    ( r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_358,plain,
    ( r1_tarski(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_368,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1820,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k3_xboole_0(X0,X2),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_370,c_368])).

cnf(c_5530,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),X2) = X2
    | r1_tarski(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1820,c_371])).

cnf(c_11440,plain,
    ( k2_xboole_0(k3_xboole_0(sK1,X0),sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_358,c_5530])).

cnf(c_12110,plain,
    ( r1_tarski(k3_xboole_0(sK1,X0),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_11440,c_362])).

cnf(c_14231,plain,
    ( r1_tarski(k3_xboole_0(sK1,sK3),sK4) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2254,c_12110])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_58750,c_14231])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:17:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 12.03/1.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.03/1.99  
% 12.03/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 12.03/1.99  
% 12.03/1.99  ------  iProver source info
% 12.03/1.99  
% 12.03/1.99  git: date: 2020-06-30 10:37:57 +0100
% 12.03/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 12.03/1.99  git: non_committed_changes: false
% 12.03/1.99  git: last_make_outside_of_git: false
% 12.03/1.99  
% 12.03/1.99  ------ 
% 12.03/1.99  
% 12.03/1.99  ------ Input Options
% 12.03/1.99  
% 12.03/1.99  --out_options                           all
% 12.03/1.99  --tptp_safe_out                         true
% 12.03/1.99  --problem_path                          ""
% 12.03/1.99  --include_path                          ""
% 12.03/1.99  --clausifier                            res/vclausify_rel
% 12.03/1.99  --clausifier_options                    --mode clausify
% 12.03/1.99  --stdin                                 false
% 12.03/1.99  --stats_out                             sel
% 12.03/1.99  
% 12.03/1.99  ------ General Options
% 12.03/1.99  
% 12.03/1.99  --fof                                   false
% 12.03/1.99  --time_out_real                         604.99
% 12.03/1.99  --time_out_virtual                      -1.
% 12.03/1.99  --symbol_type_check                     false
% 12.03/1.99  --clausify_out                          false
% 12.03/1.99  --sig_cnt_out                           false
% 12.03/1.99  --trig_cnt_out                          false
% 12.03/1.99  --trig_cnt_out_tolerance                1.
% 12.03/1.99  --trig_cnt_out_sk_spl                   false
% 12.03/1.99  --abstr_cl_out                          false
% 12.03/1.99  
% 12.03/1.99  ------ Global Options
% 12.03/1.99  
% 12.03/1.99  --schedule                              none
% 12.03/1.99  --add_important_lit                     false
% 12.03/1.99  --prop_solver_per_cl                    1000
% 12.03/1.99  --min_unsat_core                        false
% 12.03/1.99  --soft_assumptions                      false
% 12.03/1.99  --soft_lemma_size                       3
% 12.03/1.99  --prop_impl_unit_size                   0
% 12.03/1.99  --prop_impl_unit                        []
% 12.03/1.99  --share_sel_clauses                     true
% 12.03/1.99  --reset_solvers                         false
% 12.03/1.99  --bc_imp_inh                            [conj_cone]
% 12.03/1.99  --conj_cone_tolerance                   3.
% 12.03/1.99  --extra_neg_conj                        none
% 12.03/1.99  --large_theory_mode                     true
% 12.03/1.99  --prolific_symb_bound                   200
% 12.03/1.99  --lt_threshold                          2000
% 12.03/1.99  --clause_weak_htbl                      true
% 12.03/1.99  --gc_record_bc_elim                     false
% 12.03/1.99  
% 12.03/1.99  ------ Preprocessing Options
% 12.03/1.99  
% 12.03/1.99  --preprocessing_flag                    true
% 12.03/1.99  --time_out_prep_mult                    0.1
% 12.03/1.99  --splitting_mode                        input
% 12.03/1.99  --splitting_grd                         true
% 12.03/1.99  --splitting_cvd                         false
% 12.03/1.99  --splitting_cvd_svl                     false
% 12.03/1.99  --splitting_nvd                         32
% 12.03/1.99  --sub_typing                            true
% 12.03/1.99  --prep_gs_sim                           false
% 12.03/1.99  --prep_unflatten                        true
% 12.03/1.99  --prep_res_sim                          true
% 12.03/1.99  --prep_upred                            true
% 12.03/1.99  --prep_sem_filter                       exhaustive
% 12.03/1.99  --prep_sem_filter_out                   false
% 12.03/1.99  --pred_elim                             false
% 12.03/1.99  --res_sim_input                         true
% 12.03/1.99  --eq_ax_congr_red                       true
% 12.03/1.99  --pure_diseq_elim                       true
% 12.03/1.99  --brand_transform                       false
% 12.03/1.99  --non_eq_to_eq                          false
% 12.03/1.99  --prep_def_merge                        true
% 12.03/1.99  --prep_def_merge_prop_impl              false
% 12.03/1.99  --prep_def_merge_mbd                    true
% 12.03/1.99  --prep_def_merge_tr_red                 false
% 12.03/1.99  --prep_def_merge_tr_cl                  false
% 12.03/1.99  --smt_preprocessing                     true
% 12.03/1.99  --smt_ac_axioms                         fast
% 12.03/1.99  --preprocessed_out                      false
% 12.03/1.99  --preprocessed_stats                    false
% 12.03/1.99  
% 12.03/1.99  ------ Abstraction refinement Options
% 12.03/1.99  
% 12.03/1.99  --abstr_ref                             []
% 12.03/1.99  --abstr_ref_prep                        false
% 12.03/1.99  --abstr_ref_until_sat                   false
% 12.03/1.99  --abstr_ref_sig_restrict                funpre
% 12.03/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 12.03/1.99  --abstr_ref_under                       []
% 12.03/1.99  
% 12.03/1.99  ------ SAT Options
% 12.03/1.99  
% 12.03/1.99  --sat_mode                              false
% 12.03/1.99  --sat_fm_restart_options                ""
% 12.03/1.99  --sat_gr_def                            false
% 12.03/1.99  --sat_epr_types                         true
% 12.03/1.99  --sat_non_cyclic_types                  false
% 12.03/1.99  --sat_finite_models                     false
% 12.03/1.99  --sat_fm_lemmas                         false
% 12.03/1.99  --sat_fm_prep                           false
% 12.03/1.99  --sat_fm_uc_incr                        true
% 12.03/1.99  --sat_out_model                         small
% 12.03/1.99  --sat_out_clauses                       false
% 12.03/1.99  
% 12.03/1.99  ------ QBF Options
% 12.03/1.99  
% 12.03/1.99  --qbf_mode                              false
% 12.03/1.99  --qbf_elim_univ                         false
% 12.03/1.99  --qbf_dom_inst                          none
% 12.03/1.99  --qbf_dom_pre_inst                      false
% 12.03/1.99  --qbf_sk_in                             false
% 12.03/1.99  --qbf_pred_elim                         true
% 12.03/1.99  --qbf_split                             512
% 12.03/1.99  
% 12.03/1.99  ------ BMC1 Options
% 12.03/1.99  
% 12.03/1.99  --bmc1_incremental                      false
% 12.03/1.99  --bmc1_axioms                           reachable_all
% 12.03/1.99  --bmc1_min_bound                        0
% 12.03/1.99  --bmc1_max_bound                        -1
% 12.03/1.99  --bmc1_max_bound_default                -1
% 12.03/1.99  --bmc1_symbol_reachability              true
% 12.03/1.99  --bmc1_property_lemmas                  false
% 12.03/1.99  --bmc1_k_induction                      false
% 12.03/1.99  --bmc1_non_equiv_states                 false
% 12.03/1.99  --bmc1_deadlock                         false
% 12.03/1.99  --bmc1_ucm                              false
% 12.03/1.99  --bmc1_add_unsat_core                   none
% 12.03/1.99  --bmc1_unsat_core_children              false
% 12.03/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 12.03/1.99  --bmc1_out_stat                         full
% 12.03/1.99  --bmc1_ground_init                      false
% 12.03/1.99  --bmc1_pre_inst_next_state              false
% 12.03/1.99  --bmc1_pre_inst_state                   false
% 12.03/1.99  --bmc1_pre_inst_reach_state             false
% 12.03/1.99  --bmc1_out_unsat_core                   false
% 12.03/1.99  --bmc1_aig_witness_out                  false
% 12.03/1.99  --bmc1_verbose                          false
% 12.03/1.99  --bmc1_dump_clauses_tptp                false
% 12.03/1.99  --bmc1_dump_unsat_core_tptp             false
% 12.03/1.99  --bmc1_dump_file                        -
% 12.03/1.99  --bmc1_ucm_expand_uc_limit              128
% 12.03/1.99  --bmc1_ucm_n_expand_iterations          6
% 12.03/1.99  --bmc1_ucm_extend_mode                  1
% 12.03/1.99  --bmc1_ucm_init_mode                    2
% 12.03/1.99  --bmc1_ucm_cone_mode                    none
% 12.03/1.99  --bmc1_ucm_reduced_relation_type        0
% 12.03/1.99  --bmc1_ucm_relax_model                  4
% 12.03/1.99  --bmc1_ucm_full_tr_after_sat            true
% 12.03/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 12.03/1.99  --bmc1_ucm_layered_model                none
% 12.03/1.99  --bmc1_ucm_max_lemma_size               10
% 12.03/1.99  
% 12.03/1.99  ------ AIG Options
% 12.03/1.99  
% 12.03/1.99  --aig_mode                              false
% 12.03/1.99  
% 12.03/1.99  ------ Instantiation Options
% 12.03/1.99  
% 12.03/1.99  --instantiation_flag                    true
% 12.03/1.99  --inst_sos_flag                         false
% 12.03/1.99  --inst_sos_phase                        true
% 12.03/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 12.03/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 12.03/1.99  --inst_lit_sel_side                     num_symb
% 12.03/1.99  --inst_solver_per_active                1400
% 12.03/1.99  --inst_solver_calls_frac                1.
% 12.03/1.99  --inst_passive_queue_type               priority_queues
% 12.03/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 12.03/1.99  --inst_passive_queues_freq              [25;2]
% 12.03/1.99  --inst_dismatching                      true
% 12.03/1.99  --inst_eager_unprocessed_to_passive     true
% 12.03/1.99  --inst_prop_sim_given                   true
% 12.03/1.99  --inst_prop_sim_new                     false
% 12.03/1.99  --inst_subs_new                         false
% 12.03/1.99  --inst_eq_res_simp                      false
% 12.03/1.99  --inst_subs_given                       false
% 12.03/1.99  --inst_orphan_elimination               true
% 12.03/1.99  --inst_learning_loop_flag               true
% 12.03/1.99  --inst_learning_start                   3000
% 12.03/1.99  --inst_learning_factor                  2
% 12.03/1.99  --inst_start_prop_sim_after_learn       3
% 12.03/1.99  --inst_sel_renew                        solver
% 12.03/1.99  --inst_lit_activity_flag                true
% 12.03/1.99  --inst_restr_to_given                   false
% 12.03/1.99  --inst_activity_threshold               500
% 12.03/1.99  --inst_out_proof                        true
% 12.03/1.99  
% 12.03/1.99  ------ Resolution Options
% 12.03/1.99  
% 12.03/1.99  --resolution_flag                       true
% 12.03/1.99  --res_lit_sel                           adaptive
% 12.03/1.99  --res_lit_sel_side                      none
% 12.03/1.99  --res_ordering                          kbo
% 12.03/1.99  --res_to_prop_solver                    active
% 12.03/1.99  --res_prop_simpl_new                    false
% 12.03/1.99  --res_prop_simpl_given                  true
% 12.03/1.99  --res_passive_queue_type                priority_queues
% 12.03/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 12.03/1.99  --res_passive_queues_freq               [15;5]
% 12.03/1.99  --res_forward_subs                      full
% 12.03/1.99  --res_backward_subs                     full
% 12.03/1.99  --res_forward_subs_resolution           true
% 12.03/1.99  --res_backward_subs_resolution          true
% 12.03/1.99  --res_orphan_elimination                true
% 12.03/1.99  --res_time_limit                        2.
% 12.03/1.99  --res_out_proof                         true
% 12.03/1.99  
% 12.03/1.99  ------ Superposition Options
% 12.03/1.99  
% 12.03/1.99  --superposition_flag                    true
% 12.03/1.99  --sup_passive_queue_type                priority_queues
% 12.03/1.99  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 12.03/1.99  --sup_passive_queues_freq               [1;4]
% 12.03/1.99  --demod_completeness_check              fast
% 12.03/1.99  --demod_use_ground                      true
% 12.03/1.99  --sup_to_prop_solver                    passive
% 12.03/1.99  --sup_prop_simpl_new                    true
% 12.03/1.99  --sup_prop_simpl_given                  true
% 12.03/1.99  --sup_fun_splitting                     false
% 12.03/1.99  --sup_smt_interval                      50000
% 12.03/1.99  
% 12.03/1.99  ------ Superposition Simplification Setup
% 12.03/1.99  
% 12.03/1.99  --sup_indices_passive                   []
% 12.03/1.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 12.03/1.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 12.03/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 12.03/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 12.03/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 12.03/1.99  --sup_full_bw                           [BwDemod]
% 12.03/1.99  --sup_immed_triv                        [TrivRules]
% 12.03/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 12.03/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 12.03/1.99  --sup_immed_bw_main                     []
% 12.03/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 12.03/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 12.03/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 12.03/1.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 12.03/1.99  
% 12.03/1.99  ------ Combination Options
% 12.03/1.99  
% 12.03/1.99  --comb_res_mult                         3
% 12.03/1.99  --comb_sup_mult                         2
% 12.03/1.99  --comb_inst_mult                        10
% 12.03/1.99  
% 12.03/1.99  ------ Debug Options
% 12.03/1.99  
% 12.03/1.99  --dbg_backtrace                         false
% 12.03/1.99  --dbg_dump_prop_clauses                 false
% 12.03/1.99  --dbg_dump_prop_clauses_file            -
% 12.03/1.99  --dbg_out_stat                          false
% 12.03/1.99  ------ Parsing...
% 12.03/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 12.03/1.99  
% 12.03/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 12.03/1.99  
% 12.03/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 12.03/1.99  
% 12.03/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 12.03/1.99  ------ Proving...
% 12.03/1.99  ------ Problem Properties 
% 12.03/1.99  
% 12.03/1.99  
% 12.03/1.99  clauses                                 15
% 12.03/1.99  conjectures                             3
% 12.03/1.99  EPR                                     4
% 12.03/1.99  Horn                                    13
% 12.03/1.99  unary                                   6
% 12.03/1.99  binary                                  4
% 12.03/1.99  lits                                    32
% 12.03/1.99  lits eq                                 4
% 12.03/1.99  fd_pure                                 0
% 12.03/1.99  fd_pseudo                               0
% 12.03/1.99  fd_cond                                 0
% 12.03/1.99  fd_pseudo_cond                          3
% 12.03/1.99  AC symbols                              0
% 12.03/1.99  
% 12.03/1.99  ------ Input Options Time Limit: Unbounded
% 12.03/1.99  
% 12.03/1.99  
% 12.03/1.99  ------ 
% 12.03/1.99  Current options:
% 12.03/1.99  ------ 
% 12.03/1.99  
% 12.03/1.99  ------ Input Options
% 12.03/1.99  
% 12.03/1.99  --out_options                           all
% 12.03/1.99  --tptp_safe_out                         true
% 12.03/1.99  --problem_path                          ""
% 12.03/1.99  --include_path                          ""
% 12.03/1.99  --clausifier                            res/vclausify_rel
% 12.03/1.99  --clausifier_options                    --mode clausify
% 12.03/1.99  --stdin                                 false
% 12.03/1.99  --stats_out                             sel
% 12.03/1.99  
% 12.03/1.99  ------ General Options
% 12.03/1.99  
% 12.03/1.99  --fof                                   false
% 12.03/1.99  --time_out_real                         604.99
% 12.03/1.99  --time_out_virtual                      -1.
% 12.03/1.99  --symbol_type_check                     false
% 12.03/1.99  --clausify_out                          false
% 12.03/1.99  --sig_cnt_out                           false
% 12.03/1.99  --trig_cnt_out                          false
% 12.03/1.99  --trig_cnt_out_tolerance                1.
% 12.03/1.99  --trig_cnt_out_sk_spl                   false
% 12.03/1.99  --abstr_cl_out                          false
% 12.03/1.99  
% 12.03/1.99  ------ Global Options
% 12.03/1.99  
% 12.03/1.99  --schedule                              none
% 12.03/1.99  --add_important_lit                     false
% 12.03/1.99  --prop_solver_per_cl                    1000
% 12.03/1.99  --min_unsat_core                        false
% 12.03/1.99  --soft_assumptions                      false
% 12.03/1.99  --soft_lemma_size                       3
% 12.03/1.99  --prop_impl_unit_size                   0
% 12.03/1.99  --prop_impl_unit                        []
% 12.03/1.99  --share_sel_clauses                     true
% 12.03/1.99  --reset_solvers                         false
% 12.03/1.99  --bc_imp_inh                            [conj_cone]
% 12.03/1.99  --conj_cone_tolerance                   3.
% 12.03/1.99  --extra_neg_conj                        none
% 12.03/1.99  --large_theory_mode                     true
% 12.03/1.99  --prolific_symb_bound                   200
% 12.03/1.99  --lt_threshold                          2000
% 12.03/1.99  --clause_weak_htbl                      true
% 12.03/1.99  --gc_record_bc_elim                     false
% 12.03/1.99  
% 12.03/1.99  ------ Preprocessing Options
% 12.03/1.99  
% 12.03/1.99  --preprocessing_flag                    true
% 12.03/1.99  --time_out_prep_mult                    0.1
% 12.03/1.99  --splitting_mode                        input
% 12.03/1.99  --splitting_grd                         true
% 12.03/1.99  --splitting_cvd                         false
% 12.03/1.99  --splitting_cvd_svl                     false
% 12.03/1.99  --splitting_nvd                         32
% 12.03/1.99  --sub_typing                            true
% 12.03/1.99  --prep_gs_sim                           false
% 12.03/1.99  --prep_unflatten                        true
% 12.03/1.99  --prep_res_sim                          true
% 12.03/1.99  --prep_upred                            true
% 12.03/1.99  --prep_sem_filter                       exhaustive
% 12.03/1.99  --prep_sem_filter_out                   false
% 12.03/1.99  --pred_elim                             false
% 12.03/1.99  --res_sim_input                         true
% 12.03/1.99  --eq_ax_congr_red                       true
% 12.03/1.99  --pure_diseq_elim                       true
% 12.03/1.99  --brand_transform                       false
% 12.03/1.99  --non_eq_to_eq                          false
% 12.03/1.99  --prep_def_merge                        true
% 12.03/1.99  --prep_def_merge_prop_impl              false
% 12.03/1.99  --prep_def_merge_mbd                    true
% 12.03/1.99  --prep_def_merge_tr_red                 false
% 12.03/1.99  --prep_def_merge_tr_cl                  false
% 12.03/1.99  --smt_preprocessing                     true
% 12.03/1.99  --smt_ac_axioms                         fast
% 12.03/1.99  --preprocessed_out                      false
% 12.03/1.99  --preprocessed_stats                    false
% 12.03/1.99  
% 12.03/1.99  ------ Abstraction refinement Options
% 12.03/1.99  
% 12.03/1.99  --abstr_ref                             []
% 12.03/1.99  --abstr_ref_prep                        false
% 12.03/1.99  --abstr_ref_until_sat                   false
% 12.03/1.99  --abstr_ref_sig_restrict                funpre
% 12.03/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 12.03/1.99  --abstr_ref_under                       []
% 12.03/1.99  
% 12.03/1.99  ------ SAT Options
% 12.03/1.99  
% 12.03/1.99  --sat_mode                              false
% 12.03/1.99  --sat_fm_restart_options                ""
% 12.03/1.99  --sat_gr_def                            false
% 12.03/1.99  --sat_epr_types                         true
% 12.03/1.99  --sat_non_cyclic_types                  false
% 12.03/1.99  --sat_finite_models                     false
% 12.03/1.99  --sat_fm_lemmas                         false
% 12.03/1.99  --sat_fm_prep                           false
% 12.03/1.99  --sat_fm_uc_incr                        true
% 12.03/1.99  --sat_out_model                         small
% 12.03/1.99  --sat_out_clauses                       false
% 12.03/1.99  
% 12.03/1.99  ------ QBF Options
% 12.03/1.99  
% 12.03/1.99  --qbf_mode                              false
% 12.03/1.99  --qbf_elim_univ                         false
% 12.03/1.99  --qbf_dom_inst                          none
% 12.03/1.99  --qbf_dom_pre_inst                      false
% 12.03/1.99  --qbf_sk_in                             false
% 12.03/1.99  --qbf_pred_elim                         true
% 12.03/1.99  --qbf_split                             512
% 12.03/1.99  
% 12.03/1.99  ------ BMC1 Options
% 12.03/1.99  
% 12.03/1.99  --bmc1_incremental                      false
% 12.03/1.99  --bmc1_axioms                           reachable_all
% 12.03/1.99  --bmc1_min_bound                        0
% 12.03/1.99  --bmc1_max_bound                        -1
% 12.03/1.99  --bmc1_max_bound_default                -1
% 12.03/1.99  --bmc1_symbol_reachability              true
% 12.03/1.99  --bmc1_property_lemmas                  false
% 12.03/1.99  --bmc1_k_induction                      false
% 12.03/1.99  --bmc1_non_equiv_states                 false
% 12.03/1.99  --bmc1_deadlock                         false
% 12.03/1.99  --bmc1_ucm                              false
% 12.03/1.99  --bmc1_add_unsat_core                   none
% 12.03/1.99  --bmc1_unsat_core_children              false
% 12.03/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 12.03/1.99  --bmc1_out_stat                         full
% 12.03/1.99  --bmc1_ground_init                      false
% 12.03/1.99  --bmc1_pre_inst_next_state              false
% 12.03/1.99  --bmc1_pre_inst_state                   false
% 12.03/1.99  --bmc1_pre_inst_reach_state             false
% 12.03/1.99  --bmc1_out_unsat_core                   false
% 12.03/1.99  --bmc1_aig_witness_out                  false
% 12.03/1.99  --bmc1_verbose                          false
% 12.03/1.99  --bmc1_dump_clauses_tptp                false
% 12.03/1.99  --bmc1_dump_unsat_core_tptp             false
% 12.03/1.99  --bmc1_dump_file                        -
% 12.03/1.99  --bmc1_ucm_expand_uc_limit              128
% 12.03/1.99  --bmc1_ucm_n_expand_iterations          6
% 12.03/1.99  --bmc1_ucm_extend_mode                  1
% 12.03/1.99  --bmc1_ucm_init_mode                    2
% 12.03/1.99  --bmc1_ucm_cone_mode                    none
% 12.03/1.99  --bmc1_ucm_reduced_relation_type        0
% 12.03/1.99  --bmc1_ucm_relax_model                  4
% 12.03/1.99  --bmc1_ucm_full_tr_after_sat            true
% 12.03/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 12.03/1.99  --bmc1_ucm_layered_model                none
% 12.03/1.99  --bmc1_ucm_max_lemma_size               10
% 12.03/1.99  
% 12.03/1.99  ------ AIG Options
% 12.03/1.99  
% 12.03/1.99  --aig_mode                              false
% 12.03/1.99  
% 12.03/1.99  ------ Instantiation Options
% 12.03/1.99  
% 12.03/1.99  --instantiation_flag                    true
% 12.03/1.99  --inst_sos_flag                         false
% 12.03/1.99  --inst_sos_phase                        true
% 12.03/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 12.03/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 12.03/1.99  --inst_lit_sel_side                     num_symb
% 12.03/1.99  --inst_solver_per_active                1400
% 12.03/1.99  --inst_solver_calls_frac                1.
% 12.03/1.99  --inst_passive_queue_type               priority_queues
% 12.03/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 12.03/1.99  --inst_passive_queues_freq              [25;2]
% 12.03/1.99  --inst_dismatching                      true
% 12.03/1.99  --inst_eager_unprocessed_to_passive     true
% 12.03/1.99  --inst_prop_sim_given                   true
% 12.03/1.99  --inst_prop_sim_new                     false
% 12.03/1.99  --inst_subs_new                         false
% 12.03/1.99  --inst_eq_res_simp                      false
% 12.03/1.99  --inst_subs_given                       false
% 12.03/1.99  --inst_orphan_elimination               true
% 12.03/1.99  --inst_learning_loop_flag               true
% 12.03/1.99  --inst_learning_start                   3000
% 12.03/1.99  --inst_learning_factor                  2
% 12.03/1.99  --inst_start_prop_sim_after_learn       3
% 12.03/1.99  --inst_sel_renew                        solver
% 12.03/1.99  --inst_lit_activity_flag                true
% 12.03/1.99  --inst_restr_to_given                   false
% 12.03/1.99  --inst_activity_threshold               500
% 12.03/1.99  --inst_out_proof                        true
% 12.03/1.99  
% 12.03/1.99  ------ Resolution Options
% 12.03/1.99  
% 12.03/1.99  --resolution_flag                       true
% 12.03/1.99  --res_lit_sel                           adaptive
% 12.03/1.99  --res_lit_sel_side                      none
% 12.03/1.99  --res_ordering                          kbo
% 12.03/1.99  --res_to_prop_solver                    active
% 12.03/1.99  --res_prop_simpl_new                    false
% 12.03/1.99  --res_prop_simpl_given                  true
% 12.03/1.99  --res_passive_queue_type                priority_queues
% 12.03/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 12.03/1.99  --res_passive_queues_freq               [15;5]
% 12.03/1.99  --res_forward_subs                      full
% 12.03/1.99  --res_backward_subs                     full
% 12.03/1.99  --res_forward_subs_resolution           true
% 12.03/1.99  --res_backward_subs_resolution          true
% 12.03/1.99  --res_orphan_elimination                true
% 12.03/1.99  --res_time_limit                        2.
% 12.03/1.99  --res_out_proof                         true
% 12.03/1.99  
% 12.03/1.99  ------ Superposition Options
% 12.03/1.99  
% 12.03/1.99  --superposition_flag                    true
% 12.03/1.99  --sup_passive_queue_type                priority_queues
% 12.03/1.99  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 12.03/1.99  --sup_passive_queues_freq               [1;4]
% 12.03/1.99  --demod_completeness_check              fast
% 12.03/1.99  --demod_use_ground                      true
% 12.03/1.99  --sup_to_prop_solver                    passive
% 12.03/1.99  --sup_prop_simpl_new                    true
% 12.03/1.99  --sup_prop_simpl_given                  true
% 12.03/1.99  --sup_fun_splitting                     false
% 12.03/1.99  --sup_smt_interval                      50000
% 12.03/1.99  
% 12.03/1.99  ------ Superposition Simplification Setup
% 12.03/1.99  
% 12.03/1.99  --sup_indices_passive                   []
% 12.03/1.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 12.03/1.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 12.03/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 12.03/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 12.03/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 12.03/1.99  --sup_full_bw                           [BwDemod]
% 12.03/1.99  --sup_immed_triv                        [TrivRules]
% 12.03/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 12.03/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 12.03/1.99  --sup_immed_bw_main                     []
% 12.03/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 12.03/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 12.03/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 12.03/2.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 12.03/2.00  
% 12.03/2.00  ------ Combination Options
% 12.03/2.00  
% 12.03/2.00  --comb_res_mult                         3
% 12.03/2.00  --comb_sup_mult                         2
% 12.03/2.00  --comb_inst_mult                        10
% 12.03/2.00  
% 12.03/2.00  ------ Debug Options
% 12.03/2.00  
% 12.03/2.00  --dbg_backtrace                         false
% 12.03/2.00  --dbg_dump_prop_clauses                 false
% 12.03/2.00  --dbg_dump_prop_clauses_file            -
% 12.03/2.00  --dbg_out_stat                          false
% 12.03/2.00  
% 12.03/2.00  
% 12.03/2.00  
% 12.03/2.00  
% 12.03/2.00  ------ Proving...
% 12.03/2.00  
% 12.03/2.00  
% 12.03/2.00  % SZS status Theorem for theBenchmark.p
% 12.03/2.00  
% 12.03/2.00  % SZS output start CNFRefutation for theBenchmark.p
% 12.03/2.00  
% 12.03/2.00  fof(f8,axiom,(
% 12.03/2.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 12.03/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.03/2.00  
% 12.03/2.00  fof(f38,plain,(
% 12.03/2.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 12.03/2.00    inference(cnf_transformation,[],[f8])).
% 12.03/2.00  
% 12.03/2.00  fof(f6,axiom,(
% 12.03/2.00    ! [X0,X1,X2] : ((! [X3] : ((r1_tarski(X3,X2) & r1_tarski(X3,X1)) => r1_tarski(X3,X0)) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k3_xboole_0(X1,X2) = X0)),
% 12.03/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.03/2.00  
% 12.03/2.00  fof(f19,plain,(
% 12.03/2.00    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = X0 | (? [X3] : (~r1_tarski(X3,X0) & (r1_tarski(X3,X2) & r1_tarski(X3,X1))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 12.03/2.00    inference(ennf_transformation,[],[f6])).
% 12.03/2.00  
% 12.03/2.00  fof(f20,plain,(
% 12.03/2.00    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = X0 | ? [X3] : (~r1_tarski(X3,X0) & r1_tarski(X3,X2) & r1_tarski(X3,X1)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 12.03/2.00    inference(flattening,[],[f19])).
% 12.03/2.00  
% 12.03/2.00  fof(f25,plain,(
% 12.03/2.00    ! [X2,X1,X0] : (? [X3] : (~r1_tarski(X3,X0) & r1_tarski(X3,X2) & r1_tarski(X3,X1)) => (~r1_tarski(sK0(X0,X1,X2),X0) & r1_tarski(sK0(X0,X1,X2),X2) & r1_tarski(sK0(X0,X1,X2),X1)))),
% 12.03/2.00    introduced(choice_axiom,[])).
% 12.03/2.00  
% 12.03/2.00  fof(f26,plain,(
% 12.03/2.00    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = X0 | (~r1_tarski(sK0(X0,X1,X2),X0) & r1_tarski(sK0(X0,X1,X2),X2) & r1_tarski(sK0(X0,X1,X2),X1)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 12.03/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f25])).
% 12.03/2.00  
% 12.03/2.00  fof(f35,plain,(
% 12.03/2.00    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = X0 | r1_tarski(sK0(X0,X1,X2),X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 12.03/2.00    inference(cnf_transformation,[],[f26])).
% 12.03/2.00  
% 12.03/2.00  fof(f36,plain,(
% 12.03/2.00    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = X0 | ~r1_tarski(sK0(X0,X1,X2),X0) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 12.03/2.00    inference(cnf_transformation,[],[f26])).
% 12.03/2.00  
% 12.03/2.00  fof(f3,axiom,(
% 12.03/2.00    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 12.03/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.03/2.00  
% 12.03/2.00  fof(f31,plain,(
% 12.03/2.00    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 12.03/2.00    inference(cnf_transformation,[],[f3])).
% 12.03/2.00  
% 12.03/2.00  fof(f2,axiom,(
% 12.03/2.00    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 12.03/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.03/2.00  
% 12.03/2.00  fof(f14,plain,(
% 12.03/2.00    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 12.03/2.00    inference(ennf_transformation,[],[f2])).
% 12.03/2.00  
% 12.03/2.00  fof(f30,plain,(
% 12.03/2.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 12.03/2.00    inference(cnf_transformation,[],[f14])).
% 12.03/2.00  
% 12.03/2.00  fof(f10,axiom,(
% 12.03/2.00    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)))),
% 12.03/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.03/2.00  
% 12.03/2.00  fof(f22,plain,(
% 12.03/2.00    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) | ~r1_tarski(X0,X1))),
% 12.03/2.00    inference(ennf_transformation,[],[f10])).
% 12.03/2.00  
% 12.03/2.00  fof(f40,plain,(
% 12.03/2.00    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 12.03/2.00    inference(cnf_transformation,[],[f22])).
% 12.03/2.00  
% 12.03/2.00  fof(f11,conjecture,(
% 12.03/2.00    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)))),
% 12.03/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.03/2.00  
% 12.03/2.00  fof(f12,negated_conjecture,(
% 12.03/2.00    ~! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)))),
% 12.03/2.00    inference(negated_conjecture,[],[f11])).
% 12.03/2.00  
% 12.03/2.00  fof(f23,plain,(
% 12.03/2.00    ? [X0,X1,X2,X3] : (~r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) & (r1_tarski(X2,X3) & r1_tarski(X0,X1)))),
% 12.03/2.00    inference(ennf_transformation,[],[f12])).
% 12.03/2.00  
% 12.03/2.00  fof(f24,plain,(
% 12.03/2.00    ? [X0,X1,X2,X3] : (~r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) & r1_tarski(X2,X3) & r1_tarski(X0,X1))),
% 12.03/2.00    inference(flattening,[],[f23])).
% 12.03/2.00  
% 12.03/2.00  fof(f27,plain,(
% 12.03/2.00    ? [X0,X1,X2,X3] : (~r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) & r1_tarski(X2,X3) & r1_tarski(X0,X1)) => (~r1_tarski(k3_xboole_0(sK1,sK3),k3_xboole_0(sK2,sK4)) & r1_tarski(sK3,sK4) & r1_tarski(sK1,sK2))),
% 12.03/2.00    introduced(choice_axiom,[])).
% 12.03/2.00  
% 12.03/2.00  fof(f28,plain,(
% 12.03/2.00    ~r1_tarski(k3_xboole_0(sK1,sK3),k3_xboole_0(sK2,sK4)) & r1_tarski(sK3,sK4) & r1_tarski(sK1,sK2)),
% 12.03/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f24,f27])).
% 12.03/2.00  
% 12.03/2.00  fof(f42,plain,(
% 12.03/2.00    r1_tarski(sK3,sK4)),
% 12.03/2.00    inference(cnf_transformation,[],[f28])).
% 12.03/2.00  
% 12.03/2.00  fof(f9,axiom,(
% 12.03/2.00    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 12.03/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.03/2.00  
% 12.03/2.00  fof(f39,plain,(
% 12.03/2.00    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 12.03/2.00    inference(cnf_transformation,[],[f9])).
% 12.03/2.00  
% 12.03/2.00  fof(f7,axiom,(
% 12.03/2.00    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)))),
% 12.03/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.03/2.00  
% 12.03/2.00  fof(f21,plain,(
% 12.03/2.00    ! [X0,X1,X2] : (r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X1))),
% 12.03/2.00    inference(ennf_transformation,[],[f7])).
% 12.03/2.00  
% 12.03/2.00  fof(f37,plain,(
% 12.03/2.00    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 12.03/2.00    inference(cnf_transformation,[],[f21])).
% 12.03/2.00  
% 12.03/2.00  fof(f1,axiom,(
% 12.03/2.00    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 12.03/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.03/2.00  
% 12.03/2.00  fof(f13,plain,(
% 12.03/2.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 12.03/2.00    inference(ennf_transformation,[],[f1])).
% 12.03/2.00  
% 12.03/2.00  fof(f29,plain,(
% 12.03/2.00    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 12.03/2.00    inference(cnf_transformation,[],[f13])).
% 12.03/2.00  
% 12.03/2.00  fof(f4,axiom,(
% 12.03/2.00    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 12.03/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.03/2.00  
% 12.03/2.00  fof(f15,plain,(
% 12.03/2.00    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 12.03/2.00    inference(ennf_transformation,[],[f4])).
% 12.03/2.00  
% 12.03/2.00  fof(f16,plain,(
% 12.03/2.00    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 12.03/2.00    inference(flattening,[],[f15])).
% 12.03/2.00  
% 12.03/2.00  fof(f32,plain,(
% 12.03/2.00    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 12.03/2.00    inference(cnf_transformation,[],[f16])).
% 12.03/2.00  
% 12.03/2.00  fof(f43,plain,(
% 12.03/2.00    ~r1_tarski(k3_xboole_0(sK1,sK3),k3_xboole_0(sK2,sK4))),
% 12.03/2.00    inference(cnf_transformation,[],[f28])).
% 12.03/2.00  
% 12.03/2.00  fof(f41,plain,(
% 12.03/2.00    r1_tarski(sK1,sK2)),
% 12.03/2.00    inference(cnf_transformation,[],[f28])).
% 12.03/2.00  
% 12.03/2.00  fof(f5,axiom,(
% 12.03/2.00    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 12.03/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.03/2.00  
% 12.03/2.00  fof(f17,plain,(
% 12.03/2.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 12.03/2.00    inference(ennf_transformation,[],[f5])).
% 12.03/2.00  
% 12.03/2.00  fof(f18,plain,(
% 12.03/2.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 12.03/2.00    inference(flattening,[],[f17])).
% 12.03/2.00  
% 12.03/2.00  fof(f33,plain,(
% 12.03/2.00    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 12.03/2.00    inference(cnf_transformation,[],[f18])).
% 12.03/2.00  
% 12.03/2.00  cnf(c_9,plain,
% 12.03/2.00      ( r1_tarski(k1_xboole_0,X0) ),
% 12.03/2.00      inference(cnf_transformation,[],[f38]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_363,plain,
% 12.03/2.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 12.03/2.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_6,plain,
% 12.03/2.00      ( ~ r1_tarski(X0,X1)
% 12.03/2.00      | ~ r1_tarski(X0,X2)
% 12.03/2.00      | r1_tarski(sK0(X0,X1,X2),X2)
% 12.03/2.00      | k3_xboole_0(X1,X2) = X0 ),
% 12.03/2.00      inference(cnf_transformation,[],[f35]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_366,plain,
% 12.03/2.00      ( k3_xboole_0(X0,X1) = X2
% 12.03/2.00      | r1_tarski(X2,X0) != iProver_top
% 12.03/2.00      | r1_tarski(X2,X1) != iProver_top
% 12.03/2.00      | r1_tarski(sK0(X2,X0,X1),X1) = iProver_top ),
% 12.03/2.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_5,plain,
% 12.03/2.00      ( ~ r1_tarski(X0,X1)
% 12.03/2.00      | ~ r1_tarski(X0,X2)
% 12.03/2.00      | ~ r1_tarski(sK0(X0,X1,X2),X0)
% 12.03/2.00      | k3_xboole_0(X1,X2) = X0 ),
% 12.03/2.00      inference(cnf_transformation,[],[f36]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_367,plain,
% 12.03/2.00      ( k3_xboole_0(X0,X1) = X2
% 12.03/2.00      | r1_tarski(X2,X0) != iProver_top
% 12.03/2.00      | r1_tarski(X2,X1) != iProver_top
% 12.03/2.00      | r1_tarski(sK0(X2,X0,X1),X2) != iProver_top ),
% 12.03/2.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_2637,plain,
% 12.03/2.00      ( k3_xboole_0(X0,X1) = X1
% 12.03/2.00      | r1_tarski(X1,X0) != iProver_top
% 12.03/2.00      | r1_tarski(X1,X1) != iProver_top ),
% 12.03/2.00      inference(superposition,[status(thm)],[c_366,c_367]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_4811,plain,
% 12.03/2.00      ( ~ r1_tarski(X0,X1)
% 12.03/2.00      | ~ r1_tarski(X0,X0)
% 12.03/2.00      | k3_xboole_0(X1,X0) = X0 ),
% 12.03/2.00      inference(resolution,[status(thm)],[c_5,c_6]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_2664,plain,
% 12.03/2.00      ( ~ r1_tarski(X0,X1)
% 12.03/2.00      | ~ r1_tarski(X0,X0)
% 12.03/2.00      | k3_xboole_0(X1,X0) = X0 ),
% 12.03/2.00      inference(predicate_to_equality_rev,[status(thm)],[c_2637]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_2,plain,
% 12.03/2.00      ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
% 12.03/2.00      inference(cnf_transformation,[],[f31]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_370,plain,
% 12.03/2.00      ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
% 12.03/2.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_1,plain,
% 12.03/2.00      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 12.03/2.00      inference(cnf_transformation,[],[f30]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_371,plain,
% 12.03/2.00      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 12.03/2.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_1137,plain,
% 12.03/2.00      ( k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0 ),
% 12.03/2.00      inference(superposition,[status(thm)],[c_370,c_371]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_1138,plain,
% 12.03/2.00      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 12.03/2.00      inference(superposition,[status(thm)],[c_363,c_371]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_11,plain,
% 12.03/2.00      ( ~ r1_tarski(X0,X1)
% 12.03/2.00      | r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ),
% 12.03/2.00      inference(cnf_transformation,[],[f40]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_361,plain,
% 12.03/2.00      ( r1_tarski(X0,X1) != iProver_top
% 12.03/2.00      | r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) = iProver_top ),
% 12.03/2.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_2923,plain,
% 12.03/2.00      ( r1_tarski(X0,k2_xboole_0(X1,X0)) = iProver_top
% 12.03/2.00      | r1_tarski(k1_xboole_0,X1) != iProver_top ),
% 12.03/2.00      inference(superposition,[status(thm)],[c_1138,c_361]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_8944,plain,
% 12.03/2.00      ( r1_tarski(X0,k2_xboole_0(X1,X0)) = iProver_top ),
% 12.03/2.00      inference(forward_subsumption_resolution,
% 12.03/2.00                [status(thm)],
% 12.03/2.00                [c_2923,c_363]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_8946,plain,
% 12.03/2.00      ( r1_tarski(X0,X0) = iProver_top ),
% 12.03/2.00      inference(superposition,[status(thm)],[c_1137,c_8944]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_9004,plain,
% 12.03/2.00      ( r1_tarski(X0,X0) ),
% 12.03/2.00      inference(predicate_to_equality_rev,[status(thm)],[c_8946]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_9139,plain,
% 12.03/2.00      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X1,X0) = X0 ),
% 12.03/2.00      inference(global_propositional_subsumption,
% 12.03/2.00                [status(thm)],
% 12.03/2.00                [c_4811,c_2664,c_9004]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_9141,plain,
% 12.03/2.00      ( k3_xboole_0(X0,X1) = X1 | r1_tarski(X1,X0) != iProver_top ),
% 12.03/2.00      inference(predicate_to_equality,[status(thm)],[c_9139]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_22231,plain,
% 12.03/2.00      ( r1_tarski(X1,X0) != iProver_top | k3_xboole_0(X0,X1) = X1 ),
% 12.03/2.00      inference(global_propositional_subsumption,
% 12.03/2.00                [status(thm)],
% 12.03/2.00                [c_2637,c_9141]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_22232,plain,
% 12.03/2.00      ( k3_xboole_0(X0,X1) = X1 | r1_tarski(X1,X0) != iProver_top ),
% 12.03/2.00      inference(renaming,[status(thm)],[c_22231]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_22240,plain,
% 12.03/2.00      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 12.03/2.00      inference(superposition,[status(thm)],[c_363,c_22232]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_13,negated_conjecture,
% 12.03/2.00      ( r1_tarski(sK3,sK4) ),
% 12.03/2.00      inference(cnf_transformation,[],[f42]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_359,plain,
% 12.03/2.00      ( r1_tarski(sK3,sK4) = iProver_top ),
% 12.03/2.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_10,plain,
% 12.03/2.00      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 12.03/2.00      inference(cnf_transformation,[],[f39]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_362,plain,
% 12.03/2.00      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 12.03/2.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_22241,plain,
% 12.03/2.00      ( k3_xboole_0(k2_xboole_0(X0,X1),X0) = X0 ),
% 12.03/2.00      inference(superposition,[status(thm)],[c_362,c_22232]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_8,plain,
% 12.03/2.00      ( ~ r1_tarski(X0,X1)
% 12.03/2.00      | r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)) ),
% 12.03/2.00      inference(cnf_transformation,[],[f37]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_364,plain,
% 12.03/2.00      ( r1_tarski(X0,X1) != iProver_top
% 12.03/2.00      | r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)) = iProver_top ),
% 12.03/2.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_23354,plain,
% 12.03/2.00      ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
% 12.03/2.00      | r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
% 12.03/2.00      inference(superposition,[status(thm)],[c_22241,c_364]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_30511,plain,
% 12.03/2.00      ( r1_tarski(X0,X1) != iProver_top
% 12.03/2.00      | r1_tarski(k3_xboole_0(k2_xboole_0(X0,X2),X1),X1) = iProver_top ),
% 12.03/2.00      inference(superposition,[status(thm)],[c_361,c_23354]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_34639,plain,
% 12.03/2.00      ( k2_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),X2),X2) = X2
% 12.03/2.00      | r1_tarski(X0,X2) != iProver_top ),
% 12.03/2.00      inference(superposition,[status(thm)],[c_30511,c_371]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_35185,plain,
% 12.03/2.00      ( k2_xboole_0(k3_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),X2),X0),X0) = X0 ),
% 12.03/2.00      inference(superposition,[status(thm)],[c_370,c_34639]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_0,plain,
% 12.03/2.00      ( r1_tarski(X0,X1) | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 12.03/2.00      inference(cnf_transformation,[],[f29]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_372,plain,
% 12.03/2.00      ( r1_tarski(X0,X1) = iProver_top
% 12.03/2.00      | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
% 12.03/2.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_37857,plain,
% 12.03/2.00      ( r1_tarski(X0,X1) != iProver_top
% 12.03/2.00      | r1_tarski(k3_xboole_0(k2_xboole_0(k3_xboole_0(X0,X2),X3),X0),X1) = iProver_top ),
% 12.03/2.00      inference(superposition,[status(thm)],[c_35185,c_372]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_51378,plain,
% 12.03/2.00      ( k2_xboole_0(k3_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),X2),X0),X3) = X3
% 12.03/2.00      | r1_tarski(X0,X3) != iProver_top ),
% 12.03/2.00      inference(superposition,[status(thm)],[c_37857,c_371]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_55514,plain,
% 12.03/2.00      ( k2_xboole_0(k3_xboole_0(k2_xboole_0(k3_xboole_0(sK3,X0),X1),sK3),sK4) = sK4 ),
% 12.03/2.00      inference(superposition,[status(thm)],[c_359,c_51378]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_56554,plain,
% 12.03/2.00      ( r1_tarski(k3_xboole_0(k2_xboole_0(k3_xboole_0(sK3,X0),X1),sK3),sK4) = iProver_top ),
% 12.03/2.00      inference(superposition,[status(thm)],[c_55514,c_362]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_58678,plain,
% 12.03/2.00      ( r1_tarski(k3_xboole_0(k2_xboole_0(k1_xboole_0,X0),sK3),sK4) = iProver_top ),
% 12.03/2.00      inference(superposition,[status(thm)],[c_22240,c_56554]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_58745,plain,
% 12.03/2.00      ( r1_tarski(k3_xboole_0(X0,sK3),sK4) = iProver_top ),
% 12.03/2.00      inference(light_normalisation,[status(thm)],[c_58678,c_1138]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_58750,plain,
% 12.03/2.00      ( r1_tarski(k3_xboole_0(sK1,sK3),sK4) = iProver_top ),
% 12.03/2.00      inference(instantiation,[status(thm)],[c_58745]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_3,plain,
% 12.03/2.00      ( ~ r1_tarski(X0,X1)
% 12.03/2.00      | ~ r1_tarski(X0,X2)
% 12.03/2.00      | r1_tarski(X0,k3_xboole_0(X1,X2)) ),
% 12.03/2.00      inference(cnf_transformation,[],[f32]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_369,plain,
% 12.03/2.00      ( r1_tarski(X0,X1) != iProver_top
% 12.03/2.00      | r1_tarski(X0,X2) != iProver_top
% 12.03/2.00      | r1_tarski(X0,k3_xboole_0(X1,X2)) = iProver_top ),
% 12.03/2.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_12,negated_conjecture,
% 12.03/2.00      ( ~ r1_tarski(k3_xboole_0(sK1,sK3),k3_xboole_0(sK2,sK4)) ),
% 12.03/2.00      inference(cnf_transformation,[],[f43]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_360,plain,
% 12.03/2.00      ( r1_tarski(k3_xboole_0(sK1,sK3),k3_xboole_0(sK2,sK4)) != iProver_top ),
% 12.03/2.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_2254,plain,
% 12.03/2.00      ( r1_tarski(k3_xboole_0(sK1,sK3),sK4) != iProver_top
% 12.03/2.00      | r1_tarski(k3_xboole_0(sK1,sK3),sK2) != iProver_top ),
% 12.03/2.00      inference(superposition,[status(thm)],[c_369,c_360]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_14,negated_conjecture,
% 12.03/2.00      ( r1_tarski(sK1,sK2) ),
% 12.03/2.00      inference(cnf_transformation,[],[f41]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_358,plain,
% 12.03/2.00      ( r1_tarski(sK1,sK2) = iProver_top ),
% 12.03/2.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_4,plain,
% 12.03/2.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 12.03/2.00      inference(cnf_transformation,[],[f33]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_368,plain,
% 12.03/2.00      ( r1_tarski(X0,X1) != iProver_top
% 12.03/2.00      | r1_tarski(X1,X2) != iProver_top
% 12.03/2.00      | r1_tarski(X0,X2) = iProver_top ),
% 12.03/2.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_1820,plain,
% 12.03/2.00      ( r1_tarski(X0,X1) != iProver_top
% 12.03/2.00      | r1_tarski(k3_xboole_0(X0,X2),X1) = iProver_top ),
% 12.03/2.00      inference(superposition,[status(thm)],[c_370,c_368]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_5530,plain,
% 12.03/2.00      ( k2_xboole_0(k3_xboole_0(X0,X1),X2) = X2
% 12.03/2.00      | r1_tarski(X0,X2) != iProver_top ),
% 12.03/2.00      inference(superposition,[status(thm)],[c_1820,c_371]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_11440,plain,
% 12.03/2.00      ( k2_xboole_0(k3_xboole_0(sK1,X0),sK2) = sK2 ),
% 12.03/2.00      inference(superposition,[status(thm)],[c_358,c_5530]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_12110,plain,
% 12.03/2.00      ( r1_tarski(k3_xboole_0(sK1,X0),sK2) = iProver_top ),
% 12.03/2.00      inference(superposition,[status(thm)],[c_11440,c_362]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(c_14231,plain,
% 12.03/2.00      ( r1_tarski(k3_xboole_0(sK1,sK3),sK4) != iProver_top ),
% 12.03/2.00      inference(forward_subsumption_resolution,
% 12.03/2.00                [status(thm)],
% 12.03/2.00                [c_2254,c_12110]) ).
% 12.03/2.00  
% 12.03/2.00  cnf(contradiction,plain,
% 12.03/2.00      ( $false ),
% 12.03/2.00      inference(minisat,[status(thm)],[c_58750,c_14231]) ).
% 12.03/2.00  
% 12.03/2.00  
% 12.03/2.00  % SZS output end CNFRefutation for theBenchmark.p
% 12.03/2.00  
% 12.03/2.00  ------                               Statistics
% 12.03/2.00  
% 12.03/2.00  ------ Selected
% 12.03/2.00  
% 12.03/2.00  total_time:                             1.465
% 12.03/2.00  
%------------------------------------------------------------------------------
