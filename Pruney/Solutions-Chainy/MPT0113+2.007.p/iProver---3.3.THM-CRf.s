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
% DateTime   : Thu Dec  3 11:25:43 EST 2020

% Result     : Theorem 19.28s
% Output     : CNFRefutation 19.28s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 227 expanded)
%              Number of clauses        :   50 (  88 expanded)
%              Number of leaves         :   15 (  50 expanded)
%              Depth                    :   18
%              Number of atoms          :  146 ( 392 expanded)
%              Number of equality atoms :   76 ( 171 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f34,f30])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f38,f30])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
       => ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
      & r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f23,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,X2)
          | ~ r1_tarski(X0,X1) )
        & r1_tarski(X0,k4_xboole_0(X1,X2)) )
   => ( ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_tarski(sK0,sK1) )
      & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ( ~ r1_xboole_0(sK0,sK2)
      | ~ r1_tarski(sK0,sK1) )
    & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f23])).

fof(f39,plain,(
    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f24])).

fof(f45,plain,(
    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    inference(definition_unfolding,[],[f39,f30])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f11,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f43,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f36,f30])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f28,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f35,f30])).

fof(f7,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f40,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_11,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_11204,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_11209,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_11567,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_11204,c_11209])).

cnf(c_8,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_11205,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_11203,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_11568,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k1_xboole_0
    | r1_tarski(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_11203,c_11209])).

cnf(c_13415,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X2,k3_xboole_0(X2,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_11205,c_11568])).

cnf(c_14,negated_conjecture,
    ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_11201,plain,
    ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_13417,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_11201,c_11568])).

cnf(c_1,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_11210,plain,
    ( k3_xboole_0(X0,X1) != k1_xboole_0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_13582,plain,
    ( r1_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_13417,c_11210])).

cnf(c_57675,plain,
    ( r1_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,X0)),k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_13415,c_13582])).

cnf(c_10,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_13181,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(demodulation,[status(thm)],[c_11567,c_10])).

cnf(c_58659,plain,
    ( r1_xboole_0(sK0,k5_xboole_0(sK2,k3_xboole_0(sK2,X0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_57675,c_13181])).

cnf(c_61419,plain,
    ( r1_xboole_0(sK0,k5_xboole_0(sK2,k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_11567,c_58659])).

cnf(c_61423,plain,
    ( r1_xboole_0(sK0,sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_61419,c_13181])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_11206,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_11422,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = sK0 ),
    inference(superposition,[status(thm)],[c_11201,c_11206])).

cnf(c_11530,plain,
    ( r1_tarski(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) != iProver_top
    | r1_xboole_0(X0,k5_xboole_0(sK0,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_11422,c_11203])).

cnf(c_11668,plain,
    ( r1_xboole_0(sK0,k5_xboole_0(sK0,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_11201,c_11530])).

cnf(c_4,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_11208,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_11704,plain,
    ( r1_xboole_0(k5_xboole_0(sK0,sK0),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_11668,c_11208])).

cnf(c_11740,plain,
    ( k3_xboole_0(k5_xboole_0(sK0,sK0),sK0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_11704,c_11209])).

cnf(c_3,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_11370,plain,
    ( r1_tarski(k5_xboole_0(X0,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_11205])).

cnf(c_11424,plain,
    ( k3_xboole_0(k5_xboole_0(X0,X0),X0) = k5_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_11370,c_11206])).

cnf(c_11775,plain,
    ( k5_xboole_0(sK0,sK0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_11740,c_11424])).

cnf(c_9,plain,
    ( k2_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_11433,plain,
    ( k2_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK0)) = k2_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK0) ),
    inference(superposition,[status(thm)],[c_11422,c_9])).

cnf(c_12049,plain,
    ( k2_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k1_xboole_0) = k2_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK0) ),
    inference(demodulation,[status(thm)],[c_11775,c_11433])).

cnf(c_6,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_12051,plain,
    ( k2_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK0) = k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) ),
    inference(demodulation,[status(thm)],[c_12049,c_6])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_5,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_11207,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_11833,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k2_xboole_0(X2,X0),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_11207])).

cnf(c_12253,plain,
    ( r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0) != iProver_top
    | r1_tarski(sK0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_12051,c_11833])).

cnf(c_12886,plain,
    ( r1_tarski(sK0,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_11205,c_12253])).

cnf(c_13,negated_conjecture,
    ( ~ r1_tarski(sK0,sK1)
    | ~ r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_16,plain,
    ( r1_tarski(sK0,sK1) != iProver_top
    | r1_xboole_0(sK0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_61423,c_12886,c_16])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:46:48 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 19.28/3.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.28/3.01  
% 19.28/3.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.28/3.01  
% 19.28/3.01  ------  iProver source info
% 19.28/3.01  
% 19.28/3.01  git: date: 2020-06-30 10:37:57 +0100
% 19.28/3.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.28/3.01  git: non_committed_changes: false
% 19.28/3.01  git: last_make_outside_of_git: false
% 19.28/3.01  
% 19.28/3.01  ------ 
% 19.28/3.01  ------ Parsing...
% 19.28/3.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.28/3.01  
% 19.28/3.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 19.28/3.01  
% 19.28/3.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.28/3.01  
% 19.28/3.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.28/3.01  ------ Proving...
% 19.28/3.01  ------ Problem Properties 
% 19.28/3.01  
% 19.28/3.01  
% 19.28/3.01  clauses                                 15
% 19.28/3.01  conjectures                             2
% 19.28/3.01  EPR                                     3
% 19.28/3.01  Horn                                    15
% 19.28/3.01  unary                                   8
% 19.28/3.01  binary                                  7
% 19.28/3.01  lits                                    22
% 19.28/3.01  lits eq                                 8
% 19.28/3.01  fd_pure                                 0
% 19.28/3.01  fd_pseudo                               0
% 19.28/3.01  fd_cond                                 0
% 19.28/3.01  fd_pseudo_cond                          0
% 19.28/3.01  AC symbols                              0
% 19.28/3.01  
% 19.28/3.01  ------ Input Options Time Limit: Unbounded
% 19.28/3.01  
% 19.28/3.01  
% 19.28/3.01  
% 19.28/3.01  
% 19.28/3.01  ------ Preprocessing...
% 19.28/3.01  
% 19.28/3.01  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 19.28/3.01  Current options:
% 19.28/3.01  ------ 
% 19.28/3.01  
% 19.28/3.01  
% 19.28/3.01  
% 19.28/3.01  
% 19.28/3.01  ------ Proving...
% 19.28/3.01  
% 19.28/3.01  
% 19.28/3.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.28/3.01  
% 19.28/3.01  ------ Proving...
% 19.28/3.01  
% 19.28/3.01  
% 19.28/3.01  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.28/3.01  
% 19.28/3.01  ------ Proving...
% 19.28/3.01  
% 19.28/3.01  
% 19.28/3.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.28/3.01  
% 19.28/3.01  ------ Proving...
% 19.28/3.01  
% 19.28/3.01  
% 19.28/3.01  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.28/3.01  
% 19.28/3.01  ------ Proving...
% 19.28/3.01  
% 19.28/3.01  
% 19.28/3.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.28/3.01  
% 19.28/3.01  ------ Proving...
% 19.28/3.01  
% 19.28/3.01  
% 19.28/3.01  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.28/3.01  
% 19.28/3.01  ------ Proving...
% 19.28/3.01  
% 19.28/3.01  
% 19.28/3.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.28/3.01  
% 19.28/3.01  ------ Proving...
% 19.28/3.01  
% 19.28/3.01  
% 19.28/3.01  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.28/3.01  
% 19.28/3.01  ------ Proving...
% 19.28/3.01  
% 19.28/3.01  
% 19.28/3.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.28/3.01  
% 19.28/3.01  ------ Proving...
% 19.28/3.01  
% 19.28/3.01  
% 19.28/3.01  ------ Preprocessing...
% 19.28/3.01  
% 19.28/3.01  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.28/3.01  
% 19.28/3.01  ------ Proving...
% 19.28/3.01  
% 19.28/3.01  
% 19.28/3.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.28/3.01  
% 19.28/3.01  ------ Proving...
% 19.28/3.01  
% 19.28/3.01  
% 19.28/3.01  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.28/3.01  
% 19.28/3.01  ------ Proving...
% 19.28/3.01  
% 19.28/3.01  
% 19.28/3.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.28/3.01  
% 19.28/3.01  ------ Proving...
% 19.28/3.01  
% 19.28/3.01  
% 19.28/3.01  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.28/3.01  
% 19.28/3.01  ------ Proving...
% 19.28/3.01  
% 19.28/3.01  
% 19.28/3.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.28/3.01  
% 19.28/3.01  ------ Proving...
% 19.28/3.01  
% 19.28/3.01  
% 19.28/3.01  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.28/3.01  
% 19.28/3.01  ------ Proving...
% 19.28/3.01  
% 19.28/3.01  
% 19.28/3.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.28/3.01  
% 19.28/3.01  ------ Proving...
% 19.28/3.01  
% 19.28/3.01  
% 19.28/3.01  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.28/3.01  
% 19.28/3.01  ------ Proving...
% 19.28/3.01  
% 19.28/3.01  
% 19.28/3.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.28/3.01  
% 19.28/3.01  ------ Proving...
% 19.28/3.01  
% 19.28/3.01  
% 19.28/3.01  ------ Preprocessing...
% 19.28/3.01  
% 19.28/3.01  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.28/3.01  
% 19.28/3.01  ------ Proving...
% 19.28/3.01  
% 19.28/3.01  
% 19.28/3.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.28/3.01  
% 19.28/3.01  ------ Proving...
% 19.28/3.01  
% 19.28/3.01  
% 19.28/3.01  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.28/3.01  
% 19.28/3.01  ------ Proving...
% 19.28/3.01  
% 19.28/3.01  
% 19.28/3.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.28/3.01  
% 19.28/3.01  ------ Proving...
% 19.28/3.01  
% 19.28/3.01  
% 19.28/3.01  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.28/3.01  
% 19.28/3.01  ------ Proving...
% 19.28/3.01  
% 19.28/3.01  
% 19.28/3.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.28/3.01  
% 19.28/3.01  ------ Proving...
% 19.28/3.01  
% 19.28/3.01  
% 19.28/3.01  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.28/3.01  
% 19.28/3.01  ------ Proving...
% 19.28/3.01  
% 19.28/3.01  
% 19.28/3.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.28/3.01  
% 19.28/3.01  ------ Proving...
% 19.28/3.01  
% 19.28/3.01  
% 19.28/3.01  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.28/3.01  
% 19.28/3.01  ------ Proving...
% 19.28/3.01  
% 19.28/3.01  
% 19.28/3.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.28/3.01  
% 19.28/3.01  ------ Proving...
% 19.28/3.01  
% 19.28/3.01  
% 19.28/3.01  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.28/3.01  
% 19.28/3.01  ------ Proving...
% 19.28/3.01  
% 19.28/3.01  
% 19.28/3.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.28/3.01  
% 19.28/3.01  ------ Proving...
% 19.28/3.01  
% 19.28/3.01  
% 19.28/3.01  % SZS status Theorem for theBenchmark.p
% 19.28/3.01  
% 19.28/3.01  % SZS output start CNFRefutation for theBenchmark.p
% 19.28/3.01  
% 19.28/3.01  fof(f12,axiom,(
% 19.28/3.01    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 19.28/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.28/3.01  
% 19.28/3.01  fof(f37,plain,(
% 19.28/3.01    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 19.28/3.01    inference(cnf_transformation,[],[f12])).
% 19.28/3.01  
% 19.28/3.01  fof(f2,axiom,(
% 19.28/3.01    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 19.28/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.28/3.01  
% 19.28/3.01  fof(f22,plain,(
% 19.28/3.01    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 19.28/3.01    inference(nnf_transformation,[],[f2])).
% 19.28/3.01  
% 19.28/3.01  fof(f26,plain,(
% 19.28/3.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 19.28/3.01    inference(cnf_transformation,[],[f22])).
% 19.28/3.01  
% 19.28/3.01  fof(f9,axiom,(
% 19.28/3.01    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 19.28/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.28/3.01  
% 19.28/3.01  fof(f34,plain,(
% 19.28/3.01    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 19.28/3.01    inference(cnf_transformation,[],[f9])).
% 19.28/3.01  
% 19.28/3.01  fof(f5,axiom,(
% 19.28/3.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 19.28/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.28/3.01  
% 19.28/3.01  fof(f30,plain,(
% 19.28/3.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 19.28/3.01    inference(cnf_transformation,[],[f5])).
% 19.28/3.01  
% 19.28/3.01  fof(f41,plain,(
% 19.28/3.01    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 19.28/3.01    inference(definition_unfolding,[],[f34,f30])).
% 19.28/3.01  
% 19.28/3.01  fof(f13,axiom,(
% 19.28/3.01    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 19.28/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.28/3.01  
% 19.28/3.01  fof(f20,plain,(
% 19.28/3.01    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 19.28/3.01    inference(ennf_transformation,[],[f13])).
% 19.28/3.01  
% 19.28/3.01  fof(f38,plain,(
% 19.28/3.01    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 19.28/3.01    inference(cnf_transformation,[],[f20])).
% 19.28/3.01  
% 19.28/3.01  fof(f44,plain,(
% 19.28/3.01    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) | ~r1_tarski(X0,X1)) )),
% 19.28/3.01    inference(definition_unfolding,[],[f38,f30])).
% 19.28/3.01  
% 19.28/3.01  fof(f14,conjecture,(
% 19.28/3.01    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 19.28/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.28/3.01  
% 19.28/3.01  fof(f15,negated_conjecture,(
% 19.28/3.01    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 19.28/3.01    inference(negated_conjecture,[],[f14])).
% 19.28/3.01  
% 19.28/3.01  fof(f21,plain,(
% 19.28/3.01    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 19.28/3.01    inference(ennf_transformation,[],[f15])).
% 19.28/3.01  
% 19.28/3.01  fof(f23,plain,(
% 19.28/3.01    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2))) => ((~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2)))),
% 19.28/3.01    introduced(choice_axiom,[])).
% 19.28/3.01  
% 19.28/3.01  fof(f24,plain,(
% 19.28/3.01    (~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 19.28/3.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f23])).
% 19.28/3.01  
% 19.28/3.01  fof(f39,plain,(
% 19.28/3.01    r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 19.28/3.01    inference(cnf_transformation,[],[f24])).
% 19.28/3.01  
% 19.28/3.01  fof(f45,plain,(
% 19.28/3.01    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),
% 19.28/3.01    inference(definition_unfolding,[],[f39,f30])).
% 19.28/3.01  
% 19.28/3.01  fof(f27,plain,(
% 19.28/3.01    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 19.28/3.01    inference(cnf_transformation,[],[f22])).
% 19.28/3.01  
% 19.28/3.01  fof(f11,axiom,(
% 19.28/3.01    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 19.28/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.28/3.01  
% 19.28/3.01  fof(f36,plain,(
% 19.28/3.01    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 19.28/3.01    inference(cnf_transformation,[],[f11])).
% 19.28/3.01  
% 19.28/3.01  fof(f43,plain,(
% 19.28/3.01    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 19.28/3.01    inference(definition_unfolding,[],[f36,f30])).
% 19.28/3.01  
% 19.28/3.01  fof(f8,axiom,(
% 19.28/3.01    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 19.28/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.28/3.01  
% 19.28/3.01  fof(f19,plain,(
% 19.28/3.01    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 19.28/3.01    inference(ennf_transformation,[],[f8])).
% 19.28/3.01  
% 19.28/3.01  fof(f33,plain,(
% 19.28/3.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 19.28/3.01    inference(cnf_transformation,[],[f19])).
% 19.28/3.01  
% 19.28/3.01  fof(f4,axiom,(
% 19.28/3.01    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 19.28/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.28/3.01  
% 19.28/3.01  fof(f17,plain,(
% 19.28/3.01    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 19.28/3.01    inference(ennf_transformation,[],[f4])).
% 19.28/3.01  
% 19.28/3.01  fof(f29,plain,(
% 19.28/3.01    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 19.28/3.01    inference(cnf_transformation,[],[f17])).
% 19.28/3.01  
% 19.28/3.01  fof(f3,axiom,(
% 19.28/3.01    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 19.28/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.28/3.01  
% 19.28/3.01  fof(f16,plain,(
% 19.28/3.01    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 19.28/3.01    inference(rectify,[],[f3])).
% 19.28/3.01  
% 19.28/3.01  fof(f28,plain,(
% 19.28/3.01    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 19.28/3.01    inference(cnf_transformation,[],[f16])).
% 19.28/3.01  
% 19.28/3.01  fof(f10,axiom,(
% 19.28/3.01    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 19.28/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.28/3.01  
% 19.28/3.01  fof(f35,plain,(
% 19.28/3.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 19.28/3.01    inference(cnf_transformation,[],[f10])).
% 19.28/3.01  
% 19.28/3.01  fof(f42,plain,(
% 19.28/3.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 19.28/3.01    inference(definition_unfolding,[],[f35,f30])).
% 19.28/3.01  
% 19.28/3.01  fof(f7,axiom,(
% 19.28/3.01    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 19.28/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.28/3.01  
% 19.28/3.01  fof(f32,plain,(
% 19.28/3.01    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 19.28/3.01    inference(cnf_transformation,[],[f7])).
% 19.28/3.01  
% 19.28/3.01  fof(f1,axiom,(
% 19.28/3.01    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 19.28/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.28/3.01  
% 19.28/3.01  fof(f25,plain,(
% 19.28/3.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 19.28/3.01    inference(cnf_transformation,[],[f1])).
% 19.28/3.01  
% 19.28/3.01  fof(f6,axiom,(
% 19.28/3.01    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 19.28/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.28/3.01  
% 19.28/3.01  fof(f18,plain,(
% 19.28/3.01    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 19.28/3.01    inference(ennf_transformation,[],[f6])).
% 19.28/3.01  
% 19.28/3.01  fof(f31,plain,(
% 19.28/3.01    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 19.28/3.01    inference(cnf_transformation,[],[f18])).
% 19.28/3.01  
% 19.28/3.01  fof(f40,plain,(
% 19.28/3.01    ~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)),
% 19.28/3.01    inference(cnf_transformation,[],[f24])).
% 19.28/3.01  
% 19.28/3.01  cnf(c_11,plain,
% 19.28/3.01      ( r1_xboole_0(X0,k1_xboole_0) ),
% 19.28/3.01      inference(cnf_transformation,[],[f37]) ).
% 19.28/3.01  
% 19.28/3.01  cnf(c_11204,plain,
% 19.28/3.01      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 19.28/3.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 19.28/3.01  
% 19.28/3.01  cnf(c_2,plain,
% 19.28/3.01      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 19.28/3.01      inference(cnf_transformation,[],[f26]) ).
% 19.28/3.01  
% 19.28/3.01  cnf(c_11209,plain,
% 19.28/3.01      ( k3_xboole_0(X0,X1) = k1_xboole_0
% 19.28/3.01      | r1_xboole_0(X0,X1) != iProver_top ),
% 19.28/3.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 19.28/3.01  
% 19.28/3.01  cnf(c_11567,plain,
% 19.28/3.01      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 19.28/3.01      inference(superposition,[status(thm)],[c_11204,c_11209]) ).
% 19.28/3.01  
% 19.28/3.01  cnf(c_8,plain,
% 19.28/3.01      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
% 19.28/3.01      inference(cnf_transformation,[],[f41]) ).
% 19.28/3.01  
% 19.28/3.01  cnf(c_11205,plain,
% 19.28/3.01      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
% 19.28/3.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 19.28/3.01  
% 19.28/3.01  cnf(c_12,plain,
% 19.28/3.01      ( ~ r1_tarski(X0,X1)
% 19.28/3.01      | r1_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
% 19.28/3.01      inference(cnf_transformation,[],[f44]) ).
% 19.28/3.01  
% 19.28/3.01  cnf(c_11203,plain,
% 19.28/3.01      ( r1_tarski(X0,X1) != iProver_top
% 19.28/3.01      | r1_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = iProver_top ),
% 19.28/3.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 19.28/3.01  
% 19.28/3.01  cnf(c_11568,plain,
% 19.28/3.01      ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k1_xboole_0
% 19.28/3.01      | r1_tarski(X0,X2) != iProver_top ),
% 19.28/3.01      inference(superposition,[status(thm)],[c_11203,c_11209]) ).
% 19.28/3.01  
% 19.28/3.01  cnf(c_13415,plain,
% 19.28/3.01      ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X2,k3_xboole_0(X2,X0))) = k1_xboole_0 ),
% 19.28/3.01      inference(superposition,[status(thm)],[c_11205,c_11568]) ).
% 19.28/3.01  
% 19.28/3.01  cnf(c_14,negated_conjecture,
% 19.28/3.01      ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
% 19.28/3.01      inference(cnf_transformation,[],[f45]) ).
% 19.28/3.01  
% 19.28/3.01  cnf(c_11201,plain,
% 19.28/3.01      ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = iProver_top ),
% 19.28/3.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 19.28/3.01  
% 19.28/3.01  cnf(c_13417,plain,
% 19.28/3.01      ( k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))))) = k1_xboole_0 ),
% 19.28/3.01      inference(superposition,[status(thm)],[c_11201,c_11568]) ).
% 19.28/3.01  
% 19.28/3.01  cnf(c_1,plain,
% 19.28/3.01      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 19.28/3.01      inference(cnf_transformation,[],[f27]) ).
% 19.28/3.01  
% 19.28/3.01  cnf(c_11210,plain,
% 19.28/3.01      ( k3_xboole_0(X0,X1) != k1_xboole_0
% 19.28/3.01      | r1_xboole_0(X0,X1) = iProver_top ),
% 19.28/3.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 19.28/3.01  
% 19.28/3.01  cnf(c_13582,plain,
% 19.28/3.01      ( r1_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))))) = iProver_top ),
% 19.28/3.01      inference(superposition,[status(thm)],[c_13417,c_11210]) ).
% 19.28/3.01  
% 19.28/3.01  cnf(c_57675,plain,
% 19.28/3.01      ( r1_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,X0)),k1_xboole_0)) = iProver_top ),
% 19.28/3.01      inference(superposition,[status(thm)],[c_13415,c_13582]) ).
% 19.28/3.01  
% 19.28/3.01  cnf(c_10,plain,
% 19.28/3.01      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
% 19.28/3.01      inference(cnf_transformation,[],[f43]) ).
% 19.28/3.01  
% 19.28/3.01  cnf(c_13181,plain,
% 19.28/3.01      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 19.28/3.01      inference(demodulation,[status(thm)],[c_11567,c_10]) ).
% 19.28/3.01  
% 19.28/3.01  cnf(c_58659,plain,
% 19.28/3.01      ( r1_xboole_0(sK0,k5_xboole_0(sK2,k3_xboole_0(sK2,X0))) = iProver_top ),
% 19.28/3.01      inference(demodulation,[status(thm)],[c_57675,c_13181]) ).
% 19.28/3.01  
% 19.28/3.01  cnf(c_61419,plain,
% 19.28/3.01      ( r1_xboole_0(sK0,k5_xboole_0(sK2,k1_xboole_0)) = iProver_top ),
% 19.28/3.01      inference(superposition,[status(thm)],[c_11567,c_58659]) ).
% 19.28/3.01  
% 19.28/3.01  cnf(c_61423,plain,
% 19.28/3.01      ( r1_xboole_0(sK0,sK2) = iProver_top ),
% 19.28/3.01      inference(demodulation,[status(thm)],[c_61419,c_13181]) ).
% 19.28/3.01  
% 19.28/3.01  cnf(c_7,plain,
% 19.28/3.01      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 19.28/3.01      inference(cnf_transformation,[],[f33]) ).
% 19.28/3.01  
% 19.28/3.01  cnf(c_11206,plain,
% 19.28/3.01      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 19.28/3.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 19.28/3.01  
% 19.28/3.01  cnf(c_11422,plain,
% 19.28/3.01      ( k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = sK0 ),
% 19.28/3.01      inference(superposition,[status(thm)],[c_11201,c_11206]) ).
% 19.28/3.01  
% 19.28/3.01  cnf(c_11530,plain,
% 19.28/3.01      ( r1_tarski(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) != iProver_top
% 19.28/3.01      | r1_xboole_0(X0,k5_xboole_0(sK0,sK0)) = iProver_top ),
% 19.28/3.01      inference(superposition,[status(thm)],[c_11422,c_11203]) ).
% 19.28/3.01  
% 19.28/3.01  cnf(c_11668,plain,
% 19.28/3.01      ( r1_xboole_0(sK0,k5_xboole_0(sK0,sK0)) = iProver_top ),
% 19.28/3.01      inference(superposition,[status(thm)],[c_11201,c_11530]) ).
% 19.28/3.01  
% 19.28/3.01  cnf(c_4,plain,
% 19.28/3.01      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 19.28/3.01      inference(cnf_transformation,[],[f29]) ).
% 19.28/3.01  
% 19.28/3.01  cnf(c_11208,plain,
% 19.28/3.01      ( r1_xboole_0(X0,X1) != iProver_top
% 19.28/3.01      | r1_xboole_0(X1,X0) = iProver_top ),
% 19.28/3.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 19.28/3.01  
% 19.28/3.01  cnf(c_11704,plain,
% 19.28/3.01      ( r1_xboole_0(k5_xboole_0(sK0,sK0),sK0) = iProver_top ),
% 19.28/3.01      inference(superposition,[status(thm)],[c_11668,c_11208]) ).
% 19.28/3.01  
% 19.28/3.01  cnf(c_11740,plain,
% 19.28/3.01      ( k3_xboole_0(k5_xboole_0(sK0,sK0),sK0) = k1_xboole_0 ),
% 19.28/3.01      inference(superposition,[status(thm)],[c_11704,c_11209]) ).
% 19.28/3.01  
% 19.28/3.01  cnf(c_3,plain,
% 19.28/3.01      ( k3_xboole_0(X0,X0) = X0 ),
% 19.28/3.01      inference(cnf_transformation,[],[f28]) ).
% 19.28/3.01  
% 19.28/3.01  cnf(c_11370,plain,
% 19.28/3.01      ( r1_tarski(k5_xboole_0(X0,X0),X0) = iProver_top ),
% 19.28/3.01      inference(superposition,[status(thm)],[c_3,c_11205]) ).
% 19.28/3.01  
% 19.28/3.01  cnf(c_11424,plain,
% 19.28/3.01      ( k3_xboole_0(k5_xboole_0(X0,X0),X0) = k5_xboole_0(X0,X0) ),
% 19.28/3.01      inference(superposition,[status(thm)],[c_11370,c_11206]) ).
% 19.28/3.01  
% 19.28/3.01  cnf(c_11775,plain,
% 19.28/3.01      ( k5_xboole_0(sK0,sK0) = k1_xboole_0 ),
% 19.28/3.01      inference(superposition,[status(thm)],[c_11740,c_11424]) ).
% 19.28/3.01  
% 19.28/3.01  cnf(c_9,plain,
% 19.28/3.01      ( k2_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
% 19.28/3.01      inference(cnf_transformation,[],[f42]) ).
% 19.28/3.01  
% 19.28/3.01  cnf(c_11433,plain,
% 19.28/3.01      ( k2_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK0)) = k2_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK0) ),
% 19.28/3.01      inference(superposition,[status(thm)],[c_11422,c_9]) ).
% 19.28/3.01  
% 19.28/3.01  cnf(c_12049,plain,
% 19.28/3.01      ( k2_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k1_xboole_0) = k2_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK0) ),
% 19.28/3.01      inference(demodulation,[status(thm)],[c_11775,c_11433]) ).
% 19.28/3.01  
% 19.28/3.01  cnf(c_6,plain,
% 19.28/3.01      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 19.28/3.01      inference(cnf_transformation,[],[f32]) ).
% 19.28/3.01  
% 19.28/3.01  cnf(c_12051,plain,
% 19.28/3.01      ( k2_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),sK0) = k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) ),
% 19.28/3.01      inference(demodulation,[status(thm)],[c_12049,c_6]) ).
% 19.28/3.01  
% 19.28/3.01  cnf(c_0,plain,
% 19.28/3.01      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 19.28/3.01      inference(cnf_transformation,[],[f25]) ).
% 19.28/3.01  
% 19.28/3.01  cnf(c_5,plain,
% 19.28/3.01      ( r1_tarski(X0,X1) | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 19.28/3.01      inference(cnf_transformation,[],[f31]) ).
% 19.28/3.01  
% 19.28/3.01  cnf(c_11207,plain,
% 19.28/3.01      ( r1_tarski(X0,X1) = iProver_top
% 19.28/3.01      | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
% 19.28/3.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 19.28/3.01  
% 19.28/3.01  cnf(c_11833,plain,
% 19.28/3.01      ( r1_tarski(X0,X1) = iProver_top
% 19.28/3.01      | r1_tarski(k2_xboole_0(X2,X0),X1) != iProver_top ),
% 19.28/3.01      inference(superposition,[status(thm)],[c_0,c_11207]) ).
% 19.28/3.01  
% 19.28/3.01  cnf(c_12253,plain,
% 19.28/3.01      ( r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0) != iProver_top
% 19.28/3.01      | r1_tarski(sK0,X0) = iProver_top ),
% 19.28/3.01      inference(superposition,[status(thm)],[c_12051,c_11833]) ).
% 19.28/3.01  
% 19.28/3.01  cnf(c_12886,plain,
% 19.28/3.01      ( r1_tarski(sK0,sK1) = iProver_top ),
% 19.28/3.01      inference(superposition,[status(thm)],[c_11205,c_12253]) ).
% 19.28/3.01  
% 19.28/3.01  cnf(c_13,negated_conjecture,
% 19.28/3.01      ( ~ r1_tarski(sK0,sK1) | ~ r1_xboole_0(sK0,sK2) ),
% 19.28/3.01      inference(cnf_transformation,[],[f40]) ).
% 19.28/3.01  
% 19.28/3.01  cnf(c_16,plain,
% 19.28/3.01      ( r1_tarski(sK0,sK1) != iProver_top
% 19.28/3.01      | r1_xboole_0(sK0,sK2) != iProver_top ),
% 19.28/3.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 19.28/3.01  
% 19.28/3.01  cnf(contradiction,plain,
% 19.28/3.01      ( $false ),
% 19.28/3.01      inference(minisat,[status(thm)],[c_61423,c_12886,c_16]) ).
% 19.28/3.01  
% 19.28/3.01  
% 19.28/3.01  % SZS output end CNFRefutation for theBenchmark.p
% 19.28/3.01  
% 19.28/3.01  ------                               Statistics
% 19.28/3.01  
% 19.28/3.01  ------ Selected
% 19.28/3.01  
% 19.28/3.01  total_time:                             2.124
% 19.28/3.01  
%------------------------------------------------------------------------------
