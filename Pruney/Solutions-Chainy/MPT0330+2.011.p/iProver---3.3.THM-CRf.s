%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:38:10 EST 2020

% Result     : Theorem 3.22s
% Output     : CNFRefutation 3.22s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 258 expanded)
%              Number of clauses        :   39 (  59 expanded)
%              Number of leaves         :   12 (  71 expanded)
%              Depth                    :   15
%              Number of atoms          :  161 ( 463 expanded)
%              Number of equality atoms :   49 ( 162 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_tarski(X1,k2_zfmisc_1(X4,X5))
        & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
     => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( ( r1_tarski(X1,k2_zfmisc_1(X4,X5))
          & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
       => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f17,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
      & r1_tarski(X1,k2_zfmisc_1(X4,X5))
      & r1_tarski(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f18,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
      & r1_tarski(X1,k2_zfmisc_1(X4,X5))
      & r1_tarski(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f17])).

fof(f19,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
        & r1_tarski(X1,k2_zfmisc_1(X4,X5))
        & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
   => ( ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
      & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))
      & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
    & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))
    & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f18,f19])).

fof(f30,plain,(
    r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f27,f26])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k3_tarski(k1_enumset1(X0,X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f22,f32])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k3_tarski(k1_enumset1(X0,X0,X1)),X2) ) ),
    inference(definition_unfolding,[],[f21,f32])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f24,f32])).

fof(f31,plain,(
    ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) ),
    inference(cnf_transformation,[],[f20])).

fof(f38,plain,(
    ~ r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),k3_tarski(k1_enumset1(sK3,sK3,sK5)))) ),
    inference(definition_unfolding,[],[f31,f32,f32,f32])).

fof(f29,plain,(
    r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f23,f32])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f37,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f25,f26,f26])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X3)
    | r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_246,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X3) != iProver_top
    | r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_7,negated_conjecture,
    ( r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_244,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_tarski(k1_enumset1(X0,X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_249,plain,
    ( k3_tarski(k1_enumset1(X0,X0,X1)) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_831,plain,
    ( k3_tarski(k1_enumset1(sK1,sK1,k2_zfmisc_1(sK4,sK5))) = k2_zfmisc_1(sK4,sK5) ),
    inference(superposition,[status(thm)],[c_244,c_249])).

cnf(c_0,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_250,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1203,plain,
    ( r1_tarski(k2_zfmisc_1(sK4,sK5),X0) != iProver_top
    | r1_tarski(sK1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_831,c_250])).

cnf(c_2472,plain,
    ( r1_tarski(sK5,X0) != iProver_top
    | r1_tarski(sK4,X1) != iProver_top
    | r1_tarski(sK1,k2_zfmisc_1(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_246,c_1203])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_247,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_6,negated_conjecture,
    ( ~ r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),k3_tarski(k1_enumset1(sK3,sK3,sK5)))) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_245,plain,
    ( r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),k3_tarski(k1_enumset1(sK3,sK3,sK5)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1506,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),k3_tarski(k1_enumset1(sK3,sK3,sK5)))) != iProver_top
    | r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),k3_tarski(k1_enumset1(sK3,sK3,sK5)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_247,c_245])).

cnf(c_5354,plain,
    ( r1_tarski(sK5,k3_tarski(k1_enumset1(sK3,sK3,sK5))) != iProver_top
    | r1_tarski(sK4,k3_tarski(k1_enumset1(sK2,sK2,sK4))) != iProver_top
    | r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),k3_tarski(k1_enumset1(sK3,sK3,sK5)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2472,c_1506])).

cnf(c_572,plain,
    ( ~ r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),k3_tarski(k1_enumset1(sK3,sK3,sK5))))
    | ~ r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),k3_tarski(k1_enumset1(sK3,sK3,sK5)))) ),
    inference(resolution,[status(thm)],[c_6,c_3])).

cnf(c_94,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_96,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1228,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_94,c_96])).

cnf(c_1543,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(k3_tarski(k1_enumset1(X2,X2,X0)),X1) ),
    inference(resolution,[status(thm)],[c_1228,c_1])).

cnf(c_2528,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(resolution,[status(thm)],[c_1543,c_0])).

cnf(c_2551,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK4,sK5),X0)
    | r1_tarski(sK1,X0) ),
    inference(resolution,[status(thm)],[c_2528,c_7])).

cnf(c_2910,plain,
    ( ~ r1_tarski(sK5,X0)
    | ~ r1_tarski(sK4,X1)
    | r1_tarski(sK1,k2_zfmisc_1(X1,X0)) ),
    inference(resolution,[status(thm)],[c_2551,c_5])).

cnf(c_4434,plain,
    ( ~ r1_tarski(sK5,k3_tarski(k1_enumset1(sK3,sK3,sK5)))
    | ~ r1_tarski(sK4,k3_tarski(k1_enumset1(sK2,sK2,sK4)))
    | ~ r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),k3_tarski(k1_enumset1(sK3,sK3,sK5)))) ),
    inference(resolution,[status(thm)],[c_572,c_2910])).

cnf(c_8,negated_conjecture,
    ( r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_2553,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK2,sK3),X0)
    | r1_tarski(sK0,X0) ),
    inference(resolution,[status(thm)],[c_2528,c_8])).

cnf(c_2924,plain,
    ( ~ r1_tarski(sK3,X0)
    | ~ r1_tarski(sK2,X1)
    | r1_tarski(sK0,k2_zfmisc_1(X1,X0)) ),
    inference(resolution,[status(thm)],[c_2553,c_5])).

cnf(c_4511,plain,
    ( ~ r1_tarski(sK5,k3_tarski(k1_enumset1(sK3,sK3,sK5)))
    | ~ r1_tarski(sK3,k3_tarski(k1_enumset1(sK3,sK3,sK5)))
    | ~ r1_tarski(sK4,k3_tarski(k1_enumset1(sK2,sK2,sK4)))
    | ~ r1_tarski(sK2,k3_tarski(k1_enumset1(sK2,sK2,sK4))) ),
    inference(resolution,[status(thm)],[c_4434,c_2924])).

cnf(c_2,plain,
    ( r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_4754,plain,
    ( ~ r1_tarski(sK5,k3_tarski(k1_enumset1(sK3,sK3,sK5)))
    | ~ r1_tarski(sK4,k3_tarski(k1_enumset1(sK2,sK2,sK4))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4511,c_2,c_2])).

cnf(c_4755,plain,
    ( r1_tarski(sK5,k3_tarski(k1_enumset1(sK3,sK3,sK5))) != iProver_top
    | r1_tarski(sK4,k3_tarski(k1_enumset1(sK2,sK2,sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4754])).

cnf(c_5487,plain,
    ( r1_tarski(sK4,k3_tarski(k1_enumset1(sK2,sK2,sK4))) != iProver_top
    | r1_tarski(sK5,k3_tarski(k1_enumset1(sK3,sK3,sK5))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5354,c_4755])).

cnf(c_5488,plain,
    ( r1_tarski(sK5,k3_tarski(k1_enumset1(sK3,sK3,sK5))) != iProver_top
    | r1_tarski(sK4,k3_tarski(k1_enumset1(sK2,sK2,sK4))) != iProver_top ),
    inference(renaming,[status(thm)],[c_5487])).

cnf(c_4,plain,
    ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_248,plain,
    ( r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_562,plain,
    ( r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_248])).

cnf(c_5493,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5488,c_562,c_562])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:18:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.22/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/0.99  
% 3.22/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.22/0.99  
% 3.22/0.99  ------  iProver source info
% 3.22/0.99  
% 3.22/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.22/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.22/0.99  git: non_committed_changes: false
% 3.22/0.99  git: last_make_outside_of_git: false
% 3.22/0.99  
% 3.22/0.99  ------ 
% 3.22/0.99  ------ Parsing...
% 3.22/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.22/0.99  
% 3.22/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.22/0.99  
% 3.22/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.22/0.99  
% 3.22/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.22/0.99  ------ Proving...
% 3.22/0.99  ------ Problem Properties 
% 3.22/0.99  
% 3.22/0.99  
% 3.22/0.99  clauses                                 9
% 3.22/0.99  conjectures                             3
% 3.22/0.99  EPR                                     0
% 3.22/0.99  Horn                                    9
% 3.22/0.99  unary                                   5
% 3.22/0.99  binary                                  2
% 3.22/0.99  lits                                    15
% 3.22/0.99  lits eq                                 2
% 3.22/0.99  fd_pure                                 0
% 3.22/0.99  fd_pseudo                               0
% 3.22/0.99  fd_cond                                 0
% 3.22/0.99  fd_pseudo_cond                          0
% 3.22/0.99  AC symbols                              0
% 3.22/0.99  
% 3.22/0.99  ------ Input Options Time Limit: Unbounded
% 3.22/0.99  
% 3.22/0.99  
% 3.22/0.99  ------ 
% 3.22/0.99  Current options:
% 3.22/0.99  ------ 
% 3.22/0.99  
% 3.22/0.99  
% 3.22/0.99  
% 3.22/0.99  
% 3.22/0.99  ------ Proving...
% 3.22/0.99  
% 3.22/0.99  
% 3.22/0.99  % SZS status Theorem for theBenchmark.p
% 3.22/0.99  
% 3.22/0.99   Resolution empty clause
% 3.22/0.99  
% 3.22/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.22/0.99  
% 3.22/0.99  fof(f8,axiom,(
% 3.22/0.99    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))),
% 3.22/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/0.99  
% 3.22/0.99  fof(f15,plain,(
% 3.22/0.99    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | (~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)))),
% 3.22/0.99    inference(ennf_transformation,[],[f8])).
% 3.22/0.99  
% 3.22/0.99  fof(f16,plain,(
% 3.22/0.99    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 3.22/0.99    inference(flattening,[],[f15])).
% 3.22/0.99  
% 3.22/0.99  fof(f28,plain,(
% 3.22/0.99    ( ! [X2,X0,X3,X1] : (r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 3.22/0.99    inference(cnf_transformation,[],[f16])).
% 3.22/0.99  
% 3.22/0.99  fof(f9,conjecture,(
% 3.22/0.99    ! [X0,X1,X2,X3,X4,X5] : ((r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))))),
% 3.22/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/0.99  
% 3.22/0.99  fof(f10,negated_conjecture,(
% 3.22/0.99    ~! [X0,X1,X2,X3,X4,X5] : ((r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))))),
% 3.22/0.99    inference(negated_conjecture,[],[f9])).
% 3.22/0.99  
% 3.22/0.99  fof(f17,plain,(
% 3.22/0.99    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & (r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))))),
% 3.22/0.99    inference(ennf_transformation,[],[f10])).
% 3.22/0.99  
% 3.22/0.99  fof(f18,plain,(
% 3.22/0.99    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3)))),
% 3.22/0.99    inference(flattening,[],[f17])).
% 3.22/0.99  
% 3.22/0.99  fof(f19,plain,(
% 3.22/0.99    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => (~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)))),
% 3.22/0.99    introduced(choice_axiom,[])).
% 3.22/0.99  
% 3.22/0.99  fof(f20,plain,(
% 3.22/0.99    ~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))),
% 3.22/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f18,f19])).
% 3.22/0.99  
% 3.22/0.99  fof(f30,plain,(
% 3.22/0.99    r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))),
% 3.22/0.99    inference(cnf_transformation,[],[f20])).
% 3.22/0.99  
% 3.22/0.99  fof(f2,axiom,(
% 3.22/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 3.22/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/0.99  
% 3.22/0.99  fof(f12,plain,(
% 3.22/0.99    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 3.22/0.99    inference(ennf_transformation,[],[f2])).
% 3.22/0.99  
% 3.22/0.99  fof(f22,plain,(
% 3.22/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 3.22/0.99    inference(cnf_transformation,[],[f12])).
% 3.22/0.99  
% 3.22/0.99  fof(f7,axiom,(
% 3.22/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.22/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/0.99  
% 3.22/0.99  fof(f27,plain,(
% 3.22/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.22/0.99    inference(cnf_transformation,[],[f7])).
% 3.22/0.99  
% 3.22/0.99  fof(f6,axiom,(
% 3.22/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.22/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/0.99  
% 3.22/0.99  fof(f26,plain,(
% 3.22/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.22/0.99    inference(cnf_transformation,[],[f6])).
% 3.22/0.99  
% 3.22/0.99  fof(f32,plain,(
% 3.22/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 3.22/0.99    inference(definition_unfolding,[],[f27,f26])).
% 3.22/0.99  
% 3.22/0.99  fof(f34,plain,(
% 3.22/0.99    ( ! [X0,X1] : (k3_tarski(k1_enumset1(X0,X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 3.22/0.99    inference(definition_unfolding,[],[f22,f32])).
% 3.22/0.99  
% 3.22/0.99  fof(f1,axiom,(
% 3.22/0.99    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 3.22/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/0.99  
% 3.22/0.99  fof(f11,plain,(
% 3.22/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 3.22/0.99    inference(ennf_transformation,[],[f1])).
% 3.22/0.99  
% 3.22/0.99  fof(f21,plain,(
% 3.22/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 3.22/0.99    inference(cnf_transformation,[],[f11])).
% 3.22/0.99  
% 3.22/0.99  fof(f33,plain,(
% 3.22/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k3_tarski(k1_enumset1(X0,X0,X1)),X2)) )),
% 3.22/0.99    inference(definition_unfolding,[],[f21,f32])).
% 3.22/0.99  
% 3.22/0.99  fof(f4,axiom,(
% 3.22/0.99    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 3.22/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/0.99  
% 3.22/0.99  fof(f13,plain,(
% 3.22/0.99    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 3.22/0.99    inference(ennf_transformation,[],[f4])).
% 3.22/0.99  
% 3.22/0.99  fof(f14,plain,(
% 3.22/0.99    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 3.22/0.99    inference(flattening,[],[f13])).
% 3.22/0.99  
% 3.22/0.99  fof(f24,plain,(
% 3.22/0.99    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 3.22/0.99    inference(cnf_transformation,[],[f14])).
% 3.22/0.99  
% 3.22/0.99  fof(f36,plain,(
% 3.22/0.99    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 3.22/0.99    inference(definition_unfolding,[],[f24,f32])).
% 3.22/0.99  
% 3.22/0.99  fof(f31,plain,(
% 3.22/0.99    ~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))),
% 3.22/0.99    inference(cnf_transformation,[],[f20])).
% 3.22/0.99  
% 3.22/0.99  fof(f38,plain,(
% 3.22/0.99    ~r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),k3_tarski(k1_enumset1(sK3,sK3,sK5))))),
% 3.22/0.99    inference(definition_unfolding,[],[f31,f32,f32,f32])).
% 3.22/0.99  
% 3.22/0.99  fof(f29,plain,(
% 3.22/0.99    r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))),
% 3.22/0.99    inference(cnf_transformation,[],[f20])).
% 3.22/0.99  
% 3.22/0.99  fof(f3,axiom,(
% 3.22/0.99    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.22/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/0.99  
% 3.22/0.99  fof(f23,plain,(
% 3.22/0.99    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.22/0.99    inference(cnf_transformation,[],[f3])).
% 3.22/0.99  
% 3.22/0.99  fof(f35,plain,(
% 3.22/0.99    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1)))) )),
% 3.22/0.99    inference(definition_unfolding,[],[f23,f32])).
% 3.22/0.99  
% 3.22/0.99  fof(f5,axiom,(
% 3.22/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.22/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/0.99  
% 3.22/0.99  fof(f25,plain,(
% 3.22/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.22/0.99    inference(cnf_transformation,[],[f5])).
% 3.22/0.99  
% 3.22/0.99  fof(f37,plain,(
% 3.22/0.99    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 3.22/0.99    inference(definition_unfolding,[],[f25,f26,f26])).
% 3.22/0.99  
% 3.22/0.99  cnf(c_5,plain,
% 3.22/0.99      ( ~ r1_tarski(X0,X1)
% 3.22/0.99      | ~ r1_tarski(X2,X3)
% 3.22/0.99      | r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
% 3.22/0.99      inference(cnf_transformation,[],[f28]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_246,plain,
% 3.22/0.99      ( r1_tarski(X0,X1) != iProver_top
% 3.22/0.99      | r1_tarski(X2,X3) != iProver_top
% 3.22/0.99      | r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) = iProver_top ),
% 3.22/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_7,negated_conjecture,
% 3.22/0.99      ( r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) ),
% 3.22/0.99      inference(cnf_transformation,[],[f30]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_244,plain,
% 3.22/0.99      ( r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) = iProver_top ),
% 3.22/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1,plain,
% 3.22/0.99      ( ~ r1_tarski(X0,X1) | k3_tarski(k1_enumset1(X0,X0,X1)) = X1 ),
% 3.22/0.99      inference(cnf_transformation,[],[f34]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_249,plain,
% 3.22/0.99      ( k3_tarski(k1_enumset1(X0,X0,X1)) = X1
% 3.22/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 3.22/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_831,plain,
% 3.22/0.99      ( k3_tarski(k1_enumset1(sK1,sK1,k2_zfmisc_1(sK4,sK5))) = k2_zfmisc_1(sK4,sK5) ),
% 3.22/0.99      inference(superposition,[status(thm)],[c_244,c_249]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_0,plain,
% 3.22/0.99      ( r1_tarski(X0,X1) | ~ r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1) ),
% 3.22/0.99      inference(cnf_transformation,[],[f33]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_250,plain,
% 3.22/0.99      ( r1_tarski(X0,X1) = iProver_top
% 3.22/0.99      | r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1) != iProver_top ),
% 3.22/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1203,plain,
% 3.22/0.99      ( r1_tarski(k2_zfmisc_1(sK4,sK5),X0) != iProver_top
% 3.22/0.99      | r1_tarski(sK1,X0) = iProver_top ),
% 3.22/0.99      inference(superposition,[status(thm)],[c_831,c_250]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_2472,plain,
% 3.22/0.99      ( r1_tarski(sK5,X0) != iProver_top
% 3.22/0.99      | r1_tarski(sK4,X1) != iProver_top
% 3.22/0.99      | r1_tarski(sK1,k2_zfmisc_1(X1,X0)) = iProver_top ),
% 3.22/0.99      inference(superposition,[status(thm)],[c_246,c_1203]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_3,plain,
% 3.22/0.99      ( ~ r1_tarski(X0,X1)
% 3.22/0.99      | ~ r1_tarski(X2,X1)
% 3.22/0.99      | r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1) ),
% 3.22/0.99      inference(cnf_transformation,[],[f36]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_247,plain,
% 3.22/0.99      ( r1_tarski(X0,X1) != iProver_top
% 3.22/0.99      | r1_tarski(X2,X1) != iProver_top
% 3.22/0.99      | r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1) = iProver_top ),
% 3.22/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_6,negated_conjecture,
% 3.22/0.99      ( ~ r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),k3_tarski(k1_enumset1(sK3,sK3,sK5)))) ),
% 3.22/0.99      inference(cnf_transformation,[],[f38]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_245,plain,
% 3.22/0.99      ( r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),k3_tarski(k1_enumset1(sK3,sK3,sK5)))) != iProver_top ),
% 3.22/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1506,plain,
% 3.22/0.99      ( r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),k3_tarski(k1_enumset1(sK3,sK3,sK5)))) != iProver_top
% 3.22/0.99      | r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),k3_tarski(k1_enumset1(sK3,sK3,sK5)))) != iProver_top ),
% 3.22/0.99      inference(superposition,[status(thm)],[c_247,c_245]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_5354,plain,
% 3.22/0.99      ( r1_tarski(sK5,k3_tarski(k1_enumset1(sK3,sK3,sK5))) != iProver_top
% 3.22/0.99      | r1_tarski(sK4,k3_tarski(k1_enumset1(sK2,sK2,sK4))) != iProver_top
% 3.22/0.99      | r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),k3_tarski(k1_enumset1(sK3,sK3,sK5)))) != iProver_top ),
% 3.22/0.99      inference(superposition,[status(thm)],[c_2472,c_1506]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_572,plain,
% 3.22/0.99      ( ~ r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),k3_tarski(k1_enumset1(sK3,sK3,sK5))))
% 3.22/0.99      | ~ r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),k3_tarski(k1_enumset1(sK3,sK3,sK5)))) ),
% 3.22/0.99      inference(resolution,[status(thm)],[c_6,c_3]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_94,plain,( X0 = X0 ),theory(equality) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_96,plain,
% 3.22/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.22/0.99      theory(equality) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1228,plain,
% 3.22/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 3.22/0.99      inference(resolution,[status(thm)],[c_94,c_96]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1543,plain,
% 3.22/0.99      ( ~ r1_tarski(X0,X1)
% 3.22/0.99      | ~ r1_tarski(X2,X0)
% 3.22/0.99      | r1_tarski(k3_tarski(k1_enumset1(X2,X2,X0)),X1) ),
% 3.22/0.99      inference(resolution,[status(thm)],[c_1228,c_1]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_2528,plain,
% 3.22/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 3.22/0.99      inference(resolution,[status(thm)],[c_1543,c_0]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_2551,plain,
% 3.22/0.99      ( ~ r1_tarski(k2_zfmisc_1(sK4,sK5),X0) | r1_tarski(sK1,X0) ),
% 3.22/0.99      inference(resolution,[status(thm)],[c_2528,c_7]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_2910,plain,
% 3.22/0.99      ( ~ r1_tarski(sK5,X0)
% 3.22/0.99      | ~ r1_tarski(sK4,X1)
% 3.22/0.99      | r1_tarski(sK1,k2_zfmisc_1(X1,X0)) ),
% 3.22/0.99      inference(resolution,[status(thm)],[c_2551,c_5]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_4434,plain,
% 3.22/0.99      ( ~ r1_tarski(sK5,k3_tarski(k1_enumset1(sK3,sK3,sK5)))
% 3.22/0.99      | ~ r1_tarski(sK4,k3_tarski(k1_enumset1(sK2,sK2,sK4)))
% 3.22/0.99      | ~ r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),k3_tarski(k1_enumset1(sK3,sK3,sK5)))) ),
% 3.22/0.99      inference(resolution,[status(thm)],[c_572,c_2910]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_8,negated_conjecture,
% 3.22/0.99      ( r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
% 3.22/0.99      inference(cnf_transformation,[],[f29]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_2553,plain,
% 3.22/0.99      ( ~ r1_tarski(k2_zfmisc_1(sK2,sK3),X0) | r1_tarski(sK0,X0) ),
% 3.22/0.99      inference(resolution,[status(thm)],[c_2528,c_8]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_2924,plain,
% 3.22/0.99      ( ~ r1_tarski(sK3,X0)
% 3.22/0.99      | ~ r1_tarski(sK2,X1)
% 3.22/0.99      | r1_tarski(sK0,k2_zfmisc_1(X1,X0)) ),
% 3.22/0.99      inference(resolution,[status(thm)],[c_2553,c_5]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_4511,plain,
% 3.22/0.99      ( ~ r1_tarski(sK5,k3_tarski(k1_enumset1(sK3,sK3,sK5)))
% 3.22/0.99      | ~ r1_tarski(sK3,k3_tarski(k1_enumset1(sK3,sK3,sK5)))
% 3.22/0.99      | ~ r1_tarski(sK4,k3_tarski(k1_enumset1(sK2,sK2,sK4)))
% 3.22/0.99      | ~ r1_tarski(sK2,k3_tarski(k1_enumset1(sK2,sK2,sK4))) ),
% 3.22/0.99      inference(resolution,[status(thm)],[c_4434,c_2924]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_2,plain,
% 3.22/0.99      ( r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) ),
% 3.22/0.99      inference(cnf_transformation,[],[f35]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_4754,plain,
% 3.22/0.99      ( ~ r1_tarski(sK5,k3_tarski(k1_enumset1(sK3,sK3,sK5)))
% 3.22/0.99      | ~ r1_tarski(sK4,k3_tarski(k1_enumset1(sK2,sK2,sK4))) ),
% 3.22/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_4511,c_2,c_2]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_4755,plain,
% 3.22/0.99      ( r1_tarski(sK5,k3_tarski(k1_enumset1(sK3,sK3,sK5))) != iProver_top
% 3.22/0.99      | r1_tarski(sK4,k3_tarski(k1_enumset1(sK2,sK2,sK4))) != iProver_top ),
% 3.22/0.99      inference(predicate_to_equality,[status(thm)],[c_4754]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_5487,plain,
% 3.22/0.99      ( r1_tarski(sK4,k3_tarski(k1_enumset1(sK2,sK2,sK4))) != iProver_top
% 3.22/0.99      | r1_tarski(sK5,k3_tarski(k1_enumset1(sK3,sK3,sK5))) != iProver_top ),
% 3.22/0.99      inference(global_propositional_subsumption,[status(thm)],[c_5354,c_4755]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_5488,plain,
% 3.22/0.99      ( r1_tarski(sK5,k3_tarski(k1_enumset1(sK3,sK3,sK5))) != iProver_top
% 3.22/0.99      | r1_tarski(sK4,k3_tarski(k1_enumset1(sK2,sK2,sK4))) != iProver_top ),
% 3.22/0.99      inference(renaming,[status(thm)],[c_5487]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_4,plain,
% 3.22/0.99      ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
% 3.22/0.99      inference(cnf_transformation,[],[f37]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_248,plain,
% 3.22/0.99      ( r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) = iProver_top ),
% 3.22/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_562,plain,
% 3.22/0.99      ( r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X0))) = iProver_top ),
% 3.22/0.99      inference(superposition,[status(thm)],[c_4,c_248]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_5493,plain,
% 3.22/0.99      ( $false ),
% 3.22/0.99      inference(forward_subsumption_resolution,
% 3.22/0.99                [status(thm)],
% 3.22/0.99                [c_5488,c_562,c_562]) ).
% 3.22/0.99  
% 3.22/0.99  
% 3.22/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.22/0.99  
% 3.22/0.99  ------                               Statistics
% 3.22/0.99  
% 3.22/0.99  ------ Selected
% 3.22/0.99  
% 3.22/0.99  total_time:                             0.164
% 3.22/0.99  
%------------------------------------------------------------------------------
