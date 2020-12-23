%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:36:40 EST 2020

% Result     : Theorem 35.47s
% Output     : CNFRefutation 35.47s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 159 expanded)
%              Number of clauses        :   66 (  88 expanded)
%              Number of leaves         :   17 (  36 expanded)
%              Depth                    :   20
%              Number of atoms          :  186 ( 271 expanded)
%              Number of equality atoms :  125 ( 182 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    8 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,axiom,(
    ! [X0,X1] : k3_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = k1_zfmisc_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = k1_zfmisc_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k5_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k5_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k5_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f30,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f21])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k5_xboole_0(X0,X2),X1) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k5_xboole_0(X0,X2),X1) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f19,conjecture,(
    ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1))) ),
    inference(negated_conjecture,[],[f19])).

fof(f25,plain,(
    ? [X0,X1] : ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1))) ),
    inference(ennf_transformation,[],[f20])).

fof(f26,plain,
    ( ? [X0,X1] : ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1)))
   => ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f26])).

fof(f46,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    inference(cnf_transformation,[],[f27])).

fof(f10,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f4,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f53,plain,(
    ~ r1_tarski(k5_xboole_0(k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f46,f37,f31,f31])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

cnf(c_9,plain,
    ( k3_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = k1_zfmisc_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k3_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_149,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k3_xboole_0(X0,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2497,plain,
    ( r1_tarski(k1_zfmisc_1(X0),X1) != iProver_top
    | r1_tarski(k1_zfmisc_1(k3_xboole_0(X0,X2)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_149])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_6,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_147,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_321,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_147])).

cnf(c_505,plain,
    ( r1_tarski(k1_zfmisc_1(k3_xboole_0(X0,X1)),k1_zfmisc_1(X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_321])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_148,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(k5_xboole_0(X0,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_5,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_493,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(k5_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_2,c_5])).

cnf(c_10,negated_conjecture,
    ( ~ r1_tarski(k5_xboole_0(k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_7,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_63,negated_conjecture,
    ( ~ r1_tarski(k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    inference(theory_normalisation,[status(thm)],[c_10,c_7,c_1])).

cnf(c_146,plain,
    ( r1_tarski(k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_63])).

cnf(c_150,plain,
    ( r1_tarski(k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k1_zfmisc_1(k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_146,c_9])).

cnf(c_262,plain,
    ( r1_tarski(k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_0,c_150])).

cnf(c_963,plain,
    ( r1_tarski(k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k5_xboole_0(k1_zfmisc_1(k3_xboole_0(k5_xboole_0(sK1,sK0),sK1)),k1_zfmisc_1(k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(k5_xboole_0(sK1,sK0),sK1))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_493,c_262])).

cnf(c_966,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(k5_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_0,c_493])).

cnf(c_989,plain,
    ( r1_tarski(k5_xboole_0(k1_zfmisc_1(k3_xboole_0(k5_xboole_0(sK0,sK1),sK0)),k5_xboole_0(k1_zfmisc_1(k3_xboole_0(k5_xboole_0(sK1,sK0),sK1)),k1_zfmisc_1(k3_xboole_0(k3_xboole_0(k5_xboole_0(sK0,sK1),sK0),k3_xboole_0(k5_xboole_0(sK1,sK0),sK1))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_963,c_966])).

cnf(c_1001,plain,
    ( r1_tarski(k5_xboole_0(k1_zfmisc_1(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1))),k5_xboole_0(k1_zfmisc_1(k3_xboole_0(k5_xboole_0(sK1,sK0),sK1)),k1_zfmisc_1(k3_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(k5_xboole_0(sK1,sK0),sK1))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_989])).

cnf(c_1907,plain,
    ( r1_tarski(k5_xboole_0(k1_zfmisc_1(k3_xboole_0(k5_xboole_0(sK1,sK0),sK1)),k1_zfmisc_1(k3_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(k5_xboole_0(sK1,sK0),sK1)))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) != iProver_top
    | r1_tarski(k1_zfmisc_1(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_148,c_1001])).

cnf(c_3160,plain,
    ( r1_tarski(k1_zfmisc_1(k3_xboole_0(k5_xboole_0(sK1,sK0),sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) != iProver_top
    | r1_tarski(k1_zfmisc_1(k3_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(k5_xboole_0(sK1,sK0),sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) != iProver_top
    | r1_tarski(k1_zfmisc_1(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_148,c_1907])).

cnf(c_11484,plain,
    ( r1_tarski(k1_zfmisc_1(k3_xboole_0(k5_xboole_0(sK1,sK0),sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) != iProver_top
    | r1_tarski(k1_zfmisc_1(k3_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(k5_xboole_0(sK0,sK1),sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) != iProver_top
    | r1_tarski(k1_zfmisc_1(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_3160])).

cnf(c_63124,plain,
    ( r1_tarski(k1_zfmisc_1(k3_xboole_0(k5_xboole_0(sK1,sK0),sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) != iProver_top
    | r1_tarski(k1_zfmisc_1(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2497,c_11484])).

cnf(c_65396,plain,
    ( r1_tarski(k1_zfmisc_1(k3_xboole_0(k5_xboole_0(sK1,sK0),sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_505,c_63124])).

cnf(c_93059,plain,
    ( r1_tarski(k1_zfmisc_1(k5_xboole_0(sK1,sK0)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2497,c_65396])).

cnf(c_70,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_276,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
    | X2 != X0
    | k1_zfmisc_1(k5_xboole_0(sK0,sK1)) != X1 ),
    inference(instantiation,[status(thm)],[c_70])).

cnf(c_519,plain,
    ( ~ r1_tarski(X0,k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))))
    | r1_tarski(X1,k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
    | X1 != X0
    | k1_zfmisc_1(k5_xboole_0(sK0,sK1)) != k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_276])).

cnf(c_910,plain,
    ( r1_tarski(X0,k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
    | ~ r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))))
    | X0 != k3_xboole_0(X1,X2)
    | k1_zfmisc_1(k5_xboole_0(sK0,sK1)) != k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_519])).

cnf(c_2218,plain,
    ( r1_tarski(X0,k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
    | ~ r1_tarski(k3_xboole_0(k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))),X1),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))))
    | X0 != k3_xboole_0(k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))),X1)
    | k1_zfmisc_1(k5_xboole_0(sK0,sK1)) != k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_910])).

cnf(c_8747,plain,
    ( ~ r1_tarski(k3_xboole_0(k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))))
    | r1_tarski(k1_zfmisc_1(k5_xboole_0(sK1,sK0)),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
    | k1_zfmisc_1(k5_xboole_0(sK1,sK0)) != k3_xboole_0(k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))))
    | k1_zfmisc_1(k5_xboole_0(sK0,sK1)) != k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_2218])).

cnf(c_8748,plain,
    ( k1_zfmisc_1(k5_xboole_0(sK1,sK0)) != k3_xboole_0(k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))))
    | k1_zfmisc_1(k5_xboole_0(sK0,sK1)) != k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
    | r1_tarski(k3_xboole_0(k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))) != iProver_top
    | r1_tarski(k1_zfmisc_1(k5_xboole_0(sK1,sK0)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8747])).

cnf(c_794,plain,
    ( r1_tarski(k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),X0),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_6609,plain,
    ( r1_tarski(k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_794])).

cnf(c_6610,plain,
    ( r1_tarski(k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6609])).

cnf(c_378,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))))
    | X2 != X0
    | k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) != X1 ),
    inference(instantiation,[status(thm)],[c_70])).

cnf(c_630,plain,
    ( r1_tarski(X0,k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))))
    | ~ r1_tarski(X1,k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
    | X0 != X1
    | k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) != k1_zfmisc_1(k5_xboole_0(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_378])).

cnf(c_1166,plain,
    ( r1_tarski(X0,k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))))
    | ~ r1_tarski(k3_xboole_0(X1,X2),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
    | X0 != k3_xboole_0(X1,X2)
    | k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) != k1_zfmisc_1(k5_xboole_0(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_630])).

cnf(c_1854,plain,
    ( r1_tarski(X0,k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))))
    | ~ r1_tarski(k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),X1),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
    | X0 != k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),X1)
    | k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) != k1_zfmisc_1(k5_xboole_0(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_1166])).

cnf(c_4419,plain,
    ( r1_tarski(k3_xboole_0(k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))))
    | ~ r1_tarski(k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
    | k3_xboole_0(k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))) != k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
    | k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) != k1_zfmisc_1(k5_xboole_0(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_1854])).

cnf(c_4420,plain,
    ( k3_xboole_0(k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))) != k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
    | k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) != k1_zfmisc_1(k5_xboole_0(sK0,sK1))
    | r1_tarski(k3_xboole_0(k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))) = iProver_top
    | r1_tarski(k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4419])).

cnf(c_67,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1318,plain,
    ( X0 != X1
    | X0 = k3_xboole_0(k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))))
    | k3_xboole_0(k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))) != X1 ),
    inference(instantiation,[status(thm)],[c_67])).

cnf(c_2610,plain,
    ( X0 = k3_xboole_0(k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))))
    | X0 != k1_zfmisc_1(k5_xboole_0(sK0,sK1))
    | k3_xboole_0(k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))) != k1_zfmisc_1(k5_xboole_0(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_1318])).

cnf(c_3349,plain,
    ( k3_xboole_0(k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))) != k1_zfmisc_1(k5_xboole_0(sK0,sK1))
    | k1_zfmisc_1(k5_xboole_0(sK1,sK0)) = k3_xboole_0(k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))))
    | k1_zfmisc_1(k5_xboole_0(sK1,sK0)) != k1_zfmisc_1(k5_xboole_0(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_2610])).

cnf(c_836,plain,
    ( k5_xboole_0(sK1,sK0) = k5_xboole_0(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_284,plain,
    ( X0 != X1
    | X0 = k1_zfmisc_1(k5_xboole_0(sK0,sK1))
    | k1_zfmisc_1(k5_xboole_0(sK0,sK1)) != X1 ),
    inference(instantiation,[status(thm)],[c_67])).

cnf(c_520,plain,
    ( X0 != k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
    | X0 = k1_zfmisc_1(k5_xboole_0(sK0,sK1))
    | k1_zfmisc_1(k5_xboole_0(sK0,sK1)) != k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_284])).

cnf(c_802,plain,
    ( k3_xboole_0(k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))) != k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
    | k3_xboole_0(k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))) = k1_zfmisc_1(k5_xboole_0(sK0,sK1))
    | k1_zfmisc_1(k5_xboole_0(sK0,sK1)) != k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_520])).

cnf(c_651,plain,
    ( k3_xboole_0(k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))) = k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_72,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_347,plain,
    ( X0 != k5_xboole_0(sK0,sK1)
    | k1_zfmisc_1(X0) = k1_zfmisc_1(k5_xboole_0(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_72])).

cnf(c_546,plain,
    ( k5_xboole_0(sK1,sK0) != k5_xboole_0(sK0,sK1)
    | k1_zfmisc_1(k5_xboole_0(sK1,sK0)) = k1_zfmisc_1(k5_xboole_0(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_347])).

cnf(c_361,plain,
    ( k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) = k1_zfmisc_1(k5_xboole_0(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_179,plain,
    ( X0 != X1
    | k1_zfmisc_1(k5_xboole_0(sK0,sK1)) != X1
    | k1_zfmisc_1(k5_xboole_0(sK0,sK1)) = X0 ),
    inference(instantiation,[status(thm)],[c_67])).

cnf(c_208,plain,
    ( X0 != k1_zfmisc_1(k5_xboole_0(sK0,sK1))
    | k1_zfmisc_1(k5_xboole_0(sK0,sK1)) = X0
    | k1_zfmisc_1(k5_xboole_0(sK0,sK1)) != k1_zfmisc_1(k5_xboole_0(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_179])).

cnf(c_282,plain,
    ( k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) != k1_zfmisc_1(k5_xboole_0(sK0,sK1))
    | k1_zfmisc_1(k5_xboole_0(sK0,sK1)) = k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
    | k1_zfmisc_1(k5_xboole_0(sK0,sK1)) != k1_zfmisc_1(k5_xboole_0(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_208])).

cnf(c_66,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_217,plain,
    ( k1_zfmisc_1(k5_xboole_0(sK0,sK1)) = k1_zfmisc_1(k5_xboole_0(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_66])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_93059,c_8748,c_6610,c_4420,c_3349,c_836,c_802,c_651,c_546,c_361,c_282,c_217])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:09:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 35.47/5.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 35.47/5.01  
% 35.47/5.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 35.47/5.01  
% 35.47/5.01  ------  iProver source info
% 35.47/5.01  
% 35.47/5.01  git: date: 2020-06-30 10:37:57 +0100
% 35.47/5.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 35.47/5.01  git: non_committed_changes: false
% 35.47/5.01  git: last_make_outside_of_git: false
% 35.47/5.01  
% 35.47/5.01  ------ 
% 35.47/5.01  
% 35.47/5.01  ------ Input Options
% 35.47/5.01  
% 35.47/5.01  --out_options                           all
% 35.47/5.01  --tptp_safe_out                         true
% 35.47/5.01  --problem_path                          ""
% 35.47/5.01  --include_path                          ""
% 35.47/5.01  --clausifier                            res/vclausify_rel
% 35.47/5.01  --clausifier_options                    ""
% 35.47/5.01  --stdin                                 false
% 35.47/5.01  --stats_out                             all
% 35.47/5.01  
% 35.47/5.01  ------ General Options
% 35.47/5.01  
% 35.47/5.01  --fof                                   false
% 35.47/5.01  --time_out_real                         305.
% 35.47/5.01  --time_out_virtual                      -1.
% 35.47/5.01  --symbol_type_check                     false
% 35.47/5.01  --clausify_out                          false
% 35.47/5.01  --sig_cnt_out                           false
% 35.47/5.01  --trig_cnt_out                          false
% 35.47/5.01  --trig_cnt_out_tolerance                1.
% 35.47/5.01  --trig_cnt_out_sk_spl                   false
% 35.47/5.01  --abstr_cl_out                          false
% 35.47/5.01  
% 35.47/5.01  ------ Global Options
% 35.47/5.01  
% 35.47/5.01  --schedule                              default
% 35.47/5.01  --add_important_lit                     false
% 35.47/5.01  --prop_solver_per_cl                    1000
% 35.47/5.01  --min_unsat_core                        false
% 35.47/5.01  --soft_assumptions                      false
% 35.47/5.01  --soft_lemma_size                       3
% 35.47/5.01  --prop_impl_unit_size                   0
% 35.47/5.01  --prop_impl_unit                        []
% 35.47/5.01  --share_sel_clauses                     true
% 35.47/5.01  --reset_solvers                         false
% 35.47/5.01  --bc_imp_inh                            [conj_cone]
% 35.47/5.01  --conj_cone_tolerance                   3.
% 35.47/5.01  --extra_neg_conj                        none
% 35.47/5.01  --large_theory_mode                     true
% 35.47/5.01  --prolific_symb_bound                   200
% 35.47/5.01  --lt_threshold                          2000
% 35.47/5.01  --clause_weak_htbl                      true
% 35.47/5.01  --gc_record_bc_elim                     false
% 35.47/5.01  
% 35.47/5.01  ------ Preprocessing Options
% 35.47/5.01  
% 35.47/5.01  --preprocessing_flag                    true
% 35.47/5.01  --time_out_prep_mult                    0.1
% 35.47/5.01  --splitting_mode                        input
% 35.47/5.01  --splitting_grd                         true
% 35.47/5.01  --splitting_cvd                         false
% 35.47/5.01  --splitting_cvd_svl                     false
% 35.47/5.01  --splitting_nvd                         32
% 35.47/5.01  --sub_typing                            true
% 35.47/5.01  --prep_gs_sim                           true
% 35.47/5.01  --prep_unflatten                        true
% 35.47/5.01  --prep_res_sim                          true
% 35.47/5.01  --prep_upred                            true
% 35.47/5.01  --prep_sem_filter                       exhaustive
% 35.47/5.01  --prep_sem_filter_out                   false
% 35.47/5.01  --pred_elim                             true
% 35.47/5.01  --res_sim_input                         true
% 35.47/5.01  --eq_ax_congr_red                       true
% 35.47/5.01  --pure_diseq_elim                       true
% 35.47/5.01  --brand_transform                       false
% 35.47/5.01  --non_eq_to_eq                          false
% 35.47/5.01  --prep_def_merge                        true
% 35.47/5.01  --prep_def_merge_prop_impl              false
% 35.47/5.01  --prep_def_merge_mbd                    true
% 35.47/5.01  --prep_def_merge_tr_red                 false
% 35.47/5.01  --prep_def_merge_tr_cl                  false
% 35.47/5.01  --smt_preprocessing                     true
% 35.47/5.01  --smt_ac_axioms                         fast
% 35.47/5.01  --preprocessed_out                      false
% 35.47/5.01  --preprocessed_stats                    false
% 35.47/5.01  
% 35.47/5.01  ------ Abstraction refinement Options
% 35.47/5.01  
% 35.47/5.01  --abstr_ref                             []
% 35.47/5.01  --abstr_ref_prep                        false
% 35.47/5.01  --abstr_ref_until_sat                   false
% 35.47/5.01  --abstr_ref_sig_restrict                funpre
% 35.47/5.01  --abstr_ref_af_restrict_to_split_sk     false
% 35.47/5.01  --abstr_ref_under                       []
% 35.47/5.01  
% 35.47/5.01  ------ SAT Options
% 35.47/5.01  
% 35.47/5.01  --sat_mode                              false
% 35.47/5.01  --sat_fm_restart_options                ""
% 35.47/5.01  --sat_gr_def                            false
% 35.47/5.01  --sat_epr_types                         true
% 35.47/5.01  --sat_non_cyclic_types                  false
% 35.47/5.01  --sat_finite_models                     false
% 35.47/5.01  --sat_fm_lemmas                         false
% 35.47/5.01  --sat_fm_prep                           false
% 35.47/5.01  --sat_fm_uc_incr                        true
% 35.47/5.01  --sat_out_model                         small
% 35.47/5.01  --sat_out_clauses                       false
% 35.47/5.01  
% 35.47/5.01  ------ QBF Options
% 35.47/5.01  
% 35.47/5.01  --qbf_mode                              false
% 35.47/5.01  --qbf_elim_univ                         false
% 35.47/5.01  --qbf_dom_inst                          none
% 35.47/5.01  --qbf_dom_pre_inst                      false
% 35.47/5.01  --qbf_sk_in                             false
% 35.47/5.01  --qbf_pred_elim                         true
% 35.47/5.01  --qbf_split                             512
% 35.47/5.01  
% 35.47/5.01  ------ BMC1 Options
% 35.47/5.01  
% 35.47/5.01  --bmc1_incremental                      false
% 35.47/5.01  --bmc1_axioms                           reachable_all
% 35.47/5.01  --bmc1_min_bound                        0
% 35.47/5.01  --bmc1_max_bound                        -1
% 35.47/5.01  --bmc1_max_bound_default                -1
% 35.47/5.01  --bmc1_symbol_reachability              true
% 35.47/5.01  --bmc1_property_lemmas                  false
% 35.47/5.01  --bmc1_k_induction                      false
% 35.47/5.01  --bmc1_non_equiv_states                 false
% 35.47/5.01  --bmc1_deadlock                         false
% 35.47/5.01  --bmc1_ucm                              false
% 35.47/5.01  --bmc1_add_unsat_core                   none
% 35.47/5.01  --bmc1_unsat_core_children              false
% 35.47/5.01  --bmc1_unsat_core_extrapolate_axioms    false
% 35.47/5.01  --bmc1_out_stat                         full
% 35.47/5.01  --bmc1_ground_init                      false
% 35.47/5.01  --bmc1_pre_inst_next_state              false
% 35.47/5.01  --bmc1_pre_inst_state                   false
% 35.47/5.01  --bmc1_pre_inst_reach_state             false
% 35.47/5.01  --bmc1_out_unsat_core                   false
% 35.47/5.01  --bmc1_aig_witness_out                  false
% 35.47/5.01  --bmc1_verbose                          false
% 35.47/5.01  --bmc1_dump_clauses_tptp                false
% 35.47/5.01  --bmc1_dump_unsat_core_tptp             false
% 35.47/5.01  --bmc1_dump_file                        -
% 35.47/5.01  --bmc1_ucm_expand_uc_limit              128
% 35.47/5.01  --bmc1_ucm_n_expand_iterations          6
% 35.47/5.01  --bmc1_ucm_extend_mode                  1
% 35.47/5.01  --bmc1_ucm_init_mode                    2
% 35.47/5.01  --bmc1_ucm_cone_mode                    none
% 35.47/5.01  --bmc1_ucm_reduced_relation_type        0
% 35.47/5.01  --bmc1_ucm_relax_model                  4
% 35.47/5.01  --bmc1_ucm_full_tr_after_sat            true
% 35.47/5.01  --bmc1_ucm_expand_neg_assumptions       false
% 35.47/5.01  --bmc1_ucm_layered_model                none
% 35.47/5.01  --bmc1_ucm_max_lemma_size               10
% 35.47/5.01  
% 35.47/5.01  ------ AIG Options
% 35.47/5.01  
% 35.47/5.01  --aig_mode                              false
% 35.47/5.01  
% 35.47/5.01  ------ Instantiation Options
% 35.47/5.01  
% 35.47/5.01  --instantiation_flag                    true
% 35.47/5.01  --inst_sos_flag                         true
% 35.47/5.01  --inst_sos_phase                        true
% 35.47/5.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 35.47/5.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 35.47/5.01  --inst_lit_sel_side                     num_symb
% 35.47/5.01  --inst_solver_per_active                1400
% 35.47/5.01  --inst_solver_calls_frac                1.
% 35.47/5.01  --inst_passive_queue_type               priority_queues
% 35.47/5.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 35.47/5.01  --inst_passive_queues_freq              [25;2]
% 35.47/5.01  --inst_dismatching                      true
% 35.47/5.01  --inst_eager_unprocessed_to_passive     true
% 35.47/5.01  --inst_prop_sim_given                   true
% 35.47/5.01  --inst_prop_sim_new                     false
% 35.47/5.01  --inst_subs_new                         false
% 35.47/5.01  --inst_eq_res_simp                      false
% 35.47/5.01  --inst_subs_given                       false
% 35.47/5.01  --inst_orphan_elimination               true
% 35.47/5.01  --inst_learning_loop_flag               true
% 35.47/5.01  --inst_learning_start                   3000
% 35.47/5.01  --inst_learning_factor                  2
% 35.47/5.01  --inst_start_prop_sim_after_learn       3
% 35.47/5.01  --inst_sel_renew                        solver
% 35.47/5.01  --inst_lit_activity_flag                true
% 35.47/5.01  --inst_restr_to_given                   false
% 35.47/5.01  --inst_activity_threshold               500
% 35.47/5.01  --inst_out_proof                        true
% 35.47/5.01  
% 35.47/5.01  ------ Resolution Options
% 35.47/5.01  
% 35.47/5.01  --resolution_flag                       true
% 35.47/5.01  --res_lit_sel                           adaptive
% 35.47/5.01  --res_lit_sel_side                      none
% 35.47/5.01  --res_ordering                          kbo
% 35.47/5.01  --res_to_prop_solver                    active
% 35.47/5.01  --res_prop_simpl_new                    false
% 35.47/5.01  --res_prop_simpl_given                  true
% 35.47/5.01  --res_passive_queue_type                priority_queues
% 35.47/5.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 35.47/5.01  --res_passive_queues_freq               [15;5]
% 35.47/5.01  --res_forward_subs                      full
% 35.47/5.01  --res_backward_subs                     full
% 35.47/5.01  --res_forward_subs_resolution           true
% 35.47/5.01  --res_backward_subs_resolution          true
% 35.47/5.01  --res_orphan_elimination                true
% 35.47/5.01  --res_time_limit                        2.
% 35.47/5.01  --res_out_proof                         true
% 35.47/5.01  
% 35.47/5.01  ------ Superposition Options
% 35.47/5.01  
% 35.47/5.01  --superposition_flag                    true
% 35.47/5.01  --sup_passive_queue_type                priority_queues
% 35.47/5.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 35.47/5.01  --sup_passive_queues_freq               [8;1;4]
% 35.47/5.01  --demod_completeness_check              fast
% 35.47/5.01  --demod_use_ground                      true
% 35.47/5.01  --sup_to_prop_solver                    passive
% 35.47/5.01  --sup_prop_simpl_new                    true
% 35.47/5.01  --sup_prop_simpl_given                  true
% 35.47/5.01  --sup_fun_splitting                     true
% 35.47/5.01  --sup_smt_interval                      50000
% 35.47/5.01  
% 35.47/5.01  ------ Superposition Simplification Setup
% 35.47/5.01  
% 35.47/5.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 35.47/5.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 35.47/5.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 35.47/5.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 35.47/5.01  --sup_full_triv                         [TrivRules;PropSubs]
% 35.47/5.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 35.47/5.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 35.47/5.01  --sup_immed_triv                        [TrivRules]
% 35.47/5.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 35.47/5.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.47/5.01  --sup_immed_bw_main                     []
% 35.47/5.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 35.47/5.01  --sup_input_triv                        [Unflattening;TrivRules]
% 35.47/5.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.47/5.01  --sup_input_bw                          []
% 35.47/5.01  
% 35.47/5.01  ------ Combination Options
% 35.47/5.01  
% 35.47/5.01  --comb_res_mult                         3
% 35.47/5.01  --comb_sup_mult                         2
% 35.47/5.01  --comb_inst_mult                        10
% 35.47/5.01  
% 35.47/5.01  ------ Debug Options
% 35.47/5.01  
% 35.47/5.01  --dbg_backtrace                         false
% 35.47/5.01  --dbg_dump_prop_clauses                 false
% 35.47/5.01  --dbg_dump_prop_clauses_file            -
% 35.47/5.01  --dbg_out_stat                          false
% 35.47/5.01  ------ Parsing...
% 35.47/5.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 35.47/5.01  
% 35.47/5.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 35.47/5.01  
% 35.47/5.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 35.47/5.01  
% 35.47/5.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.47/5.01  ------ Proving...
% 35.47/5.01  ------ Problem Properties 
% 35.47/5.01  
% 35.47/5.01  
% 35.47/5.01  clauses                                 11
% 35.47/5.01  conjectures                             1
% 35.47/5.01  EPR                                     0
% 35.47/5.01  Horn                                    11
% 35.47/5.01  unary                                   9
% 35.47/5.01  binary                                  1
% 35.47/5.01  lits                                    14
% 35.47/5.01  lits eq                                 7
% 35.47/5.01  fd_pure                                 0
% 35.47/5.01  fd_pseudo                               0
% 35.47/5.01  fd_cond                                 0
% 35.47/5.01  fd_pseudo_cond                          0
% 35.47/5.01  AC symbols                              1
% 35.47/5.01  
% 35.47/5.01  ------ Schedule dynamic 5 is on 
% 35.47/5.01  
% 35.47/5.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 35.47/5.01  
% 35.47/5.01  
% 35.47/5.01  ------ 
% 35.47/5.01  Current options:
% 35.47/5.01  ------ 
% 35.47/5.01  
% 35.47/5.01  ------ Input Options
% 35.47/5.01  
% 35.47/5.01  --out_options                           all
% 35.47/5.01  --tptp_safe_out                         true
% 35.47/5.01  --problem_path                          ""
% 35.47/5.01  --include_path                          ""
% 35.47/5.01  --clausifier                            res/vclausify_rel
% 35.47/5.01  --clausifier_options                    ""
% 35.47/5.01  --stdin                                 false
% 35.47/5.01  --stats_out                             all
% 35.47/5.01  
% 35.47/5.01  ------ General Options
% 35.47/5.01  
% 35.47/5.01  --fof                                   false
% 35.47/5.01  --time_out_real                         305.
% 35.47/5.01  --time_out_virtual                      -1.
% 35.47/5.01  --symbol_type_check                     false
% 35.47/5.01  --clausify_out                          false
% 35.47/5.01  --sig_cnt_out                           false
% 35.47/5.01  --trig_cnt_out                          false
% 35.47/5.01  --trig_cnt_out_tolerance                1.
% 35.47/5.01  --trig_cnt_out_sk_spl                   false
% 35.47/5.01  --abstr_cl_out                          false
% 35.47/5.01  
% 35.47/5.01  ------ Global Options
% 35.47/5.01  
% 35.47/5.01  --schedule                              default
% 35.47/5.01  --add_important_lit                     false
% 35.47/5.01  --prop_solver_per_cl                    1000
% 35.47/5.01  --min_unsat_core                        false
% 35.47/5.01  --soft_assumptions                      false
% 35.47/5.01  --soft_lemma_size                       3
% 35.47/5.01  --prop_impl_unit_size                   0
% 35.47/5.01  --prop_impl_unit                        []
% 35.47/5.01  --share_sel_clauses                     true
% 35.47/5.01  --reset_solvers                         false
% 35.47/5.01  --bc_imp_inh                            [conj_cone]
% 35.47/5.01  --conj_cone_tolerance                   3.
% 35.47/5.01  --extra_neg_conj                        none
% 35.47/5.01  --large_theory_mode                     true
% 35.47/5.01  --prolific_symb_bound                   200
% 35.47/5.01  --lt_threshold                          2000
% 35.47/5.01  --clause_weak_htbl                      true
% 35.47/5.01  --gc_record_bc_elim                     false
% 35.47/5.01  
% 35.47/5.01  ------ Preprocessing Options
% 35.47/5.01  
% 35.47/5.01  --preprocessing_flag                    true
% 35.47/5.01  --time_out_prep_mult                    0.1
% 35.47/5.01  --splitting_mode                        input
% 35.47/5.01  --splitting_grd                         true
% 35.47/5.01  --splitting_cvd                         false
% 35.47/5.01  --splitting_cvd_svl                     false
% 35.47/5.01  --splitting_nvd                         32
% 35.47/5.01  --sub_typing                            true
% 35.47/5.01  --prep_gs_sim                           true
% 35.47/5.01  --prep_unflatten                        true
% 35.47/5.01  --prep_res_sim                          true
% 35.47/5.01  --prep_upred                            true
% 35.47/5.01  --prep_sem_filter                       exhaustive
% 35.47/5.01  --prep_sem_filter_out                   false
% 35.47/5.01  --pred_elim                             true
% 35.47/5.01  --res_sim_input                         true
% 35.47/5.01  --eq_ax_congr_red                       true
% 35.47/5.01  --pure_diseq_elim                       true
% 35.47/5.01  --brand_transform                       false
% 35.47/5.01  --non_eq_to_eq                          false
% 35.47/5.01  --prep_def_merge                        true
% 35.47/5.01  --prep_def_merge_prop_impl              false
% 35.47/5.01  --prep_def_merge_mbd                    true
% 35.47/5.01  --prep_def_merge_tr_red                 false
% 35.47/5.01  --prep_def_merge_tr_cl                  false
% 35.47/5.01  --smt_preprocessing                     true
% 35.47/5.01  --smt_ac_axioms                         fast
% 35.47/5.01  --preprocessed_out                      false
% 35.47/5.01  --preprocessed_stats                    false
% 35.47/5.01  
% 35.47/5.01  ------ Abstraction refinement Options
% 35.47/5.01  
% 35.47/5.01  --abstr_ref                             []
% 35.47/5.01  --abstr_ref_prep                        false
% 35.47/5.01  --abstr_ref_until_sat                   false
% 35.47/5.01  --abstr_ref_sig_restrict                funpre
% 35.47/5.01  --abstr_ref_af_restrict_to_split_sk     false
% 35.47/5.01  --abstr_ref_under                       []
% 35.47/5.01  
% 35.47/5.01  ------ SAT Options
% 35.47/5.01  
% 35.47/5.01  --sat_mode                              false
% 35.47/5.01  --sat_fm_restart_options                ""
% 35.47/5.01  --sat_gr_def                            false
% 35.47/5.01  --sat_epr_types                         true
% 35.47/5.01  --sat_non_cyclic_types                  false
% 35.47/5.01  --sat_finite_models                     false
% 35.47/5.01  --sat_fm_lemmas                         false
% 35.47/5.01  --sat_fm_prep                           false
% 35.47/5.01  --sat_fm_uc_incr                        true
% 35.47/5.01  --sat_out_model                         small
% 35.47/5.01  --sat_out_clauses                       false
% 35.47/5.01  
% 35.47/5.01  ------ QBF Options
% 35.47/5.01  
% 35.47/5.01  --qbf_mode                              false
% 35.47/5.01  --qbf_elim_univ                         false
% 35.47/5.01  --qbf_dom_inst                          none
% 35.47/5.01  --qbf_dom_pre_inst                      false
% 35.47/5.01  --qbf_sk_in                             false
% 35.47/5.01  --qbf_pred_elim                         true
% 35.47/5.01  --qbf_split                             512
% 35.47/5.01  
% 35.47/5.01  ------ BMC1 Options
% 35.47/5.01  
% 35.47/5.01  --bmc1_incremental                      false
% 35.47/5.01  --bmc1_axioms                           reachable_all
% 35.47/5.01  --bmc1_min_bound                        0
% 35.47/5.01  --bmc1_max_bound                        -1
% 35.47/5.01  --bmc1_max_bound_default                -1
% 35.47/5.01  --bmc1_symbol_reachability              true
% 35.47/5.01  --bmc1_property_lemmas                  false
% 35.47/5.01  --bmc1_k_induction                      false
% 35.47/5.01  --bmc1_non_equiv_states                 false
% 35.47/5.01  --bmc1_deadlock                         false
% 35.47/5.01  --bmc1_ucm                              false
% 35.47/5.01  --bmc1_add_unsat_core                   none
% 35.47/5.01  --bmc1_unsat_core_children              false
% 35.47/5.01  --bmc1_unsat_core_extrapolate_axioms    false
% 35.47/5.01  --bmc1_out_stat                         full
% 35.47/5.01  --bmc1_ground_init                      false
% 35.47/5.01  --bmc1_pre_inst_next_state              false
% 35.47/5.01  --bmc1_pre_inst_state                   false
% 35.47/5.01  --bmc1_pre_inst_reach_state             false
% 35.47/5.01  --bmc1_out_unsat_core                   false
% 35.47/5.01  --bmc1_aig_witness_out                  false
% 35.47/5.01  --bmc1_verbose                          false
% 35.47/5.01  --bmc1_dump_clauses_tptp                false
% 35.47/5.01  --bmc1_dump_unsat_core_tptp             false
% 35.47/5.01  --bmc1_dump_file                        -
% 35.47/5.01  --bmc1_ucm_expand_uc_limit              128
% 35.47/5.01  --bmc1_ucm_n_expand_iterations          6
% 35.47/5.01  --bmc1_ucm_extend_mode                  1
% 35.47/5.01  --bmc1_ucm_init_mode                    2
% 35.47/5.01  --bmc1_ucm_cone_mode                    none
% 35.47/5.01  --bmc1_ucm_reduced_relation_type        0
% 35.47/5.01  --bmc1_ucm_relax_model                  4
% 35.47/5.01  --bmc1_ucm_full_tr_after_sat            true
% 35.47/5.01  --bmc1_ucm_expand_neg_assumptions       false
% 35.47/5.01  --bmc1_ucm_layered_model                none
% 35.47/5.01  --bmc1_ucm_max_lemma_size               10
% 35.47/5.01  
% 35.47/5.01  ------ AIG Options
% 35.47/5.01  
% 35.47/5.01  --aig_mode                              false
% 35.47/5.01  
% 35.47/5.01  ------ Instantiation Options
% 35.47/5.01  
% 35.47/5.01  --instantiation_flag                    true
% 35.47/5.01  --inst_sos_flag                         true
% 35.47/5.01  --inst_sos_phase                        true
% 35.47/5.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 35.47/5.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 35.47/5.01  --inst_lit_sel_side                     none
% 35.47/5.01  --inst_solver_per_active                1400
% 35.47/5.01  --inst_solver_calls_frac                1.
% 35.47/5.01  --inst_passive_queue_type               priority_queues
% 35.47/5.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 35.47/5.01  --inst_passive_queues_freq              [25;2]
% 35.47/5.01  --inst_dismatching                      true
% 35.47/5.01  --inst_eager_unprocessed_to_passive     true
% 35.47/5.01  --inst_prop_sim_given                   true
% 35.47/5.01  --inst_prop_sim_new                     false
% 35.47/5.01  --inst_subs_new                         false
% 35.47/5.01  --inst_eq_res_simp                      false
% 35.47/5.01  --inst_subs_given                       false
% 35.47/5.01  --inst_orphan_elimination               true
% 35.47/5.01  --inst_learning_loop_flag               true
% 35.47/5.01  --inst_learning_start                   3000
% 35.47/5.01  --inst_learning_factor                  2
% 35.47/5.01  --inst_start_prop_sim_after_learn       3
% 35.47/5.01  --inst_sel_renew                        solver
% 35.47/5.01  --inst_lit_activity_flag                true
% 35.47/5.01  --inst_restr_to_given                   false
% 35.47/5.01  --inst_activity_threshold               500
% 35.47/5.01  --inst_out_proof                        true
% 35.47/5.01  
% 35.47/5.01  ------ Resolution Options
% 35.47/5.01  
% 35.47/5.01  --resolution_flag                       false
% 35.47/5.01  --res_lit_sel                           adaptive
% 35.47/5.01  --res_lit_sel_side                      none
% 35.47/5.01  --res_ordering                          kbo
% 35.47/5.01  --res_to_prop_solver                    active
% 35.47/5.01  --res_prop_simpl_new                    false
% 35.47/5.01  --res_prop_simpl_given                  true
% 35.47/5.01  --res_passive_queue_type                priority_queues
% 35.47/5.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 35.47/5.01  --res_passive_queues_freq               [15;5]
% 35.47/5.01  --res_forward_subs                      full
% 35.47/5.01  --res_backward_subs                     full
% 35.47/5.01  --res_forward_subs_resolution           true
% 35.47/5.01  --res_backward_subs_resolution          true
% 35.47/5.01  --res_orphan_elimination                true
% 35.47/5.01  --res_time_limit                        2.
% 35.47/5.01  --res_out_proof                         true
% 35.47/5.01  
% 35.47/5.01  ------ Superposition Options
% 35.47/5.01  
% 35.47/5.01  --superposition_flag                    true
% 35.47/5.01  --sup_passive_queue_type                priority_queues
% 35.47/5.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 35.47/5.01  --sup_passive_queues_freq               [8;1;4]
% 35.47/5.01  --demod_completeness_check              fast
% 35.47/5.01  --demod_use_ground                      true
% 35.47/5.01  --sup_to_prop_solver                    passive
% 35.47/5.01  --sup_prop_simpl_new                    true
% 35.47/5.01  --sup_prop_simpl_given                  true
% 35.47/5.01  --sup_fun_splitting                     true
% 35.47/5.01  --sup_smt_interval                      50000
% 35.47/5.01  
% 35.47/5.01  ------ Superposition Simplification Setup
% 35.47/5.01  
% 35.47/5.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 35.47/5.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 35.47/5.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 35.47/5.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 35.47/5.01  --sup_full_triv                         [TrivRules;PropSubs]
% 35.47/5.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 35.47/5.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 35.47/5.01  --sup_immed_triv                        [TrivRules]
% 35.47/5.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 35.47/5.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.47/5.01  --sup_immed_bw_main                     []
% 35.47/5.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 35.47/5.01  --sup_input_triv                        [Unflattening;TrivRules]
% 35.47/5.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.47/5.01  --sup_input_bw                          []
% 35.47/5.01  
% 35.47/5.01  ------ Combination Options
% 35.47/5.01  
% 35.47/5.01  --comb_res_mult                         3
% 35.47/5.01  --comb_sup_mult                         2
% 35.47/5.01  --comb_inst_mult                        10
% 35.47/5.01  
% 35.47/5.01  ------ Debug Options
% 35.47/5.01  
% 35.47/5.01  --dbg_backtrace                         false
% 35.47/5.01  --dbg_dump_prop_clauses                 false
% 35.47/5.01  --dbg_dump_prop_clauses_file            -
% 35.47/5.01  --dbg_out_stat                          false
% 35.47/5.01  
% 35.47/5.01  
% 35.47/5.01  
% 35.47/5.01  
% 35.47/5.01  ------ Proving...
% 35.47/5.01  
% 35.47/5.01  
% 35.47/5.01  % SZS status Theorem for theBenchmark.p
% 35.47/5.01  
% 35.47/5.01  % SZS output start CNFRefutation for theBenchmark.p
% 35.47/5.01  
% 35.47/5.01  fof(f18,axiom,(
% 35.47/5.01    ! [X0,X1] : k3_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = k1_zfmisc_1(k3_xboole_0(X0,X1))),
% 35.47/5.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.47/5.01  
% 35.47/5.01  fof(f45,plain,(
% 35.47/5.01    ( ! [X0,X1] : (k3_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = k1_zfmisc_1(k3_xboole_0(X0,X1))) )),
% 35.47/5.01    inference(cnf_transformation,[],[f18])).
% 35.47/5.01  
% 35.47/5.01  fof(f5,axiom,(
% 35.47/5.01    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),X1))),
% 35.47/5.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.47/5.01  
% 35.47/5.01  fof(f22,plain,(
% 35.47/5.01    ! [X0,X1,X2] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 35.47/5.01    inference(ennf_transformation,[],[f5])).
% 35.47/5.01  
% 35.47/5.01  fof(f32,plain,(
% 35.47/5.01    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 35.47/5.01    inference(cnf_transformation,[],[f22])).
% 35.47/5.01  
% 35.47/5.01  fof(f1,axiom,(
% 35.47/5.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 35.47/5.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.47/5.01  
% 35.47/5.01  fof(f28,plain,(
% 35.47/5.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 35.47/5.01    inference(cnf_transformation,[],[f1])).
% 35.47/5.01  
% 35.47/5.01  fof(f8,axiom,(
% 35.47/5.01    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 35.47/5.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.47/5.01  
% 35.47/5.01  fof(f35,plain,(
% 35.47/5.01    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 35.47/5.01    inference(cnf_transformation,[],[f8])).
% 35.47/5.01  
% 35.47/5.01  fof(f2,axiom,(
% 35.47/5.01    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 35.47/5.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.47/5.01  
% 35.47/5.01  fof(f29,plain,(
% 35.47/5.01    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 35.47/5.01    inference(cnf_transformation,[],[f2])).
% 35.47/5.01  
% 35.47/5.01  fof(f6,axiom,(
% 35.47/5.01    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k5_xboole_0(X0,X2),X1))),
% 35.47/5.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.47/5.01  
% 35.47/5.01  fof(f23,plain,(
% 35.47/5.01    ! [X0,X1,X2] : (r1_tarski(k5_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 35.47/5.01    inference(ennf_transformation,[],[f6])).
% 35.47/5.01  
% 35.47/5.01  fof(f24,plain,(
% 35.47/5.01    ! [X0,X1,X2] : (r1_tarski(k5_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 35.47/5.01    inference(flattening,[],[f23])).
% 35.47/5.01  
% 35.47/5.01  fof(f33,plain,(
% 35.47/5.01    ( ! [X2,X0,X1] : (r1_tarski(k5_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 35.47/5.01    inference(cnf_transformation,[],[f24])).
% 35.47/5.01  
% 35.47/5.01  fof(f3,axiom,(
% 35.47/5.01    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 35.47/5.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.47/5.01  
% 35.47/5.01  fof(f21,plain,(
% 35.47/5.01    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 35.47/5.01    inference(rectify,[],[f3])).
% 35.47/5.01  
% 35.47/5.01  fof(f30,plain,(
% 35.47/5.01    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 35.47/5.01    inference(cnf_transformation,[],[f21])).
% 35.47/5.01  
% 35.47/5.01  fof(f7,axiom,(
% 35.47/5.01    ! [X0,X1,X2] : k3_xboole_0(k5_xboole_0(X0,X2),X1) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1))),
% 35.47/5.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.47/5.01  
% 35.47/5.01  fof(f34,plain,(
% 35.47/5.01    ( ! [X2,X0,X1] : (k3_xboole_0(k5_xboole_0(X0,X2),X1) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1))) )),
% 35.47/5.01    inference(cnf_transformation,[],[f7])).
% 35.47/5.01  
% 35.47/5.01  fof(f19,conjecture,(
% 35.47/5.01    ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1)))),
% 35.47/5.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.47/5.01  
% 35.47/5.01  fof(f20,negated_conjecture,(
% 35.47/5.01    ~! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1)))),
% 35.47/5.01    inference(negated_conjecture,[],[f19])).
% 35.47/5.01  
% 35.47/5.01  fof(f25,plain,(
% 35.47/5.01    ? [X0,X1] : ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1)))),
% 35.47/5.01    inference(ennf_transformation,[],[f20])).
% 35.47/5.01  
% 35.47/5.01  fof(f26,plain,(
% 35.47/5.01    ? [X0,X1] : ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1))) => ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 35.47/5.01    introduced(choice_axiom,[])).
% 35.47/5.01  
% 35.47/5.01  fof(f27,plain,(
% 35.47/5.01    ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 35.47/5.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f26])).
% 35.47/5.01  
% 35.47/5.01  fof(f46,plain,(
% 35.47/5.01    ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 35.47/5.01    inference(cnf_transformation,[],[f27])).
% 35.47/5.01  
% 35.47/5.01  fof(f10,axiom,(
% 35.47/5.01    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)),
% 35.47/5.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.47/5.01  
% 35.47/5.01  fof(f37,plain,(
% 35.47/5.01    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 35.47/5.01    inference(cnf_transformation,[],[f10])).
% 35.47/5.01  
% 35.47/5.01  fof(f4,axiom,(
% 35.47/5.01    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 35.47/5.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.47/5.01  
% 35.47/5.01  fof(f31,plain,(
% 35.47/5.01    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 35.47/5.01    inference(cnf_transformation,[],[f4])).
% 35.47/5.01  
% 35.47/5.01  fof(f53,plain,(
% 35.47/5.01    ~r1_tarski(k5_xboole_0(k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 35.47/5.01    inference(definition_unfolding,[],[f46,f37,f31,f31])).
% 35.47/5.01  
% 35.47/5.01  fof(f9,axiom,(
% 35.47/5.01    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 35.47/5.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.47/5.01  
% 35.47/5.01  fof(f36,plain,(
% 35.47/5.01    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 35.47/5.01    inference(cnf_transformation,[],[f9])).
% 35.47/5.01  
% 35.47/5.01  cnf(c_9,plain,
% 35.47/5.01      ( k3_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = k1_zfmisc_1(k3_xboole_0(X0,X1)) ),
% 35.47/5.01      inference(cnf_transformation,[],[f45]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_3,plain,
% 35.47/5.01      ( ~ r1_tarski(X0,X1) | r1_tarski(k3_xboole_0(X0,X2),X1) ),
% 35.47/5.01      inference(cnf_transformation,[],[f32]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_149,plain,
% 35.47/5.01      ( r1_tarski(X0,X1) != iProver_top
% 35.47/5.01      | r1_tarski(k3_xboole_0(X0,X2),X1) = iProver_top ),
% 35.47/5.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_2497,plain,
% 35.47/5.01      ( r1_tarski(k1_zfmisc_1(X0),X1) != iProver_top
% 35.47/5.01      | r1_tarski(k1_zfmisc_1(k3_xboole_0(X0,X2)),X1) = iProver_top ),
% 35.47/5.01      inference(superposition,[status(thm)],[c_9,c_149]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_0,plain,
% 35.47/5.01      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 35.47/5.01      inference(cnf_transformation,[],[f28]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_6,plain,
% 35.47/5.01      ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
% 35.47/5.01      inference(cnf_transformation,[],[f35]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_147,plain,
% 35.47/5.01      ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
% 35.47/5.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_321,plain,
% 35.47/5.01      ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
% 35.47/5.01      inference(superposition,[status(thm)],[c_0,c_147]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_505,plain,
% 35.47/5.01      ( r1_tarski(k1_zfmisc_1(k3_xboole_0(X0,X1)),k1_zfmisc_1(X1)) = iProver_top ),
% 35.47/5.01      inference(superposition,[status(thm)],[c_9,c_321]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_1,plain,
% 35.47/5.01      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 35.47/5.01      inference(cnf_transformation,[],[f29]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_4,plain,
% 35.47/5.01      ( ~ r1_tarski(X0,X1)
% 35.47/5.01      | ~ r1_tarski(X2,X1)
% 35.47/5.01      | r1_tarski(k5_xboole_0(X0,X2),X1) ),
% 35.47/5.01      inference(cnf_transformation,[],[f33]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_148,plain,
% 35.47/5.01      ( r1_tarski(X0,X1) != iProver_top
% 35.47/5.01      | r1_tarski(X2,X1) != iProver_top
% 35.47/5.01      | r1_tarski(k5_xboole_0(X0,X2),X1) = iProver_top ),
% 35.47/5.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_2,plain,
% 35.47/5.01      ( k3_xboole_0(X0,X0) = X0 ),
% 35.47/5.01      inference(cnf_transformation,[],[f30]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_5,plain,
% 35.47/5.01      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
% 35.47/5.01      inference(cnf_transformation,[],[f34]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_493,plain,
% 35.47/5.01      ( k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(k5_xboole_0(X0,X1),X0) ),
% 35.47/5.01      inference(superposition,[status(thm)],[c_2,c_5]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_10,negated_conjecture,
% 35.47/5.01      ( ~ r1_tarski(k5_xboole_0(k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
% 35.47/5.01      inference(cnf_transformation,[],[f53]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_7,plain,
% 35.47/5.01      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 35.47/5.01      inference(cnf_transformation,[],[f36]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_63,negated_conjecture,
% 35.47/5.01      ( ~ r1_tarski(k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
% 35.47/5.01      inference(theory_normalisation,[status(thm)],[c_10,c_7,c_1]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_146,plain,
% 35.47/5.01      ( r1_tarski(k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) != iProver_top ),
% 35.47/5.01      inference(predicate_to_equality,[status(thm)],[c_63]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_150,plain,
% 35.47/5.01      ( r1_tarski(k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k1_zfmisc_1(k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) != iProver_top ),
% 35.47/5.01      inference(demodulation,[status(thm)],[c_146,c_9]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_262,plain,
% 35.47/5.01      ( r1_tarski(k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) != iProver_top ),
% 35.47/5.01      inference(demodulation,[status(thm)],[c_0,c_150]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_963,plain,
% 35.47/5.01      ( r1_tarski(k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k5_xboole_0(k1_zfmisc_1(k3_xboole_0(k5_xboole_0(sK1,sK0),sK1)),k1_zfmisc_1(k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(k5_xboole_0(sK1,sK0),sK1))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) != iProver_top ),
% 35.47/5.01      inference(demodulation,[status(thm)],[c_493,c_262]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_966,plain,
% 35.47/5.01      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(k5_xboole_0(X0,X1),X0) ),
% 35.47/5.01      inference(superposition,[status(thm)],[c_0,c_493]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_989,plain,
% 35.47/5.01      ( r1_tarski(k5_xboole_0(k1_zfmisc_1(k3_xboole_0(k5_xboole_0(sK0,sK1),sK0)),k5_xboole_0(k1_zfmisc_1(k3_xboole_0(k5_xboole_0(sK1,sK0),sK1)),k1_zfmisc_1(k3_xboole_0(k3_xboole_0(k5_xboole_0(sK0,sK1),sK0),k3_xboole_0(k5_xboole_0(sK1,sK0),sK1))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) != iProver_top ),
% 35.47/5.01      inference(demodulation,[status(thm)],[c_963,c_966]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_1001,plain,
% 35.47/5.01      ( r1_tarski(k5_xboole_0(k1_zfmisc_1(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1))),k5_xboole_0(k1_zfmisc_1(k3_xboole_0(k5_xboole_0(sK1,sK0),sK1)),k1_zfmisc_1(k3_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(k5_xboole_0(sK1,sK0),sK1))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) != iProver_top ),
% 35.47/5.01      inference(superposition,[status(thm)],[c_0,c_989]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_1907,plain,
% 35.47/5.01      ( r1_tarski(k5_xboole_0(k1_zfmisc_1(k3_xboole_0(k5_xboole_0(sK1,sK0),sK1)),k1_zfmisc_1(k3_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(k5_xboole_0(sK1,sK0),sK1)))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) != iProver_top
% 35.47/5.01      | r1_tarski(k1_zfmisc_1(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) != iProver_top ),
% 35.47/5.01      inference(superposition,[status(thm)],[c_148,c_1001]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_3160,plain,
% 35.47/5.01      ( r1_tarski(k1_zfmisc_1(k3_xboole_0(k5_xboole_0(sK1,sK0),sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) != iProver_top
% 35.47/5.01      | r1_tarski(k1_zfmisc_1(k3_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(k5_xboole_0(sK1,sK0),sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) != iProver_top
% 35.47/5.01      | r1_tarski(k1_zfmisc_1(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) != iProver_top ),
% 35.47/5.01      inference(superposition,[status(thm)],[c_148,c_1907]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_11484,plain,
% 35.47/5.01      ( r1_tarski(k1_zfmisc_1(k3_xboole_0(k5_xboole_0(sK1,sK0),sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) != iProver_top
% 35.47/5.01      | r1_tarski(k1_zfmisc_1(k3_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(k5_xboole_0(sK0,sK1),sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) != iProver_top
% 35.47/5.01      | r1_tarski(k1_zfmisc_1(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) != iProver_top ),
% 35.47/5.01      inference(superposition,[status(thm)],[c_1,c_3160]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_63124,plain,
% 35.47/5.01      ( r1_tarski(k1_zfmisc_1(k3_xboole_0(k5_xboole_0(sK1,sK0),sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) != iProver_top
% 35.47/5.01      | r1_tarski(k1_zfmisc_1(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) != iProver_top ),
% 35.47/5.01      inference(superposition,[status(thm)],[c_2497,c_11484]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_65396,plain,
% 35.47/5.01      ( r1_tarski(k1_zfmisc_1(k3_xboole_0(k5_xboole_0(sK1,sK0),sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) != iProver_top ),
% 35.47/5.01      inference(superposition,[status(thm)],[c_505,c_63124]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_93059,plain,
% 35.47/5.01      ( r1_tarski(k1_zfmisc_1(k5_xboole_0(sK1,sK0)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) != iProver_top ),
% 35.47/5.01      inference(superposition,[status(thm)],[c_2497,c_65396]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_70,plain,
% 35.47/5.01      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 35.47/5.01      theory(equality) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_276,plain,
% 35.47/5.01      ( ~ r1_tarski(X0,X1)
% 35.47/5.01      | r1_tarski(X2,k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
% 35.47/5.01      | X2 != X0
% 35.47/5.01      | k1_zfmisc_1(k5_xboole_0(sK0,sK1)) != X1 ),
% 35.47/5.01      inference(instantiation,[status(thm)],[c_70]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_519,plain,
% 35.47/5.01      ( ~ r1_tarski(X0,k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))))
% 35.47/5.01      | r1_tarski(X1,k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
% 35.47/5.01      | X1 != X0
% 35.47/5.01      | k1_zfmisc_1(k5_xboole_0(sK0,sK1)) != k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
% 35.47/5.01      inference(instantiation,[status(thm)],[c_276]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_910,plain,
% 35.47/5.01      ( r1_tarski(X0,k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
% 35.47/5.01      | ~ r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))))
% 35.47/5.01      | X0 != k3_xboole_0(X1,X2)
% 35.47/5.01      | k1_zfmisc_1(k5_xboole_0(sK0,sK1)) != k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
% 35.47/5.01      inference(instantiation,[status(thm)],[c_519]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_2218,plain,
% 35.47/5.01      ( r1_tarski(X0,k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
% 35.47/5.01      | ~ r1_tarski(k3_xboole_0(k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))),X1),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))))
% 35.47/5.01      | X0 != k3_xboole_0(k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))),X1)
% 35.47/5.01      | k1_zfmisc_1(k5_xboole_0(sK0,sK1)) != k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
% 35.47/5.01      inference(instantiation,[status(thm)],[c_910]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_8747,plain,
% 35.47/5.01      ( ~ r1_tarski(k3_xboole_0(k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))))
% 35.47/5.01      | r1_tarski(k1_zfmisc_1(k5_xboole_0(sK1,sK0)),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
% 35.47/5.01      | k1_zfmisc_1(k5_xboole_0(sK1,sK0)) != k3_xboole_0(k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))))
% 35.47/5.01      | k1_zfmisc_1(k5_xboole_0(sK0,sK1)) != k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
% 35.47/5.01      inference(instantiation,[status(thm)],[c_2218]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_8748,plain,
% 35.47/5.01      ( k1_zfmisc_1(k5_xboole_0(sK1,sK0)) != k3_xboole_0(k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))))
% 35.47/5.01      | k1_zfmisc_1(k5_xboole_0(sK0,sK1)) != k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
% 35.47/5.01      | r1_tarski(k3_xboole_0(k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))) != iProver_top
% 35.47/5.01      | r1_tarski(k1_zfmisc_1(k5_xboole_0(sK1,sK0)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) = iProver_top ),
% 35.47/5.01      inference(predicate_to_equality,[status(thm)],[c_8747]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_794,plain,
% 35.47/5.01      ( r1_tarski(k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),X0),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
% 35.47/5.01      inference(instantiation,[status(thm)],[c_6]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_6609,plain,
% 35.47/5.01      ( r1_tarski(k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
% 35.47/5.01      inference(instantiation,[status(thm)],[c_794]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_6610,plain,
% 35.47/5.01      ( r1_tarski(k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) = iProver_top ),
% 35.47/5.01      inference(predicate_to_equality,[status(thm)],[c_6609]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_378,plain,
% 35.47/5.01      ( ~ r1_tarski(X0,X1)
% 35.47/5.01      | r1_tarski(X2,k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))))
% 35.47/5.01      | X2 != X0
% 35.47/5.01      | k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) != X1 ),
% 35.47/5.01      inference(instantiation,[status(thm)],[c_70]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_630,plain,
% 35.47/5.01      ( r1_tarski(X0,k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))))
% 35.47/5.01      | ~ r1_tarski(X1,k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
% 35.47/5.01      | X0 != X1
% 35.47/5.01      | k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) != k1_zfmisc_1(k5_xboole_0(sK0,sK1)) ),
% 35.47/5.01      inference(instantiation,[status(thm)],[c_378]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_1166,plain,
% 35.47/5.01      ( r1_tarski(X0,k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))))
% 35.47/5.01      | ~ r1_tarski(k3_xboole_0(X1,X2),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
% 35.47/5.01      | X0 != k3_xboole_0(X1,X2)
% 35.47/5.01      | k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) != k1_zfmisc_1(k5_xboole_0(sK0,sK1)) ),
% 35.47/5.01      inference(instantiation,[status(thm)],[c_630]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_1854,plain,
% 35.47/5.01      ( r1_tarski(X0,k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))))
% 35.47/5.01      | ~ r1_tarski(k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),X1),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
% 35.47/5.01      | X0 != k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),X1)
% 35.47/5.01      | k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) != k1_zfmisc_1(k5_xboole_0(sK0,sK1)) ),
% 35.47/5.01      inference(instantiation,[status(thm)],[c_1166]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_4419,plain,
% 35.47/5.01      ( r1_tarski(k3_xboole_0(k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))))
% 35.47/5.01      | ~ r1_tarski(k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
% 35.47/5.01      | k3_xboole_0(k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))) != k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
% 35.47/5.01      | k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) != k1_zfmisc_1(k5_xboole_0(sK0,sK1)) ),
% 35.47/5.01      inference(instantiation,[status(thm)],[c_1854]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_4420,plain,
% 35.47/5.01      ( k3_xboole_0(k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))) != k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
% 35.47/5.01      | k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) != k1_zfmisc_1(k5_xboole_0(sK0,sK1))
% 35.47/5.01      | r1_tarski(k3_xboole_0(k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))) = iProver_top
% 35.47/5.01      | r1_tarski(k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) != iProver_top ),
% 35.47/5.01      inference(predicate_to_equality,[status(thm)],[c_4419]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_67,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_1318,plain,
% 35.47/5.01      ( X0 != X1
% 35.47/5.01      | X0 = k3_xboole_0(k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))))
% 35.47/5.01      | k3_xboole_0(k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))) != X1 ),
% 35.47/5.01      inference(instantiation,[status(thm)],[c_67]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_2610,plain,
% 35.47/5.01      ( X0 = k3_xboole_0(k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))))
% 35.47/5.01      | X0 != k1_zfmisc_1(k5_xboole_0(sK0,sK1))
% 35.47/5.01      | k3_xboole_0(k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))) != k1_zfmisc_1(k5_xboole_0(sK0,sK1)) ),
% 35.47/5.01      inference(instantiation,[status(thm)],[c_1318]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_3349,plain,
% 35.47/5.01      ( k3_xboole_0(k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))) != k1_zfmisc_1(k5_xboole_0(sK0,sK1))
% 35.47/5.01      | k1_zfmisc_1(k5_xboole_0(sK1,sK0)) = k3_xboole_0(k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))))
% 35.47/5.01      | k1_zfmisc_1(k5_xboole_0(sK1,sK0)) != k1_zfmisc_1(k5_xboole_0(sK0,sK1)) ),
% 35.47/5.01      inference(instantiation,[status(thm)],[c_2610]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_836,plain,
% 35.47/5.01      ( k5_xboole_0(sK1,sK0) = k5_xboole_0(sK0,sK1) ),
% 35.47/5.01      inference(instantiation,[status(thm)],[c_1]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_284,plain,
% 35.47/5.01      ( X0 != X1
% 35.47/5.01      | X0 = k1_zfmisc_1(k5_xboole_0(sK0,sK1))
% 35.47/5.01      | k1_zfmisc_1(k5_xboole_0(sK0,sK1)) != X1 ),
% 35.47/5.01      inference(instantiation,[status(thm)],[c_67]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_520,plain,
% 35.47/5.01      ( X0 != k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
% 35.47/5.01      | X0 = k1_zfmisc_1(k5_xboole_0(sK0,sK1))
% 35.47/5.01      | k1_zfmisc_1(k5_xboole_0(sK0,sK1)) != k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
% 35.47/5.01      inference(instantiation,[status(thm)],[c_284]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_802,plain,
% 35.47/5.01      ( k3_xboole_0(k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))) != k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
% 35.47/5.01      | k3_xboole_0(k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))) = k1_zfmisc_1(k5_xboole_0(sK0,sK1))
% 35.47/5.01      | k1_zfmisc_1(k5_xboole_0(sK0,sK1)) != k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
% 35.47/5.01      inference(instantiation,[status(thm)],[c_520]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_651,plain,
% 35.47/5.01      ( k3_xboole_0(k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))) = k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
% 35.47/5.01      inference(instantiation,[status(thm)],[c_2]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_72,plain,
% 35.47/5.01      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 35.47/5.01      theory(equality) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_347,plain,
% 35.47/5.01      ( X0 != k5_xboole_0(sK0,sK1)
% 35.47/5.01      | k1_zfmisc_1(X0) = k1_zfmisc_1(k5_xboole_0(sK0,sK1)) ),
% 35.47/5.01      inference(instantiation,[status(thm)],[c_72]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_546,plain,
% 35.47/5.01      ( k5_xboole_0(sK1,sK0) != k5_xboole_0(sK0,sK1)
% 35.47/5.01      | k1_zfmisc_1(k5_xboole_0(sK1,sK0)) = k1_zfmisc_1(k5_xboole_0(sK0,sK1)) ),
% 35.47/5.01      inference(instantiation,[status(thm)],[c_347]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_361,plain,
% 35.47/5.01      ( k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) = k1_zfmisc_1(k5_xboole_0(sK0,sK1)) ),
% 35.47/5.01      inference(instantiation,[status(thm)],[c_2]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_179,plain,
% 35.47/5.01      ( X0 != X1
% 35.47/5.01      | k1_zfmisc_1(k5_xboole_0(sK0,sK1)) != X1
% 35.47/5.01      | k1_zfmisc_1(k5_xboole_0(sK0,sK1)) = X0 ),
% 35.47/5.01      inference(instantiation,[status(thm)],[c_67]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_208,plain,
% 35.47/5.01      ( X0 != k1_zfmisc_1(k5_xboole_0(sK0,sK1))
% 35.47/5.01      | k1_zfmisc_1(k5_xboole_0(sK0,sK1)) = X0
% 35.47/5.01      | k1_zfmisc_1(k5_xboole_0(sK0,sK1)) != k1_zfmisc_1(k5_xboole_0(sK0,sK1)) ),
% 35.47/5.01      inference(instantiation,[status(thm)],[c_179]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_282,plain,
% 35.47/5.01      ( k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) != k1_zfmisc_1(k5_xboole_0(sK0,sK1))
% 35.47/5.01      | k1_zfmisc_1(k5_xboole_0(sK0,sK1)) = k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,sK1)),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
% 35.47/5.01      | k1_zfmisc_1(k5_xboole_0(sK0,sK1)) != k1_zfmisc_1(k5_xboole_0(sK0,sK1)) ),
% 35.47/5.01      inference(instantiation,[status(thm)],[c_208]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_66,plain,( X0 = X0 ),theory(equality) ).
% 35.47/5.01  
% 35.47/5.01  cnf(c_217,plain,
% 35.47/5.01      ( k1_zfmisc_1(k5_xboole_0(sK0,sK1)) = k1_zfmisc_1(k5_xboole_0(sK0,sK1)) ),
% 35.47/5.01      inference(instantiation,[status(thm)],[c_66]) ).
% 35.47/5.01  
% 35.47/5.01  cnf(contradiction,plain,
% 35.47/5.01      ( $false ),
% 35.47/5.01      inference(minisat,
% 35.47/5.01                [status(thm)],
% 35.47/5.01                [c_93059,c_8748,c_6610,c_4420,c_3349,c_836,c_802,c_651,
% 35.47/5.01                 c_546,c_361,c_282,c_217]) ).
% 35.47/5.01  
% 35.47/5.01  
% 35.47/5.01  % SZS output end CNFRefutation for theBenchmark.p
% 35.47/5.01  
% 35.47/5.01  ------                               Statistics
% 35.47/5.01  
% 35.47/5.01  ------ General
% 35.47/5.01  
% 35.47/5.01  abstr_ref_over_cycles:                  0
% 35.47/5.01  abstr_ref_under_cycles:                 0
% 35.47/5.01  gc_basic_clause_elim:                   0
% 35.47/5.01  forced_gc_time:                         0
% 35.47/5.01  parsing_time:                           0.012
% 35.47/5.01  unif_index_cands_time:                  0.
% 35.47/5.01  unif_index_add_time:                    0.
% 35.47/5.01  orderings_time:                         0.
% 35.47/5.01  out_proof_time:                         0.013
% 35.47/5.01  total_time:                             4.469
% 35.47/5.01  num_of_symbols:                         39
% 35.47/5.01  num_of_terms:                           159936
% 35.47/5.01  
% 35.47/5.01  ------ Preprocessing
% 35.47/5.01  
% 35.47/5.01  num_of_splits:                          0
% 35.47/5.01  num_of_split_atoms:                     0
% 35.47/5.01  num_of_reused_defs:                     0
% 35.47/5.01  num_eq_ax_congr_red:                    16
% 35.47/5.01  num_of_sem_filtered_clauses:            1
% 35.47/5.01  num_of_subtypes:                        0
% 35.47/5.01  monotx_restored_types:                  0
% 35.47/5.01  sat_num_of_epr_types:                   0
% 35.47/5.01  sat_num_of_non_cyclic_types:            0
% 35.47/5.01  sat_guarded_non_collapsed_types:        0
% 35.47/5.01  num_pure_diseq_elim:                    0
% 35.47/5.01  simp_replaced_by:                       0
% 35.47/5.01  res_preprocessed:                       48
% 35.47/5.01  prep_upred:                             0
% 35.47/5.01  prep_unflattend:                        0
% 35.47/5.01  smt_new_axioms:                         0
% 35.47/5.01  pred_elim_cands:                        1
% 35.47/5.01  pred_elim:                              0
% 35.47/5.01  pred_elim_cl:                           0
% 35.47/5.01  pred_elim_cycles:                       1
% 35.47/5.01  merged_defs:                            0
% 35.47/5.01  merged_defs_ncl:                        0
% 35.47/5.01  bin_hyper_res:                          0
% 35.47/5.01  prep_cycles:                            3
% 35.47/5.01  pred_elim_time:                         0.
% 35.47/5.01  splitting_time:                         0.
% 35.47/5.01  sem_filter_time:                        0.
% 35.47/5.01  monotx_time:                            0.
% 35.47/5.01  subtype_inf_time:                       0.
% 35.47/5.01  
% 35.47/5.01  ------ Problem properties
% 35.47/5.01  
% 35.47/5.01  clauses:                                11
% 35.47/5.01  conjectures:                            1
% 35.47/5.01  epr:                                    0
% 35.47/5.01  horn:                                   11
% 35.47/5.01  ground:                                 1
% 35.47/5.01  unary:                                  9
% 35.47/5.01  binary:                                 1
% 35.47/5.01  lits:                                   14
% 35.47/5.01  lits_eq:                                7
% 35.47/5.01  fd_pure:                                0
% 35.47/5.01  fd_pseudo:                              0
% 35.47/5.01  fd_cond:                                0
% 35.47/5.01  fd_pseudo_cond:                         0
% 35.47/5.01  ac_symbols:                             1
% 35.47/5.01  
% 35.47/5.01  ------ Propositional Solver
% 35.47/5.01  
% 35.47/5.01  prop_solver_calls:                      32
% 35.47/5.01  prop_fast_solver_calls:                 806
% 35.47/5.01  smt_solver_calls:                       0
% 35.47/5.01  smt_fast_solver_calls:                  0
% 35.47/5.01  prop_num_of_clauses:                    28312
% 35.47/5.01  prop_preprocess_simplified:             29741
% 35.47/5.01  prop_fo_subsumed:                       55
% 35.47/5.01  prop_solver_time:                       0.
% 35.47/5.01  smt_solver_time:                        0.
% 35.47/5.01  smt_fast_solver_time:                   0.
% 35.47/5.01  prop_fast_solver_time:                  0.
% 35.47/5.01  prop_unsat_core_time:                   0.003
% 35.47/5.01  
% 35.47/5.01  ------ QBF
% 35.47/5.01  
% 35.47/5.01  qbf_q_res:                              0
% 35.47/5.01  qbf_num_tautologies:                    0
% 35.47/5.01  qbf_prep_cycles:                        0
% 35.47/5.01  
% 35.47/5.01  ------ BMC1
% 35.47/5.01  
% 35.47/5.01  bmc1_current_bound:                     -1
% 35.47/5.01  bmc1_last_solved_bound:                 -1
% 35.47/5.01  bmc1_unsat_core_size:                   -1
% 35.47/5.01  bmc1_unsat_core_parents_size:           -1
% 35.47/5.01  bmc1_merge_next_fun:                    0
% 35.47/5.01  bmc1_unsat_core_clauses_time:           0.
% 35.47/5.01  
% 35.47/5.01  ------ Instantiation
% 35.47/5.01  
% 35.47/5.01  inst_num_of_clauses:                    5875
% 35.47/5.01  inst_num_in_passive:                    1726
% 35.47/5.01  inst_num_in_active:                     1428
% 35.47/5.01  inst_num_in_unprocessed:                2724
% 35.47/5.01  inst_num_of_loops:                      1760
% 35.47/5.01  inst_num_of_learning_restarts:          0
% 35.47/5.01  inst_num_moves_active_passive:          325
% 35.47/5.01  inst_lit_activity:                      0
% 35.47/5.01  inst_lit_activity_moves:                1
% 35.47/5.01  inst_num_tautologies:                   0
% 35.47/5.01  inst_num_prop_implied:                  0
% 35.47/5.01  inst_num_existing_simplified:           0
% 35.47/5.01  inst_num_eq_res_simplified:             0
% 35.47/5.01  inst_num_child_elim:                    0
% 35.47/5.01  inst_num_of_dismatching_blockings:      4639
% 35.47/5.01  inst_num_of_non_proper_insts:           4652
% 35.47/5.01  inst_num_of_duplicates:                 0
% 35.47/5.01  inst_inst_num_from_inst_to_res:         0
% 35.47/5.01  inst_dismatching_checking_time:         0.
% 35.47/5.01  
% 35.47/5.01  ------ Resolution
% 35.47/5.01  
% 35.47/5.01  res_num_of_clauses:                     0
% 35.47/5.01  res_num_in_passive:                     0
% 35.47/5.01  res_num_in_active:                      0
% 35.47/5.01  res_num_of_loops:                       51
% 35.47/5.01  res_forward_subset_subsumed:            1786
% 35.47/5.01  res_backward_subset_subsumed:           8
% 35.47/5.01  res_forward_subsumed:                   0
% 35.47/5.01  res_backward_subsumed:                  0
% 35.47/5.01  res_forward_subsumption_resolution:     0
% 35.47/5.01  res_backward_subsumption_resolution:    0
% 35.47/5.01  res_clause_to_clause_subsumption:       352283
% 35.47/5.01  res_orphan_elimination:                 0
% 35.47/5.01  res_tautology_del:                      294
% 35.47/5.01  res_num_eq_res_simplified:              0
% 35.47/5.01  res_num_sel_changes:                    0
% 35.47/5.01  res_moves_from_active_to_pass:          0
% 35.47/5.01  
% 35.47/5.01  ------ Superposition
% 35.47/5.01  
% 35.47/5.01  sup_time_total:                         0.
% 35.47/5.01  sup_time_generating:                    0.
% 35.47/5.01  sup_time_sim_full:                      0.
% 35.47/5.01  sup_time_sim_immed:                     0.
% 35.47/5.01  
% 35.47/5.01  sup_num_of_clauses:                     11036
% 35.47/5.01  sup_num_in_active:                      258
% 35.47/5.01  sup_num_in_passive:                     10778
% 35.47/5.01  sup_num_of_loops:                       350
% 35.47/5.01  sup_fw_superposition:                   22338
% 35.47/5.01  sup_bw_superposition:                   13635
% 35.47/5.01  sup_immediate_simplified:               10668
% 35.47/5.01  sup_given_eliminated:                   1
% 35.47/5.01  comparisons_done:                       0
% 35.47/5.01  comparisons_avoided:                    0
% 35.47/5.01  
% 35.47/5.01  ------ Simplifications
% 35.47/5.01  
% 35.47/5.01  
% 35.47/5.01  sim_fw_subset_subsumed:                 11
% 35.47/5.01  sim_bw_subset_subsumed:                 32
% 35.47/5.01  sim_fw_subsumed:                        478
% 35.47/5.01  sim_bw_subsumed:                        75
% 35.47/5.01  sim_fw_subsumption_res:                 0
% 35.47/5.01  sim_bw_subsumption_res:                 0
% 35.47/5.01  sim_tautology_del:                      7
% 35.47/5.01  sim_eq_tautology_del:                   618
% 35.47/5.01  sim_eq_res_simp:                        0
% 35.47/5.01  sim_fw_demodulated:                     11701
% 35.47/5.01  sim_bw_demodulated:                     390
% 35.47/5.01  sim_light_normalised:                   3133
% 35.47/5.01  sim_joinable_taut:                      282
% 35.47/5.01  sim_joinable_simp:                      0
% 35.47/5.01  sim_ac_normalised:                      0
% 35.47/5.01  sim_smt_subsumption:                    0
% 35.47/5.01  
%------------------------------------------------------------------------------
