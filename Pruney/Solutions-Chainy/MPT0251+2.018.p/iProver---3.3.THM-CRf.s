%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:33:04 EST 2020

% Result     : Theorem 11.81s
% Output     : CNFRefutation 11.81s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 535 expanded)
%              Number of clauses        :   35 (  71 expanded)
%              Number of leaves         :   17 ( 167 expanded)
%              Depth                    :   14
%              Number of atoms          :  137 ( 612 expanded)
%              Number of equality atoms :   83 ( 528 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f16])).

fof(f19,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f24,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),X1) != X1
        & r2_hidden(X0,X1) )
   => ( k2_xboole_0(k1_tarski(sK0),sK1) != sK1
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( k2_xboole_0(k1_tarski(sK0),sK1) != sK1
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f24])).

fof(f45,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f22])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f47,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f39,f40])).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f38,f47])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f44,f48])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f49,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f41,f48])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f52,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f33,f49,f49,f30])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f51,plain,(
    ! [X0] : k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f31,f49])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f55,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f36,f48,f48])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f53,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1)) ),
    inference(definition_unfolding,[],[f34,f30,f30,f49])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f20])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f61,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f27])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f54,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f35,f49])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f46,plain,(
    k2_xboole_0(k1_tarski(sK0),sK1) != sK1 ),
    inference(cnf_transformation,[],[f25])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f50,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f37,f48])).

fof(f59,plain,(
    k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) != sK1 ),
    inference(definition_unfolding,[],[f46,f49,f50])).

cnf(c_14,negated_conjecture,
    ( r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_322,plain,
    ( r2_hidden(sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | r1_tarski(k3_enumset1(X2,X2,X2,X2,X0),X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_325,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r1_tarski(k3_enumset1(X2,X2,X2,X2,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_327,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2152,plain,
    ( k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),X2) = k3_enumset1(X0,X0,X0,X0,X1)
    | r2_hidden(X1,X2) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_325,c_327])).

cnf(c_35776,plain,
    ( k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,X0),sK1) = k3_enumset1(sK0,sK0,sK0,sK0,X0)
    | r2_hidden(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_322,c_2152])).

cnf(c_37645,plain,
    ( k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(superposition,[status(thm)],[c_322,c_35776])).

cnf(c_6,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_37774,plain,
    ( k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    inference(superposition,[status(thm)],[c_37645,c_6])).

cnf(c_4,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_9,plain,
    ( k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_644,plain,
    ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_9,c_4])).

cnf(c_7,plain,
    ( k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1)) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_847,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_644,c_7])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_328,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_557,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_328,c_327])).

cnf(c_852,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k5_xboole_0(X0,X0) ),
    inference(light_normalisation,[status(thm)],[c_847,c_557])).

cnf(c_8,plain,
    ( r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_326,plain,
    ( r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_849,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_644,c_326])).

cnf(c_929,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_849,c_327])).

cnf(c_1090,plain,
    ( k5_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_852,c_929])).

cnf(c_850,plain,
    ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_644,c_6])).

cnf(c_851,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(demodulation,[status(thm)],[c_850,c_644])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_935,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_929,c_0])).

cnf(c_1014,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_851,c_851,c_935])).

cnf(c_1091,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1090,c_1014])).

cnf(c_37776,plain,
    ( k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = sK1 ),
    inference(demodulation,[status(thm)],[c_37774,c_4,c_1091])).

cnf(c_13,negated_conjecture,
    ( k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) != sK1 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_640,plain,
    ( k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) != sK1 ),
    inference(demodulation,[status(thm)],[c_9,c_13])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_37776,c_640])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:39:04 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 11.81/1.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.81/1.98  
% 11.81/1.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.81/1.98  
% 11.81/1.98  ------  iProver source info
% 11.81/1.98  
% 11.81/1.98  git: date: 2020-06-30 10:37:57 +0100
% 11.81/1.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.81/1.98  git: non_committed_changes: false
% 11.81/1.98  git: last_make_outside_of_git: false
% 11.81/1.98  
% 11.81/1.98  ------ 
% 11.81/1.98  
% 11.81/1.98  ------ Input Options
% 11.81/1.98  
% 11.81/1.98  --out_options                           all
% 11.81/1.98  --tptp_safe_out                         true
% 11.81/1.98  --problem_path                          ""
% 11.81/1.98  --include_path                          ""
% 11.81/1.98  --clausifier                            res/vclausify_rel
% 11.81/1.98  --clausifier_options                    ""
% 11.81/1.98  --stdin                                 false
% 11.81/1.98  --stats_out                             all
% 11.81/1.98  
% 11.81/1.98  ------ General Options
% 11.81/1.98  
% 11.81/1.98  --fof                                   false
% 11.81/1.98  --time_out_real                         305.
% 11.81/1.98  --time_out_virtual                      -1.
% 11.81/1.98  --symbol_type_check                     false
% 11.81/1.98  --clausify_out                          false
% 11.81/1.98  --sig_cnt_out                           false
% 11.81/1.98  --trig_cnt_out                          false
% 11.81/1.98  --trig_cnt_out_tolerance                1.
% 11.81/1.98  --trig_cnt_out_sk_spl                   false
% 11.81/1.98  --abstr_cl_out                          false
% 11.81/1.98  
% 11.81/1.98  ------ Global Options
% 11.81/1.98  
% 11.81/1.98  --schedule                              default
% 11.81/1.98  --add_important_lit                     false
% 11.81/1.98  --prop_solver_per_cl                    1000
% 11.81/1.98  --min_unsat_core                        false
% 11.81/1.98  --soft_assumptions                      false
% 11.81/1.98  --soft_lemma_size                       3
% 11.81/1.98  --prop_impl_unit_size                   0
% 11.81/1.98  --prop_impl_unit                        []
% 11.81/1.98  --share_sel_clauses                     true
% 11.81/1.98  --reset_solvers                         false
% 11.81/1.98  --bc_imp_inh                            [conj_cone]
% 11.81/1.98  --conj_cone_tolerance                   3.
% 11.81/1.98  --extra_neg_conj                        none
% 11.81/1.98  --large_theory_mode                     true
% 11.81/1.98  --prolific_symb_bound                   200
% 11.81/1.98  --lt_threshold                          2000
% 11.81/1.98  --clause_weak_htbl                      true
% 11.81/1.98  --gc_record_bc_elim                     false
% 11.81/1.98  
% 11.81/1.98  ------ Preprocessing Options
% 11.81/1.98  
% 11.81/1.98  --preprocessing_flag                    true
% 11.81/1.98  --time_out_prep_mult                    0.1
% 11.81/1.98  --splitting_mode                        input
% 11.81/1.98  --splitting_grd                         true
% 11.81/1.98  --splitting_cvd                         false
% 11.81/1.98  --splitting_cvd_svl                     false
% 11.81/1.98  --splitting_nvd                         32
% 11.81/1.98  --sub_typing                            true
% 11.81/1.98  --prep_gs_sim                           true
% 11.81/1.98  --prep_unflatten                        true
% 11.81/1.98  --prep_res_sim                          true
% 11.81/1.98  --prep_upred                            true
% 11.81/1.98  --prep_sem_filter                       exhaustive
% 11.81/1.98  --prep_sem_filter_out                   false
% 11.81/1.98  --pred_elim                             true
% 11.81/1.98  --res_sim_input                         true
% 11.81/1.98  --eq_ax_congr_red                       true
% 11.81/1.98  --pure_diseq_elim                       true
% 11.81/1.98  --brand_transform                       false
% 11.81/1.98  --non_eq_to_eq                          false
% 11.81/1.98  --prep_def_merge                        true
% 11.81/1.98  --prep_def_merge_prop_impl              false
% 11.81/1.98  --prep_def_merge_mbd                    true
% 11.81/1.98  --prep_def_merge_tr_red                 false
% 11.81/1.98  --prep_def_merge_tr_cl                  false
% 11.81/1.98  --smt_preprocessing                     true
% 11.81/1.98  --smt_ac_axioms                         fast
% 11.81/1.98  --preprocessed_out                      false
% 11.81/1.98  --preprocessed_stats                    false
% 11.81/1.98  
% 11.81/1.98  ------ Abstraction refinement Options
% 11.81/1.98  
% 11.81/1.98  --abstr_ref                             []
% 11.81/1.98  --abstr_ref_prep                        false
% 11.81/1.98  --abstr_ref_until_sat                   false
% 11.81/1.98  --abstr_ref_sig_restrict                funpre
% 11.81/1.98  --abstr_ref_af_restrict_to_split_sk     false
% 11.81/1.98  --abstr_ref_under                       []
% 11.81/1.98  
% 11.81/1.98  ------ SAT Options
% 11.81/1.98  
% 11.81/1.98  --sat_mode                              false
% 11.81/1.98  --sat_fm_restart_options                ""
% 11.81/1.98  --sat_gr_def                            false
% 11.81/1.98  --sat_epr_types                         true
% 11.81/1.98  --sat_non_cyclic_types                  false
% 11.81/1.98  --sat_finite_models                     false
% 11.81/1.98  --sat_fm_lemmas                         false
% 11.81/1.98  --sat_fm_prep                           false
% 11.81/1.98  --sat_fm_uc_incr                        true
% 11.81/1.98  --sat_out_model                         small
% 11.81/1.98  --sat_out_clauses                       false
% 11.81/1.98  
% 11.81/1.98  ------ QBF Options
% 11.81/1.98  
% 11.81/1.98  --qbf_mode                              false
% 11.81/1.98  --qbf_elim_univ                         false
% 11.81/1.98  --qbf_dom_inst                          none
% 11.81/1.98  --qbf_dom_pre_inst                      false
% 11.81/1.98  --qbf_sk_in                             false
% 11.81/1.98  --qbf_pred_elim                         true
% 11.81/1.98  --qbf_split                             512
% 11.81/1.98  
% 11.81/1.98  ------ BMC1 Options
% 11.81/1.98  
% 11.81/1.98  --bmc1_incremental                      false
% 11.81/1.98  --bmc1_axioms                           reachable_all
% 11.81/1.98  --bmc1_min_bound                        0
% 11.81/1.98  --bmc1_max_bound                        -1
% 11.81/1.98  --bmc1_max_bound_default                -1
% 11.81/1.98  --bmc1_symbol_reachability              true
% 11.81/1.98  --bmc1_property_lemmas                  false
% 11.81/1.98  --bmc1_k_induction                      false
% 11.81/1.98  --bmc1_non_equiv_states                 false
% 11.81/1.98  --bmc1_deadlock                         false
% 11.81/1.98  --bmc1_ucm                              false
% 11.81/1.98  --bmc1_add_unsat_core                   none
% 11.81/1.98  --bmc1_unsat_core_children              false
% 11.81/1.98  --bmc1_unsat_core_extrapolate_axioms    false
% 11.81/1.98  --bmc1_out_stat                         full
% 11.81/1.98  --bmc1_ground_init                      false
% 11.81/1.98  --bmc1_pre_inst_next_state              false
% 11.81/1.98  --bmc1_pre_inst_state                   false
% 11.81/1.98  --bmc1_pre_inst_reach_state             false
% 11.81/1.98  --bmc1_out_unsat_core                   false
% 11.81/1.98  --bmc1_aig_witness_out                  false
% 11.81/1.98  --bmc1_verbose                          false
% 11.81/1.98  --bmc1_dump_clauses_tptp                false
% 11.81/1.98  --bmc1_dump_unsat_core_tptp             false
% 11.81/1.98  --bmc1_dump_file                        -
% 11.81/1.98  --bmc1_ucm_expand_uc_limit              128
% 11.81/1.98  --bmc1_ucm_n_expand_iterations          6
% 11.81/1.98  --bmc1_ucm_extend_mode                  1
% 11.81/1.98  --bmc1_ucm_init_mode                    2
% 11.81/1.98  --bmc1_ucm_cone_mode                    none
% 11.81/1.98  --bmc1_ucm_reduced_relation_type        0
% 11.81/1.98  --bmc1_ucm_relax_model                  4
% 11.81/1.98  --bmc1_ucm_full_tr_after_sat            true
% 11.81/1.98  --bmc1_ucm_expand_neg_assumptions       false
% 11.81/1.98  --bmc1_ucm_layered_model                none
% 11.81/1.98  --bmc1_ucm_max_lemma_size               10
% 11.81/1.98  
% 11.81/1.98  ------ AIG Options
% 11.81/1.98  
% 11.81/1.98  --aig_mode                              false
% 11.81/1.98  
% 11.81/1.98  ------ Instantiation Options
% 11.81/1.98  
% 11.81/1.98  --instantiation_flag                    true
% 11.81/1.98  --inst_sos_flag                         true
% 11.81/1.98  --inst_sos_phase                        true
% 11.81/1.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.81/1.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.81/1.98  --inst_lit_sel_side                     num_symb
% 11.81/1.98  --inst_solver_per_active                1400
% 11.81/1.98  --inst_solver_calls_frac                1.
% 11.81/1.98  --inst_passive_queue_type               priority_queues
% 11.81/1.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.81/1.98  --inst_passive_queues_freq              [25;2]
% 11.81/1.98  --inst_dismatching                      true
% 11.81/1.98  --inst_eager_unprocessed_to_passive     true
% 11.81/1.98  --inst_prop_sim_given                   true
% 11.81/1.98  --inst_prop_sim_new                     false
% 11.81/1.98  --inst_subs_new                         false
% 11.81/1.98  --inst_eq_res_simp                      false
% 11.81/1.98  --inst_subs_given                       false
% 11.81/1.98  --inst_orphan_elimination               true
% 11.81/1.98  --inst_learning_loop_flag               true
% 11.81/1.98  --inst_learning_start                   3000
% 11.81/1.98  --inst_learning_factor                  2
% 11.81/1.98  --inst_start_prop_sim_after_learn       3
% 11.81/1.98  --inst_sel_renew                        solver
% 11.81/1.98  --inst_lit_activity_flag                true
% 11.81/1.98  --inst_restr_to_given                   false
% 11.81/1.98  --inst_activity_threshold               500
% 11.81/1.98  --inst_out_proof                        true
% 11.81/1.98  
% 11.81/1.98  ------ Resolution Options
% 11.81/1.98  
% 11.81/1.98  --resolution_flag                       true
% 11.81/1.98  --res_lit_sel                           adaptive
% 11.81/1.98  --res_lit_sel_side                      none
% 11.81/1.98  --res_ordering                          kbo
% 11.81/1.98  --res_to_prop_solver                    active
% 11.81/1.98  --res_prop_simpl_new                    false
% 11.81/1.98  --res_prop_simpl_given                  true
% 11.81/1.98  --res_passive_queue_type                priority_queues
% 11.81/1.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.81/1.98  --res_passive_queues_freq               [15;5]
% 11.81/1.98  --res_forward_subs                      full
% 11.81/1.98  --res_backward_subs                     full
% 11.81/1.98  --res_forward_subs_resolution           true
% 11.81/1.98  --res_backward_subs_resolution          true
% 11.81/1.98  --res_orphan_elimination                true
% 11.81/1.98  --res_time_limit                        2.
% 11.81/1.98  --res_out_proof                         true
% 11.81/1.98  
% 11.81/1.98  ------ Superposition Options
% 11.81/1.98  
% 11.81/1.98  --superposition_flag                    true
% 11.81/1.98  --sup_passive_queue_type                priority_queues
% 11.81/1.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.81/1.98  --sup_passive_queues_freq               [8;1;4]
% 11.81/1.98  --demod_completeness_check              fast
% 11.81/1.98  --demod_use_ground                      true
% 11.81/1.98  --sup_to_prop_solver                    passive
% 11.81/1.98  --sup_prop_simpl_new                    true
% 11.81/1.98  --sup_prop_simpl_given                  true
% 11.81/1.98  --sup_fun_splitting                     true
% 11.81/1.98  --sup_smt_interval                      50000
% 11.81/1.98  
% 11.81/1.98  ------ Superposition Simplification Setup
% 11.81/1.98  
% 11.81/1.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.81/1.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.81/1.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.81/1.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.81/1.98  --sup_full_triv                         [TrivRules;PropSubs]
% 11.81/1.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.81/1.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.81/1.98  --sup_immed_triv                        [TrivRules]
% 11.81/1.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.81/1.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.81/1.98  --sup_immed_bw_main                     []
% 11.81/1.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.81/1.98  --sup_input_triv                        [Unflattening;TrivRules]
% 11.81/1.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.81/1.98  --sup_input_bw                          []
% 11.81/1.98  
% 11.81/1.98  ------ Combination Options
% 11.81/1.98  
% 11.81/1.98  --comb_res_mult                         3
% 11.81/1.98  --comb_sup_mult                         2
% 11.81/1.98  --comb_inst_mult                        10
% 11.81/1.98  
% 11.81/1.98  ------ Debug Options
% 11.81/1.98  
% 11.81/1.98  --dbg_backtrace                         false
% 11.81/1.98  --dbg_dump_prop_clauses                 false
% 11.81/1.98  --dbg_dump_prop_clauses_file            -
% 11.81/1.98  --dbg_out_stat                          false
% 11.81/1.98  ------ Parsing...
% 11.81/1.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.81/1.98  
% 11.81/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 11.81/1.98  
% 11.81/1.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.81/1.98  
% 11.81/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.81/1.98  ------ Proving...
% 11.81/1.98  ------ Problem Properties 
% 11.81/1.98  
% 11.81/1.98  
% 11.81/1.98  clauses                                 14
% 11.81/1.98  conjectures                             2
% 11.81/1.98  EPR                                     3
% 11.81/1.98  Horn                                    14
% 11.81/1.98  unary                                   9
% 11.81/1.98  binary                                  3
% 11.81/1.98  lits                                    21
% 11.81/1.98  lits eq                                 8
% 11.81/1.98  fd_pure                                 0
% 11.81/1.98  fd_pseudo                               0
% 11.81/1.98  fd_cond                                 0
% 11.81/1.98  fd_pseudo_cond                          1
% 11.81/1.98  AC symbols                              0
% 11.81/1.98  
% 11.81/1.98  ------ Schedule dynamic 5 is on 
% 11.81/1.98  
% 11.81/1.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.81/1.98  
% 11.81/1.98  
% 11.81/1.98  ------ 
% 11.81/1.98  Current options:
% 11.81/1.98  ------ 
% 11.81/1.98  
% 11.81/1.98  ------ Input Options
% 11.81/1.98  
% 11.81/1.98  --out_options                           all
% 11.81/1.98  --tptp_safe_out                         true
% 11.81/1.98  --problem_path                          ""
% 11.81/1.98  --include_path                          ""
% 11.81/1.98  --clausifier                            res/vclausify_rel
% 11.81/1.98  --clausifier_options                    ""
% 11.81/1.98  --stdin                                 false
% 11.81/1.98  --stats_out                             all
% 11.81/1.98  
% 11.81/1.98  ------ General Options
% 11.81/1.98  
% 11.81/1.98  --fof                                   false
% 11.81/1.98  --time_out_real                         305.
% 11.81/1.98  --time_out_virtual                      -1.
% 11.81/1.98  --symbol_type_check                     false
% 11.81/1.98  --clausify_out                          false
% 11.81/1.98  --sig_cnt_out                           false
% 11.81/1.98  --trig_cnt_out                          false
% 11.81/1.98  --trig_cnt_out_tolerance                1.
% 11.81/1.98  --trig_cnt_out_sk_spl                   false
% 11.81/1.98  --abstr_cl_out                          false
% 11.81/1.98  
% 11.81/1.98  ------ Global Options
% 11.81/1.98  
% 11.81/1.98  --schedule                              default
% 11.81/1.98  --add_important_lit                     false
% 11.81/1.98  --prop_solver_per_cl                    1000
% 11.81/1.98  --min_unsat_core                        false
% 11.81/1.98  --soft_assumptions                      false
% 11.81/1.98  --soft_lemma_size                       3
% 11.81/1.98  --prop_impl_unit_size                   0
% 11.81/1.98  --prop_impl_unit                        []
% 11.81/1.98  --share_sel_clauses                     true
% 11.81/1.98  --reset_solvers                         false
% 11.81/1.98  --bc_imp_inh                            [conj_cone]
% 11.81/1.98  --conj_cone_tolerance                   3.
% 11.81/1.98  --extra_neg_conj                        none
% 11.81/1.98  --large_theory_mode                     true
% 11.81/1.98  --prolific_symb_bound                   200
% 11.81/1.98  --lt_threshold                          2000
% 11.81/1.98  --clause_weak_htbl                      true
% 11.81/1.98  --gc_record_bc_elim                     false
% 11.81/1.98  
% 11.81/1.98  ------ Preprocessing Options
% 11.81/1.98  
% 11.81/1.98  --preprocessing_flag                    true
% 11.81/1.98  --time_out_prep_mult                    0.1
% 11.81/1.98  --splitting_mode                        input
% 11.81/1.98  --splitting_grd                         true
% 11.81/1.98  --splitting_cvd                         false
% 11.81/1.98  --splitting_cvd_svl                     false
% 11.81/1.98  --splitting_nvd                         32
% 11.81/1.98  --sub_typing                            true
% 11.81/1.98  --prep_gs_sim                           true
% 11.81/1.98  --prep_unflatten                        true
% 11.81/1.98  --prep_res_sim                          true
% 11.81/1.98  --prep_upred                            true
% 11.81/1.98  --prep_sem_filter                       exhaustive
% 11.81/1.98  --prep_sem_filter_out                   false
% 11.81/1.98  --pred_elim                             true
% 11.81/1.98  --res_sim_input                         true
% 11.81/1.98  --eq_ax_congr_red                       true
% 11.81/1.98  --pure_diseq_elim                       true
% 11.81/1.98  --brand_transform                       false
% 11.81/1.98  --non_eq_to_eq                          false
% 11.81/1.98  --prep_def_merge                        true
% 11.81/1.98  --prep_def_merge_prop_impl              false
% 11.81/1.98  --prep_def_merge_mbd                    true
% 11.81/1.98  --prep_def_merge_tr_red                 false
% 11.81/1.98  --prep_def_merge_tr_cl                  false
% 11.81/1.98  --smt_preprocessing                     true
% 11.81/1.98  --smt_ac_axioms                         fast
% 11.81/1.98  --preprocessed_out                      false
% 11.81/1.98  --preprocessed_stats                    false
% 11.81/1.98  
% 11.81/1.98  ------ Abstraction refinement Options
% 11.81/1.98  
% 11.81/1.98  --abstr_ref                             []
% 11.81/1.98  --abstr_ref_prep                        false
% 11.81/1.98  --abstr_ref_until_sat                   false
% 11.81/1.98  --abstr_ref_sig_restrict                funpre
% 11.81/1.98  --abstr_ref_af_restrict_to_split_sk     false
% 11.81/1.98  --abstr_ref_under                       []
% 11.81/1.98  
% 11.81/1.98  ------ SAT Options
% 11.81/1.98  
% 11.81/1.98  --sat_mode                              false
% 11.81/1.98  --sat_fm_restart_options                ""
% 11.81/1.98  --sat_gr_def                            false
% 11.81/1.98  --sat_epr_types                         true
% 11.81/1.98  --sat_non_cyclic_types                  false
% 11.81/1.98  --sat_finite_models                     false
% 11.81/1.98  --sat_fm_lemmas                         false
% 11.81/1.98  --sat_fm_prep                           false
% 11.81/1.98  --sat_fm_uc_incr                        true
% 11.81/1.98  --sat_out_model                         small
% 11.81/1.98  --sat_out_clauses                       false
% 11.81/1.98  
% 11.81/1.98  ------ QBF Options
% 11.81/1.98  
% 11.81/1.98  --qbf_mode                              false
% 11.81/1.98  --qbf_elim_univ                         false
% 11.81/1.98  --qbf_dom_inst                          none
% 11.81/1.98  --qbf_dom_pre_inst                      false
% 11.81/1.98  --qbf_sk_in                             false
% 11.81/1.98  --qbf_pred_elim                         true
% 11.81/1.98  --qbf_split                             512
% 11.81/1.98  
% 11.81/1.98  ------ BMC1 Options
% 11.81/1.98  
% 11.81/1.98  --bmc1_incremental                      false
% 11.81/1.98  --bmc1_axioms                           reachable_all
% 11.81/1.98  --bmc1_min_bound                        0
% 11.81/1.98  --bmc1_max_bound                        -1
% 11.81/1.98  --bmc1_max_bound_default                -1
% 11.81/1.98  --bmc1_symbol_reachability              true
% 11.81/1.98  --bmc1_property_lemmas                  false
% 11.81/1.98  --bmc1_k_induction                      false
% 11.81/1.98  --bmc1_non_equiv_states                 false
% 11.81/1.98  --bmc1_deadlock                         false
% 11.81/1.98  --bmc1_ucm                              false
% 11.81/1.98  --bmc1_add_unsat_core                   none
% 11.81/1.98  --bmc1_unsat_core_children              false
% 11.81/1.98  --bmc1_unsat_core_extrapolate_axioms    false
% 11.81/1.98  --bmc1_out_stat                         full
% 11.81/1.98  --bmc1_ground_init                      false
% 11.81/1.98  --bmc1_pre_inst_next_state              false
% 11.81/1.98  --bmc1_pre_inst_state                   false
% 11.81/1.98  --bmc1_pre_inst_reach_state             false
% 11.81/1.98  --bmc1_out_unsat_core                   false
% 11.81/1.98  --bmc1_aig_witness_out                  false
% 11.81/1.98  --bmc1_verbose                          false
% 11.81/1.98  --bmc1_dump_clauses_tptp                false
% 11.81/1.98  --bmc1_dump_unsat_core_tptp             false
% 11.81/1.98  --bmc1_dump_file                        -
% 11.81/1.98  --bmc1_ucm_expand_uc_limit              128
% 11.81/1.98  --bmc1_ucm_n_expand_iterations          6
% 11.81/1.98  --bmc1_ucm_extend_mode                  1
% 11.81/1.98  --bmc1_ucm_init_mode                    2
% 11.81/1.98  --bmc1_ucm_cone_mode                    none
% 11.81/1.98  --bmc1_ucm_reduced_relation_type        0
% 11.81/1.98  --bmc1_ucm_relax_model                  4
% 11.81/1.98  --bmc1_ucm_full_tr_after_sat            true
% 11.81/1.98  --bmc1_ucm_expand_neg_assumptions       false
% 11.81/1.98  --bmc1_ucm_layered_model                none
% 11.81/1.98  --bmc1_ucm_max_lemma_size               10
% 11.81/1.98  
% 11.81/1.98  ------ AIG Options
% 11.81/1.98  
% 11.81/1.98  --aig_mode                              false
% 11.81/1.98  
% 11.81/1.98  ------ Instantiation Options
% 11.81/1.98  
% 11.81/1.98  --instantiation_flag                    true
% 11.81/1.98  --inst_sos_flag                         true
% 11.81/1.98  --inst_sos_phase                        true
% 11.81/1.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.81/1.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.81/1.98  --inst_lit_sel_side                     none
% 11.81/1.98  --inst_solver_per_active                1400
% 11.81/1.98  --inst_solver_calls_frac                1.
% 11.81/1.98  --inst_passive_queue_type               priority_queues
% 11.81/1.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.81/1.98  --inst_passive_queues_freq              [25;2]
% 11.81/1.98  --inst_dismatching                      true
% 11.81/1.98  --inst_eager_unprocessed_to_passive     true
% 11.81/1.98  --inst_prop_sim_given                   true
% 11.81/1.98  --inst_prop_sim_new                     false
% 11.81/1.98  --inst_subs_new                         false
% 11.81/1.98  --inst_eq_res_simp                      false
% 11.81/1.98  --inst_subs_given                       false
% 11.81/1.98  --inst_orphan_elimination               true
% 11.81/1.98  --inst_learning_loop_flag               true
% 11.81/1.98  --inst_learning_start                   3000
% 11.81/1.98  --inst_learning_factor                  2
% 11.81/1.98  --inst_start_prop_sim_after_learn       3
% 11.81/1.98  --inst_sel_renew                        solver
% 11.81/1.98  --inst_lit_activity_flag                true
% 11.81/1.98  --inst_restr_to_given                   false
% 11.81/1.98  --inst_activity_threshold               500
% 11.81/1.98  --inst_out_proof                        true
% 11.81/1.98  
% 11.81/1.98  ------ Resolution Options
% 11.81/1.98  
% 11.81/1.98  --resolution_flag                       false
% 11.81/1.98  --res_lit_sel                           adaptive
% 11.81/1.98  --res_lit_sel_side                      none
% 11.81/1.98  --res_ordering                          kbo
% 11.81/1.98  --res_to_prop_solver                    active
% 11.81/1.98  --res_prop_simpl_new                    false
% 11.81/1.98  --res_prop_simpl_given                  true
% 11.81/1.98  --res_passive_queue_type                priority_queues
% 11.81/1.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.81/1.98  --res_passive_queues_freq               [15;5]
% 11.81/1.98  --res_forward_subs                      full
% 11.81/1.98  --res_backward_subs                     full
% 11.81/1.98  --res_forward_subs_resolution           true
% 11.81/1.98  --res_backward_subs_resolution          true
% 11.81/1.98  --res_orphan_elimination                true
% 11.81/1.98  --res_time_limit                        2.
% 11.81/1.98  --res_out_proof                         true
% 11.81/1.98  
% 11.81/1.98  ------ Superposition Options
% 11.81/1.98  
% 11.81/1.98  --superposition_flag                    true
% 11.81/1.98  --sup_passive_queue_type                priority_queues
% 11.81/1.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.81/1.98  --sup_passive_queues_freq               [8;1;4]
% 11.81/1.98  --demod_completeness_check              fast
% 11.81/1.98  --demod_use_ground                      true
% 11.81/1.98  --sup_to_prop_solver                    passive
% 11.81/1.98  --sup_prop_simpl_new                    true
% 11.81/1.98  --sup_prop_simpl_given                  true
% 11.81/1.98  --sup_fun_splitting                     true
% 11.81/1.98  --sup_smt_interval                      50000
% 11.81/1.98  
% 11.81/1.98  ------ Superposition Simplification Setup
% 11.81/1.98  
% 11.81/1.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.81/1.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.81/1.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.81/1.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.81/1.98  --sup_full_triv                         [TrivRules;PropSubs]
% 11.81/1.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.81/1.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.81/1.98  --sup_immed_triv                        [TrivRules]
% 11.81/1.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.81/1.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.81/1.98  --sup_immed_bw_main                     []
% 11.81/1.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.81/1.98  --sup_input_triv                        [Unflattening;TrivRules]
% 11.81/1.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.81/1.98  --sup_input_bw                          []
% 11.81/1.98  
% 11.81/1.98  ------ Combination Options
% 11.81/1.98  
% 11.81/1.98  --comb_res_mult                         3
% 11.81/1.98  --comb_sup_mult                         2
% 11.81/1.98  --comb_inst_mult                        10
% 11.81/1.98  
% 11.81/1.98  ------ Debug Options
% 11.81/1.98  
% 11.81/1.98  --dbg_backtrace                         false
% 11.81/1.98  --dbg_dump_prop_clauses                 false
% 11.81/1.98  --dbg_dump_prop_clauses_file            -
% 11.81/1.98  --dbg_out_stat                          false
% 11.81/1.98  
% 11.81/1.98  
% 11.81/1.98  
% 11.81/1.98  
% 11.81/1.98  ------ Proving...
% 11.81/1.98  
% 11.81/1.98  
% 11.81/1.98  % SZS status Theorem for theBenchmark.p
% 11.81/1.98  
% 11.81/1.98  % SZS output start CNFRefutation for theBenchmark.p
% 11.81/1.98  
% 11.81/1.98  fof(f16,conjecture,(
% 11.81/1.98    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 11.81/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.81/1.98  
% 11.81/1.98  fof(f17,negated_conjecture,(
% 11.81/1.98    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 11.81/1.98    inference(negated_conjecture,[],[f16])).
% 11.81/1.98  
% 11.81/1.98  fof(f19,plain,(
% 11.81/1.98    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1))),
% 11.81/1.98    inference(ennf_transformation,[],[f17])).
% 11.81/1.98  
% 11.81/1.98  fof(f24,plain,(
% 11.81/1.98    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1)) => (k2_xboole_0(k1_tarski(sK0),sK1) != sK1 & r2_hidden(sK0,sK1))),
% 11.81/1.98    introduced(choice_axiom,[])).
% 11.81/1.98  
% 11.81/1.98  fof(f25,plain,(
% 11.81/1.98    k2_xboole_0(k1_tarski(sK0),sK1) != sK1 & r2_hidden(sK0,sK1)),
% 11.81/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f24])).
% 11.81/1.98  
% 11.81/1.98  fof(f45,plain,(
% 11.81/1.98    r2_hidden(sK0,sK1)),
% 11.81/1.98    inference(cnf_transformation,[],[f25])).
% 11.81/1.98  
% 11.81/1.98  fof(f15,axiom,(
% 11.81/1.98    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 11.81/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.81/1.98  
% 11.81/1.98  fof(f22,plain,(
% 11.81/1.98    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 11.81/1.98    inference(nnf_transformation,[],[f15])).
% 11.81/1.98  
% 11.81/1.98  fof(f23,plain,(
% 11.81/1.98    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 11.81/1.98    inference(flattening,[],[f22])).
% 11.81/1.98  
% 11.81/1.98  fof(f44,plain,(
% 11.81/1.98    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 11.81/1.98    inference(cnf_transformation,[],[f23])).
% 11.81/1.98  
% 11.81/1.98  fof(f11,axiom,(
% 11.81/1.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 11.81/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.81/1.98  
% 11.81/1.98  fof(f38,plain,(
% 11.81/1.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 11.81/1.98    inference(cnf_transformation,[],[f11])).
% 11.81/1.98  
% 11.81/1.98  fof(f12,axiom,(
% 11.81/1.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 11.81/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.81/1.98  
% 11.81/1.98  fof(f39,plain,(
% 11.81/1.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 11.81/1.98    inference(cnf_transformation,[],[f12])).
% 11.81/1.98  
% 11.81/1.98  fof(f13,axiom,(
% 11.81/1.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 11.81/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.81/1.98  
% 11.81/1.98  fof(f40,plain,(
% 11.81/1.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 11.81/1.98    inference(cnf_transformation,[],[f13])).
% 11.81/1.98  
% 11.81/1.98  fof(f47,plain,(
% 11.81/1.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 11.81/1.98    inference(definition_unfolding,[],[f39,f40])).
% 11.81/1.98  
% 11.81/1.98  fof(f48,plain,(
% 11.81/1.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 11.81/1.98    inference(definition_unfolding,[],[f38,f47])).
% 11.81/1.98  
% 11.81/1.98  fof(f56,plain,(
% 11.81/1.98    ( ! [X2,X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 11.81/1.98    inference(definition_unfolding,[],[f44,f48])).
% 11.81/1.98  
% 11.81/1.98  fof(f5,axiom,(
% 11.81/1.98    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 11.81/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.81/1.98  
% 11.81/1.98  fof(f18,plain,(
% 11.81/1.98    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 11.81/1.98    inference(ennf_transformation,[],[f5])).
% 11.81/1.98  
% 11.81/1.98  fof(f32,plain,(
% 11.81/1.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 11.81/1.98    inference(cnf_transformation,[],[f18])).
% 11.81/1.98  
% 11.81/1.98  fof(f6,axiom,(
% 11.81/1.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 11.81/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.81/1.98  
% 11.81/1.98  fof(f33,plain,(
% 11.81/1.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 11.81/1.98    inference(cnf_transformation,[],[f6])).
% 11.81/1.98  
% 11.81/1.98  fof(f14,axiom,(
% 11.81/1.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 11.81/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.81/1.98  
% 11.81/1.98  fof(f41,plain,(
% 11.81/1.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 11.81/1.98    inference(cnf_transformation,[],[f14])).
% 11.81/1.98  
% 11.81/1.98  fof(f49,plain,(
% 11.81/1.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 11.81/1.98    inference(definition_unfolding,[],[f41,f48])).
% 11.81/1.98  
% 11.81/1.98  fof(f3,axiom,(
% 11.81/1.98    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 11.81/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.81/1.98  
% 11.81/1.98  fof(f30,plain,(
% 11.81/1.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 11.81/1.98    inference(cnf_transformation,[],[f3])).
% 11.81/1.98  
% 11.81/1.98  fof(f52,plain,(
% 11.81/1.98    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 11.81/1.98    inference(definition_unfolding,[],[f33,f49,f49,f30])).
% 11.81/1.98  
% 11.81/1.98  fof(f4,axiom,(
% 11.81/1.98    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 11.81/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.81/1.98  
% 11.81/1.98  fof(f31,plain,(
% 11.81/1.98    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 11.81/1.98    inference(cnf_transformation,[],[f4])).
% 11.81/1.98  
% 11.81/1.98  fof(f51,plain,(
% 11.81/1.98    ( ! [X0] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0) )),
% 11.81/1.98    inference(definition_unfolding,[],[f31,f49])).
% 11.81/1.98  
% 11.81/1.98  fof(f9,axiom,(
% 11.81/1.98    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 11.81/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.81/1.98  
% 11.81/1.98  fof(f36,plain,(
% 11.81/1.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 11.81/1.98    inference(cnf_transformation,[],[f9])).
% 11.81/1.98  
% 11.81/1.98  fof(f55,plain,(
% 11.81/1.98    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0)) )),
% 11.81/1.98    inference(definition_unfolding,[],[f36,f48,f48])).
% 11.81/1.98  
% 11.81/1.98  fof(f7,axiom,(
% 11.81/1.98    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 11.81/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.81/1.98  
% 11.81/1.98  fof(f34,plain,(
% 11.81/1.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 11.81/1.98    inference(cnf_transformation,[],[f7])).
% 11.81/1.98  
% 11.81/1.98  fof(f53,plain,(
% 11.81/1.98    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1))) )),
% 11.81/1.98    inference(definition_unfolding,[],[f34,f30,f30,f49])).
% 11.81/1.98  
% 11.81/1.98  fof(f2,axiom,(
% 11.81/1.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.81/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.81/1.98  
% 11.81/1.98  fof(f20,plain,(
% 11.81/1.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.81/1.98    inference(nnf_transformation,[],[f2])).
% 11.81/1.98  
% 11.81/1.98  fof(f21,plain,(
% 11.81/1.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.81/1.98    inference(flattening,[],[f20])).
% 11.81/1.98  
% 11.81/1.98  fof(f27,plain,(
% 11.81/1.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 11.81/1.98    inference(cnf_transformation,[],[f21])).
% 11.81/1.98  
% 11.81/1.98  fof(f61,plain,(
% 11.81/1.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.81/1.98    inference(equality_resolution,[],[f27])).
% 11.81/1.98  
% 11.81/1.98  fof(f8,axiom,(
% 11.81/1.98    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 11.81/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.81/1.98  
% 11.81/1.98  fof(f35,plain,(
% 11.81/1.98    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 11.81/1.98    inference(cnf_transformation,[],[f8])).
% 11.81/1.98  
% 11.81/1.98  fof(f54,plain,(
% 11.81/1.98    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 11.81/1.98    inference(definition_unfolding,[],[f35,f49])).
% 11.81/1.98  
% 11.81/1.98  fof(f1,axiom,(
% 11.81/1.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 11.81/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.81/1.98  
% 11.81/1.98  fof(f26,plain,(
% 11.81/1.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 11.81/1.98    inference(cnf_transformation,[],[f1])).
% 11.81/1.98  
% 11.81/1.98  fof(f46,plain,(
% 11.81/1.98    k2_xboole_0(k1_tarski(sK0),sK1) != sK1),
% 11.81/1.98    inference(cnf_transformation,[],[f25])).
% 11.81/1.98  
% 11.81/1.98  fof(f10,axiom,(
% 11.81/1.98    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 11.81/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.81/1.98  
% 11.81/1.98  fof(f37,plain,(
% 11.81/1.98    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 11.81/1.98    inference(cnf_transformation,[],[f10])).
% 11.81/1.98  
% 11.81/1.98  fof(f50,plain,(
% 11.81/1.98    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 11.81/1.98    inference(definition_unfolding,[],[f37,f48])).
% 11.81/1.98  
% 11.81/1.98  fof(f59,plain,(
% 11.81/1.98    k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) != sK1),
% 11.81/1.98    inference(definition_unfolding,[],[f46,f49,f50])).
% 11.81/1.98  
% 11.81/1.98  cnf(c_14,negated_conjecture,
% 11.81/1.98      ( r2_hidden(sK0,sK1) ),
% 11.81/1.98      inference(cnf_transformation,[],[f45]) ).
% 11.81/1.98  
% 11.81/1.98  cnf(c_322,plain,
% 11.81/1.98      ( r2_hidden(sK0,sK1) = iProver_top ),
% 11.81/1.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 11.81/1.98  
% 11.81/1.98  cnf(c_10,plain,
% 11.81/1.98      ( ~ r2_hidden(X0,X1)
% 11.81/1.98      | ~ r2_hidden(X2,X1)
% 11.81/1.98      | r1_tarski(k3_enumset1(X2,X2,X2,X2,X0),X1) ),
% 11.81/1.98      inference(cnf_transformation,[],[f56]) ).
% 11.81/1.98  
% 11.81/1.98  cnf(c_325,plain,
% 11.81/1.98      ( r2_hidden(X0,X1) != iProver_top
% 11.81/1.98      | r2_hidden(X2,X1) != iProver_top
% 11.81/1.98      | r1_tarski(k3_enumset1(X2,X2,X2,X2,X0),X1) = iProver_top ),
% 11.81/1.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.81/1.98  
% 11.81/1.98  cnf(c_5,plain,
% 11.81/1.98      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 11.81/1.98      inference(cnf_transformation,[],[f32]) ).
% 11.81/1.98  
% 11.81/1.98  cnf(c_327,plain,
% 11.81/1.98      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 11.81/1.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.81/1.98  
% 11.81/1.98  cnf(c_2152,plain,
% 11.81/1.98      ( k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),X2) = k3_enumset1(X0,X0,X0,X0,X1)
% 11.81/1.98      | r2_hidden(X1,X2) != iProver_top
% 11.81/1.98      | r2_hidden(X0,X2) != iProver_top ),
% 11.81/1.98      inference(superposition,[status(thm)],[c_325,c_327]) ).
% 11.81/1.98  
% 11.81/1.98  cnf(c_35776,plain,
% 11.81/1.98      ( k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,X0),sK1) = k3_enumset1(sK0,sK0,sK0,sK0,X0)
% 11.81/1.98      | r2_hidden(X0,sK1) != iProver_top ),
% 11.81/1.98      inference(superposition,[status(thm)],[c_322,c_2152]) ).
% 11.81/1.98  
% 11.81/1.98  cnf(c_37645,plain,
% 11.81/1.98      ( k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
% 11.81/1.98      inference(superposition,[status(thm)],[c_322,c_35776]) ).
% 11.81/1.98  
% 11.81/1.98  cnf(c_6,plain,
% 11.81/1.98      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
% 11.81/1.98      inference(cnf_transformation,[],[f52]) ).
% 11.81/1.98  
% 11.81/1.98  cnf(c_37774,plain,
% 11.81/1.98      ( k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
% 11.81/1.98      inference(superposition,[status(thm)],[c_37645,c_6]) ).
% 11.81/1.98  
% 11.81/1.98  cnf(c_4,plain,
% 11.81/1.98      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
% 11.81/1.98      inference(cnf_transformation,[],[f51]) ).
% 11.81/1.98  
% 11.81/1.98  cnf(c_9,plain,
% 11.81/1.98      ( k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
% 11.81/1.98      inference(cnf_transformation,[],[f55]) ).
% 11.81/1.98  
% 11.81/1.98  cnf(c_644,plain,
% 11.81/1.98      ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
% 11.81/1.98      inference(superposition,[status(thm)],[c_9,c_4]) ).
% 11.81/1.98  
% 11.81/1.98  cnf(c_7,plain,
% 11.81/1.98      ( k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1)) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 11.81/1.98      inference(cnf_transformation,[],[f53]) ).
% 11.81/1.98  
% 11.81/1.98  cnf(c_847,plain,
% 11.81/1.98      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
% 11.81/1.98      inference(superposition,[status(thm)],[c_644,c_7]) ).
% 11.81/1.98  
% 11.81/1.98  cnf(c_3,plain,
% 11.81/1.98      ( r1_tarski(X0,X0) ),
% 11.81/1.98      inference(cnf_transformation,[],[f61]) ).
% 11.81/1.98  
% 11.81/1.98  cnf(c_328,plain,
% 11.81/1.98      ( r1_tarski(X0,X0) = iProver_top ),
% 11.81/1.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.81/1.98  
% 11.81/1.98  cnf(c_557,plain,
% 11.81/1.98      ( k3_xboole_0(X0,X0) = X0 ),
% 11.81/1.98      inference(superposition,[status(thm)],[c_328,c_327]) ).
% 11.81/1.98  
% 11.81/1.98  cnf(c_852,plain,
% 11.81/1.98      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k5_xboole_0(X0,X0) ),
% 11.81/1.98      inference(light_normalisation,[status(thm)],[c_847,c_557]) ).
% 11.81/1.98  
% 11.81/1.98  cnf(c_8,plain,
% 11.81/1.98      ( r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
% 11.81/1.98      inference(cnf_transformation,[],[f54]) ).
% 11.81/1.98  
% 11.81/1.98  cnf(c_326,plain,
% 11.81/1.98      ( r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = iProver_top ),
% 11.81/1.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 11.81/1.98  
% 11.81/1.98  cnf(c_849,plain,
% 11.81/1.98      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 11.81/1.98      inference(superposition,[status(thm)],[c_644,c_326]) ).
% 11.81/1.98  
% 11.81/1.98  cnf(c_929,plain,
% 11.81/1.98      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 11.81/1.98      inference(superposition,[status(thm)],[c_849,c_327]) ).
% 11.81/1.98  
% 11.81/1.98  cnf(c_1090,plain,
% 11.81/1.98      ( k5_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 11.81/1.98      inference(light_normalisation,[status(thm)],[c_852,c_929]) ).
% 11.81/1.98  
% 11.81/1.98  cnf(c_850,plain,
% 11.81/1.98      ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
% 11.81/1.98      inference(superposition,[status(thm)],[c_644,c_6]) ).
% 11.81/1.98  
% 11.81/1.98  cnf(c_851,plain,
% 11.81/1.98      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
% 11.81/1.98      inference(demodulation,[status(thm)],[c_850,c_644]) ).
% 11.81/1.98  
% 11.81/1.98  cnf(c_0,plain,
% 11.81/1.98      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 11.81/1.98      inference(cnf_transformation,[],[f26]) ).
% 11.81/1.98  
% 11.81/1.98  cnf(c_935,plain,
% 11.81/1.98      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 11.81/1.98      inference(superposition,[status(thm)],[c_929,c_0]) ).
% 11.81/1.98  
% 11.81/1.98  cnf(c_1014,plain,
% 11.81/1.98      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 11.81/1.98      inference(light_normalisation,[status(thm)],[c_851,c_851,c_935]) ).
% 11.81/1.98  
% 11.81/1.98  cnf(c_1091,plain,
% 11.81/1.98      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 11.81/1.98      inference(demodulation,[status(thm)],[c_1090,c_1014]) ).
% 11.81/1.98  
% 11.81/1.98  cnf(c_37776,plain,
% 11.81/1.98      ( k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = sK1 ),
% 11.81/1.98      inference(demodulation,[status(thm)],[c_37774,c_4,c_1091]) ).
% 11.81/1.98  
% 11.81/1.98  cnf(c_13,negated_conjecture,
% 11.81/1.98      ( k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) != sK1 ),
% 11.81/1.98      inference(cnf_transformation,[],[f59]) ).
% 11.81/1.98  
% 11.81/1.98  cnf(c_640,plain,
% 11.81/1.98      ( k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) != sK1 ),
% 11.81/1.98      inference(demodulation,[status(thm)],[c_9,c_13]) ).
% 11.81/1.98  
% 11.81/1.98  cnf(contradiction,plain,
% 11.81/1.98      ( $false ),
% 11.81/1.98      inference(minisat,[status(thm)],[c_37776,c_640]) ).
% 11.81/1.98  
% 11.81/1.98  
% 11.81/1.98  % SZS output end CNFRefutation for theBenchmark.p
% 11.81/1.98  
% 11.81/1.98  ------                               Statistics
% 11.81/1.98  
% 11.81/1.98  ------ General
% 11.81/1.98  
% 11.81/1.98  abstr_ref_over_cycles:                  0
% 11.81/1.98  abstr_ref_under_cycles:                 0
% 11.81/1.98  gc_basic_clause_elim:                   0
% 11.81/1.98  forced_gc_time:                         0
% 11.81/1.98  parsing_time:                           0.007
% 11.81/1.98  unif_index_cands_time:                  0.
% 11.81/1.98  unif_index_add_time:                    0.
% 11.81/1.98  orderings_time:                         0.
% 11.81/1.98  out_proof_time:                         0.007
% 11.81/1.98  total_time:                             1.155
% 11.81/1.98  num_of_symbols:                         40
% 11.81/1.98  num_of_terms:                           28392
% 11.81/1.98  
% 11.81/1.98  ------ Preprocessing
% 11.81/1.98  
% 11.81/1.98  num_of_splits:                          0
% 11.81/1.98  num_of_split_atoms:                     0
% 11.81/1.98  num_of_reused_defs:                     0
% 11.81/1.98  num_eq_ax_congr_red:                    3
% 11.81/1.98  num_of_sem_filtered_clauses:            1
% 11.81/1.98  num_of_subtypes:                        0
% 11.81/1.98  monotx_restored_types:                  0
% 11.81/1.98  sat_num_of_epr_types:                   0
% 11.81/1.98  sat_num_of_non_cyclic_types:            0
% 11.81/1.98  sat_guarded_non_collapsed_types:        0
% 11.81/1.98  num_pure_diseq_elim:                    0
% 11.81/1.98  simp_replaced_by:                       0
% 11.81/1.98  res_preprocessed:                       73
% 11.81/1.98  prep_upred:                             0
% 11.81/1.98  prep_unflattend:                        0
% 11.81/1.98  smt_new_axioms:                         0
% 11.81/1.98  pred_elim_cands:                        2
% 11.81/1.98  pred_elim:                              0
% 11.81/1.98  pred_elim_cl:                           0
% 11.81/1.98  pred_elim_cycles:                       2
% 11.81/1.98  merged_defs:                            0
% 11.81/1.98  merged_defs_ncl:                        0
% 11.81/1.98  bin_hyper_res:                          0
% 11.81/1.98  prep_cycles:                            4
% 11.81/1.98  pred_elim_time:                         0.
% 11.81/1.98  splitting_time:                         0.
% 11.81/1.98  sem_filter_time:                        0.
% 11.81/1.98  monotx_time:                            0.
% 11.81/1.98  subtype_inf_time:                       0.
% 11.81/1.98  
% 11.81/1.98  ------ Problem properties
% 11.81/1.98  
% 11.81/1.98  clauses:                                14
% 11.81/1.98  conjectures:                            2
% 11.81/1.98  epr:                                    3
% 11.81/1.98  horn:                                   14
% 11.81/1.98  ground:                                 2
% 11.81/1.98  unary:                                  9
% 11.81/1.98  binary:                                 3
% 11.81/1.98  lits:                                   21
% 11.81/1.98  lits_eq:                                8
% 11.81/1.98  fd_pure:                                0
% 11.81/1.98  fd_pseudo:                              0
% 11.81/1.98  fd_cond:                                0
% 11.81/1.98  fd_pseudo_cond:                         1
% 11.81/1.98  ac_symbols:                             0
% 11.81/1.98  
% 11.81/1.98  ------ Propositional Solver
% 11.81/1.98  
% 11.81/1.98  prop_solver_calls:                      36
% 11.81/1.98  prop_fast_solver_calls:                 531
% 11.81/1.98  smt_solver_calls:                       0
% 11.81/1.98  smt_fast_solver_calls:                  0
% 11.81/1.98  prop_num_of_clauses:                    7982
% 11.81/1.98  prop_preprocess_simplified:             14748
% 11.81/1.98  prop_fo_subsumed:                       0
% 11.81/1.98  prop_solver_time:                       0.
% 11.81/1.98  smt_solver_time:                        0.
% 11.81/1.98  smt_fast_solver_time:                   0.
% 11.81/1.98  prop_fast_solver_time:                  0.
% 11.81/1.98  prop_unsat_core_time:                   0.001
% 11.81/1.98  
% 11.81/1.98  ------ QBF
% 11.81/1.98  
% 11.81/1.98  qbf_q_res:                              0
% 11.81/1.98  qbf_num_tautologies:                    0
% 11.81/1.98  qbf_prep_cycles:                        0
% 11.81/1.98  
% 11.81/1.98  ------ BMC1
% 11.81/1.98  
% 11.81/1.98  bmc1_current_bound:                     -1
% 11.81/1.98  bmc1_last_solved_bound:                 -1
% 11.81/1.98  bmc1_unsat_core_size:                   -1
% 11.81/1.98  bmc1_unsat_core_parents_size:           -1
% 11.81/1.98  bmc1_merge_next_fun:                    0
% 11.81/1.98  bmc1_unsat_core_clauses_time:           0.
% 11.81/1.98  
% 11.81/1.98  ------ Instantiation
% 11.81/1.98  
% 11.81/1.98  inst_num_of_clauses:                    2508
% 11.81/1.98  inst_num_in_passive:                    1598
% 11.81/1.98  inst_num_in_active:                     862
% 11.81/1.98  inst_num_in_unprocessed:                49
% 11.81/1.98  inst_num_of_loops:                      940
% 11.81/1.98  inst_num_of_learning_restarts:          0
% 11.81/1.98  inst_num_moves_active_passive:          70
% 11.81/1.98  inst_lit_activity:                      0
% 11.81/1.98  inst_lit_activity_moves:                0
% 11.81/1.98  inst_num_tautologies:                   0
% 11.81/1.98  inst_num_prop_implied:                  0
% 11.81/1.98  inst_num_existing_simplified:           0
% 11.81/1.98  inst_num_eq_res_simplified:             0
% 11.81/1.98  inst_num_child_elim:                    0
% 11.81/1.98  inst_num_of_dismatching_blockings:      1306
% 11.81/1.98  inst_num_of_non_proper_insts:           3555
% 11.81/1.98  inst_num_of_duplicates:                 0
% 11.81/1.98  inst_inst_num_from_inst_to_res:         0
% 11.81/1.98  inst_dismatching_checking_time:         0.
% 11.81/1.98  
% 11.81/1.98  ------ Resolution
% 11.81/1.98  
% 11.81/1.98  res_num_of_clauses:                     0
% 11.81/1.98  res_num_in_passive:                     0
% 11.81/1.98  res_num_in_active:                      0
% 11.81/1.98  res_num_of_loops:                       77
% 11.81/1.98  res_forward_subset_subsumed:            550
% 11.81/1.98  res_backward_subset_subsumed:           8
% 11.81/1.98  res_forward_subsumed:                   0
% 11.81/1.98  res_backward_subsumed:                  0
% 11.81/1.98  res_forward_subsumption_resolution:     0
% 11.81/1.98  res_backward_subsumption_resolution:    0
% 11.81/1.98  res_clause_to_clause_subsumption:       16666
% 11.81/1.98  res_orphan_elimination:                 0
% 11.81/1.98  res_tautology_del:                      280
% 11.81/1.98  res_num_eq_res_simplified:              0
% 11.81/1.98  res_num_sel_changes:                    0
% 11.81/1.98  res_moves_from_active_to_pass:          0
% 11.81/1.98  
% 11.81/1.98  ------ Superposition
% 11.81/1.98  
% 11.81/1.98  sup_time_total:                         0.
% 11.81/1.98  sup_time_generating:                    0.
% 11.81/1.98  sup_time_sim_full:                      0.
% 11.81/1.98  sup_time_sim_immed:                     0.
% 11.81/1.98  
% 11.81/1.98  sup_num_of_clauses:                     989
% 11.81/1.98  sup_num_in_active:                      183
% 11.81/1.98  sup_num_in_passive:                     806
% 11.81/1.98  sup_num_of_loops:                       187
% 11.81/1.98  sup_fw_superposition:                   8143
% 11.81/1.98  sup_bw_superposition:                   5072
% 11.81/1.98  sup_immediate_simplified:               6983
% 11.81/1.98  sup_given_eliminated:                   2
% 11.81/1.98  comparisons_done:                       0
% 11.81/1.98  comparisons_avoided:                    0
% 11.81/1.98  
% 11.81/1.98  ------ Simplifications
% 11.81/1.98  
% 11.81/1.98  
% 11.81/1.98  sim_fw_subset_subsumed:                 9
% 11.81/1.98  sim_bw_subset_subsumed:                 2
% 11.81/1.98  sim_fw_subsumed:                        511
% 11.81/1.98  sim_bw_subsumed:                        0
% 11.81/1.98  sim_fw_subsumption_res:                 0
% 11.81/1.98  sim_bw_subsumption_res:                 0
% 11.81/1.98  sim_tautology_del:                      2
% 11.81/1.98  sim_eq_tautology_del:                   2736
% 11.81/1.98  sim_eq_res_simp:                        0
% 11.81/1.98  sim_fw_demodulated:                     4347
% 11.81/1.98  sim_bw_demodulated:                     53
% 11.81/1.98  sim_light_normalised:                   4681
% 11.81/1.98  sim_joinable_taut:                      0
% 11.81/1.98  sim_joinable_simp:                      0
% 11.81/1.98  sim_ac_normalised:                      0
% 11.81/1.98  sim_smt_subsumption:                    0
% 11.81/1.98  
%------------------------------------------------------------------------------
