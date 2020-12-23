%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0232+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:29 EST 2020

% Result     : Theorem 14.85s
% Output     : CNFRefutation 14.85s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 133 expanded)
%              Number of clauses        :   28 (  39 expanded)
%              Number of leaves         :   14 (  36 expanded)
%              Depth                    :   15
%              Number of atoms          :  102 ( 171 expanded)
%              Number of equality atoms :   75 ( 138 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f316,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
     => k2_tarski(X0,X1) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f317,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
       => k2_tarski(X0,X1) = k1_tarski(X2) ) ),
    inference(negated_conjecture,[],[f316])).

fof(f454,plain,(
    ? [X0,X1,X2] :
      ( k2_tarski(X0,X1) != k1_tarski(X2)
      & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) ) ),
    inference(ennf_transformation,[],[f317])).

fof(f571,plain,
    ( ? [X0,X1,X2] :
        ( k2_tarski(X0,X1) != k1_tarski(X2)
        & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) )
   => ( k2_tarski(sK28,sK29) != k1_tarski(sK30)
      & r1_tarski(k2_tarski(sK28,sK29),k1_tarski(sK30)) ) ),
    introduced(choice_axiom,[])).

fof(f572,plain,
    ( k2_tarski(sK28,sK29) != k1_tarski(sK30)
    & r1_tarski(k2_tarski(sK28,sK29),k1_tarski(sK30)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK28,sK29,sK30])],[f454,f571])).

fof(f988,plain,(
    r1_tarski(k2_tarski(sK28,sK29),k1_tarski(sK30)) ),
    inference(cnf_transformation,[],[f572])).

fof(f226,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f884,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f226])).

fof(f166,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f788,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f166])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f728,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f994,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f788,f728])).

fof(f995,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f884,f994])).

fof(f1271,plain,(
    r1_tarski(k5_xboole_0(k5_xboole_0(k1_tarski(sK28),k1_tarski(sK29)),k4_xboole_0(k1_tarski(sK28),k4_xboole_0(k1_tarski(sK28),k1_tarski(sK29)))),k1_tarski(sK30)) ),
    inference(definition_unfolding,[],[f988,f995])).

fof(f163,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f785,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f163])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f577,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f170,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f792,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f170])).

fof(f1138,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f792,f994])).

fof(f299,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f568,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f299])).

fof(f569,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f568])).

fof(f968,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f569])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f580,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f1257,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | o_0_0_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(definition_unfolding,[],[f968,f580])).

fof(f989,plain,(
    k2_tarski(sK28,sK29) != k1_tarski(sK30) ),
    inference(cnf_transformation,[],[f572])).

fof(f1270,plain,(
    k5_xboole_0(k5_xboole_0(k1_tarski(sK28),k1_tarski(sK29)),k4_xboole_0(k1_tarski(sK28),k4_xboole_0(k1_tarski(sK28),k1_tarski(sK29)))) != k1_tarski(sK30) ),
    inference(definition_unfolding,[],[f989,f995])).

fof(f164,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f786,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f164])).

fof(f1135,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = o_0_0_xboole_0 ),
    inference(definition_unfolding,[],[f786,f580])).

fof(f124,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f742,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f124])).

fof(f1108,plain,(
    ! [X0] : k5_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f742,f580])).

fof(f147,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f768,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f147])).

fof(f304,axiom,(
    ! [X0,X1] :
      ~ ( X0 = X1
        & r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f446,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f304])).

fof(f975,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f446])).

fof(f1333,plain,(
    ! [X1] : ~ r1_xboole_0(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f975])).

cnf(c_404,negated_conjecture,
    ( r1_tarski(k5_xboole_0(k5_xboole_0(k1_tarski(sK28),k1_tarski(sK29)),k4_xboole_0(k1_tarski(sK28),k4_xboole_0(k1_tarski(sK28),k1_tarski(sK29)))),k1_tarski(sK30)) ),
    inference(cnf_transformation,[],[f1271])).

cnf(c_211,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f785])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f577])).

cnf(c_7462,negated_conjecture,
    ( r1_tarski(k5_xboole_0(k1_tarski(sK28),k5_xboole_0(k1_tarski(sK29),k4_xboole_0(k1_tarski(sK28),k4_xboole_0(k1_tarski(sK28),k1_tarski(sK29))))),k1_tarski(sK30)) ),
    inference(theory_normalisation,[status(thm)],[c_404,c_211,c_7])).

cnf(c_12563,plain,
    ( r1_tarski(k5_xboole_0(k1_tarski(sK28),k5_xboole_0(k1_tarski(sK29),k4_xboole_0(k1_tarski(sK28),k4_xboole_0(k1_tarski(sK28),k1_tarski(sK29))))),k1_tarski(sK30)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7462])).

cnf(c_217,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f1138])).

cnf(c_7572,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(theory_normalisation,[status(thm)],[c_217,c_211,c_7])).

cnf(c_13273,plain,
    ( r1_tarski(k5_xboole_0(k1_tarski(sK28),k4_xboole_0(k1_tarski(sK29),k1_tarski(sK28))),k1_tarski(sK30)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_12563,c_7572])).

cnf(c_385,plain,
    ( ~ r1_tarski(X0,k1_tarski(X1))
    | k1_tarski(X1) = X0
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f1257])).

cnf(c_12570,plain,
    ( k1_tarski(X0) = X1
    | o_0_0_xboole_0 = X1
    | r1_tarski(X1,k1_tarski(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_385])).

cnf(c_16764,plain,
    ( k5_xboole_0(k1_tarski(sK28),k4_xboole_0(k1_tarski(sK29),k1_tarski(sK28))) = k1_tarski(sK30)
    | k5_xboole_0(k1_tarski(sK28),k4_xboole_0(k1_tarski(sK29),k1_tarski(sK28))) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_13273,c_12570])).

cnf(c_403,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(sK28),k1_tarski(sK29)),k4_xboole_0(k1_tarski(sK28),k4_xboole_0(k1_tarski(sK28),k1_tarski(sK29)))) != k1_tarski(sK30) ),
    inference(cnf_transformation,[],[f1270])).

cnf(c_7463,negated_conjecture,
    ( k5_xboole_0(k1_tarski(sK28),k5_xboole_0(k1_tarski(sK29),k4_xboole_0(k1_tarski(sK28),k4_xboole_0(k1_tarski(sK28),k1_tarski(sK29))))) != k1_tarski(sK30) ),
    inference(theory_normalisation,[status(thm)],[c_403,c_211,c_7])).

cnf(c_13230,plain,
    ( k5_xboole_0(k1_tarski(sK28),k4_xboole_0(k1_tarski(sK29),k1_tarski(sK28))) != k1_tarski(sK30) ),
    inference(demodulation,[status(thm)],[c_7463,c_7572])).

cnf(c_17510,plain,
    ( k5_xboole_0(k1_tarski(sK28),k4_xboole_0(k1_tarski(sK29),k1_tarski(sK28))) = o_0_0_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_16764,c_13230])).

cnf(c_212,plain,
    ( k5_xboole_0(X0,X0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1135])).

cnf(c_15638,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(o_0_0_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_212,c_211])).

cnf(c_168,plain,
    ( k5_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f1108])).

cnf(c_15157,plain,
    ( k5_xboole_0(o_0_0_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_7,c_168])).

cnf(c_15659,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_15638,c_15157])).

cnf(c_17521,plain,
    ( k4_xboole_0(k1_tarski(sK29),k1_tarski(sK28)) = k5_xboole_0(k1_tarski(sK28),o_0_0_xboole_0) ),
    inference(superposition,[status(thm)],[c_17510,c_15659])).

cnf(c_17535,plain,
    ( k4_xboole_0(k1_tarski(sK29),k1_tarski(sK28)) = k1_tarski(sK28) ),
    inference(demodulation,[status(thm)],[c_17521,c_168])).

cnf(c_194,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f768])).

cnf(c_12668,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_194])).

cnf(c_18020,plain,
    ( r1_xboole_0(k1_tarski(sK28),k1_tarski(sK28)) = iProver_top ),
    inference(superposition,[status(thm)],[c_17535,c_12668])).

cnf(c_390,plain,
    ( ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f1333])).

cnf(c_12568,plain,
    ( r1_xboole_0(k1_tarski(X0),k1_tarski(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_390])).

cnf(c_18397,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_18020,c_12568])).

%------------------------------------------------------------------------------
