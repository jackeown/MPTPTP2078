%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0211+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:27 EST 2020

% Result     : Theorem 15.83s
% Output     : CNFRefutation 15.83s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 821 expanded)
%              Number of clauses        :   57 ( 211 expanded)
%              Number of leaves         :   20 ( 253 expanded)
%              Depth                    :   21
%              Number of atoms          :  115 ( 822 expanded)
%              Number of equality atoms :  114 ( 821 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :   14 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f163,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f712,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f163])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f504,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f503,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f655,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f883,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f503,f655,f655])).

fof(f225,conjecture,(
    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f226,negated_conjecture,(
    ~ ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2) ),
    inference(negated_conjecture,[],[f225])).

fof(f401,plain,(
    ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) != k1_enumset1(X0,X1,X2) ),
    inference(ennf_transformation,[],[f226])).

fof(f498,plain,
    ( ? [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) != k1_enumset1(X0,X1,X2)
   => k2_xboole_0(k2_tarski(sK25,sK24),k2_tarski(sK26,sK24)) != k1_enumset1(sK24,sK25,sK26) ),
    introduced(choice_axiom,[])).

fof(f499,plain,(
    k2_xboole_0(k2_tarski(sK25,sK24),k2_tarski(sK26,sK24)) != k1_enumset1(sK24,sK25,sK26) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK24,sK25,sK26])],[f401,f498])).

fof(f810,plain,(
    k2_xboole_0(k2_tarski(sK25,sK24),k2_tarski(sK26,sK24)) != k1_enumset1(sK24,sK25,sK26) ),
    inference(cnf_transformation,[],[f499])).

fof(f228,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f812,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f228])).

fof(f227,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f811,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f227])).

fof(f166,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f715,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f166])).

fof(f869,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f715,f655])).

fof(f870,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f811,f869])).

fof(f871,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X2))))),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X2))))))) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f812,f869,f870])).

fof(f1064,plain,(
    k5_xboole_0(k5_xboole_0(k1_tarski(sK24),k5_xboole_0(k5_xboole_0(k1_tarski(sK25),k1_tarski(sK26)),k4_xboole_0(k1_tarski(sK25),k4_xboole_0(k1_tarski(sK25),k1_tarski(sK26))))),k4_xboole_0(k1_tarski(sK24),k4_xboole_0(k1_tarski(sK24),k5_xboole_0(k5_xboole_0(k1_tarski(sK25),k1_tarski(sK26)),k4_xboole_0(k1_tarski(sK25),k4_xboole_0(k1_tarski(sK25),k1_tarski(sK26))))))) != k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK25),k1_tarski(sK24)),k4_xboole_0(k1_tarski(sK25),k4_xboole_0(k1_tarski(sK25),k1_tarski(sK24)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK26),k1_tarski(sK24)),k4_xboole_0(k1_tarski(sK26),k4_xboole_0(k1_tarski(sK26),k1_tarski(sK24))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK25),k1_tarski(sK24)),k4_xboole_0(k1_tarski(sK25),k4_xboole_0(k1_tarski(sK25),k1_tarski(sK24)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK25),k1_tarski(sK24)),k4_xboole_0(k1_tarski(sK25),k4_xboole_0(k1_tarski(sK25),k1_tarski(sK24)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK26),k1_tarski(sK24)),k4_xboole_0(k1_tarski(sK26),k4_xboole_0(k1_tarski(sK26),k1_tarski(sK24))))))) ),
    inference(definition_unfolding,[],[f810,f869,f870,f870,f871])).

fof(f48,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f582,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

fof(f880,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f582,f655])).

fof(f170,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f719,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f170])).

fof(f1013,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f719,f869])).

fof(f103,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f648,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f103])).

fof(f967,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(definition_unfolding,[],[f648,f869])).

fof(f82,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f626,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f82])).

fof(f950,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) = k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k5_xboole_0(k5_xboole_0(X0,X2),k4_xboole_0(X0,k4_xboole_0(X0,X2))))) ),
    inference(definition_unfolding,[],[f626,f869,f655,f655,f869,f869])).

fof(f111,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f656,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f111])).

fof(f974,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f656,f655,f655])).

fof(f198,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f783,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0) ),
    inference(cnf_transformation,[],[f198])).

fof(f1038,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X2))))),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X2))))))) = k5_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X0)),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))))),k4_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X2),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X0)),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))))))) ),
    inference(definition_unfolding,[],[f783,f871,f871])).

fof(f109,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f654,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f109])).

fof(f973,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f654,f655])).

fof(f164,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f713,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f164])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f507,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f1010,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = o_0_0_xboole_0 ),
    inference(definition_unfolding,[],[f713,f507])).

fof(f124,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f669,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f124])).

fof(f983,plain,(
    ! [X0] : k5_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f669,f507])).

fof(f60,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k4_xboole_0(X0,X2),X1) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f600,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k4_xboole_0(X0,X2),X1) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f60])).

fof(f925,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(k4_xboole_0(X0,X2),X1)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(definition_unfolding,[],[f600,f655,f655,f655])).

cnf(c_211,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f712])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f504])).

cnf(c_11519,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_211,c_7])).

cnf(c_6,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f883])).

cnf(c_301,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(sK24),k5_xboole_0(k5_xboole_0(k1_tarski(sK25),k1_tarski(sK26)),k4_xboole_0(k1_tarski(sK25),k4_xboole_0(k1_tarski(sK25),k1_tarski(sK26))))),k4_xboole_0(k1_tarski(sK24),k4_xboole_0(k1_tarski(sK24),k5_xboole_0(k5_xboole_0(k1_tarski(sK25),k1_tarski(sK26)),k4_xboole_0(k1_tarski(sK25),k4_xboole_0(k1_tarski(sK25),k1_tarski(sK26))))))) != k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK25),k1_tarski(sK24)),k4_xboole_0(k1_tarski(sK25),k4_xboole_0(k1_tarski(sK25),k1_tarski(sK24)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK26),k1_tarski(sK24)),k4_xboole_0(k1_tarski(sK26),k4_xboole_0(k1_tarski(sK26),k1_tarski(sK24))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK25),k1_tarski(sK24)),k4_xboole_0(k1_tarski(sK25),k4_xboole_0(k1_tarski(sK25),k1_tarski(sK24)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK25),k1_tarski(sK24)),k4_xboole_0(k1_tarski(sK25),k4_xboole_0(k1_tarski(sK25),k1_tarski(sK24)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK26),k1_tarski(sK24)),k4_xboole_0(k1_tarski(sK26),k4_xboole_0(k1_tarski(sK26),k1_tarski(sK24))))))) ),
    inference(cnf_transformation,[],[f1064])).

cnf(c_6692,negated_conjecture,
    ( k5_xboole_0(k1_tarski(sK24),k5_xboole_0(k1_tarski(sK24),k5_xboole_0(k1_tarski(sK25),k5_xboole_0(k1_tarski(sK26),k5_xboole_0(k4_xboole_0(k1_tarski(sK25),k4_xboole_0(k1_tarski(sK25),k1_tarski(sK24))),k5_xboole_0(k4_xboole_0(k1_tarski(sK26),k4_xboole_0(k1_tarski(sK26),k1_tarski(sK24))),k4_xboole_0(k5_xboole_0(k1_tarski(sK24),k5_xboole_0(k1_tarski(sK25),k4_xboole_0(k1_tarski(sK25),k4_xboole_0(k1_tarski(sK25),k1_tarski(sK24))))),k4_xboole_0(k5_xboole_0(k1_tarski(sK24),k5_xboole_0(k1_tarski(sK25),k4_xboole_0(k1_tarski(sK25),k4_xboole_0(k1_tarski(sK25),k1_tarski(sK24))))),k5_xboole_0(k1_tarski(sK24),k5_xboole_0(k1_tarski(sK26),k4_xboole_0(k1_tarski(sK26),k4_xboole_0(k1_tarski(sK26),k1_tarski(sK24))))))))))))) != k5_xboole_0(k1_tarski(sK24),k5_xboole_0(k1_tarski(sK25),k5_xboole_0(k1_tarski(sK26),k5_xboole_0(k4_xboole_0(k1_tarski(sK25),k4_xboole_0(k1_tarski(sK25),k1_tarski(sK26))),k4_xboole_0(k1_tarski(sK24),k4_xboole_0(k1_tarski(sK24),k5_xboole_0(k1_tarski(sK25),k5_xboole_0(k1_tarski(sK26),k4_xboole_0(k1_tarski(sK25),k4_xboole_0(k1_tarski(sK25),k1_tarski(sK26))))))))))) ),
    inference(theory_normalisation,[status(thm)],[c_301,c_211,c_7])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f880])).

cnf(c_217,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f1013])).

cnf(c_6740,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(theory_normalisation,[status(thm)],[c_217,c_211,c_7])).

cnf(c_148,plain,
    ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f967])).

cnf(c_6766,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(theory_normalisation,[status(thm)],[c_148,c_211,c_7])).

cnf(c_11005,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(demodulation,[status(thm)],[c_6766,c_6740])).

cnf(c_126,plain,
    ( k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k5_xboole_0(k5_xboole_0(X0,X2),k4_xboole_0(X0,k4_xboole_0(X0,X2))))) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) ),
    inference(cnf_transformation,[],[f950])).

cnf(c_6773,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k5_xboole_0(X0,k5_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X2)))))) = k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))))) ),
    inference(theory_normalisation,[status(thm)],[c_126,c_211,c_7])).

cnf(c_11074,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X0,k5_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X2)))))) = k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))))) ),
    inference(light_normalisation,[status(thm)],[c_6773,c_6740])).

cnf(c_155,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(cnf_transformation,[],[f974])).

cnf(c_11075,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X0),X2)) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X0)))) ),
    inference(demodulation,[status(thm)],[c_11074,c_155,c_6740,c_11005])).

cnf(c_275,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X2))))),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X2))))))) = k5_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X0)),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))))),k4_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X2),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X0)),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))))))) ),
    inference(cnf_transformation,[],[f1038])).

cnf(c_6715,plain,
    ( k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X1),k5_xboole_0(k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))),k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))))))))))) = k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k5_xboole_0(k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X2))),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X2))))))))))) ),
    inference(theory_normalisation,[status(thm)],[c_275,c_211,c_7])).

cnf(c_11094,plain,
    ( k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X1),k5_xboole_0(k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))),k4_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))))))))) = k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k5_xboole_0(k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X2))),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k4_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2))))))) ),
    inference(demodulation,[status(thm)],[c_6715,c_1,c_6740,c_11005])).

cnf(c_11095,plain,
    ( k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k5_xboole_0(k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X2))),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k4_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2))))))) = k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X1),k5_xboole_0(k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))),k4_xboole_0(k4_xboole_0(k1_tarski(X2),k1_tarski(X0)),k1_tarski(X1))))) ),
    inference(demodulation,[status(thm)],[c_11094,c_1,c_11005])).

cnf(c_11106,plain,
    ( k5_xboole_0(k1_tarski(sK24),k5_xboole_0(k1_tarski(sK24),k5_xboole_0(k1_tarski(sK25),k5_xboole_0(k1_tarski(sK26),k5_xboole_0(k4_xboole_0(k1_tarski(sK25),k4_xboole_0(k1_tarski(sK25),k1_tarski(sK24))),k5_xboole_0(k4_xboole_0(k1_tarski(sK26),k4_xboole_0(k1_tarski(sK26),k1_tarski(sK24))),k5_xboole_0(k1_tarski(sK24),k4_xboole_0(k1_tarski(sK25),k4_xboole_0(k1_tarski(sK25),k4_xboole_0(k1_tarski(sK26),k1_tarski(sK24))))))))))) != k5_xboole_0(k1_tarski(sK24),k5_xboole_0(k1_tarski(sK25),k5_xboole_0(k4_xboole_0(k1_tarski(sK25),k4_xboole_0(k1_tarski(sK25),k1_tarski(sK24))),k4_xboole_0(k4_xboole_0(k1_tarski(sK26),k1_tarski(sK24)),k1_tarski(sK25))))) ),
    inference(demodulation,[status(thm)],[c_6692,c_1,c_6740,c_11005,c_11075,c_11095])).

cnf(c_13838,plain,
    ( k5_xboole_0(k1_tarski(sK24),k5_xboole_0(k1_tarski(sK24),k5_xboole_0(k1_tarski(sK25),k5_xboole_0(k1_tarski(sK26),k5_xboole_0(k4_xboole_0(k1_tarski(sK24),k4_xboole_0(k1_tarski(sK24),k1_tarski(sK25))),k5_xboole_0(k4_xboole_0(k1_tarski(sK26),k4_xboole_0(k1_tarski(sK26),k1_tarski(sK24))),k5_xboole_0(k1_tarski(sK24),k4_xboole_0(k1_tarski(sK25),k4_xboole_0(k1_tarski(sK25),k4_xboole_0(k1_tarski(sK26),k1_tarski(sK24))))))))))) != k5_xboole_0(k1_tarski(sK24),k5_xboole_0(k1_tarski(sK25),k5_xboole_0(k4_xboole_0(k1_tarski(sK24),k4_xboole_0(k1_tarski(sK24),k1_tarski(sK25))),k4_xboole_0(k4_xboole_0(k1_tarski(sK26),k1_tarski(sK24)),k1_tarski(sK25))))) ),
    inference(demodulation,[status(thm)],[c_6,c_11106])).

cnf(c_154,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f973])).

cnf(c_14039,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k5_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_154,c_1])).

cnf(c_14046,plain,
    ( k5_xboole_0(k1_tarski(sK24),k5_xboole_0(k1_tarski(sK24),k5_xboole_0(k1_tarski(sK25),k5_xboole_0(k1_tarski(sK26),k5_xboole_0(k5_xboole_0(k1_tarski(sK24),k4_xboole_0(k1_tarski(sK24),k1_tarski(sK25))),k5_xboole_0(k5_xboole_0(k1_tarski(sK26),k4_xboole_0(k1_tarski(sK26),k1_tarski(sK24))),k5_xboole_0(k1_tarski(sK24),k5_xboole_0(k1_tarski(sK25),k4_xboole_0(k1_tarski(sK25),k4_xboole_0(k1_tarski(sK26),k1_tarski(sK24))))))))))) != k5_xboole_0(k1_tarski(sK24),k5_xboole_0(k1_tarski(sK25),k5_xboole_0(k5_xboole_0(k1_tarski(sK24),k4_xboole_0(k1_tarski(sK24),k1_tarski(sK25))),k4_xboole_0(k4_xboole_0(k1_tarski(sK26),k1_tarski(sK24)),k1_tarski(sK25))))) ),
    inference(demodulation,[status(thm)],[c_13838,c_14039])).

cnf(c_15128,plain,
    ( k5_xboole_0(k1_tarski(sK24),k5_xboole_0(k1_tarski(sK24),k5_xboole_0(k1_tarski(sK25),k5_xboole_0(k1_tarski(sK26),k5_xboole_0(k5_xboole_0(k1_tarski(sK24),k4_xboole_0(k1_tarski(sK24),k1_tarski(sK25))),k5_xboole_0(k1_tarski(sK26),k5_xboole_0(k4_xboole_0(k1_tarski(sK26),k1_tarski(sK24)),k5_xboole_0(k1_tarski(sK24),k5_xboole_0(k1_tarski(sK25),k4_xboole_0(k1_tarski(sK25),k4_xboole_0(k1_tarski(sK26),k1_tarski(sK24)))))))))))) != k5_xboole_0(k1_tarski(sK24),k5_xboole_0(k1_tarski(sK25),k5_xboole_0(k5_xboole_0(k1_tarski(sK24),k4_xboole_0(k1_tarski(sK24),k1_tarski(sK25))),k4_xboole_0(k4_xboole_0(k1_tarski(sK26),k1_tarski(sK24)),k1_tarski(sK25))))) ),
    inference(demodulation,[status(thm)],[c_211,c_14046])).

cnf(c_212,plain,
    ( k5_xboole_0(X0,X0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1010])).

cnf(c_15135,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(o_0_0_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_212,c_211])).

cnf(c_168,plain,
    ( k5_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f983])).

cnf(c_13671,plain,
    ( k5_xboole_0(o_0_0_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_168,c_7])).

cnf(c_15156,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_15135,c_13671])).

cnf(c_16161,plain,
    ( k5_xboole_0(k1_tarski(sK25),k5_xboole_0(k1_tarski(sK26),k5_xboole_0(k5_xboole_0(k1_tarski(sK24),k4_xboole_0(k1_tarski(sK24),k1_tarski(sK25))),k5_xboole_0(k1_tarski(sK26),k5_xboole_0(k4_xboole_0(k1_tarski(sK26),k1_tarski(sK24)),k5_xboole_0(k1_tarski(sK24),k5_xboole_0(k1_tarski(sK25),k4_xboole_0(k1_tarski(sK25),k4_xboole_0(k1_tarski(sK26),k1_tarski(sK24)))))))))) != k5_xboole_0(k1_tarski(sK24),k5_xboole_0(k1_tarski(sK25),k5_xboole_0(k5_xboole_0(k1_tarski(sK24),k4_xboole_0(k1_tarski(sK24),k1_tarski(sK25))),k4_xboole_0(k4_xboole_0(k1_tarski(sK26),k1_tarski(sK24)),k1_tarski(sK25))))) ),
    inference(demodulation,[status(thm)],[c_15128,c_15156])).

cnf(c_27400,plain,
    ( k5_xboole_0(k1_tarski(sK25),k5_xboole_0(k1_tarski(sK26),k5_xboole_0(k5_xboole_0(k1_tarski(sK24),k4_xboole_0(k1_tarski(sK24),k1_tarski(sK25))),k5_xboole_0(k1_tarski(sK26),k5_xboole_0(k1_tarski(sK24),k5_xboole_0(k4_xboole_0(k1_tarski(sK26),k1_tarski(sK24)),k5_xboole_0(k1_tarski(sK25),k4_xboole_0(k1_tarski(sK25),k4_xboole_0(k1_tarski(sK26),k1_tarski(sK24)))))))))) != k5_xboole_0(k1_tarski(sK24),k5_xboole_0(k1_tarski(sK25),k5_xboole_0(k5_xboole_0(k1_tarski(sK24),k4_xboole_0(k1_tarski(sK24),k1_tarski(sK25))),k4_xboole_0(k4_xboole_0(k1_tarski(sK26),k1_tarski(sK24)),k1_tarski(sK25))))) ),
    inference(demodulation,[status(thm)],[c_11519,c_16161])).

cnf(c_100,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k4_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(k4_xboole_0(X0,X2),X1)) ),
    inference(cnf_transformation,[],[f925])).

cnf(c_17787,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k4_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(k4_xboole_0(X0,X2),X1)) ),
    inference(light_normalisation,[status(thm)],[c_100,c_100,c_14039])).

cnf(c_15603,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(light_normalisation,[status(thm)],[c_155,c_155,c_14039])).

cnf(c_15604,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(demodulation,[status(thm)],[c_15603,c_14039])).

cnf(c_17788,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X2,X1))))) = k5_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(k4_xboole_0(X0,X2),X1)) ),
    inference(demodulation,[status(thm)],[c_17787,c_14039,c_15604])).

cnf(c_14030,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_6,c_154])).

cnf(c_14058,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_14030,c_14039])).

cnf(c_17789,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2)) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,X1))) ),
    inference(demodulation,[status(thm)],[c_17788,c_14058])).

cnf(c_17800,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1)))) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X1))) ),
    inference(superposition,[status(thm)],[c_6,c_17789])).

cnf(c_17813,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X1))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_17789,c_1])).

cnf(c_17840,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1)))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(demodulation,[status(thm)],[c_17800,c_17813])).

cnf(c_13852,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_6,c_1])).

cnf(c_17841,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1)))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(demodulation,[status(thm)],[c_17840,c_13852,c_14039])).

cnf(c_27401,plain,
    ( k5_xboole_0(k1_tarski(sK25),k5_xboole_0(k1_tarski(sK26),k5_xboole_0(k5_xboole_0(k1_tarski(sK24),k4_xboole_0(k1_tarski(sK24),k1_tarski(sK25))),k5_xboole_0(k1_tarski(sK26),k5_xboole_0(k1_tarski(sK24),k4_xboole_0(k4_xboole_0(k1_tarski(sK26),k1_tarski(sK24)),k1_tarski(sK25))))))) != k5_xboole_0(k1_tarski(sK24),k5_xboole_0(k1_tarski(sK25),k5_xboole_0(k5_xboole_0(k1_tarski(sK24),k4_xboole_0(k1_tarski(sK24),k1_tarski(sK25))),k4_xboole_0(k4_xboole_0(k1_tarski(sK26),k1_tarski(sK24)),k1_tarski(sK25))))) ),
    inference(demodulation,[status(thm)],[c_27400,c_17841])).

cnf(c_27472,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X2))) = k5_xboole_0(X1,X2) ),
    inference(superposition,[status(thm)],[c_11519,c_15156])).

cnf(c_27515,plain,
    ( k5_xboole_0(k1_tarski(sK25),k5_xboole_0(k5_xboole_0(k1_tarski(sK24),k4_xboole_0(k1_tarski(sK24),k1_tarski(sK25))),k5_xboole_0(k1_tarski(sK24),k4_xboole_0(k4_xboole_0(k1_tarski(sK26),k1_tarski(sK24)),k1_tarski(sK25))))) != k5_xboole_0(k1_tarski(sK24),k5_xboole_0(k1_tarski(sK25),k5_xboole_0(k5_xboole_0(k1_tarski(sK24),k4_xboole_0(k1_tarski(sK24),k1_tarski(sK25))),k4_xboole_0(k4_xboole_0(k1_tarski(sK26),k1_tarski(sK24)),k1_tarski(sK25))))) ),
    inference(demodulation,[status(thm)],[c_27401,c_27472])).

cnf(c_18671,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(superposition,[status(thm)],[c_7,c_15156])).

cnf(c_19420,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X0) = X1 ),
    inference(superposition,[status(thm)],[c_18671,c_18671])).

cnf(c_19856,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X2)) = k5_xboole_0(X1,X2) ),
    inference(superposition,[status(thm)],[c_19420,c_211])).

cnf(c_27516,plain,
    ( k5_xboole_0(k1_tarski(sK24),k5_xboole_0(k1_tarski(sK25),k5_xboole_0(k5_xboole_0(k1_tarski(sK24),k4_xboole_0(k1_tarski(sK24),k1_tarski(sK25))),k4_xboole_0(k4_xboole_0(k1_tarski(sK26),k1_tarski(sK24)),k1_tarski(sK25))))) != k5_xboole_0(k1_tarski(sK25),k5_xboole_0(k4_xboole_0(k1_tarski(sK24),k1_tarski(sK25)),k4_xboole_0(k4_xboole_0(k1_tarski(sK26),k1_tarski(sK24)),k1_tarski(sK25)))) ),
    inference(demodulation,[status(thm)],[c_27515,c_19856])).

cnf(c_27517,plain,
    ( k5_xboole_0(k1_tarski(sK24),k5_xboole_0(k1_tarski(sK25),k5_xboole_0(k1_tarski(sK24),k5_xboole_0(k4_xboole_0(k1_tarski(sK24),k1_tarski(sK25)),k4_xboole_0(k4_xboole_0(k1_tarski(sK26),k1_tarski(sK24)),k1_tarski(sK25)))))) != k5_xboole_0(k1_tarski(sK25),k5_xboole_0(k4_xboole_0(k1_tarski(sK24),k1_tarski(sK25)),k4_xboole_0(k4_xboole_0(k1_tarski(sK26),k1_tarski(sK24)),k1_tarski(sK25)))) ),
    inference(superposition,[status(thm)],[c_211,c_27516])).

cnf(c_27518,plain,
    ( k5_xboole_0(k1_tarski(sK25),k5_xboole_0(k4_xboole_0(k1_tarski(sK24),k1_tarski(sK25)),k4_xboole_0(k4_xboole_0(k1_tarski(sK26),k1_tarski(sK24)),k1_tarski(sK25)))) != k5_xboole_0(k1_tarski(sK25),k5_xboole_0(k4_xboole_0(k1_tarski(sK24),k1_tarski(sK25)),k4_xboole_0(k4_xboole_0(k1_tarski(sK26),k1_tarski(sK24)),k1_tarski(sK25)))) ),
    inference(demodulation,[status(thm)],[c_27517,c_27472])).

cnf(c_27519,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_27518])).

%------------------------------------------------------------------------------
