%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0173+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:14 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   19 (  24 expanded)
%              Number of leaves         :    6 (   8 expanded)
%              Depth                    :    6
%              Number of atoms          :   20 (  25 expanded)
%              Number of equality atoms :   19 (  24 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f908,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f752])).

fof(f752,plain,(
    k5_xboole_0(k5_xboole_0(k4_enumset1(sK17,sK17,sK17,sK17,sK17,sK18),k1_tarski(sK19)),k3_xboole_0(k4_enumset1(sK17,sK17,sK17,sK17,sK17,sK18),k1_tarski(sK19))) != k5_xboole_0(k5_xboole_0(k4_enumset1(sK17,sK17,sK17,sK17,sK17,sK18),k1_tarski(sK19)),k3_xboole_0(k4_enumset1(sK17,sK17,sK17,sK17,sK17,sK18),k1_tarski(sK19))) ),
    inference(definition_unfolding,[],[f460,f745,f743])).

fof(f743,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k5_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)),k3_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6))) ),
    inference(definition_unfolding,[],[f461,f633])).

fof(f633,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f166])).

fof(f166,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f461,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    inference(cnf_transformation,[],[f210])).

fof(f210,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_enumset1)).

fof(f745,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_xboole_0(k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X1),k1_tarski(X2)),k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X1),k1_tarski(X2))) ),
    inference(definition_unfolding,[],[f486,f744])).

fof(f744,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_xboole_0(k5_xboole_0(k4_enumset1(X0,X0,X0,X1,X2,X3),k1_tarski(X4)),k3_xboole_0(k4_enumset1(X0,X0,X0,X1,X2,X3),k1_tarski(X4))) ),
    inference(definition_unfolding,[],[f469,f743])).

fof(f469,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f229])).

fof(f229,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_enumset1)).

fof(f486,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f227])).

fof(f227,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_enumset1)).

fof(f460,plain,(
    k1_enumset1(sK17,sK18,sK19) != k5_enumset1(sK17,sK17,sK17,sK17,sK17,sK18,sK19) ),
    inference(cnf_transformation,[],[f370])).

fof(f370,plain,(
    k1_enumset1(sK17,sK18,sK19) != k5_enumset1(sK17,sK17,sK17,sK17,sK17,sK18,sK19) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK17,sK18,sK19])],[f245,f369])).

fof(f369,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k5_enumset1(X0,X0,X0,X0,X0,X1,X2)
   => k1_enumset1(sK17,sK18,sK19) != k5_enumset1(sK17,sK17,sK17,sK17,sK17,sK18,sK19) ),
    introduced(choice_axiom,[])).

fof(f245,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(ennf_transformation,[],[f239])).

fof(f239,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(negated_conjecture,[],[f238])).

fof(f238,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_enumset1)).
%------------------------------------------------------------------------------
