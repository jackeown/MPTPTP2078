%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0168+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:14 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   21 (  28 expanded)
%              Number of leaves         :    7 (  10 expanded)
%              Depth                    :    6
%              Number of atoms          :   22 (  29 expanded)
%              Number of equality atoms :   21 (  28 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f874,plain,(
    $false ),
    inference(subsumption_resolution,[],[f731,f740])).

fof(f740,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_xboole_0(k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),k1_enumset1(X2,X2,X2)),k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),k1_enumset1(X2,X2,X2))) ),
    inference(definition_unfolding,[],[f478,f726])).

fof(f726,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k5_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k1_enumset1(X3,X3,X3)),k3_xboole_0(k3_enumset1(X0,X0,X0,X1,X2),k1_enumset1(X3,X3,X3))) ),
    inference(definition_unfolding,[],[f463,f725])).

fof(f725,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_xboole_0(k5_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X5,X5)),k3_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X5,X5))) ),
    inference(definition_unfolding,[],[f456,f615,f480])).

fof(f480,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(cnf_transformation,[],[f225])).

fof(f225,axiom,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_enumset1)).

fof(f615,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f166])).

fof(f166,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f456,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(cnf_transformation,[],[f204])).

fof(f204,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).

fof(f463,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f228])).

fof(f228,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_enumset1)).

fof(f478,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f220])).

fof(f220,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f731,plain,(
    k1_enumset1(sK17,sK18,sK19) != k5_xboole_0(k5_xboole_0(k3_enumset1(sK17,sK17,sK17,sK17,sK18),k1_enumset1(sK19,sK19,sK19)),k3_xboole_0(k3_enumset1(sK17,sK17,sK17,sK17,sK18),k1_enumset1(sK19,sK19,sK19))) ),
    inference(definition_unfolding,[],[f455,f725])).

fof(f455,plain,(
    k1_enumset1(sK17,sK18,sK19) != k4_enumset1(sK17,sK17,sK17,sK17,sK18,sK19) ),
    inference(cnf_transformation,[],[f365])).

% (4649)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_6 on theBenchmark
fof(f365,plain,(
    k1_enumset1(sK17,sK18,sK19) != k4_enumset1(sK17,sK17,sK17,sK17,sK18,sK19) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK17,sK18,sK19])],[f240,f364])).

fof(f364,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k4_enumset1(X0,X0,X0,X0,X1,X2)
   => k1_enumset1(sK17,sK18,sK19) != k4_enumset1(sK17,sK17,sK17,sK17,sK18,sK19) ),
    introduced(choice_axiom,[])).

fof(f240,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(ennf_transformation,[],[f234])).

fof(f234,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(negated_conjecture,[],[f233])).

fof(f233,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_enumset1)).
%------------------------------------------------------------------------------
