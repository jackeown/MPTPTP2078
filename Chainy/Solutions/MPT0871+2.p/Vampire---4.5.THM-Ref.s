%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0871+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:55 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   13 (  13 expanded)
%              Number of leaves         :    4 (   4 expanded)
%              Depth                    :    6
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2040,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f1939])).

fof(f1939,plain,(
    k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3) != k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3) ),
    inference(definition_unfolding,[],[f1632,f1938])).

fof(f1938,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f1721,f1934])).

fof(f1934,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1274])).

fof(f1274,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f1721,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f1275])).

fof(f1275,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_mcart_1)).

fof(f1632,plain,(
    k4_mcart_1(sK0,sK1,sK2,sK3) != k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3) ),
    inference(cnf_transformation,[],[f1483])).

fof(f1483,plain,(
    k4_mcart_1(sK0,sK1,sK2,sK3) != k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f1326,f1482])).

fof(f1482,plain,
    ( ? [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) != k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)
   => k4_mcart_1(sK0,sK1,sK2,sK3) != k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3) ),
    introduced(choice_axiom,[])).

fof(f1326,plain,(
    ? [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) != k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    inference(ennf_transformation,[],[f1316])).

fof(f1316,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    inference(negated_conjecture,[],[f1315])).

fof(f1315,conjecture,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_mcart_1)).
%------------------------------------------------------------------------------
