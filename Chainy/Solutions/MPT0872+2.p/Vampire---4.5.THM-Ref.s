%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0872+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:55 EST 2020

% Result     : Theorem 1.33s
% Output     : Refutation 1.33s
% Verified   : 
% Statistics : Number of formulae       :   12 (  12 expanded)
%              Number of leaves         :    4 (   4 expanded)
%              Depth                    :    6
%              Number of atoms          :   13 (  13 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2042,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f1940])).

fof(f1940,plain,(
    k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3) != k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3) ),
    inference(definition_unfolding,[],[f1633,f1729,f1637])).

% (30783)ott+11_8:1_av=off:bs=on:bce=on:fde=none:gsp=input_only:gs=on:gsem=on:irw=on:lcm=predicate:nm=6:nwc=1.5:sd=2:ss=axioms:st=1.2:sos=theory:urr=on:updr=off_49 on theBenchmark
fof(f1637,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1274])).

fof(f1274,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f1729,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    inference(cnf_transformation,[],[f1315])).

fof(f1315,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_mcart_1)).

fof(f1633,plain,(
    k4_mcart_1(sK0,sK1,sK2,sK3) != k3_mcart_1(k4_tarski(sK0,sK1),sK2,sK3) ),
    inference(cnf_transformation,[],[f1484])).

fof(f1484,plain,(
    k4_mcart_1(sK0,sK1,sK2,sK3) != k3_mcart_1(k4_tarski(sK0,sK1),sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f1327,f1483])).

fof(f1483,plain,
    ( ? [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) != k3_mcart_1(k4_tarski(X0,X1),X2,X3)
   => k4_mcart_1(sK0,sK1,sK2,sK3) != k3_mcart_1(k4_tarski(sK0,sK1),sK2,sK3) ),
    introduced(choice_axiom,[])).

fof(f1327,plain,(
    ? [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) != k3_mcart_1(k4_tarski(X0,X1),X2,X3) ),
    inference(ennf_transformation,[],[f1317])).

fof(f1317,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k3_mcart_1(k4_tarski(X0,X1),X2,X3) ),
    inference(negated_conjecture,[],[f1316])).

fof(f1316,conjecture,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k3_mcart_1(k4_tarski(X0,X1),X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_mcart_1)).
%------------------------------------------------------------------------------
