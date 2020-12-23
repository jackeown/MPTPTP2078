%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0936+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:58 EST 2020

% Result     : Theorem 1.73s
% Output     : Refutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :   15 (  21 expanded)
%              Number of leaves         :    5 (   8 expanded)
%              Depth                    :    6
%              Number of atoms          :   16 (  22 expanded)
%              Number of equality atoms :   15 (  21 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2430,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2174,f2193])).

fof(f2193,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_tarski(X0,X3) = k1_relat_1(k1_relat_1(k2_tarski(k4_tarski(k4_tarski(X0,X1),X2),k4_tarski(k4_tarski(X3,X4),X5)))) ),
    inference(definition_unfolding,[],[f1970,f2024,f2024])).

fof(f2024,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1280])).

fof(f1280,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f1970,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k1_relat_1(k1_relat_1(k2_tarski(k3_mcart_1(X0,X1,X2),k3_mcart_1(X3,X4,X5)))) = k2_tarski(X0,X3) ),
    inference(cnf_transformation,[],[f1415])).

fof(f1415,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k1_relat_1(k1_relat_1(k2_tarski(k3_mcart_1(X0,X1,X2),k3_mcart_1(X3,X4,X5)))) = k2_tarski(X0,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_mcart_1)).

fof(f2174,plain,(
    k2_tarski(sK0,sK0) != k1_relat_1(k1_relat_1(k2_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2)))) ),
    inference(definition_unfolding,[],[f1786,f2168,f2168,f2024])).

fof(f2168,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f254])).

fof(f254,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f1786,plain,(
    k1_tarski(sK0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(sK0,sK1,sK2)))) ),
    inference(cnf_transformation,[],[f1625])).

fof(f1625,plain,(
    k1_tarski(sK0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(sK0,sK1,sK2)))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f1420,f1624])).

fof(f1624,plain,
    ( ? [X0,X1,X2] : k1_tarski(X0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2))))
   => k1_tarski(sK0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(sK0,sK1,sK2)))) ),
    introduced(choice_axiom,[])).

fof(f1420,plain,(
    ? [X0,X1,X2] : k1_tarski(X0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2)))) ),
    inference(ennf_transformation,[],[f1417])).

fof(f1417,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_tarski(X0) = k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2)))) ),
    inference(negated_conjecture,[],[f1416])).

fof(f1416,conjecture,(
    ! [X0,X1,X2] : k1_tarski(X0) = k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2)))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_mcart_1)).
%------------------------------------------------------------------------------
