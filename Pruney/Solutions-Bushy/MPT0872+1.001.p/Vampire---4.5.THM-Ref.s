%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0872+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:48 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   13 (  15 expanded)
%              Number of leaves         :    4 (   5 expanded)
%              Depth                    :    6
%              Number of atoms          :   14 (  16 expanded)
%              Number of equality atoms :   13 (  15 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f12])).

fof(f12,plain,(
    k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3) != k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3) ),
    inference(definition_unfolding,[],[f8,f11,f9])).

fof(f9,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f11,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f10,f9])).

fof(f10,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_mcart_1)).

fof(f8,plain,(
    k4_mcart_1(sK0,sK1,sK2,sK3) != k3_mcart_1(k4_tarski(sK0,sK1),sK2,sK3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    k4_mcart_1(sK0,sK1,sK2,sK3) != k3_mcart_1(k4_tarski(sK0,sK1),sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f5,f6])).

fof(f6,plain,
    ( ? [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) != k3_mcart_1(k4_tarski(X0,X1),X2,X3)
   => k4_mcart_1(sK0,sK1,sK2,sK3) != k3_mcart_1(k4_tarski(sK0,sK1),sK2,sK3) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) != k3_mcart_1(k4_tarski(X0,X1),X2,X3) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k3_mcart_1(k4_tarski(X0,X1),X2,X3) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k3_mcart_1(k4_tarski(X0,X1),X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_mcart_1)).

%------------------------------------------------------------------------------
