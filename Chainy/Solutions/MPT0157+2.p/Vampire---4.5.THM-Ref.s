%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0157+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:13 EST 2020

% Result     : Theorem 1.29s
% Output     : Refutation 1.29s
% Verified   : 
% Statistics : Number of formulae       :   17 (  21 expanded)
%              Number of leaves         :    5 (   7 expanded)
%              Depth                    :    7
%              Number of atoms          :   18 (  22 expanded)
%              Number of equality atoms :   17 (  21 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f405,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f404])).

fof(f404,plain,(
    k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k1_tarski(sK4)) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k1_tarski(sK4)) ),
    inference(forward_demodulation,[],[f356,f355])).

fof(f355,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_enumset1(X0,X0,X1,X2),k1_tarski(X3)) ),
    inference(definition_unfolding,[],[f351,f346])).

fof(f346,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(cnf_transformation,[],[f199])).

fof(f199,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).

fof(f351,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f221])).

fof(f221,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f356,plain,(
    k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k1_tarski(sK4)) != k2_xboole_0(k2_xboole_0(k2_enumset1(sK0,sK0,sK1,sK2),k1_tarski(sK3)),k1_tarski(sK4)) ),
    inference(definition_unfolding,[],[f262,f346,f352])).

fof(f352,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)),k1_tarski(X5)) ),
    inference(definition_unfolding,[],[f336,f346])).

fof(f336,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(cnf_transformation,[],[f204])).

fof(f204,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).

fof(f262,plain,(
    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k4_enumset1(sK0,sK0,sK1,sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f251])).

fof(f251,plain,(
    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k4_enumset1(sK0,sK0,sK1,sK2,sK3,sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f226,f250])).

fof(f250,plain,
    ( ? [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) != k4_enumset1(X0,X0,X1,X2,X3,X4)
   => k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k4_enumset1(sK0,sK0,sK1,sK2,sK3,sK4) ),
    introduced(choice_axiom,[])).

fof(f226,plain,(
    ? [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) != k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(ennf_transformation,[],[f223])).

fof(f223,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(negated_conjecture,[],[f222])).

fof(f222,conjecture,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
%------------------------------------------------------------------------------
