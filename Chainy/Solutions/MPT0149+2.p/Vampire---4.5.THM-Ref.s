%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0149+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:12 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   19 (  43 expanded)
%              Number of leaves         :    6 (  15 expanded)
%              Depth                    :    6
%              Number of atoms          :   20 (  44 expanded)
%              Number of equality atoms :   19 (  43 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f494,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f454])).

fof(f454,plain,(
    k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK15),k1_tarski(sK16)),k1_tarski(sK17)),k1_tarski(sK18)),k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK19),k1_tarski(sK20)),k1_tarski(sK21)),k1_tarski(sK22))) != k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK15),k1_tarski(sK16)),k1_tarski(sK17)),k1_tarski(sK18)),k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK19),k1_tarski(sK20)),k1_tarski(sK21)),k1_tarski(sK22))) ),
    inference(definition_unfolding,[],[f328,f450,f449,f449])).

fof(f449,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2)),k1_tarski(X3)) ),
    inference(definition_unfolding,[],[f335,f448])).

fof(f448,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2)) ),
    inference(definition_unfolding,[],[f343,f351])).

fof(f351,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f190])).

fof(f190,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(f343,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f192])).

fof(f192,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

fof(f335,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f195])).

fof(f195,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

fof(f450,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2)),k1_tarski(X3)),k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X4),k1_tarski(X5)),k1_tarski(X6)),k1_tarski(X7))) ),
    inference(definition_unfolding,[],[f339,f449,f449])).

fof(f339,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f189])).

fof(f189,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l75_enumset1)).

fof(f328,plain,(
    k6_enumset1(sK15,sK16,sK17,sK18,sK19,sK20,sK21,sK22) != k2_xboole_0(k2_enumset1(sK15,sK16,sK17,sK18),k2_enumset1(sK19,sK20,sK21,sK22)) ),
    inference(cnf_transformation,[],[f256])).

fof(f256,plain,(
    k6_enumset1(sK15,sK16,sK17,sK18,sK19,sK20,sK21,sK22) != k2_xboole_0(k2_enumset1(sK15,sK16,sK17,sK18),k2_enumset1(sK19,sK20,sK21,sK22)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15,sK16,sK17,sK18,sK19,sK20,sK21,sK22])],[f219,f255])).

fof(f255,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))
   => k6_enumset1(sK15,sK16,sK17,sK18,sK19,sK20,sK21,sK22) != k2_xboole_0(k2_enumset1(sK15,sK16,sK17,sK18),k2_enumset1(sK19,sK20,sK21,sK22)) ),
    introduced(choice_axiom,[])).

fof(f219,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    inference(ennf_transformation,[],[f215])).

fof(f215,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    inference(negated_conjecture,[],[f214])).

fof(f214,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_enumset1)).
%------------------------------------------------------------------------------
