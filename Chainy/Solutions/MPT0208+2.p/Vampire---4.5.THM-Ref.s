%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0208+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:16 EST 2020

% Result     : Theorem 8.07s
% Output     : Refutation 8.07s
% Verified   : 
% Statistics : Number of formulae       :   29 (  44 expanded)
%              Number of leaves         :    9 (  16 expanded)
%              Depth                    :    7
%              Number of atoms          :   30 (  45 expanded)
%              Number of equality atoms :   29 (  44 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f993,plain,(
    $false ),
    inference(subsumption_resolution,[],[f988,f895])).

fof(f895,plain,(
    ! [X30,X28,X35,X33,X31,X29,X36,X34,X32] : k2_xboole_0(k6_enumset1(X28,X29,X30,X31,X32,X33,X34,X35),X36) = k2_xboole_0(k6_enumset1(X28,X28,X29,X30,X31,X32,X33,X34),k2_xboole_0(k1_enumset1(X35,X35,X35),X36)) ),
    inference(forward_demodulation,[],[f881,f329])).

fof(f329,plain,(
    ! [X0] : k1_enumset1(X0,X0,X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f296,f295])).

fof(f295,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f262])).

fof(f262,axiom,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_enumset1)).

fof(f296,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(cnf_transformation,[],[f256])).

fof(f256,axiom,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_enumset1)).

fof(f881,plain,(
    ! [X30,X28,X35,X33,X31,X29,X36,X34,X32] : k2_xboole_0(k6_enumset1(X28,X29,X30,X31,X32,X33,X34,X35),X36) = k2_xboole_0(k6_enumset1(X28,X28,X29,X30,X31,X32,X33,X34),k2_xboole_0(k2_enumset1(X35,X35,X35,X35),X36)) ),
    inference(superposition,[],[f286,f325])).

fof(f325,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k2_enumset1(X7,X7,X7,X7)) ),
    inference(definition_unfolding,[],[f298,f306,f295])).

fof(f306,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f255])).

fof(f255,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f298,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    inference(cnf_transformation,[],[f248])).

fof(f248,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_enumset1)).

fof(f286,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f113])).

fof(f113,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f988,plain,(
    k2_xboole_0(k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7),k2_enumset1(sK8,sK8,sK8,sK8)) != k2_xboole_0(k6_enumset1(sK0,sK0,sK1,sK2,sK3,sK4,sK5,sK6),k2_xboole_0(k1_enumset1(sK7,sK7,sK7),k2_enumset1(sK8,sK8,sK8,sK8))) ),
    inference(superposition,[],[f326,f329])).

fof(f326,plain,(
    k2_xboole_0(k6_enumset1(sK0,sK0,sK1,sK2,sK3,sK4,sK5,sK6),k2_xboole_0(k2_enumset1(sK7,sK7,sK7,sK7),k2_enumset1(sK8,sK8,sK8,sK8))) != k2_xboole_0(k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7),k2_enumset1(sK8,sK8,sK8,sK8)) ),
    inference(definition_unfolding,[],[f283,f322,f295])).

fof(f322,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k2_xboole_0(k2_enumset1(X7,X7,X7,X7),k2_enumset1(X8,X8,X8,X8))) ),
    inference(definition_unfolding,[],[f313,f306,f321])).

fof(f321,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) ),
    inference(definition_unfolding,[],[f294,f295,f295])).

fof(f294,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f221])).

fof(f221,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(f313,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) ),
    inference(cnf_transformation,[],[f218])).

fof(f218,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t133_enumset1)).

fof(f283,plain,(
    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7),k1_tarski(sK8)) ),
    inference(cnf_transformation,[],[f282])).

fof(f282,plain,(
    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7),k1_tarski(sK8)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f280,f281])).

fof(f281,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8))
   => k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7),k1_tarski(sK8)) ),
    introduced(choice_axiom,[])).

fof(f280,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) ),
    inference(ennf_transformation,[],[f220])).

fof(f220,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) ),
    inference(negated_conjecture,[],[f219])).

fof(f219,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_enumset1)).
%------------------------------------------------------------------------------
