%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : enumset1__t62_enumset1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:01 EDT 2019

% Result     : Theorem 16.61s
% Output     : Refutation 16.61s
% Verified   : 
% Statistics : Number of formulae       :   24 (  25 expanded)
%              Number of leaves         :    7 (   8 expanded)
%              Depth                    :    8
%              Number of atoms          :   29 (  31 expanded)
%              Number of equality atoms :   21 (  22 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f193834,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2738,f193833])).

fof(f193833,plain,(
    spl8_1 ),
    inference(avatar_contradiction_clause,[],[f193832])).

fof(f193832,plain,
    ( $false
    | ~ spl8_1 ),
    inference(trivial_inequality_removal,[],[f193830])).

fof(f193830,plain,
    ( k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7)
    | ~ spl8_1 ),
    inference(superposition,[],[f2737,f79538])).

fof(f79538,plain,(
    ! [X6,X12,X10,X8,X7,X5,X11,X9] : k6_enumset1(X12,X5,X6,X7,X8,X9,X10,X11) = k2_xboole_0(k1_tarski(X12),k5_enumset1(X5,X6,X7,X8,X9,X10,X11)) ),
    inference(forward_demodulation,[],[f79356,f25])).

fof(f25,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/enumset1__t62_enumset1.p',l75_enumset1)).

fof(f79356,plain,(
    ! [X6,X12,X10,X8,X7,X5,X11,X9] : k2_xboole_0(k1_tarski(X12),k5_enumset1(X5,X6,X7,X8,X9,X10,X11)) = k2_xboole_0(k2_enumset1(X12,X5,X6,X7),k2_enumset1(X8,X9,X10,X11)) ),
    inference(superposition,[],[f2361,f24])).

fof(f24,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/enumset1__t62_enumset1.p',t58_enumset1)).

fof(f2361,plain,(
    ! [X12,X10,X8,X11,X9] : k2_xboole_0(k2_enumset1(X8,X9,X10,X11),X12) = k2_xboole_0(k1_tarski(X8),k2_xboole_0(k1_enumset1(X9,X10,X11),X12)) ),
    inference(superposition,[],[f22,f23])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/enumset1__t62_enumset1.p',t44_enumset1)).

fof(f22,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/enumset1__t62_enumset1.p',t4_xboole_1)).

fof(f2737,plain,
    ( k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k1_tarski(sK0),k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7))
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f2736])).

fof(f2736,plain,
    ( spl8_1
  <=> k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k1_tarski(sK0),k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f2738,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f19,f2736])).

fof(f19,plain,(
    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k1_tarski(sK0),k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k1_tarski(sK0),k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f16,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7))
   => k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k1_tarski(sK0),k5_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7)) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/enumset1__t62_enumset1.p',t62_enumset1)).
%------------------------------------------------------------------------------
