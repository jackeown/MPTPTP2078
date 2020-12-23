%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : enumset1__t127_enumset1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:35:57 EDT 2019

% Result     : Theorem 16.51s
% Output     : Refutation 16.51s
% Verified   : 
% Statistics : Number of formulae       :   24 (  25 expanded)
%              Number of leaves         :    7 (   8 expanded)
%              Depth                    :    8
%              Number of atoms          :   29 (  31 expanded)
%              Number of equality atoms :   21 (  22 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f199922,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2738,f199920])).

fof(f199920,plain,(
    spl9_1 ),
    inference(avatar_contradiction_clause,[],[f199919])).

fof(f199919,plain,
    ( $false
    | ~ spl9_1 ),
    inference(trivial_inequality_removal,[],[f199892])).

fof(f199892,plain,
    ( k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)
    | ~ spl9_1 ),
    inference(superposition,[],[f2737,f80779])).

fof(f80779,plain,(
    ! [X6,X12,X10,X8,X7,X5,X13,X11,X9] : k7_enumset1(X13,X5,X6,X7,X8,X9,X10,X11,X12) = k2_xboole_0(k1_tarski(X13),k6_enumset1(X5,X6,X7,X8,X9,X10,X11,X12)) ),
    inference(forward_demodulation,[],[f80586,f26])).

fof(f26,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t127_enumset1.p',l142_enumset1)).

fof(f80586,plain,(
    ! [X6,X12,X10,X8,X7,X5,X13,X11,X9] : k2_xboole_0(k1_tarski(X13),k6_enumset1(X5,X6,X7,X8,X9,X10,X11,X12)) = k2_xboole_0(k2_enumset1(X13,X5,X6,X7),k3_enumset1(X8,X9,X10,X11,X12)) ),
    inference(superposition,[],[f2362,f25])).

fof(f25,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_enumset1(X0,X1,X2),k3_enumset1(X3,X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_enumset1(X0,X1,X2),k3_enumset1(X3,X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t127_enumset1.p',t64_enumset1)).

fof(f2362,plain,(
    ! [X12,X10,X8,X11,X9] : k2_xboole_0(k2_enumset1(X8,X9,X10,X11),X12) = k2_xboole_0(k1_tarski(X8),k2_xboole_0(k1_enumset1(X9,X10,X11),X12)) ),
    inference(superposition,[],[f23,f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t127_enumset1.p',t44_enumset1)).

fof(f23,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t127_enumset1.p',t4_xboole_1)).

fof(f2737,plain,
    ( k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k1_tarski(sK0),k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8))
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f2736])).

fof(f2736,plain,
    ( spl9_1
  <=> k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k1_tarski(sK0),k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f2738,plain,(
    ~ spl9_1 ),
    inference(avatar_split_clause,[],[f20,f2736])).

fof(f20,plain,(
    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k1_tarski(sK0),k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k1_tarski(sK0),k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f17,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))
   => k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k1_tarski(sK0),k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t127_enumset1.p',t127_enumset1)).
%------------------------------------------------------------------------------
