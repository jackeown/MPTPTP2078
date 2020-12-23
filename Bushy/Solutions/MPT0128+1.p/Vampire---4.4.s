%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : enumset1__t44_enumset1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:35:59 EDT 2019

% Result     : Theorem 0.71s
% Output     : Refutation 0.71s
% Verified   : 
% Statistics : Number of formulae       :   29 (  36 expanded)
%              Number of leaves         :    8 (  12 expanded)
%              Depth                    :    8
%              Number of atoms          :   34 (  42 expanded)
%              Number of equality atoms :   26 (  33 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12675,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f12656])).

fof(f12656,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f12655])).

fof(f12655,plain,
    ( $false
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f12599,f6231])).

fof(f6231,plain,(
    ! [X10,X8,X11,X9] : k2_enumset1(X8,X9,X10,X11) = k2_enumset1(X8,X9,X11,X10) ),
    inference(superposition,[],[f600,f26])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t44_enumset1.p',l53_enumset1)).

fof(f600,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X2,X3,X0,X1) = k2_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X0)) ),
    inference(superposition,[],[f26,f22])).

fof(f22,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t44_enumset1.p',commutativity_k2_tarski)).

fof(f12599,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK1,sK3,sK2)
    | ~ spl4_1 ),
    inference(superposition,[],[f46,f3220])).

fof(f3220,plain,(
    ! [X12,X10,X11,X9] : k2_enumset1(X12,X9,X10,X11) = k2_xboole_0(k1_tarski(X12),k1_enumset1(X9,X11,X10)) ),
    inference(forward_demodulation,[],[f3133,f26])).

fof(f3133,plain,(
    ! [X12,X10,X11,X9] : k2_xboole_0(k1_tarski(X12),k1_enumset1(X9,X11,X10)) = k2_xboole_0(k2_tarski(X12,X9),k2_tarski(X10,X11)) ),
    inference(superposition,[],[f52,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] : k1_enumset1(X2,X0,X1) = k2_xboole_0(k1_tarski(X2),k2_tarski(X1,X0)) ),
    inference(superposition,[],[f25,f22])).

fof(f25,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t44_enumset1.p',t42_enumset1)).

fof(f52,plain,(
    ! [X12,X13,X11] : k2_xboole_0(k2_tarski(X11,X12),X13) = k2_xboole_0(k1_tarski(X11),k2_xboole_0(k1_tarski(X12),X13)) ),
    inference(superposition,[],[f24,f23])).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t44_enumset1.p',t41_enumset1)).

fof(f24,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t44_enumset1.p',t4_xboole_1)).

fof(f46,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK2,sK3))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl4_1
  <=> k2_enumset1(sK0,sK1,sK2,sK3) != k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f47,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f19,f45])).

fof(f19,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK2,sK3)) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t44_enumset1.p',t44_enumset1)).
%------------------------------------------------------------------------------
