%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : enumset1__t55_enumset1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:01 EDT 2019

% Result     : Theorem 10.25s
% Output     : Refutation 10.25s
% Verified   : 
% Statistics : Number of formulae       :   37 (  53 expanded)
%              Number of leaves         :   11 (  20 expanded)
%              Depth                    :    8
%              Number of atoms          :   48 (  71 expanded)
%              Number of equality atoms :   32 (  48 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f114724,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2091,f43436,f98202,f114723])).

fof(f114723,plain,(
    spl6_1 ),
    inference(avatar_contradiction_clause,[],[f114722])).

fof(f114722,plain,
    ( $false
    | ~ spl6_1 ),
    inference(trivial_inequality_removal,[],[f114716])).

fof(f114716,plain,
    ( k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5)
    | ~ spl6_1 ),
    inference(superposition,[],[f2090,f77548])).

fof(f77548,plain,(
    ! [X6,X10,X8,X7,X11,X9] : k4_enumset1(X9,X10,X11,X6,X7,X8) = k2_xboole_0(k3_enumset1(X9,X10,X11,X6,X7),k1_tarski(X8)) ),
    inference(forward_demodulation,[],[f77364,f27])).

fof(f27,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t55_enumset1.p',l62_enumset1)).

fof(f77364,plain,(
    ! [X6,X10,X8,X7,X11,X9] : k2_xboole_0(k3_enumset1(X9,X10,X11,X6,X7),k1_tarski(X8)) = k2_xboole_0(k1_enumset1(X9,X10,X11),k1_enumset1(X6,X7,X8)) ),
    inference(superposition,[],[f20569,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t55_enumset1.p',t43_enumset1)).

fof(f20569,plain,(
    ! [X21,X19,X17,X20,X18,X16] : k2_xboole_0(k3_enumset1(X16,X17,X18,X19,X20),X21) = k2_xboole_0(k1_enumset1(X16,X17,X18),k2_xboole_0(k2_tarski(X19,X20),X21)) ),
    inference(superposition,[],[f25,f26])).

fof(f26,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t55_enumset1.p',l57_enumset1)).

fof(f25,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t55_enumset1.p',t4_xboole_1)).

fof(f2090,plain,
    ( k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k1_tarski(sK5))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f2089])).

fof(f2089,plain,
    ( spl6_1
  <=> k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k1_tarski(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f98202,plain,
    ( ~ spl6_5
    | spl6_1 ),
    inference(avatar_split_clause,[],[f98191,f2089,f98200])).

fof(f98200,plain,
    ( spl6_5
  <=> k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k4_enumset1(sK0,sK1,sK2,sK4,sK3,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f98191,plain,
    ( k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k4_enumset1(sK0,sK1,sK2,sK4,sK3,sK5)
    | ~ spl6_1 ),
    inference(superposition,[],[f2090,f77547])).

fof(f77547,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X3,X4,X5,X1,X0,X2) = k2_xboole_0(k3_enumset1(X3,X4,X5,X0,X1),k1_tarski(X2)) ),
    inference(forward_demodulation,[],[f77363,f27])).

fof(f77363,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k3_enumset1(X3,X4,X5,X0,X1),k1_tarski(X2)) = k2_xboole_0(k1_enumset1(X3,X4,X5),k1_enumset1(X1,X0,X2)) ),
    inference(superposition,[],[f20569,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_tarski(X1,X0),k1_tarski(X2)) = k1_enumset1(X0,X1,X2) ),
    inference(superposition,[],[f24,f23])).

fof(f23,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t55_enumset1.p',commutativity_k2_tarski)).

fof(f43436,plain,
    ( ~ spl6_3
    | spl6_1 ),
    inference(avatar_split_clause,[],[f8539,f2089,f43434])).

fof(f43434,plain,
    ( spl6_3
  <=> k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k1_tarski(sK5),k3_enumset1(sK0,sK1,sK2,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f8539,plain,
    ( k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k1_tarski(sK5),k3_enumset1(sK0,sK1,sK2,sK3,sK4))
    | ~ spl6_1 ),
    inference(superposition,[],[f2090,f22])).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t55_enumset1.p',commutativity_k2_xboole_0)).

fof(f2091,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f20,f2089])).

fof(f20,plain,(
    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k1_tarski(sK5)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k1_tarski(sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f17,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))
   => k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k1_tarski(sK5)) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t55_enumset1.p',t55_enumset1)).
%------------------------------------------------------------------------------
