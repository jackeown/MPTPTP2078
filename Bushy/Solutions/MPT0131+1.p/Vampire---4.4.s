%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : enumset1__t47_enumset1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:00 EDT 2019

% Result     : Theorem 6.75s
% Output     : Refutation 6.75s
% Verified   : 
% Statistics : Number of formulae       :   24 (  25 expanded)
%              Number of leaves         :    7 (   8 expanded)
%              Depth                    :    8
%              Number of atoms          :   29 (  31 expanded)
%              Number of equality atoms :   21 (  22 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f81556,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2091,f81545])).

fof(f81545,plain,(
    spl5_1 ),
    inference(avatar_contradiction_clause,[],[f81544])).

fof(f81544,plain,
    ( $false
    | ~ spl5_1 ),
    inference(trivial_inequality_removal,[],[f81521])).

fof(f81521,plain,
    ( k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k3_enumset1(sK0,sK1,sK2,sK3,sK4)
    | ~ spl5_1 ),
    inference(superposition,[],[f2090,f13310])).

fof(f13310,plain,(
    ! [X12,X10,X8,X11,X9] : k3_enumset1(X12,X8,X9,X10,X11) = k2_xboole_0(k1_tarski(X12),k2_enumset1(X8,X9,X10,X11)) ),
    inference(forward_demodulation,[],[f13151,f27])).

fof(f27,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t47_enumset1.p',l57_enumset1)).

fof(f13151,plain,(
    ! [X12,X10,X8,X11,X9] : k2_xboole_0(k1_tarski(X12),k2_enumset1(X8,X9,X10,X11)) = k2_xboole_0(k1_enumset1(X12,X8,X9),k2_tarski(X10,X11)) ),
    inference(superposition,[],[f37,f26])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t47_enumset1.p',l53_enumset1)).

fof(f37,plain,(
    ! [X10,X8,X11,X9] : k2_xboole_0(k1_enumset1(X8,X9,X10),X11) = k2_xboole_0(k1_tarski(X8),k2_xboole_0(k2_tarski(X9,X10),X11)) ),
    inference(superposition,[],[f25,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t47_enumset1.p',t42_enumset1)).

fof(f25,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t47_enumset1.p',t4_xboole_1)).

fof(f2090,plain,
    ( k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k2_xboole_0(k1_tarski(sK0),k2_enumset1(sK1,sK2,sK3,sK4))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f2089])).

fof(f2089,plain,
    ( spl5_1
  <=> k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k2_xboole_0(k1_tarski(sK0),k2_enumset1(sK1,sK2,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f2091,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f20,f2089])).

fof(f20,plain,(
    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k2_xboole_0(k1_tarski(sK0),k2_enumset1(sK1,sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k2_xboole_0(k1_tarski(sK0),k2_enumset1(sK1,sK2,sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f17,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) != k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))
   => k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k2_xboole_0(k1_tarski(sK0),k2_enumset1(sK1,sK2,sK3,sK4)) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) != k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t47_enumset1.p',t47_enumset1)).
%------------------------------------------------------------------------------
