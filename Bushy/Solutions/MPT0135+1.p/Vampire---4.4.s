%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : enumset1__t51_enumset1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:00 EDT 2019

% Result     : Theorem 10.43s
% Output     : Refutation 10.43s
% Verified   : 
% Statistics : Number of formulae       :   24 (  25 expanded)
%              Number of leaves         :    7 (   8 expanded)
%              Depth                    :    8
%              Number of atoms          :   29 (  31 expanded)
%              Number of equality atoms :   21 (  22 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f113450,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2091,f113449])).

fof(f113449,plain,(
    spl6_1 ),
    inference(avatar_contradiction_clause,[],[f113448])).

fof(f113448,plain,
    ( $false
    | ~ spl6_1 ),
    inference(trivial_inequality_removal,[],[f113443])).

fof(f113443,plain,
    ( k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5)
    | ~ spl6_1 ),
    inference(superposition,[],[f2090,f44713])).

fof(f44713,plain,(
    ! [X28,X26,X24,X29,X27,X25] : k4_enumset1(X29,X24,X25,X26,X27,X28) = k2_xboole_0(k1_tarski(X29),k3_enumset1(X24,X25,X26,X27,X28)) ),
    inference(forward_demodulation,[],[f44478,f27])).

fof(f27,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/enumset1__t51_enumset1.p',l62_enumset1)).

fof(f44478,plain,(
    ! [X28,X26,X24,X29,X27,X25] : k2_xboole_0(k1_tarski(X29),k3_enumset1(X24,X25,X26,X27,X28)) = k2_xboole_0(k1_enumset1(X29,X24,X25),k1_enumset1(X26,X27,X28)) ),
    inference(superposition,[],[f37,f26])).

fof(f26,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/enumset1__t51_enumset1.p',t48_enumset1)).

fof(f37,plain,(
    ! [X10,X8,X11,X9] : k2_xboole_0(k1_enumset1(X8,X9,X10),X11) = k2_xboole_0(k1_tarski(X8),k2_xboole_0(k2_tarski(X9,X10),X11)) ),
    inference(superposition,[],[f25,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/enumset1__t51_enumset1.p',t42_enumset1)).

fof(f25,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/enumset1__t51_enumset1.p',t4_xboole_1)).

fof(f2090,plain,
    ( k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK1,sK2,sK3,sK4,sK5))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f2089])).

fof(f2089,plain,
    ( spl6_1
  <=> k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK1,sK2,sK3,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f2091,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f20,f2089])).

fof(f20,plain,(
    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK1,sK2,sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK1,sK2,sK3,sK4,sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f17,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))
   => k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK1,sK2,sK3,sK4,sK5)) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/enumset1__t51_enumset1.p',t51_enumset1)).
%------------------------------------------------------------------------------
