%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : enumset1__t60_enumset1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:01 EDT 2019

% Result     : Theorem 5.87s
% Output     : Refutation 5.87s
% Verified   : 
% Statistics : Number of formulae       :   30 (  35 expanded)
%              Number of leaves         :    9 (  13 expanded)
%              Depth                    :    8
%              Number of atoms          :   38 (  46 expanded)
%              Number of equality atoms :   26 (  31 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f66777,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2091,f66774,f66776])).

fof(f66776,plain,(
    spl7_3 ),
    inference(avatar_contradiction_clause,[],[f66775])).

fof(f66775,plain,
    ( $false
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f66773,f60789])).

fof(f60789,plain,(
    ! [X158,X156,X154,X159,X157,X155,X153] : k5_enumset1(X153,X154,X155,X156,X157,X158,X159) = k2_xboole_0(k2_tarski(X158,X159),k3_enumset1(X153,X154,X155,X156,X157)) ),
    inference(forward_demodulation,[],[f60653,f28])).

fof(f28,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/enumset1__t60_enumset1.p',l68_enumset1)).

fof(f60653,plain,(
    ! [X158,X156,X154,X159,X157,X155,X153] : k2_xboole_0(k2_tarski(X158,X159),k3_enumset1(X153,X154,X155,X156,X157)) = k2_xboole_0(k2_enumset1(X153,X154,X155,X156),k1_enumset1(X157,X158,X159)) ),
    inference(superposition,[],[f175,f27])).

fof(f27,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox/benchmark/enumset1__t60_enumset1.p',t50_enumset1)).

fof(f175,plain,(
    ! [X35,X33,X36,X34] : k2_xboole_0(X36,k1_enumset1(X33,X34,X35)) = k2_xboole_0(k2_tarski(X34,X35),k2_xboole_0(X36,k1_tarski(X33))) ),
    inference(superposition,[],[f34,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/enumset1__t60_enumset1.p',t42_enumset1)).

fof(f34,plain,(
    ! [X6,X7,X5] : k2_xboole_0(X5,k2_xboole_0(X6,X7)) = k2_xboole_0(X7,k2_xboole_0(X5,X6)) ),
    inference(superposition,[],[f25,f24])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/enumset1__t60_enumset1.p',commutativity_k2_xboole_0)).

fof(f25,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/enumset1__t60_enumset1.p',t4_xboole_1)).

fof(f66773,plain,
    ( k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k2_tarski(sK5,sK6),k3_enumset1(sK0,sK1,sK2,sK3,sK4))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f66772])).

fof(f66772,plain,
    ( spl7_3
  <=> k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k2_tarski(sK5,sK6),k3_enumset1(sK0,sK1,sK2,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f66774,plain,
    ( ~ spl7_3
    | spl7_1 ),
    inference(avatar_split_clause,[],[f20727,f2089,f66772])).

fof(f2089,plain,
    ( spl7_1
  <=> k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k2_tarski(sK5,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f20727,plain,
    ( k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k2_tarski(sK5,sK6),k3_enumset1(sK0,sK1,sK2,sK3,sK4))
    | ~ spl7_1 ),
    inference(superposition,[],[f2090,f24])).

fof(f2090,plain,
    ( k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k2_tarski(sK5,sK6))
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f2089])).

fof(f2091,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f21,f2089])).

fof(f21,plain,(
    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k2_tarski(sK5,sK6)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k2_tarski(sK5,sK6)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f18,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))
   => k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k2_tarski(sK5,sK6)) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/enumset1__t60_enumset1.p',t60_enumset1)).
%------------------------------------------------------------------------------
