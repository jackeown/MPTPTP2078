%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : enumset1__t61_enumset1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:01 EDT 2019

% Result     : Theorem 6.24s
% Output     : Refutation 6.24s
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
fof(f68449,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2092,f68446,f68448])).

fof(f68448,plain,(
    spl7_3 ),
    inference(avatar_contradiction_clause,[],[f68447])).

fof(f68447,plain,
    ( $false
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f68445,f60581])).

fof(f60581,plain,(
    ! [X156,X154,X152,X151,X157,X155,X153] : k5_enumset1(X151,X152,X153,X154,X155,X156,X157) = k2_xboole_0(k1_tarski(X157),k4_enumset1(X151,X152,X153,X154,X155,X156)) ),
    inference(forward_demodulation,[],[f60443,f28])).

fof(f28,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/enumset1__t61_enumset1.p',l68_enumset1)).

fof(f60443,plain,(
    ! [X156,X154,X152,X151,X157,X155,X153] : k2_xboole_0(k1_tarski(X157),k4_enumset1(X151,X152,X153,X154,X155,X156)) = k2_xboole_0(k2_enumset1(X151,X152,X153,X154),k1_enumset1(X155,X156,X157)) ),
    inference(superposition,[],[f175,f27])).

fof(f27,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/enumset1__t61_enumset1.p',t54_enumset1)).

fof(f175,plain,(
    ! [X35,X33,X36,X34] : k2_xboole_0(X36,k1_enumset1(X33,X34,X35)) = k2_xboole_0(k1_tarski(X35),k2_xboole_0(X36,k2_tarski(X33,X34))) ),
    inference(superposition,[],[f34,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/enumset1__t61_enumset1.p',t43_enumset1)).

fof(f34,plain,(
    ! [X6,X7,X5] : k2_xboole_0(X5,k2_xboole_0(X6,X7)) = k2_xboole_0(X7,k2_xboole_0(X5,X6)) ),
    inference(superposition,[],[f25,f24])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/enumset1__t61_enumset1.p',commutativity_k2_xboole_0)).

fof(f25,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/enumset1__t61_enumset1.p',t4_xboole_1)).

fof(f68445,plain,
    ( k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k1_tarski(sK6),k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f68444])).

fof(f68444,plain,
    ( spl7_3
  <=> k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k1_tarski(sK6),k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f68446,plain,
    ( ~ spl7_3
    | spl7_1 ),
    inference(avatar_split_clause,[],[f8557,f2090,f68444])).

fof(f2090,plain,
    ( spl7_1
  <=> k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tarski(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f8557,plain,
    ( k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k1_tarski(sK6),k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ spl7_1 ),
    inference(superposition,[],[f2091,f24])).

fof(f2091,plain,
    ( k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tarski(sK6))
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f2090])).

fof(f2092,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f21,f2090])).

fof(f21,plain,(
    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tarski(sK6)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tarski(sK6)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f18,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6))
   => k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tarski(sK6)) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    file('/export/starexec/sandbox/benchmark/enumset1__t61_enumset1.p',t61_enumset1)).
%------------------------------------------------------------------------------
