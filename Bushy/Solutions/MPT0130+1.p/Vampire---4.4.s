%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : enumset1__t46_enumset1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:35:59 EDT 2019

% Result     : Theorem 0.63s
% Output     : Refutation 0.63s
% Verified   : 
% Statistics : Number of formulae       :   36 (  47 expanded)
%              Number of leaves         :   10 (  17 expanded)
%              Depth                    :    8
%              Number of atoms          :   45 (  59 expanded)
%              Number of equality atoms :   32 (  43 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11590,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f56,f11571])).

fof(f11571,plain,(
    spl4_3 ),
    inference(avatar_contradiction_clause,[],[f11570])).

fof(f11570,plain,
    ( $false
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f11512,f6490])).

fof(f6490,plain,(
    ! [X6,X4,X7,X5] : k2_enumset1(X4,X5,X7,X6) = k2_enumset1(X6,X7,X4,X5) ),
    inference(superposition,[],[f588,f584])).

fof(f584,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X2,X3,X0,X1) = k2_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X0)) ),
    inference(superposition,[],[f26,f22])).

fof(f22,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/enumset1__t46_enumset1.p',commutativity_k2_tarski)).

fof(f26,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/enumset1__t46_enumset1.p',l53_enumset1)).

fof(f588,plain,(
    ! [X6,X8,X7,X9] : k2_enumset1(X6,X7,X8,X9) = k2_xboole_0(k2_tarski(X8,X9),k2_tarski(X6,X7)) ),
    inference(superposition,[],[f26,f21])).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/enumset1__t46_enumset1.p',commutativity_k2_xboole_0)).

fof(f11512,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK3,sK2,sK0,sK1)
    | ~ spl4_3 ),
    inference(superposition,[],[f55,f2861])).

fof(f2861,plain,(
    ! [X23,X21,X22,X20] : k2_enumset1(X23,X20,X21,X22) = k2_xboole_0(k1_tarski(X23),k1_enumset1(X21,X22,X20)) ),
    inference(forward_demodulation,[],[f2775,f26])).

fof(f2775,plain,(
    ! [X23,X21,X22,X20] : k2_xboole_0(k1_tarski(X23),k1_enumset1(X21,X22,X20)) = k2_xboole_0(k2_tarski(X23,X20),k2_tarski(X21,X22)) ),
    inference(superposition,[],[f61,f114])).

fof(f114,plain,(
    ! [X4,X5,X3] : k1_enumset1(X3,X4,X5) = k2_xboole_0(k1_tarski(X5),k2_tarski(X3,X4)) ),
    inference(superposition,[],[f25,f21])).

fof(f25,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox/benchmark/enumset1__t46_enumset1.p',t43_enumset1)).

fof(f61,plain,(
    ! [X12,X13,X11] : k2_xboole_0(k2_tarski(X11,X12),X13) = k2_xboole_0(k1_tarski(X11),k2_xboole_0(k1_tarski(X12),X13)) ),
    inference(superposition,[],[f24,f23])).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/enumset1__t46_enumset1.p',t41_enumset1)).

fof(f24,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/enumset1__t46_enumset1.p',t4_xboole_1)).

fof(f55,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_xboole_0(k1_tarski(sK3),k1_enumset1(sK0,sK1,sK2))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl4_3
  <=> k2_enumset1(sK0,sK1,sK2,sK3) != k2_xboole_0(k1_tarski(sK3),k1_enumset1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f56,plain,
    ( ~ spl4_3
    | spl4_1 ),
    inference(avatar_split_clause,[],[f48,f45,f54])).

fof(f45,plain,
    ( spl4_1
  <=> k2_enumset1(sK0,sK1,sK2,sK3) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f48,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_xboole_0(k1_tarski(sK3),k1_enumset1(sK0,sK1,sK2))
    | ~ spl4_1 ),
    inference(superposition,[],[f46,f21])).

fof(f46,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK3))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f47,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f19,f45])).

fof(f19,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK3)) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox/benchmark/enumset1__t46_enumset1.p',t46_enumset1)).
%------------------------------------------------------------------------------
