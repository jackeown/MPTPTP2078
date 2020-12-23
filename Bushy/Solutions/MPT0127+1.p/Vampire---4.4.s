%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : enumset1__t43_enumset1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:35:59 EDT 2019

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   39 (  63 expanded)
%              Number of leaves         :   11 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :   54 (  87 expanded)
%              Number of equality atoms :   33 (  57 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3163,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f30,f53,f130,f502,f3149])).

fof(f3149,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f3148])).

fof(f3148,plain,
    ( $false
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f3112,f474])).

fof(f474,plain,(
    ! [X6,X7,X5] : k1_enumset1(X5,X6,X7) = k1_enumset1(X5,X7,X6) ),
    inference(superposition,[],[f108,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t43_enumset1.p',t42_enumset1)).

fof(f108,plain,(
    ! [X2,X0,X1] : k1_enumset1(X2,X0,X1) = k2_xboole_0(k1_tarski(X2),k2_tarski(X1,X0)) ),
    inference(superposition,[],[f23,f20])).

fof(f20,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t43_enumset1.p',commutativity_k2_tarski)).

fof(f3112,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK2,sK1)
    | ~ spl3_1 ),
    inference(superposition,[],[f29,f3041])).

fof(f3041,plain,(
    ! [X2,X0,X1] : k1_enumset1(X2,X1,X0) = k2_xboole_0(k2_tarski(X2,X0),k1_tarski(X1)) ),
    inference(forward_demodulation,[],[f2956,f23])).

fof(f2956,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_tarski(X2,X0),k1_tarski(X1)) = k2_xboole_0(k1_tarski(X2),k2_tarski(X1,X0)) ),
    inference(superposition,[],[f58,f32])).

fof(f32,plain,(
    ! [X4,X3] : k2_tarski(X3,X4) = k2_xboole_0(k1_tarski(X4),k1_tarski(X3)) ),
    inference(superposition,[],[f21,f19])).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t43_enumset1.p',commutativity_k2_xboole_0)).

fof(f21,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t43_enumset1.p',t41_enumset1)).

fof(f58,plain,(
    ! [X12,X13,X11] : k2_xboole_0(k2_tarski(X11,X12),X13) = k2_xboole_0(k1_tarski(X11),k2_xboole_0(k1_tarski(X12),X13)) ),
    inference(superposition,[],[f22,f21])).

fof(f22,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t43_enumset1.p',t4_xboole_1)).

fof(f29,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK2))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f28])).

fof(f28,plain,
    ( spl3_1
  <=> k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f502,plain,
    ( ~ spl3_7
    | spl3_3 ),
    inference(avatar_split_clause,[],[f478,f51,f500])).

fof(f500,plain,
    ( spl3_7
  <=> k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK2,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f51,plain,
    ( spl3_3
  <=> k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k1_tarski(sK2),k2_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f478,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK2,sK1,sK0)
    | ~ spl3_3 ),
    inference(superposition,[],[f52,f108])).

fof(f52,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k1_tarski(sK2),k2_tarski(sK0,sK1))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f51])).

fof(f130,plain,
    ( ~ spl3_5
    | spl3_3 ),
    inference(avatar_split_clause,[],[f115,f51,f128])).

fof(f128,plain,
    ( spl3_5
  <=> k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f115,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK2,sK0,sK1)
    | ~ spl3_3 ),
    inference(superposition,[],[f52,f23])).

fof(f53,plain,
    ( ~ spl3_3
    | spl3_1 ),
    inference(avatar_split_clause,[],[f45,f28,f51])).

fof(f45,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k1_tarski(sK2),k2_tarski(sK0,sK1))
    | ~ spl3_1 ),
    inference(superposition,[],[f29,f19])).

fof(f30,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f17,f28])).

fof(f17,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))
   => k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK2)) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t43_enumset1.p',t43_enumset1)).
%------------------------------------------------------------------------------
