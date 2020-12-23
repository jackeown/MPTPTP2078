%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : enumset1__t50_enumset1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:00 EDT 2019

% Result     : Theorem 8.70s
% Output     : Refutation 8.70s
% Verified   : 
% Statistics : Number of formulae       :   31 (  36 expanded)
%              Number of leaves         :    9 (  13 expanded)
%              Depth                    :    9
%              Number of atoms          :   40 (  48 expanded)
%              Number of equality atoms :   27 (  32 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f132138,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1629,f3392,f132135])).

fof(f132135,plain,(
    spl5_3 ),
    inference(avatar_contradiction_clause,[],[f132134])).

fof(f132134,plain,
    ( $false
    | ~ spl5_3 ),
    inference(trivial_inequality_removal,[],[f132127])).

fof(f132127,plain,
    ( k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k3_enumset1(sK0,sK1,sK2,sK3,sK4)
    | ~ spl5_3 ),
    inference(superposition,[],[f3391,f4727])).

fof(f4727,plain,(
    ! [X70,X74,X72,X71,X73] : k3_enumset1(X70,X71,X72,X73,X74) = k2_xboole_0(k1_tarski(X74),k2_enumset1(X70,X71,X72,X73)) ),
    inference(forward_demodulation,[],[f4643,f27])).

fof(f27,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/enumset1__t50_enumset1.p',l57_enumset1)).

fof(f4643,plain,(
    ! [X70,X74,X72,X71,X73] : k2_xboole_0(k1_tarski(X74),k2_enumset1(X70,X71,X72,X73)) = k2_xboole_0(k1_enumset1(X70,X71,X72),k2_tarski(X73,X74)) ),
    inference(superposition,[],[f205,f26])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox/benchmark/enumset1__t50_enumset1.p',t46_enumset1)).

fof(f205,plain,(
    ! [X30,X28,X29] : k2_xboole_0(X30,k2_tarski(X28,X29)) = k2_xboole_0(k1_tarski(X29),k2_xboole_0(X30,k1_tarski(X28))) ),
    inference(superposition,[],[f49,f24])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/enumset1__t50_enumset1.p',t41_enumset1)).

fof(f49,plain,(
    ! [X6,X7,X5] : k2_xboole_0(X5,k2_xboole_0(X6,X7)) = k2_xboole_0(X7,k2_xboole_0(X5,X6)) ),
    inference(superposition,[],[f25,f22])).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/enumset1__t50_enumset1.p',commutativity_k2_xboole_0)).

fof(f25,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/enumset1__t50_enumset1.p',t4_xboole_1)).

fof(f3391,plain,
    ( k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k2_xboole_0(k1_tarski(sK4),k2_enumset1(sK0,sK1,sK2,sK3))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f3390])).

fof(f3390,plain,
    ( spl5_3
  <=> k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k2_xboole_0(k1_tarski(sK4),k2_enumset1(sK0,sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f3392,plain,
    ( ~ spl5_3
    | spl5_1 ),
    inference(avatar_split_clause,[],[f3384,f1627,f3390])).

fof(f1627,plain,
    ( spl5_1
  <=> k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k1_tarski(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f3384,plain,
    ( k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k2_xboole_0(k1_tarski(sK4),k2_enumset1(sK0,sK1,sK2,sK3))
    | ~ spl5_1 ),
    inference(superposition,[],[f1628,f22])).

fof(f1628,plain,
    ( k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k1_tarski(sK4))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f1627])).

fof(f1629,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f20,f1627])).

fof(f20,plain,(
    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k1_tarski(sK4)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k1_tarski(sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f17,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) != k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))
   => k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k1_tarski(sK4)) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) != k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox/benchmark/enumset1__t50_enumset1.p',t50_enumset1)).
%------------------------------------------------------------------------------
