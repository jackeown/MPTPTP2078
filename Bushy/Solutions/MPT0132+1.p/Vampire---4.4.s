%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : enumset1__t48_enumset1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:00 EDT 2019

% Result     : Theorem 8.28s
% Output     : Refutation 8.28s
% Verified   : 
% Statistics : Number of formulae       :   35 (  47 expanded)
%              Number of leaves         :   10 (  17 expanded)
%              Depth                    :    8
%              Number of atoms          :   43 (  59 expanded)
%              Number of equality atoms :   31 (  43 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f116067,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f870,f41400,f116044])).

fof(f116044,plain,(
    spl5_1 ),
    inference(avatar_contradiction_clause,[],[f116043])).

fof(f116043,plain,
    ( $false
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f115929,f26799])).

fof(f26799,plain,(
    ! [X21,X19,X17,X20,X18] : k3_enumset1(X17,X18,X19,X20,X21) = k3_enumset1(X17,X18,X19,X21,X20) ),
    inference(superposition,[],[f4627,f26])).

fof(f26,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t48_enumset1.p',l57_enumset1)).

fof(f4627,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X2,X3,X4,X0,X1) = k2_xboole_0(k1_enumset1(X2,X3,X4),k2_tarski(X1,X0)) ),
    inference(superposition,[],[f26,f22])).

fof(f22,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t48_enumset1.p',commutativity_k2_tarski)).

fof(f115929,plain,
    ( k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k3_enumset1(sK0,sK1,sK2,sK4,sK3)
    | ~ spl5_1 ),
    inference(superposition,[],[f869,f15326])).

fof(f15326,plain,(
    ! [X6,X8,X7,X5,X9] : k3_enumset1(X8,X9,X5,X6,X7) = k2_xboole_0(k2_tarski(X8,X9),k1_enumset1(X5,X7,X6)) ),
    inference(forward_demodulation,[],[f15160,f26])).

fof(f15160,plain,(
    ! [X6,X8,X7,X5,X9] : k2_xboole_0(k2_tarski(X8,X9),k1_enumset1(X5,X7,X6)) = k2_xboole_0(k1_enumset1(X8,X9,X5),k2_tarski(X6,X7)) ),
    inference(superposition,[],[f42,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] : k1_enumset1(X2,X0,X1) = k2_xboole_0(k1_tarski(X2),k2_tarski(X1,X0)) ),
    inference(superposition,[],[f24,f22])).

fof(f24,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t48_enumset1.p',t42_enumset1)).

fof(f42,plain,(
    ! [X10,X8,X11,X9] : k2_xboole_0(k1_enumset1(X8,X9,X10),X11) = k2_xboole_0(k2_tarski(X8,X9),k2_xboole_0(k1_tarski(X10),X11)) ),
    inference(superposition,[],[f25,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t48_enumset1.p',t43_enumset1)).

fof(f25,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t48_enumset1.p',t4_xboole_1)).

fof(f869,plain,
    ( k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k2_xboole_0(k2_tarski(sK0,sK1),k1_enumset1(sK2,sK3,sK4))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f868])).

fof(f868,plain,
    ( spl5_1
  <=> k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k2_xboole_0(k2_tarski(sK0,sK1),k1_enumset1(sK2,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f41400,plain,
    ( ~ spl5_3
    | spl5_1 ),
    inference(avatar_split_clause,[],[f41211,f868,f41398])).

fof(f41398,plain,
    ( spl5_3
  <=> k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k3_enumset1(sK2,sK3,sK4,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f41211,plain,
    ( k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k3_enumset1(sK2,sK3,sK4,sK0,sK1)
    | ~ spl5_1 ),
    inference(superposition,[],[f869,f4629])).

fof(f4629,plain,(
    ! [X6,X8,X7,X5,X9] : k3_enumset1(X5,X6,X7,X8,X9) = k2_xboole_0(k2_tarski(X8,X9),k1_enumset1(X5,X6,X7)) ),
    inference(superposition,[],[f26,f21])).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t48_enumset1.p',commutativity_k2_xboole_0)).

fof(f870,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f19,f868])).

fof(f19,plain,(
    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k2_xboole_0(k2_tarski(sK0,sK1),k1_enumset1(sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k2_xboole_0(k2_tarski(sK0,sK1),k1_enumset1(sK2,sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f16,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) != k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))
   => k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k2_xboole_0(k2_tarski(sK0,sK1),k1_enumset1(sK2,sK3,sK4)) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) != k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t48_enumset1.p',t48_enumset1)).
%------------------------------------------------------------------------------
