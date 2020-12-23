%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : enumset1__t74_enumset1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:03 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   21 (  22 expanded)
%              Number of leaves         :    6 (   7 expanded)
%              Depth                    :    7
%              Number of atoms          :   26 (  28 expanded)
%              Number of equality atoms :   18 (  19 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f52,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f32,f51])).

fof(f51,plain,(
    spl6_1 ),
    inference(avatar_contradiction_clause,[],[f50])).

fof(f50,plain,
    ( $false
    | ~ spl6_1 ),
    inference(trivial_inequality_removal,[],[f49])).

fof(f49,plain,
    ( k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5)
    | ~ spl6_1 ),
    inference(superposition,[],[f31,f48])).

fof(f48,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(forward_demodulation,[],[f41,f24])).

fof(f24,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t74_enumset1.p',t51_enumset1)).

fof(f41,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    inference(superposition,[],[f25,f20])).

fof(f20,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t74_enumset1.p',t69_enumset1)).

fof(f25,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t74_enumset1.p',t57_enumset1)).

fof(f31,plain,
    ( k5_enumset1(sK0,sK0,sK1,sK2,sK3,sK4,sK5) != k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f30])).

fof(f30,plain,
    ( spl6_1
  <=> k5_enumset1(sK0,sK0,sK1,sK2,sK3,sK4,sK5) != k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f32,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f19,f30])).

fof(f19,plain,(
    k5_enumset1(sK0,sK0,sK1,sK2,sK3,sK4,sK5) != k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    k5_enumset1(sK0,sK0,sK1,sK2,sK3,sK4,sK5) != k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f16,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) != k4_enumset1(X0,X1,X2,X3,X4,X5)
   => k5_enumset1(sK0,sK0,sK1,sK2,sK3,sK4,sK5) != k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) != k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t74_enumset1.p',t74_enumset1)).
%------------------------------------------------------------------------------
