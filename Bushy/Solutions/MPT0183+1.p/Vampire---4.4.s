%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : enumset1__t100_enumset1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:35:55 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   21 (  22 expanded)
%              Number of leaves         :    6 (   7 expanded)
%              Depth                    :    7
%              Number of atoms          :   26 (  28 expanded)
%              Number of equality atoms :   18 (  19 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f70,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f28,f69])).

fof(f69,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f68])).

fof(f68,plain,
    ( $false
    | ~ spl3_1 ),
    inference(trivial_inequality_removal,[],[f65])).

fof(f65,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2)
    | ~ spl3_1 ),
    inference(superposition,[],[f27,f51])).

fof(f51,plain,(
    ! [X4,X5,X3] : k1_enumset1(X3,X4,X5) = k1_enumset1(X4,X5,X3) ),
    inference(superposition,[],[f31,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t100_enumset1.p',t42_enumset1)).

fof(f31,plain,(
    ! [X4,X5,X3] : k1_enumset1(X3,X4,X5) = k2_xboole_0(k1_tarski(X5),k2_tarski(X3,X4)) ),
    inference(superposition,[],[f20,f19])).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t100_enumset1.p',commutativity_k2_xboole_0)).

fof(f20,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t100_enumset1.p',t43_enumset1)).

fof(f27,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK1,sK2,sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f26])).

fof(f26,plain,
    ( spl3_1
  <=> k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK1,sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f28,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f16,f26])).

fof(f16,plain,(
    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK1,sK2,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK1,sK2,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X1,X2,X0)
   => k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK1,sK2,sK0) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X1,X2,X0) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t100_enumset1.p',t100_enumset1)).
%------------------------------------------------------------------------------
