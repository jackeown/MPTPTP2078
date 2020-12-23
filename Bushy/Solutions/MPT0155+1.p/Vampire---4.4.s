%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : enumset1__t71_enumset1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:03 EDT 2019

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
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
fof(f113,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f31,f110])).

fof(f110,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f109])).

fof(f109,plain,
    ( $false
    | ~ spl3_1 ),
    inference(trivial_inequality_removal,[],[f107])).

fof(f107,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2)
    | ~ spl3_1 ),
    inference(superposition,[],[f30,f104])).

fof(f104,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(forward_demodulation,[],[f92,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t71_enumset1.p',t42_enumset1)).

fof(f92,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(superposition,[],[f24,f19])).

fof(f19,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t71_enumset1.p',t69_enumset1)).

fof(f24,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t71_enumset1.p',l53_enumset1)).

fof(f30,plain,
    ( k2_enumset1(sK0,sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f29])).

fof(f29,plain,
    ( spl3_1
  <=> k2_enumset1(sK0,sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f31,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f18,f29])).

fof(f18,plain,(
    k2_enumset1(sK0,sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    k2_enumset1(sK0,sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) != k1_enumset1(X0,X1,X2)
   => k2_enumset1(sK0,sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) != k1_enumset1(X0,X1,X2) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t71_enumset1.p',t71_enumset1)).
%------------------------------------------------------------------------------
