%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : enumset1__t103_enumset1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:35:55 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   22 (  35 expanded)
%              Number of leaves         :    5 (  11 expanded)
%              Depth                    :    7
%              Number of atoms          :   29 (  45 expanded)
%              Number of equality atoms :   17 (  30 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f47,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f26,f44,f46])).

fof(f46,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f45])).

fof(f45,plain,
    ( $false
    | ~ spl4_1 ),
    inference(trivial_inequality_removal,[],[f41])).

fof(f41,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK1,sK2,sK3)
    | ~ spl4_1 ),
    inference(superposition,[],[f25,f35])).

fof(f35,plain,(
    ! [X6,X4,X7,X5] : k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X4,X5,X7,X6) ),
    inference(superposition,[],[f27,f19])).

fof(f19,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t103_enumset1.p',t44_enumset1)).

fof(f27,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X3,X0,X1,X2) = k2_xboole_0(k1_tarski(X3),k1_enumset1(X0,X2,X1)) ),
    inference(superposition,[],[f19,f18])).

fof(f18,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t103_enumset1.p',t98_enumset1)).

fof(f25,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK1,sK3,sK2)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f24])).

fof(f24,plain,
    ( spl4_1
  <=> k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK1,sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f44,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f43])).

fof(f43,plain,
    ( $false
    | ~ spl4_1 ),
    inference(trivial_inequality_removal,[],[f42])).

fof(f42,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK1,sK2,sK3)
    | ~ spl4_1 ),
    inference(superposition,[],[f25,f35])).

fof(f26,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f15,f24])).

fof(f15,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK1,sK3,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK1,sK3,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X0,X1,X3,X2)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK1,sK3,sK2) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X0,X1,X3,X2) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t103_enumset1.p',t103_enumset1)).
%------------------------------------------------------------------------------
