%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : enumset1__t76_enumset1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:03 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   17 (  18 expanded)
%              Number of leaves         :    5 (   6 expanded)
%              Depth                    :    6
%              Number of atoms          :   22 (  24 expanded)
%              Number of equality atoms :   14 (  15 expanded)
%              Maximal formula depth    :    4 (   2 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f26,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f22,f25])).

fof(f25,plain,(
    spl1_1 ),
    inference(avatar_contradiction_clause,[],[f24])).

fof(f24,plain,
    ( $false
    | ~ spl1_1 ),
    inference(subsumption_resolution,[],[f23,f13])).

fof(f13,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/enumset1__t76_enumset1.p',t69_enumset1)).

fof(f23,plain,
    ( k1_tarski(sK0) != k2_tarski(sK0,sK0)
    | ~ spl1_1 ),
    inference(superposition,[],[f21,f15])).

fof(f15,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/enumset1__t76_enumset1.p',t70_enumset1)).

fof(f21,plain,
    ( k1_enumset1(sK0,sK0,sK0) != k1_tarski(sK0)
    | ~ spl1_1 ),
    inference(avatar_component_clause,[],[f20])).

fof(f20,plain,
    ( spl1_1
  <=> k1_enumset1(sK0,sK0,sK0) != k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f22,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f12,f20])).

fof(f12,plain,(
    k1_enumset1(sK0,sK0,sK0) != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    k1_enumset1(sK0,sK0,sK0) != k1_tarski(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f10])).

fof(f10,plain,
    ( ? [X0] : k1_enumset1(X0,X0,X0) != k1_tarski(X0)
   => k1_enumset1(sK0,sK0,sK0) != k1_tarski(sK0) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] : k1_enumset1(X0,X0,X0) != k1_tarski(X0) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/enumset1__t76_enumset1.p',t76_enumset1)).
%------------------------------------------------------------------------------
