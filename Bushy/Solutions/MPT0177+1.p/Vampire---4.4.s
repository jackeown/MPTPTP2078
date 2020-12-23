%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : enumset1__t93_enumset1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:06 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   17 (  18 expanded)
%              Number of leaves         :    5 (   6 expanded)
%              Depth                    :    6
%              Number of atoms          :   22 (  24 expanded)
%              Number of equality atoms :   14 (  15 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f24,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f20,f23])).

fof(f23,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f22])).

fof(f22,plain,
    ( $false
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f21,f12])).

fof(f12,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t93_enumset1.p',t71_enumset1)).

fof(f21,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2)
    | ~ spl3_1 ),
    inference(superposition,[],[f19,f13])).

fof(f13,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t93_enumset1.p',t90_enumset1)).

fof(f19,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f18])).

fof(f18,plain,
    ( spl3_1
  <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f20,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f11,f18])).

fof(f11,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2] : k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != k1_enumset1(X0,X1,X2)
   => k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2] : k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != k1_enumset1(X0,X1,X2) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] : k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] : k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t93_enumset1.p',t93_enumset1)).
%------------------------------------------------------------------------------
