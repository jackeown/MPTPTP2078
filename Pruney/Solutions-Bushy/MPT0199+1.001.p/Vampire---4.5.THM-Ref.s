%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0199+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:31 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   15 (  16 expanded)
%              Number of leaves         :    4 (   5 expanded)
%              Depth                    :    5
%              Number of atoms          :   19 (  21 expanded)
%              Number of equality atoms :   11 (  12 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f25,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f13,f24])).

fof(f24,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f23])).

fof(f23,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f17,f8])).

fof(f8,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X3,X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X3,X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_enumset1)).

fof(f17,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK3,sK1,sK0)
    | spl4_1 ),
    inference(superposition,[],[f12,f7])).

fof(f7,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l123_enumset1)).

fof(f12,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK3,sK1,sK2,sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f10])).

fof(f10,plain,
    ( spl4_1
  <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK3,sK1,sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f13,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f6,f10])).

fof(f6,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK3,sK1,sK2,sK0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X3,X1,X2,X0) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X1,X2,X0) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X1,X2,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_enumset1)).

%------------------------------------------------------------------------------
