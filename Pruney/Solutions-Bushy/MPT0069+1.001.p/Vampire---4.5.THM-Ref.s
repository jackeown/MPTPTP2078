%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0069+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:17 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   27 (  34 expanded)
%              Number of leaves         :    9 (  15 expanded)
%              Depth                    :    5
%              Number of atoms          :   50 (  64 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f41,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f20,f27,f32,f39,f40])).

fof(f40,plain,
    ( k1_xboole_0 != sK0
    | r2_xboole_0(k1_xboole_0,sK0)
    | ~ r2_xboole_0(sK0,k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f39,plain,
    ( spl1_4
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f33,f24,f36])).

fof(f36,plain,
    ( spl1_4
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f24,plain,
    ( spl1_2
  <=> r1_tarski(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f33,plain,
    ( k1_xboole_0 = sK0
    | ~ spl1_2 ),
    inference(resolution,[],[f26,f10])).

fof(f10,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f26,plain,
    ( r1_tarski(sK0,k1_xboole_0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f24])).

fof(f32,plain,
    ( ~ spl1_3
    | ~ spl1_1 ),
    inference(avatar_split_clause,[],[f22,f17,f29])).

fof(f29,plain,
    ( spl1_3
  <=> r2_xboole_0(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f17,plain,
    ( spl1_1
  <=> r2_xboole_0(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f22,plain,
    ( ~ r2_xboole_0(k1_xboole_0,sK0)
    | ~ spl1_1 ),
    inference(resolution,[],[f19,f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | ~ r2_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
     => ~ r2_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_xboole_0)).

fof(f19,plain,
    ( r2_xboole_0(sK0,k1_xboole_0)
    | ~ spl1_1 ),
    inference(avatar_component_clause,[],[f17])).

fof(f27,plain,
    ( spl1_2
    | ~ spl1_1 ),
    inference(avatar_split_clause,[],[f21,f17,f24])).

fof(f21,plain,
    ( r1_tarski(sK0,k1_xboole_0)
    | ~ spl1_1 ),
    inference(resolution,[],[f19,f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f20,plain,(
    spl1_1 ),
    inference(avatar_split_clause,[],[f9,f17])).

fof(f9,plain,(
    r2_xboole_0(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0] : r2_xboole_0(X0,k1_xboole_0) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] : ~ r2_xboole_0(X0,k1_xboole_0) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] : ~ r2_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_xboole_1)).

%------------------------------------------------------------------------------
