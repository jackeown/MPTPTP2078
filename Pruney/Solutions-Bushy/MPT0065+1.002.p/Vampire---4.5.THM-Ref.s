%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0065+1.002 : TPTP v7.4.0. Released v7.4.0.
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
% Statistics : Number of formulae       :   50 (  76 expanded)
%              Number of leaves         :   15 (  33 expanded)
%              Depth                    :    7
%              Number of atoms          :  113 ( 176 expanded)
%              Number of equality atoms :    9 (  12 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f83,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f24,f29,f34,f43,f59,f60,f67,f73,f81,f82])).

fof(f82,plain,
    ( sK0 != sK2
    | r2_xboole_0(sK2,sK1)
    | ~ r2_xboole_0(sK0,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f81,plain,
    ( spl3_10
    | spl3_3
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f76,f70,f31,f78])).

fof(f78,plain,
    ( spl3_10
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f31,plain,
    ( spl3_3
  <=> r2_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f70,plain,
    ( spl3_9
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f76,plain,
    ( sK0 = sK2
    | spl3_3
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f75,f33])).

fof(f33,plain,
    ( ~ r2_xboole_0(sK0,sK2)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f31])).

fof(f75,plain,
    ( sK0 = sK2
    | r2_xboole_0(sK0,sK2)
    | ~ spl3_9 ),
    inference(resolution,[],[f72,f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f72,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f70])).

fof(f73,plain,
    ( spl3_9
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f68,f40,f26,f70])).

fof(f26,plain,
    ( spl3_2
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f40,plain,
    ( spl3_4
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f68,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(resolution,[],[f49,f28])).

fof(f28,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f26])).

fof(f49,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,X0)
        | r1_tarski(sK0,X0) )
    | ~ spl3_4 ),
    inference(resolution,[],[f42,f18])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f42,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f40])).

fof(f67,plain,
    ( ~ spl3_8
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f62,f52,f64])).

fof(f64,plain,
    ( spl3_8
  <=> r2_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f52,plain,
    ( spl3_6
  <=> r2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f62,plain,
    ( ~ r2_xboole_0(sK2,sK1)
    | ~ spl3_6 ),
    inference(resolution,[],[f54,f14])).

fof(f14,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_xboole_0)).

fof(f54,plain,
    ( r2_xboole_0(sK1,sK2)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f52])).

fof(f60,plain,
    ( sK1 != sK2
    | r2_xboole_0(sK0,sK2)
    | ~ r2_xboole_0(sK0,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f59,plain,
    ( spl3_6
    | spl3_7
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f38,f26,f56,f52])).

fof(f56,plain,
    ( spl3_7
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f38,plain,
    ( sK1 = sK2
    | r2_xboole_0(sK1,sK2)
    | ~ spl3_2 ),
    inference(resolution,[],[f28,f17])).

fof(f43,plain,
    ( spl3_4
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f35,f21,f40])).

fof(f21,plain,
    ( spl3_1
  <=> r2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f35,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_1 ),
    inference(resolution,[],[f23,f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f23,plain,
    ( r2_xboole_0(sK0,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f21])).

fof(f34,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f13,f31])).

fof(f13,plain,(
    ~ r2_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_xboole_0(X0,X2)
      & r1_tarski(X1,X2)
      & r2_xboole_0(X0,X1) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_xboole_0(X0,X2)
      & r1_tarski(X1,X2)
      & r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_tarski(X1,X2)
          & r2_xboole_0(X0,X1) )
       => r2_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r2_xboole_0(X0,X1) )
     => r2_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_xboole_1)).

fof(f29,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f12,f26])).

fof(f12,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f7])).

fof(f24,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f11,f21])).

fof(f11,plain,(
    r2_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f7])).

%------------------------------------------------------------------------------
