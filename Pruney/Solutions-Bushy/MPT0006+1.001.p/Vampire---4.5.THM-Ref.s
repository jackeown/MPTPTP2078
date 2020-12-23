%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0006+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:10 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   31 (  41 expanded)
%              Number of leaves         :    9 (  16 expanded)
%              Depth                    :    8
%              Number of atoms          :   67 (  92 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f57,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f23,f29,f45,f55,f56])).

fof(f56,plain,
    ( sK0 != sK1
    | r2_xboole_0(sK1,sK0)
    | ~ r2_xboole_0(sK0,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f55,plain,
    ( spl3_2
    | spl3_5
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f50,f42,f52,f26])).

fof(f26,plain,
    ( spl3_2
  <=> r2_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f52,plain,
    ( spl3_5
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f42,plain,
    ( spl3_4
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f50,plain,
    ( sK0 = sK1
    | r2_xboole_0(sK1,sK0)
    | ~ spl3_4 ),
    inference(resolution,[],[f17,f44])).

fof(f44,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f42])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

% (29102)Refutation not found, incomplete strategy% (29102)------------------------------
% (29102)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (29102)Termination reason: Refutation not found, incomplete strategy

% (29102)Memory used [KB]: 10618
% (29102)Time elapsed: 0.102 s
% (29102)------------------------------
% (29102)------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f45,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f40,f42])).

fof(f40,plain,(
    r1_tarski(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f39])).

fof(f39,plain,
    ( r1_tarski(sK1,sK0)
    | r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f36,f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f36,plain,(
    ! [X0] :
      ( r2_hidden(sK2(sK1,X0),sK0)
      | r1_tarski(sK1,X0) ) ),
    inference(resolution,[],[f13,f9])).

fof(f9,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK1)
      | r2_hidden(X2,sK0) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      & r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ~ ( ~ r2_hidden(X2,X0)
                & r2_hidden(X2,X1) )
          & r2_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ~ r2_hidden(X2,X0)
              & r2_hidden(X2,X1) )
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).

fof(f13,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f29,plain,
    ( ~ spl3_2
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f24,f20,f26])).

fof(f20,plain,
    ( spl3_1
  <=> r2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f24,plain,
    ( ~ r2_xboole_0(sK1,sK0)
    | ~ spl3_1 ),
    inference(resolution,[],[f11,f22])).

fof(f22,plain,
    ( r2_xboole_0(sK0,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f20])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | ~ r2_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
     => ~ r2_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_xboole_0)).

fof(f23,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f10,f20])).

fof(f10,plain,(
    r2_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f6])).

%------------------------------------------------------------------------------
