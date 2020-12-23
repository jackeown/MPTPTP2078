%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:35 EST 2020

% Result     : Theorem 1.23s
% Output     : Refutation 1.23s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 219 expanded)
%              Number of leaves         :   34 (  78 expanded)
%              Depth                    :   10
%              Number of atoms          :  302 ( 490 expanded)
%              Number of equality atoms :   51 (  99 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f409,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f83,f84,f180,f190,f203,f205,f210,f240,f275,f301,f305,f312,f323,f362,f376,f406])).

fof(f406,plain,
    ( spl4_2
    | ~ spl4_23 ),
    inference(avatar_contradiction_clause,[],[f396])).

fof(f396,plain,
    ( $false
    | spl4_2
    | ~ spl4_23 ),
    inference(unit_resulting_resolution,[],[f37,f82,f381,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k7_relat_1(X1,X0)
      | r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

fof(f381,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ spl4_23 ),
    inference(resolution,[],[f361,f112])).

fof(f112,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f57,f39])).

fof(f39,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f361,plain,
    ( r1_tarski(k7_relat_1(sK1,sK0),k1_xboole_0)
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f359])).

fof(f359,plain,
    ( spl4_23
  <=> r1_tarski(k7_relat_1(sK1,sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f82,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl4_2
  <=> r1_xboole_0(k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f37,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k9_relat_1(X1,X0)
      <~> r1_xboole_0(k1_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k9_relat_1(X1,X0)
        <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

fof(f376,plain,(
    spl4_22 ),
    inference(avatar_contradiction_clause,[],[f372])).

fof(f372,plain,
    ( $false
    | spl4_22 ),
    inference(resolution,[],[f357,f40])).

fof(f40,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f357,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | spl4_22 ),
    inference(avatar_component_clause,[],[f355])).

fof(f355,plain,
    ( spl4_22
  <=> r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f362,plain,
    ( ~ spl4_22
    | spl4_23
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f338,f298,f359,f355])).

fof(f298,plain,
    ( spl4_18
  <=> r1_tarski(k7_relat_1(sK1,sK0),k2_zfmisc_1(k1_relat_1(k7_relat_1(sK1,sK0)),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f338,plain,
    ( r1_tarski(k7_relat_1(sK1,sK0),k1_xboole_0)
    | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl4_18 ),
    inference(superposition,[],[f300,f125])).

fof(f125,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X1,X0)
      | ~ r1_xboole_0(X0,X0) ) ),
    inference(resolution,[],[f62,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ( ~ r1_xboole_0(X2,X3)
        & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X3)
        | r1_xboole_0(X0,X1) )
     => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).

fof(f300,plain,
    ( r1_tarski(k7_relat_1(sK1,sK0),k2_zfmisc_1(k1_relat_1(k7_relat_1(sK1,sK0)),k1_xboole_0))
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f298])).

fof(f323,plain,
    ( spl4_11
    | ~ spl4_15 ),
    inference(avatar_contradiction_clause,[],[f316])).

fof(f316,plain,
    ( $false
    | spl4_11
    | ~ spl4_15 ),
    inference(unit_resulting_resolution,[],[f39,f202,f274,f114])).

fof(f114,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,X3)
      | X2 = X3
      | ~ v1_xboole_0(X3) ) ),
    inference(resolution,[],[f57,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f39,f43])).

fof(f43,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f274,plain,
    ( v1_xboole_0(k2_relat_1(k1_xboole_0))
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f272])).

fof(f272,plain,
    ( spl4_15
  <=> v1_xboole_0(k2_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f202,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | spl4_11 ),
    inference(avatar_component_clause,[],[f200])).

fof(f200,plain,
    ( spl4_11
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f312,plain,
    ( ~ spl4_9
    | ~ spl4_14 ),
    inference(avatar_contradiction_clause,[],[f307])).

fof(f307,plain,
    ( $false
    | ~ spl4_9
    | ~ spl4_14 ),
    inference(unit_resulting_resolution,[],[f179,f40,f270])).

fof(f270,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(k1_relat_1(X0),k1_xboole_0)
        | ~ v1_relat_1(X0) )
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f269])).

fof(f269,plain,
    ( spl4_14
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ r1_xboole_0(k1_relat_1(X0),k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f179,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f177])).

fof(f177,plain,
    ( spl4_9
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f305,plain,(
    spl4_17 ),
    inference(avatar_contradiction_clause,[],[f302])).

fof(f302,plain,
    ( $false
    | spl4_17 ),
    inference(unit_resulting_resolution,[],[f37,f296,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f296,plain,
    ( ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | spl4_17 ),
    inference(avatar_component_clause,[],[f294])).

fof(f294,plain,
    ( spl4_17
  <=> v1_relat_1(k7_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f301,plain,
    ( ~ spl4_10
    | ~ spl4_17
    | spl4_18
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f288,f76,f298,f294,f196])).

fof(f196,plain,
    ( spl4_10
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f76,plain,
    ( spl4_1
  <=> k1_xboole_0 = k9_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f288,plain,
    ( r1_tarski(k7_relat_1(sK1,sK0),k2_zfmisc_1(k1_relat_1(k7_relat_1(sK1,sK0)),k1_xboole_0))
    | ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | ~ v1_relat_1(sK1)
    | ~ spl4_1 ),
    inference(superposition,[],[f120,f77])).

fof(f77,plain,
    ( k1_xboole_0 = k9_relat_1(sK1,sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f76])).

fof(f120,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(k7_relat_1(X0,X1)),k9_relat_1(X0,X1)))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f45,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f45,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

fof(f275,plain,
    ( spl4_14
    | spl4_15
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f267,f238,f272,f269])).

fof(f238,plain,
    ( spl4_12
  <=> ! [X1,X0] :
        ( v1_xboole_0(k9_relat_1(X0,X1))
        | ~ r1_xboole_0(k1_relat_1(X0),X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f267,plain,
    ( ! [X0] :
        ( v1_xboole_0(k2_relat_1(k1_xboole_0))
        | ~ v1_relat_1(X0)
        | ~ r1_xboole_0(k1_relat_1(X0),k1_xboole_0) )
    | ~ spl4_12 ),
    inference(duplicate_literal_removal,[],[f266])).

fof(f266,plain,
    ( ! [X0] :
        ( v1_xboole_0(k2_relat_1(k1_xboole_0))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(X0)
        | ~ r1_xboole_0(k1_relat_1(X0),k1_xboole_0) )
    | ~ spl4_12 ),
    inference(superposition,[],[f252,f172])).

fof(f172,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X0,X1) = k2_relat_1(k1_xboole_0)
      | ~ v1_relat_1(X0)
      | ~ r1_xboole_0(k1_relat_1(X0),X1) ) ),
    inference(duplicate_literal_removal,[],[f169])).

fof(f169,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X0,X1) = k2_relat_1(k1_xboole_0)
      | ~ v1_relat_1(X0)
      | ~ r1_xboole_0(k1_relat_1(X0),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f50,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X1,X0)
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f252,plain,
    ( ! [X0] :
        ( v1_xboole_0(k9_relat_1(X0,k1_xboole_0))
        | ~ v1_relat_1(X0) )
    | ~ spl4_12 ),
    inference(resolution,[],[f239,f40])).

fof(f239,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(k1_relat_1(X0),X1)
        | v1_xboole_0(k9_relat_1(X0,X1))
        | ~ v1_relat_1(X0) )
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f238])).

fof(f240,plain,
    ( spl4_12
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f236,f98,f238])).

fof(f98,plain,
    ( spl4_3
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f236,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | v1_xboole_0(k9_relat_1(X0,X1))
      | ~ v1_relat_1(X0)
      | ~ r1_xboole_0(k1_relat_1(X0),X1) ) ),
    inference(duplicate_literal_removal,[],[f235])).

fof(f235,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | v1_xboole_0(k9_relat_1(X0,X1))
      | ~ v1_relat_1(X0)
      | ~ r1_xboole_0(k1_relat_1(X0),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f217,f51])).

fof(f217,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k7_relat_1(X0,X1))
      | v1_xboole_0(k9_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f44,f50])).

fof(f44,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc11_relat_1)).

fof(f210,plain,(
    spl4_3 ),
    inference(avatar_contradiction_clause,[],[f207])).

fof(f207,plain,
    ( $false
    | spl4_3 ),
    inference(unit_resulting_resolution,[],[f108,f40,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f59,f70])).

fof(f70,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f48,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f58,f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f60,f67])).

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f63,f66])).

fof(f66,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f64,f65])).

fof(f65,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f64,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f63,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f60,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f58,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f48,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X0,X2)
        & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

fof(f108,plain,
    ( ! [X0] : r2_hidden(sK2(X0),X0)
    | spl4_3 ),
    inference(subsumption_resolution,[],[f46,f106])).

fof(f106,plain,
    ( ! [X0] : ~ v1_xboole_0(X0)
    | spl4_3 ),
    inference(duplicate_literal_removal,[],[f105])).

fof(f105,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ v1_xboole_0(X0) )
    | spl4_3 ),
    inference(superposition,[],[f100,f43])).

fof(f100,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f98])).

fof(f46,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f205,plain,(
    spl4_10 ),
    inference(avatar_contradiction_clause,[],[f204])).

fof(f204,plain,
    ( $false
    | spl4_10 ),
    inference(subsumption_resolution,[],[f37,f198])).

fof(f198,plain,
    ( ~ v1_relat_1(sK1)
    | spl4_10 ),
    inference(avatar_component_clause,[],[f196])).

fof(f203,plain,
    ( ~ spl4_2
    | ~ spl4_10
    | ~ spl4_11
    | spl4_1 ),
    inference(avatar_split_clause,[],[f194,f76,f200,f196,f80])).

fof(f194,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1(sK1)
    | ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | spl4_1 ),
    inference(superposition,[],[f78,f172])).

fof(f78,plain,
    ( k1_xboole_0 != k9_relat_1(sK1,sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f76])).

fof(f190,plain,(
    ~ spl4_8 ),
    inference(avatar_contradiction_clause,[],[f185])).

fof(f185,plain,
    ( $false
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f37,f40,f175])).

fof(f175,plain,
    ( ! [X2,X3] :
        ( ~ r1_xboole_0(k1_relat_1(X2),X3)
        | ~ v1_relat_1(X2) )
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl4_8
  <=> ! [X3,X2] :
        ( ~ v1_relat_1(X2)
        | ~ r1_xboole_0(k1_relat_1(X2),X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f180,plain,
    ( spl4_8
    | spl4_9 ),
    inference(avatar_split_clause,[],[f171,f177,f174])).

fof(f171,plain,(
    ! [X2,X3] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(X2)
      | ~ r1_xboole_0(k1_relat_1(X2),X3) ) ),
    inference(duplicate_literal_removal,[],[f170])).

fof(f170,plain,(
    ! [X2,X3] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(X2)
      | ~ r1_xboole_0(k1_relat_1(X2),X3)
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f49,f51])).

fof(f84,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f35,f80,f76])).

fof(f35,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 = k9_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f83,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f36,f80,f76])).

fof(f36,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 != k9_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:04:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (29840)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.51  % (29863)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.51  % (29843)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (29853)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.52  % (29857)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.52  % (29838)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (29863)Refutation not found, incomplete strategy% (29863)------------------------------
% 0.21/0.52  % (29863)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (29863)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (29863)Memory used [KB]: 10746
% 0.21/0.52  % (29863)Time elapsed: 0.057 s
% 0.21/0.52  % (29863)------------------------------
% 0.21/0.52  % (29863)------------------------------
% 0.21/0.52  % (29851)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.52  % (29845)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.23/0.53  % (29848)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.23/0.53  % (29846)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.23/0.53  % (29842)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.23/0.53  % (29839)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.23/0.53  % (29851)Refutation found. Thanks to Tanya!
% 1.23/0.53  % SZS status Theorem for theBenchmark
% 1.23/0.53  % (29844)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.23/0.54  % (29860)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.23/0.54  % SZS output start Proof for theBenchmark
% 1.23/0.54  fof(f409,plain,(
% 1.23/0.54    $false),
% 1.23/0.54    inference(avatar_sat_refutation,[],[f83,f84,f180,f190,f203,f205,f210,f240,f275,f301,f305,f312,f323,f362,f376,f406])).
% 1.23/0.54  fof(f406,plain,(
% 1.23/0.54    spl4_2 | ~spl4_23),
% 1.23/0.54    inference(avatar_contradiction_clause,[],[f396])).
% 1.23/0.54  fof(f396,plain,(
% 1.23/0.54    $false | (spl4_2 | ~spl4_23)),
% 1.23/0.54    inference(unit_resulting_resolution,[],[f37,f82,f381,f52])).
% 1.23/0.54  fof(f52,plain,(
% 1.23/0.54    ( ! [X0,X1] : (k1_xboole_0 != k7_relat_1(X1,X0) | r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.23/0.54    inference(cnf_transformation,[],[f31])).
% 1.23/0.54  fof(f31,plain,(
% 1.23/0.54    ! [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.23/0.54    inference(ennf_transformation,[],[f21])).
% 1.23/0.54  fof(f21,axiom,(
% 1.23/0.54    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 1.23/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).
% 1.23/0.54  fof(f381,plain,(
% 1.23/0.54    k1_xboole_0 = k7_relat_1(sK1,sK0) | ~spl4_23),
% 1.23/0.54    inference(resolution,[],[f361,f112])).
% 1.23/0.54  fof(f112,plain,(
% 1.23/0.54    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.23/0.54    inference(resolution,[],[f57,f39])).
% 1.23/0.54  fof(f39,plain,(
% 1.23/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.23/0.54    inference(cnf_transformation,[],[f4])).
% 1.23/0.54  fof(f4,axiom,(
% 1.23/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.23/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.23/0.54  fof(f57,plain,(
% 1.23/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 1.23/0.54    inference(cnf_transformation,[],[f3])).
% 1.23/0.54  fof(f3,axiom,(
% 1.23/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.23/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.23/0.54  fof(f361,plain,(
% 1.23/0.54    r1_tarski(k7_relat_1(sK1,sK0),k1_xboole_0) | ~spl4_23),
% 1.23/0.54    inference(avatar_component_clause,[],[f359])).
% 1.23/0.54  fof(f359,plain,(
% 1.23/0.54    spl4_23 <=> r1_tarski(k7_relat_1(sK1,sK0),k1_xboole_0)),
% 1.23/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 1.23/0.54  fof(f82,plain,(
% 1.23/0.54    ~r1_xboole_0(k1_relat_1(sK1),sK0) | spl4_2),
% 1.23/0.54    inference(avatar_component_clause,[],[f80])).
% 1.23/0.54  fof(f80,plain,(
% 1.23/0.54    spl4_2 <=> r1_xboole_0(k1_relat_1(sK1),sK0)),
% 1.23/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.23/0.54  fof(f37,plain,(
% 1.23/0.54    v1_relat_1(sK1)),
% 1.23/0.54    inference(cnf_transformation,[],[f24])).
% 1.23/0.54  fof(f24,plain,(
% 1.23/0.54    ? [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) <~> r1_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1))),
% 1.23/0.54    inference(ennf_transformation,[],[f23])).
% 1.23/0.54  fof(f23,negated_conjecture,(
% 1.23/0.54    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 1.23/0.54    inference(negated_conjecture,[],[f22])).
% 1.23/0.54  fof(f22,conjecture,(
% 1.23/0.54    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 1.23/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).
% 1.23/0.54  fof(f376,plain,(
% 1.23/0.54    spl4_22),
% 1.23/0.54    inference(avatar_contradiction_clause,[],[f372])).
% 1.23/0.54  fof(f372,plain,(
% 1.23/0.54    $false | spl4_22),
% 1.23/0.54    inference(resolution,[],[f357,f40])).
% 1.23/0.54  fof(f40,plain,(
% 1.23/0.54    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.23/0.54    inference(cnf_transformation,[],[f5])).
% 1.23/0.54  fof(f5,axiom,(
% 1.23/0.54    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.23/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.23/0.54  fof(f357,plain,(
% 1.23/0.54    ~r1_xboole_0(k1_xboole_0,k1_xboole_0) | spl4_22),
% 1.23/0.54    inference(avatar_component_clause,[],[f355])).
% 1.23/0.54  fof(f355,plain,(
% 1.23/0.54    spl4_22 <=> r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.23/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 1.23/0.54  fof(f362,plain,(
% 1.23/0.54    ~spl4_22 | spl4_23 | ~spl4_18),
% 1.23/0.54    inference(avatar_split_clause,[],[f338,f298,f359,f355])).
% 1.23/0.54  fof(f298,plain,(
% 1.23/0.54    spl4_18 <=> r1_tarski(k7_relat_1(sK1,sK0),k2_zfmisc_1(k1_relat_1(k7_relat_1(sK1,sK0)),k1_xboole_0))),
% 1.23/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 1.23/0.54  fof(f338,plain,(
% 1.23/0.54    r1_tarski(k7_relat_1(sK1,sK0),k1_xboole_0) | ~r1_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl4_18),
% 1.23/0.54    inference(superposition,[],[f300,f125])).
% 1.23/0.54  fof(f125,plain,(
% 1.23/0.54    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X1,X0) | ~r1_xboole_0(X0,X0)) )),
% 1.23/0.54    inference(resolution,[],[f62,f41])).
% 1.23/0.54  fof(f41,plain,(
% 1.23/0.54    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 1.23/0.54    inference(cnf_transformation,[],[f25])).
% 1.23/0.54  fof(f25,plain,(
% 1.23/0.54    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 1.23/0.54    inference(ennf_transformation,[],[f6])).
% 1.23/0.54  fof(f6,axiom,(
% 1.23/0.54    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 1.23/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).
% 1.23/0.54  fof(f62,plain,(
% 1.23/0.54    ( ! [X2,X0,X3,X1] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | ~r1_xboole_0(X2,X3)) )),
% 1.23/0.54    inference(cnf_transformation,[],[f34])).
% 1.23/0.54  fof(f34,plain,(
% 1.23/0.54    ! [X0,X1,X2,X3] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | (~r1_xboole_0(X2,X3) & ~r1_xboole_0(X0,X1)))),
% 1.23/0.54    inference(ennf_transformation,[],[f13])).
% 1.23/0.54  fof(f13,axiom,(
% 1.23/0.54    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X3) | r1_xboole_0(X0,X1)) => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))),
% 1.23/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).
% 1.23/0.54  fof(f300,plain,(
% 1.23/0.54    r1_tarski(k7_relat_1(sK1,sK0),k2_zfmisc_1(k1_relat_1(k7_relat_1(sK1,sK0)),k1_xboole_0)) | ~spl4_18),
% 1.23/0.54    inference(avatar_component_clause,[],[f298])).
% 1.23/0.54  fof(f323,plain,(
% 1.23/0.54    spl4_11 | ~spl4_15),
% 1.23/0.54    inference(avatar_contradiction_clause,[],[f316])).
% 1.23/0.54  fof(f316,plain,(
% 1.23/0.54    $false | (spl4_11 | ~spl4_15)),
% 1.23/0.54    inference(unit_resulting_resolution,[],[f39,f202,f274,f114])).
% 1.23/0.54  fof(f114,plain,(
% 1.23/0.54    ( ! [X2,X3] : (~r1_tarski(X2,X3) | X2 = X3 | ~v1_xboole_0(X3)) )),
% 1.23/0.54    inference(resolution,[],[f57,f88])).
% 1.23/0.54  fof(f88,plain,(
% 1.23/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~v1_xboole_0(X0)) )),
% 1.23/0.54    inference(superposition,[],[f39,f43])).
% 1.23/0.54  fof(f43,plain,(
% 1.23/0.54    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 1.23/0.54    inference(cnf_transformation,[],[f26])).
% 1.23/0.54  fof(f26,plain,(
% 1.23/0.54    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.23/0.54    inference(ennf_transformation,[],[f2])).
% 1.23/0.54  fof(f2,axiom,(
% 1.23/0.54    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.23/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.23/0.54  fof(f274,plain,(
% 1.23/0.54    v1_xboole_0(k2_relat_1(k1_xboole_0)) | ~spl4_15),
% 1.23/0.54    inference(avatar_component_clause,[],[f272])).
% 1.23/0.54  fof(f272,plain,(
% 1.23/0.54    spl4_15 <=> v1_xboole_0(k2_relat_1(k1_xboole_0))),
% 1.23/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 1.23/0.54  fof(f202,plain,(
% 1.23/0.54    k1_xboole_0 != k2_relat_1(k1_xboole_0) | spl4_11),
% 1.23/0.54    inference(avatar_component_clause,[],[f200])).
% 1.23/0.54  fof(f200,plain,(
% 1.23/0.54    spl4_11 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.23/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.23/0.54  fof(f312,plain,(
% 1.23/0.54    ~spl4_9 | ~spl4_14),
% 1.23/0.54    inference(avatar_contradiction_clause,[],[f307])).
% 1.23/0.54  fof(f307,plain,(
% 1.23/0.54    $false | (~spl4_9 | ~spl4_14)),
% 1.23/0.54    inference(unit_resulting_resolution,[],[f179,f40,f270])).
% 1.23/0.54  fof(f270,plain,(
% 1.23/0.54    ( ! [X0] : (~r1_xboole_0(k1_relat_1(X0),k1_xboole_0) | ~v1_relat_1(X0)) ) | ~spl4_14),
% 1.23/0.54    inference(avatar_component_clause,[],[f269])).
% 1.23/0.54  fof(f269,plain,(
% 1.23/0.54    spl4_14 <=> ! [X0] : (~v1_relat_1(X0) | ~r1_xboole_0(k1_relat_1(X0),k1_xboole_0))),
% 1.23/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 1.23/0.54  fof(f179,plain,(
% 1.23/0.54    v1_relat_1(k1_xboole_0) | ~spl4_9),
% 1.23/0.54    inference(avatar_component_clause,[],[f177])).
% 1.23/0.54  fof(f177,plain,(
% 1.23/0.54    spl4_9 <=> v1_relat_1(k1_xboole_0)),
% 1.23/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.23/0.54  fof(f305,plain,(
% 1.23/0.54    spl4_17),
% 1.23/0.54    inference(avatar_contradiction_clause,[],[f302])).
% 1.23/0.54  fof(f302,plain,(
% 1.23/0.54    $false | spl4_17),
% 1.23/0.54    inference(unit_resulting_resolution,[],[f37,f296,f49])).
% 1.23/0.54  fof(f49,plain,(
% 1.23/0.54    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.23/0.54    inference(cnf_transformation,[],[f29])).
% 1.23/0.54  fof(f29,plain,(
% 1.23/0.54    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 1.23/0.54    inference(ennf_transformation,[],[f17])).
% 1.23/0.54  fof(f17,axiom,(
% 1.23/0.54    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 1.23/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 1.23/0.54  fof(f296,plain,(
% 1.23/0.54    ~v1_relat_1(k7_relat_1(sK1,sK0)) | spl4_17),
% 1.23/0.54    inference(avatar_component_clause,[],[f294])).
% 1.23/0.54  fof(f294,plain,(
% 1.23/0.54    spl4_17 <=> v1_relat_1(k7_relat_1(sK1,sK0))),
% 1.23/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 1.23/0.54  fof(f301,plain,(
% 1.23/0.54    ~spl4_10 | ~spl4_17 | spl4_18 | ~spl4_1),
% 1.23/0.54    inference(avatar_split_clause,[],[f288,f76,f298,f294,f196])).
% 1.23/0.54  fof(f196,plain,(
% 1.23/0.54    spl4_10 <=> v1_relat_1(sK1)),
% 1.23/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.23/0.54  fof(f76,plain,(
% 1.23/0.54    spl4_1 <=> k1_xboole_0 = k9_relat_1(sK1,sK0)),
% 1.23/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.23/0.54  fof(f288,plain,(
% 1.23/0.54    r1_tarski(k7_relat_1(sK1,sK0),k2_zfmisc_1(k1_relat_1(k7_relat_1(sK1,sK0)),k1_xboole_0)) | ~v1_relat_1(k7_relat_1(sK1,sK0)) | ~v1_relat_1(sK1) | ~spl4_1),
% 1.23/0.54    inference(superposition,[],[f120,f77])).
% 1.23/0.54  fof(f77,plain,(
% 1.23/0.54    k1_xboole_0 = k9_relat_1(sK1,sK0) | ~spl4_1),
% 1.23/0.54    inference(avatar_component_clause,[],[f76])).
% 1.23/0.54  fof(f120,plain,(
% 1.23/0.54    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(k7_relat_1(X0,X1)),k9_relat_1(X0,X1))) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.23/0.54    inference(superposition,[],[f45,f50])).
% 1.23/0.54  fof(f50,plain,(
% 1.23/0.54    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.23/0.54    inference(cnf_transformation,[],[f30])).
% 1.23/0.54  fof(f30,plain,(
% 1.23/0.54    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.23/0.54    inference(ennf_transformation,[],[f19])).
% 1.23/0.54  fof(f19,axiom,(
% 1.23/0.54    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.23/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 1.23/0.54  fof(f45,plain,(
% 1.23/0.54    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 1.23/0.54    inference(cnf_transformation,[],[f28])).
% 1.23/0.54  fof(f28,plain,(
% 1.23/0.54    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.23/0.54    inference(ennf_transformation,[],[f20])).
% 1.23/0.54  fof(f20,axiom,(
% 1.23/0.54    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 1.23/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).
% 1.23/0.54  fof(f275,plain,(
% 1.23/0.54    spl4_14 | spl4_15 | ~spl4_12),
% 1.23/0.54    inference(avatar_split_clause,[],[f267,f238,f272,f269])).
% 1.23/0.54  fof(f238,plain,(
% 1.23/0.54    spl4_12 <=> ! [X1,X0] : (v1_xboole_0(k9_relat_1(X0,X1)) | ~r1_xboole_0(k1_relat_1(X0),X1) | ~v1_relat_1(X0))),
% 1.23/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 1.23/0.54  fof(f267,plain,(
% 1.23/0.54    ( ! [X0] : (v1_xboole_0(k2_relat_1(k1_xboole_0)) | ~v1_relat_1(X0) | ~r1_xboole_0(k1_relat_1(X0),k1_xboole_0)) ) | ~spl4_12),
% 1.23/0.54    inference(duplicate_literal_removal,[],[f266])).
% 1.23/0.54  fof(f266,plain,(
% 1.23/0.54    ( ! [X0] : (v1_xboole_0(k2_relat_1(k1_xboole_0)) | ~v1_relat_1(X0) | ~v1_relat_1(X0) | ~r1_xboole_0(k1_relat_1(X0),k1_xboole_0)) ) | ~spl4_12),
% 1.23/0.54    inference(superposition,[],[f252,f172])).
% 1.23/0.54  fof(f172,plain,(
% 1.23/0.54    ( ! [X0,X1] : (k9_relat_1(X0,X1) = k2_relat_1(k1_xboole_0) | ~v1_relat_1(X0) | ~r1_xboole_0(k1_relat_1(X0),X1)) )),
% 1.23/0.54    inference(duplicate_literal_removal,[],[f169])).
% 1.23/0.54  fof(f169,plain,(
% 1.23/0.54    ( ! [X0,X1] : (k9_relat_1(X0,X1) = k2_relat_1(k1_xboole_0) | ~v1_relat_1(X0) | ~r1_xboole_0(k1_relat_1(X0),X1) | ~v1_relat_1(X0)) )),
% 1.23/0.54    inference(superposition,[],[f50,f51])).
% 1.23/0.54  fof(f51,plain,(
% 1.23/0.54    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.23/0.54    inference(cnf_transformation,[],[f31])).
% 1.23/0.54  fof(f252,plain,(
% 1.23/0.54    ( ! [X0] : (v1_xboole_0(k9_relat_1(X0,k1_xboole_0)) | ~v1_relat_1(X0)) ) | ~spl4_12),
% 1.23/0.54    inference(resolution,[],[f239,f40])).
% 1.23/0.54  fof(f239,plain,(
% 1.23/0.54    ( ! [X0,X1] : (~r1_xboole_0(k1_relat_1(X0),X1) | v1_xboole_0(k9_relat_1(X0,X1)) | ~v1_relat_1(X0)) ) | ~spl4_12),
% 1.23/0.54    inference(avatar_component_clause,[],[f238])).
% 1.23/0.54  fof(f240,plain,(
% 1.23/0.54    spl4_12 | ~spl4_3),
% 1.23/0.54    inference(avatar_split_clause,[],[f236,f98,f238])).
% 1.23/0.54  fof(f98,plain,(
% 1.23/0.54    spl4_3 <=> v1_xboole_0(k1_xboole_0)),
% 1.23/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.23/0.54  fof(f236,plain,(
% 1.23/0.54    ( ! [X0,X1] : (~v1_xboole_0(k1_xboole_0) | v1_xboole_0(k9_relat_1(X0,X1)) | ~v1_relat_1(X0) | ~r1_xboole_0(k1_relat_1(X0),X1)) )),
% 1.23/0.54    inference(duplicate_literal_removal,[],[f235])).
% 1.23/0.54  fof(f235,plain,(
% 1.23/0.54    ( ! [X0,X1] : (~v1_xboole_0(k1_xboole_0) | v1_xboole_0(k9_relat_1(X0,X1)) | ~v1_relat_1(X0) | ~r1_xboole_0(k1_relat_1(X0),X1) | ~v1_relat_1(X0)) )),
% 1.23/0.54    inference(superposition,[],[f217,f51])).
% 1.23/0.54  fof(f217,plain,(
% 1.23/0.54    ( ! [X0,X1] : (~v1_xboole_0(k7_relat_1(X0,X1)) | v1_xboole_0(k9_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.23/0.54    inference(superposition,[],[f44,f50])).
% 1.23/0.54  fof(f44,plain,(
% 1.23/0.54    ( ! [X0] : (v1_xboole_0(k2_relat_1(X0)) | ~v1_xboole_0(X0)) )),
% 1.23/0.54    inference(cnf_transformation,[],[f27])).
% 1.23/0.54  fof(f27,plain,(
% 1.23/0.54    ! [X0] : (v1_xboole_0(k2_relat_1(X0)) | ~v1_xboole_0(X0))),
% 1.23/0.54    inference(ennf_transformation,[],[f18])).
% 1.23/0.54  fof(f18,axiom,(
% 1.23/0.54    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k2_relat_1(X0)))),
% 1.23/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc11_relat_1)).
% 1.23/0.54  fof(f210,plain,(
% 1.23/0.54    spl4_3),
% 1.23/0.54    inference(avatar_contradiction_clause,[],[f207])).
% 1.23/0.54  fof(f207,plain,(
% 1.23/0.54    $false | spl4_3),
% 1.23/0.54    inference(unit_resulting_resolution,[],[f108,f40,f71])).
% 1.23/0.54  fof(f71,plain,(
% 1.23/0.54    ( ! [X2,X0,X1] : (~r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) | ~r2_hidden(X0,X2)) )),
% 1.23/0.54    inference(definition_unfolding,[],[f59,f70])).
% 1.23/0.54  fof(f70,plain,(
% 1.23/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.23/0.54    inference(definition_unfolding,[],[f48,f69])).
% 1.23/0.54  fof(f69,plain,(
% 1.23/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.23/0.54    inference(definition_unfolding,[],[f58,f68])).
% 1.23/0.54  fof(f68,plain,(
% 1.23/0.54    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.23/0.54    inference(definition_unfolding,[],[f60,f67])).
% 1.23/0.54  fof(f67,plain,(
% 1.23/0.54    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.23/0.54    inference(definition_unfolding,[],[f63,f66])).
% 1.23/0.54  fof(f66,plain,(
% 1.23/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.23/0.54    inference(definition_unfolding,[],[f64,f65])).
% 1.23/0.54  fof(f65,plain,(
% 1.23/0.54    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.23/0.54    inference(cnf_transformation,[],[f12])).
% 1.23/0.54  fof(f12,axiom,(
% 1.23/0.54    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.23/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 1.23/0.54  fof(f64,plain,(
% 1.23/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.23/0.54    inference(cnf_transformation,[],[f11])).
% 1.23/0.54  fof(f11,axiom,(
% 1.23/0.54    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.23/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.23/0.54  fof(f63,plain,(
% 1.23/0.54    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.23/0.54    inference(cnf_transformation,[],[f10])).
% 1.23/0.54  fof(f10,axiom,(
% 1.23/0.54    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.23/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.23/0.54  fof(f60,plain,(
% 1.23/0.54    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.23/0.54    inference(cnf_transformation,[],[f9])).
% 1.23/0.54  fof(f9,axiom,(
% 1.23/0.54    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.23/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.23/0.54  fof(f58,plain,(
% 1.23/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.23/0.54    inference(cnf_transformation,[],[f8])).
% 1.23/0.54  fof(f8,axiom,(
% 1.23/0.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.23/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.23/0.54  fof(f48,plain,(
% 1.23/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.23/0.54    inference(cnf_transformation,[],[f7])).
% 1.23/0.54  fof(f7,axiom,(
% 1.23/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.23/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.23/0.54  fof(f59,plain,(
% 1.23/0.54    ( ! [X2,X0,X1] : (~r1_xboole_0(k2_tarski(X0,X1),X2) | ~r2_hidden(X0,X2)) )),
% 1.23/0.54    inference(cnf_transformation,[],[f33])).
% 1.23/0.54  fof(f33,plain,(
% 1.23/0.54    ! [X0,X1,X2] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2))),
% 1.23/0.54    inference(ennf_transformation,[],[f15])).
% 1.23/0.54  fof(f15,axiom,(
% 1.23/0.54    ! [X0,X1,X2] : ~(r2_hidden(X0,X2) & r1_xboole_0(k2_tarski(X0,X1),X2))),
% 1.23/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).
% 1.23/0.54  fof(f108,plain,(
% 1.23/0.54    ( ! [X0] : (r2_hidden(sK2(X0),X0)) ) | spl4_3),
% 1.23/0.54    inference(subsumption_resolution,[],[f46,f106])).
% 1.23/0.54  fof(f106,plain,(
% 1.23/0.54    ( ! [X0] : (~v1_xboole_0(X0)) ) | spl4_3),
% 1.23/0.54    inference(duplicate_literal_removal,[],[f105])).
% 1.23/0.54  fof(f105,plain,(
% 1.23/0.54    ( ! [X0] : (~v1_xboole_0(X0) | ~v1_xboole_0(X0)) ) | spl4_3),
% 1.23/0.54    inference(superposition,[],[f100,f43])).
% 1.23/0.54  fof(f100,plain,(
% 1.23/0.54    ~v1_xboole_0(k1_xboole_0) | spl4_3),
% 1.23/0.54    inference(avatar_component_clause,[],[f98])).
% 1.23/0.54  fof(f46,plain,(
% 1.23/0.54    ( ! [X0] : (r2_hidden(sK2(X0),X0) | v1_xboole_0(X0)) )),
% 1.23/0.54    inference(cnf_transformation,[],[f1])).
% 1.23/0.54  fof(f1,axiom,(
% 1.23/0.54    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.23/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.23/0.54  fof(f205,plain,(
% 1.23/0.54    spl4_10),
% 1.23/0.54    inference(avatar_contradiction_clause,[],[f204])).
% 1.23/0.54  fof(f204,plain,(
% 1.23/0.54    $false | spl4_10),
% 1.23/0.54    inference(subsumption_resolution,[],[f37,f198])).
% 1.23/0.54  fof(f198,plain,(
% 1.23/0.54    ~v1_relat_1(sK1) | spl4_10),
% 1.23/0.54    inference(avatar_component_clause,[],[f196])).
% 1.23/0.54  fof(f203,plain,(
% 1.23/0.54    ~spl4_2 | ~spl4_10 | ~spl4_11 | spl4_1),
% 1.23/0.54    inference(avatar_split_clause,[],[f194,f76,f200,f196,f80])).
% 1.23/0.54  fof(f194,plain,(
% 1.23/0.54    k1_xboole_0 != k2_relat_1(k1_xboole_0) | ~v1_relat_1(sK1) | ~r1_xboole_0(k1_relat_1(sK1),sK0) | spl4_1),
% 1.23/0.54    inference(superposition,[],[f78,f172])).
% 1.23/0.54  fof(f78,plain,(
% 1.23/0.54    k1_xboole_0 != k9_relat_1(sK1,sK0) | spl4_1),
% 1.23/0.54    inference(avatar_component_clause,[],[f76])).
% 1.23/0.54  fof(f190,plain,(
% 1.23/0.54    ~spl4_8),
% 1.23/0.54    inference(avatar_contradiction_clause,[],[f185])).
% 1.23/0.54  fof(f185,plain,(
% 1.23/0.54    $false | ~spl4_8),
% 1.23/0.54    inference(unit_resulting_resolution,[],[f37,f40,f175])).
% 1.23/0.54  fof(f175,plain,(
% 1.23/0.54    ( ! [X2,X3] : (~r1_xboole_0(k1_relat_1(X2),X3) | ~v1_relat_1(X2)) ) | ~spl4_8),
% 1.23/0.54    inference(avatar_component_clause,[],[f174])).
% 1.23/0.54  fof(f174,plain,(
% 1.23/0.54    spl4_8 <=> ! [X3,X2] : (~v1_relat_1(X2) | ~r1_xboole_0(k1_relat_1(X2),X3))),
% 1.23/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.23/0.54  fof(f180,plain,(
% 1.23/0.54    spl4_8 | spl4_9),
% 1.23/0.54    inference(avatar_split_clause,[],[f171,f177,f174])).
% 1.23/0.54  fof(f171,plain,(
% 1.23/0.54    ( ! [X2,X3] : (v1_relat_1(k1_xboole_0) | ~v1_relat_1(X2) | ~r1_xboole_0(k1_relat_1(X2),X3)) )),
% 1.23/0.54    inference(duplicate_literal_removal,[],[f170])).
% 1.23/0.54  fof(f170,plain,(
% 1.23/0.54    ( ! [X2,X3] : (v1_relat_1(k1_xboole_0) | ~v1_relat_1(X2) | ~r1_xboole_0(k1_relat_1(X2),X3) | ~v1_relat_1(X2)) )),
% 1.23/0.54    inference(superposition,[],[f49,f51])).
% 1.23/0.54  fof(f84,plain,(
% 1.23/0.54    spl4_1 | spl4_2),
% 1.23/0.54    inference(avatar_split_clause,[],[f35,f80,f76])).
% 1.23/0.54  fof(f35,plain,(
% 1.23/0.54    r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k9_relat_1(sK1,sK0)),
% 1.23/0.54    inference(cnf_transformation,[],[f24])).
% 1.23/0.54  fof(f83,plain,(
% 1.23/0.54    ~spl4_1 | ~spl4_2),
% 1.23/0.54    inference(avatar_split_clause,[],[f36,f80,f76])).
% 1.23/0.54  fof(f36,plain,(
% 1.23/0.54    ~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k9_relat_1(sK1,sK0)),
% 1.23/0.54    inference(cnf_transformation,[],[f24])).
% 1.23/0.54  % SZS output end Proof for theBenchmark
% 1.23/0.54  % (29851)------------------------------
% 1.23/0.54  % (29851)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.54  % (29851)Termination reason: Refutation
% 1.23/0.54  
% 1.23/0.54  % (29851)Memory used [KB]: 6396
% 1.23/0.54  % (29851)Time elapsed: 0.126 s
% 1.23/0.54  % (29851)------------------------------
% 1.23/0.54  % (29851)------------------------------
% 1.23/0.54  % (29862)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.37/0.54  % (29834)Success in time 0.178 s
%------------------------------------------------------------------------------
