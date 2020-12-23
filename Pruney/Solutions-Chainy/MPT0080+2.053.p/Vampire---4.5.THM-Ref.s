%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:06 EST 2020

% Result     : Theorem 0.14s
% Output     : Refutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 117 expanded)
%              Number of leaves         :   22 (  51 expanded)
%              Depth                    :    7
%              Number of atoms          :  199 ( 306 expanded)
%              Number of equality atoms :   15 (  19 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f520,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f42,f47,f51,f55,f59,f71,f75,f79,f197,f207,f227,f486,f516,f519])).

fof(f519,plain,
    ( ~ spl3_4
    | spl3_28
    | ~ spl3_83 ),
    inference(avatar_contradiction_clause,[],[f518])).

fof(f518,plain,
    ( $false
    | ~ spl3_4
    | spl3_28
    | ~ spl3_83 ),
    inference(subsumption_resolution,[],[f517,f196])).

fof(f196,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK1)
    | spl3_28 ),
    inference(avatar_component_clause,[],[f194])).

fof(f194,plain,
    ( spl3_28
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f517,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_4
    | ~ spl3_83 ),
    inference(resolution,[],[f515,f50])).

fof(f50,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl3_4
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f515,plain,
    ( v1_xboole_0(k4_xboole_0(sK0,sK1))
    | ~ spl3_83 ),
    inference(avatar_component_clause,[],[f513])).

fof(f513,plain,
    ( spl3_83
  <=> v1_xboole_0(k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_83])])).

fof(f516,plain,
    ( spl3_83
    | ~ spl3_6
    | ~ spl3_34
    | ~ spl3_78 ),
    inference(avatar_split_clause,[],[f511,f483,f225,f57,f513])).

fof(f57,plain,
    ( spl3_6
  <=> ! [X1,X0] :
        ( ~ r1_xboole_0(X1,X0)
        | ~ r1_tarski(X1,X0)
        | v1_xboole_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f225,plain,
    ( spl3_34
  <=> ! [X1] : r1_xboole_0(k4_xboole_0(sK0,X1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f483,plain,
    ( spl3_78
  <=> r1_tarski(k4_xboole_0(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_78])])).

fof(f511,plain,
    ( v1_xboole_0(k4_xboole_0(sK0,sK1))
    | ~ spl3_6
    | ~ spl3_34
    | ~ spl3_78 ),
    inference(subsumption_resolution,[],[f491,f226])).

fof(f226,plain,
    ( ! [X1] : r1_xboole_0(k4_xboole_0(sK0,X1),sK2)
    | ~ spl3_34 ),
    inference(avatar_component_clause,[],[f225])).

fof(f491,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK0,sK1),sK2)
    | v1_xboole_0(k4_xboole_0(sK0,sK1))
    | ~ spl3_6
    | ~ spl3_78 ),
    inference(resolution,[],[f485,f58])).

fof(f58,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X1,X0)
        | ~ r1_xboole_0(X1,X0)
        | v1_xboole_0(X1) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f57])).

fof(f485,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK1),sK2)
    | ~ spl3_78 ),
    inference(avatar_component_clause,[],[f483])).

fof(f486,plain,
    ( spl3_78
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f473,f73,f44,f483])).

fof(f44,plain,
    ( spl3_3
  <=> r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f73,plain,
    ( spl3_10
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k4_xboole_0(X0,X1),X2)
        | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f473,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK1),sK2)
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(resolution,[],[f74,f46])).

fof(f46,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f44])).

fof(f74,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
        | r1_tarski(k4_xboole_0(X0,X1),X2) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f73])).

fof(f227,plain,
    ( spl3_34
    | ~ spl3_5
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f214,f205,f53,f225])).

fof(f53,plain,
    ( spl3_5
  <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f205,plain,
    ( spl3_30
  <=> ! [X0] :
        ( r1_xboole_0(X0,sK2)
        | ~ r1_tarski(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f214,plain,
    ( ! [X1] : r1_xboole_0(k4_xboole_0(sK0,X1),sK2)
    | ~ spl3_5
    | ~ spl3_30 ),
    inference(resolution,[],[f206,f54])).

fof(f54,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f53])).

fof(f206,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | r1_xboole_0(X0,sK2) )
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f205])).

fof(f207,plain,
    ( spl3_30
    | ~ spl3_2
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f202,f77,f39,f205])).

fof(f39,plain,
    ( spl3_2
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f77,plain,
    ( spl3_11
  <=> ! [X1,X0,X2] :
        ( r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X1,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f202,plain,
    ( ! [X0] :
        ( r1_xboole_0(X0,sK2)
        | ~ r1_tarski(X0,sK0) )
    | ~ spl3_2
    | ~ spl3_11 ),
    inference(resolution,[],[f78,f41])).

fof(f41,plain,
    ( r1_xboole_0(sK0,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f78,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(X1,X2)
        | r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f77])).

fof(f197,plain,
    ( ~ spl3_28
    | spl3_1
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f190,f69,f34,f194])).

fof(f34,plain,
    ( spl3_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f69,plain,
    ( spl3_9
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f190,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK1)
    | spl3_1
    | ~ spl3_9 ),
    inference(resolution,[],[f70,f36])).

fof(f36,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f70,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f69])).

fof(f79,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f32,f77])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f75,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f31,f73])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f71,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f29,f69])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f59,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f27,f57])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f55,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f26,f53])).

fof(f26,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f51,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f25,f49])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f47,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f22,f44])).

fof(f22,plain,(
    r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ~ r1_tarski(sK0,sK1)
    & r1_xboole_0(sK0,sK2)
    & r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
   => ( ~ r1_tarski(sK0,sK1)
      & r1_xboole_0(sK0,sK2)
      & r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
       => r1_tarski(X0,X1) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

fof(f42,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f23,f39])).

fof(f23,plain,(
    r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f37,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f24,f34])).

fof(f24,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:27:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.39  % (24110)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.14/0.40  % (24110)Refutation found. Thanks to Tanya!
% 0.14/0.40  % SZS status Theorem for theBenchmark
% 0.14/0.40  % SZS output start Proof for theBenchmark
% 0.14/0.40  fof(f520,plain,(
% 0.14/0.40    $false),
% 0.14/0.40    inference(avatar_sat_refutation,[],[f37,f42,f47,f51,f55,f59,f71,f75,f79,f197,f207,f227,f486,f516,f519])).
% 0.14/0.40  fof(f519,plain,(
% 0.14/0.40    ~spl3_4 | spl3_28 | ~spl3_83),
% 0.14/0.40    inference(avatar_contradiction_clause,[],[f518])).
% 0.14/0.40  fof(f518,plain,(
% 0.14/0.40    $false | (~spl3_4 | spl3_28 | ~spl3_83)),
% 0.14/0.40    inference(subsumption_resolution,[],[f517,f196])).
% 0.14/0.40  fof(f196,plain,(
% 0.14/0.40    k1_xboole_0 != k4_xboole_0(sK0,sK1) | spl3_28),
% 0.14/0.40    inference(avatar_component_clause,[],[f194])).
% 0.14/0.40  fof(f194,plain,(
% 0.14/0.40    spl3_28 <=> k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 0.14/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.14/0.40  fof(f517,plain,(
% 0.14/0.40    k1_xboole_0 = k4_xboole_0(sK0,sK1) | (~spl3_4 | ~spl3_83)),
% 0.14/0.40    inference(resolution,[],[f515,f50])).
% 0.14/0.40  fof(f50,plain,(
% 0.14/0.40    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) ) | ~spl3_4),
% 0.14/0.40    inference(avatar_component_clause,[],[f49])).
% 0.14/0.40  fof(f49,plain,(
% 0.14/0.40    spl3_4 <=> ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.14/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.14/0.40  fof(f515,plain,(
% 0.14/0.40    v1_xboole_0(k4_xboole_0(sK0,sK1)) | ~spl3_83),
% 0.14/0.40    inference(avatar_component_clause,[],[f513])).
% 0.14/0.40  fof(f513,plain,(
% 0.14/0.40    spl3_83 <=> v1_xboole_0(k4_xboole_0(sK0,sK1))),
% 0.14/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_83])])).
% 0.14/0.40  fof(f516,plain,(
% 0.14/0.40    spl3_83 | ~spl3_6 | ~spl3_34 | ~spl3_78),
% 0.14/0.40    inference(avatar_split_clause,[],[f511,f483,f225,f57,f513])).
% 0.14/0.40  fof(f57,plain,(
% 0.14/0.40    spl3_6 <=> ! [X1,X0] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 0.14/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.14/0.40  fof(f225,plain,(
% 0.14/0.40    spl3_34 <=> ! [X1] : r1_xboole_0(k4_xboole_0(sK0,X1),sK2)),
% 0.14/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 0.14/0.40  fof(f483,plain,(
% 0.14/0.40    spl3_78 <=> r1_tarski(k4_xboole_0(sK0,sK1),sK2)),
% 0.14/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_78])])).
% 0.14/0.40  fof(f511,plain,(
% 0.14/0.40    v1_xboole_0(k4_xboole_0(sK0,sK1)) | (~spl3_6 | ~spl3_34 | ~spl3_78)),
% 0.14/0.40    inference(subsumption_resolution,[],[f491,f226])).
% 0.14/0.40  fof(f226,plain,(
% 0.14/0.40    ( ! [X1] : (r1_xboole_0(k4_xboole_0(sK0,X1),sK2)) ) | ~spl3_34),
% 0.14/0.40    inference(avatar_component_clause,[],[f225])).
% 0.14/0.40  fof(f491,plain,(
% 0.14/0.40    ~r1_xboole_0(k4_xboole_0(sK0,sK1),sK2) | v1_xboole_0(k4_xboole_0(sK0,sK1)) | (~spl3_6 | ~spl3_78)),
% 0.14/0.40    inference(resolution,[],[f485,f58])).
% 0.14/0.40  fof(f58,plain,(
% 0.14/0.40    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_xboole_0(X1,X0) | v1_xboole_0(X1)) ) | ~spl3_6),
% 0.14/0.40    inference(avatar_component_clause,[],[f57])).
% 0.14/0.40  fof(f485,plain,(
% 0.14/0.40    r1_tarski(k4_xboole_0(sK0,sK1),sK2) | ~spl3_78),
% 0.14/0.40    inference(avatar_component_clause,[],[f483])).
% 0.14/0.40  fof(f486,plain,(
% 0.14/0.40    spl3_78 | ~spl3_3 | ~spl3_10),
% 0.14/0.40    inference(avatar_split_clause,[],[f473,f73,f44,f483])).
% 0.14/0.40  fof(f44,plain,(
% 0.14/0.40    spl3_3 <=> r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 0.14/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.14/0.40  fof(f73,plain,(
% 0.14/0.40    spl3_10 <=> ! [X1,X0,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.14/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.14/0.40  fof(f473,plain,(
% 0.14/0.40    r1_tarski(k4_xboole_0(sK0,sK1),sK2) | (~spl3_3 | ~spl3_10)),
% 0.14/0.40    inference(resolution,[],[f74,f46])).
% 0.14/0.40  fof(f46,plain,(
% 0.14/0.40    r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | ~spl3_3),
% 0.14/0.40    inference(avatar_component_clause,[],[f44])).
% 0.14/0.40  fof(f74,plain,(
% 0.14/0.40    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | r1_tarski(k4_xboole_0(X0,X1),X2)) ) | ~spl3_10),
% 0.14/0.40    inference(avatar_component_clause,[],[f73])).
% 0.14/0.40  fof(f227,plain,(
% 0.14/0.40    spl3_34 | ~spl3_5 | ~spl3_30),
% 0.14/0.40    inference(avatar_split_clause,[],[f214,f205,f53,f225])).
% 0.14/0.40  fof(f53,plain,(
% 0.14/0.40    spl3_5 <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.14/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.14/0.40  fof(f205,plain,(
% 0.14/0.40    spl3_30 <=> ! [X0] : (r1_xboole_0(X0,sK2) | ~r1_tarski(X0,sK0))),
% 0.14/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.14/0.40  fof(f214,plain,(
% 0.14/0.40    ( ! [X1] : (r1_xboole_0(k4_xboole_0(sK0,X1),sK2)) ) | (~spl3_5 | ~spl3_30)),
% 0.14/0.40    inference(resolution,[],[f206,f54])).
% 0.14/0.40  fof(f54,plain,(
% 0.14/0.40    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) ) | ~spl3_5),
% 0.14/0.40    inference(avatar_component_clause,[],[f53])).
% 0.14/0.40  fof(f206,plain,(
% 0.14/0.40    ( ! [X0] : (~r1_tarski(X0,sK0) | r1_xboole_0(X0,sK2)) ) | ~spl3_30),
% 0.14/0.40    inference(avatar_component_clause,[],[f205])).
% 0.14/0.40  fof(f207,plain,(
% 0.14/0.40    spl3_30 | ~spl3_2 | ~spl3_11),
% 0.14/0.40    inference(avatar_split_clause,[],[f202,f77,f39,f205])).
% 0.14/0.40  fof(f39,plain,(
% 0.14/0.40    spl3_2 <=> r1_xboole_0(sK0,sK2)),
% 0.14/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.14/0.40  fof(f77,plain,(
% 0.14/0.40    spl3_11 <=> ! [X1,X0,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.14/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.14/0.40  fof(f202,plain,(
% 0.14/0.40    ( ! [X0] : (r1_xboole_0(X0,sK2) | ~r1_tarski(X0,sK0)) ) | (~spl3_2 | ~spl3_11)),
% 0.14/0.40    inference(resolution,[],[f78,f41])).
% 0.14/0.40  fof(f41,plain,(
% 0.14/0.40    r1_xboole_0(sK0,sK2) | ~spl3_2),
% 0.14/0.40    inference(avatar_component_clause,[],[f39])).
% 0.14/0.40  fof(f78,plain,(
% 0.14/0.40    ( ! [X2,X0,X1] : (~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) ) | ~spl3_11),
% 0.14/0.40    inference(avatar_component_clause,[],[f77])).
% 0.14/0.40  fof(f197,plain,(
% 0.14/0.40    ~spl3_28 | spl3_1 | ~spl3_9),
% 0.14/0.40    inference(avatar_split_clause,[],[f190,f69,f34,f194])).
% 0.14/0.40  fof(f34,plain,(
% 0.14/0.40    spl3_1 <=> r1_tarski(sK0,sK1)),
% 0.14/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.14/0.40  fof(f69,plain,(
% 0.14/0.40    spl3_9 <=> ! [X1,X0] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1))),
% 0.14/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.14/0.40  fof(f190,plain,(
% 0.14/0.40    k1_xboole_0 != k4_xboole_0(sK0,sK1) | (spl3_1 | ~spl3_9)),
% 0.14/0.40    inference(resolution,[],[f70,f36])).
% 0.14/0.40  fof(f36,plain,(
% 0.14/0.40    ~r1_tarski(sK0,sK1) | spl3_1),
% 0.14/0.40    inference(avatar_component_clause,[],[f34])).
% 0.14/0.40  fof(f70,plain,(
% 0.14/0.40    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) ) | ~spl3_9),
% 0.14/0.40    inference(avatar_component_clause,[],[f69])).
% 0.14/0.40  fof(f79,plain,(
% 0.14/0.40    spl3_11),
% 0.14/0.40    inference(avatar_split_clause,[],[f32,f77])).
% 0.14/0.40  fof(f32,plain,(
% 0.14/0.40    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.14/0.40    inference(cnf_transformation,[],[f18])).
% 0.14/0.40  fof(f18,plain,(
% 0.14/0.40    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.14/0.40    inference(flattening,[],[f17])).
% 0.14/0.40  fof(f17,plain,(
% 0.14/0.40    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.14/0.40    inference(ennf_transformation,[],[f6])).
% 0.14/0.40  fof(f6,axiom,(
% 0.14/0.40    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.14/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.14/0.40  fof(f75,plain,(
% 0.14/0.40    spl3_10),
% 0.14/0.40    inference(avatar_split_clause,[],[f31,f73])).
% 0.14/0.40  fof(f31,plain,(
% 0.14/0.40    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 0.14/0.40    inference(cnf_transformation,[],[f16])).
% 0.14/0.40  fof(f16,plain,(
% 0.14/0.40    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.14/0.40    inference(ennf_transformation,[],[f5])).
% 0.14/0.40  fof(f5,axiom,(
% 0.14/0.40    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.14/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 0.14/0.40  fof(f71,plain,(
% 0.14/0.40    spl3_9),
% 0.14/0.40    inference(avatar_split_clause,[],[f29,f69])).
% 0.14/0.40  fof(f29,plain,(
% 0.14/0.40    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 0.14/0.40    inference(cnf_transformation,[],[f21])).
% 0.14/0.40  fof(f21,plain,(
% 0.14/0.40    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 0.14/0.40    inference(nnf_transformation,[],[f3])).
% 0.14/0.40  fof(f3,axiom,(
% 0.14/0.40    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.14/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.14/0.40  fof(f59,plain,(
% 0.14/0.40    spl3_6),
% 0.14/0.40    inference(avatar_split_clause,[],[f27,f57])).
% 0.14/0.40  fof(f27,plain,(
% 0.14/0.40    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 0.14/0.40    inference(cnf_transformation,[],[f14])).
% 0.14/0.40  fof(f14,plain,(
% 0.14/0.40    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 0.14/0.40    inference(flattening,[],[f13])).
% 0.14/0.40  fof(f13,plain,(
% 0.14/0.40    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 0.14/0.40    inference(ennf_transformation,[],[f7])).
% 0.14/0.40  fof(f7,axiom,(
% 0.14/0.40    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 0.14/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).
% 0.14/0.40  fof(f55,plain,(
% 0.14/0.40    spl3_5),
% 0.14/0.40    inference(avatar_split_clause,[],[f26,f53])).
% 0.14/0.40  fof(f26,plain,(
% 0.14/0.40    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.14/0.40    inference(cnf_transformation,[],[f4])).
% 0.14/0.40  fof(f4,axiom,(
% 0.14/0.40    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.14/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.14/0.40  fof(f51,plain,(
% 0.14/0.40    spl3_4),
% 0.14/0.40    inference(avatar_split_clause,[],[f25,f49])).
% 0.14/0.40  fof(f25,plain,(
% 0.14/0.40    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.14/0.40    inference(cnf_transformation,[],[f12])).
% 0.14/0.40  fof(f12,plain,(
% 0.14/0.40    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.14/0.40    inference(ennf_transformation,[],[f1])).
% 0.14/0.40  fof(f1,axiom,(
% 0.14/0.40    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.14/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.14/0.40  fof(f47,plain,(
% 0.14/0.40    spl3_3),
% 0.14/0.40    inference(avatar_split_clause,[],[f22,f44])).
% 0.14/0.40  fof(f22,plain,(
% 0.14/0.40    r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 0.14/0.40    inference(cnf_transformation,[],[f20])).
% 0.14/0.40  fof(f20,plain,(
% 0.14/0.40    ~r1_tarski(sK0,sK1) & r1_xboole_0(sK0,sK2) & r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 0.14/0.40    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f19])).
% 0.14/0.40  fof(f19,plain,(
% 0.14/0.40    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => (~r1_tarski(sK0,sK1) & r1_xboole_0(sK0,sK2) & r1_tarski(sK0,k2_xboole_0(sK1,sK2)))),
% 0.14/0.40    introduced(choice_axiom,[])).
% 0.14/0.40  fof(f11,plain,(
% 0.14/0.40    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.14/0.40    inference(flattening,[],[f10])).
% 0.14/0.40  fof(f10,plain,(
% 0.14/0.40    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & (r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 0.14/0.40    inference(ennf_transformation,[],[f9])).
% 0.14/0.40  fof(f9,negated_conjecture,(
% 0.14/0.40    ~! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 0.14/0.40    inference(negated_conjecture,[],[f8])).
% 0.14/0.40  fof(f8,conjecture,(
% 0.14/0.40    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 0.14/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).
% 0.14/0.40  fof(f42,plain,(
% 0.14/0.40    spl3_2),
% 0.14/0.40    inference(avatar_split_clause,[],[f23,f39])).
% 0.14/0.40  fof(f23,plain,(
% 0.14/0.40    r1_xboole_0(sK0,sK2)),
% 0.14/0.40    inference(cnf_transformation,[],[f20])).
% 0.14/0.40  fof(f37,plain,(
% 0.14/0.40    ~spl3_1),
% 0.14/0.40    inference(avatar_split_clause,[],[f24,f34])).
% 0.14/0.40  fof(f24,plain,(
% 0.14/0.40    ~r1_tarski(sK0,sK1)),
% 0.14/0.40    inference(cnf_transformation,[],[f20])).
% 0.14/0.40  % SZS output end Proof for theBenchmark
% 0.14/0.40  % (24110)------------------------------
% 0.14/0.40  % (24110)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.14/0.40  % (24110)Termination reason: Refutation
% 0.14/0.40  
% 0.14/0.40  % (24110)Memory used [KB]: 10746
% 0.14/0.40  % (24110)Time elapsed: 0.007 s
% 0.14/0.40  % (24110)------------------------------
% 0.14/0.40  % (24110)------------------------------
% 0.14/0.40  % (24103)Success in time 0.041 s
%------------------------------------------------------------------------------
