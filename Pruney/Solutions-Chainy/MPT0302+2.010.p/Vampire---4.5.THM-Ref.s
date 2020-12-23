%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:00 EST 2020

% Result     : Theorem 1.68s
% Output     : Refutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 142 expanded)
%              Number of leaves         :   16 (  51 expanded)
%              Depth                    :    8
%              Number of atoms          :  179 ( 367 expanded)
%              Number of equality atoms :   39 ( 108 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f197,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f56,f61,f66,f71,f93,f102,f108,f121,f155,f162,f196])).

fof(f196,plain,
    ( spl8_2
    | ~ spl8_5 ),
    inference(avatar_contradiction_clause,[],[f193])).

fof(f193,plain,
    ( $false
    | spl8_2
    | ~ spl8_5 ),
    inference(unit_resulting_resolution,[],[f60,f164,f183,f21])).

fof(f21,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f183,plain,
    ( ! [X2] : r1_tarski(k1_xboole_0,X2)
    | ~ spl8_5 ),
    inference(resolution,[],[f179,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f179,plain,
    ( ! [X1] : ~ r2_hidden(X1,k1_xboole_0)
    | ~ spl8_5 ),
    inference(superposition,[],[f165,f45])).

fof(f45,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f165,plain,
    ( ! [X4,X3] : ~ r2_hidden(X3,k2_zfmisc_1(sK1,X4))
    | ~ spl8_5 ),
    inference(resolution,[],[f89,f51])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK4(X0,X1,X3),X0)
      | ~ r2_hidden(X3,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK4(X0,X1,X3),X0)
      | ~ r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f89,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK1)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl8_5
  <=> ! [X1] : ~ r2_hidden(X1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f164,plain,
    ( ! [X2] : r1_tarski(sK1,X2)
    | ~ spl8_5 ),
    inference(resolution,[],[f89,f23])).

fof(f60,plain,
    ( k1_xboole_0 != sK1
    | spl8_2 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl8_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f162,plain,
    ( spl8_8
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f161,f119,f105])).

fof(f105,plain,
    ( spl8_8
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f119,plain,
    ( spl8_10
  <=> ! [X0] :
        ( r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f161,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl8_10 ),
    inference(duplicate_literal_removal,[],[f158])).

fof(f158,plain,
    ( r1_tarski(sK1,sK0)
    | r1_tarski(sK1,sK0)
    | ~ spl8_10 ),
    inference(resolution,[],[f157,f23])).

fof(f157,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK2(X1,sK0),sK1)
        | r1_tarski(X1,sK0) )
    | ~ spl8_10 ),
    inference(resolution,[],[f120,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f120,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f119])).

fof(f155,plain,
    ( spl8_1
    | ~ spl8_9 ),
    inference(avatar_contradiction_clause,[],[f152])).

fof(f152,plain,
    ( $false
    | spl8_1
    | ~ spl8_9 ),
    inference(unit_resulting_resolution,[],[f55,f123,f142,f21])).

fof(f142,plain,
    ( ! [X2] : r1_tarski(k1_xboole_0,X2)
    | ~ spl8_9 ),
    inference(resolution,[],[f138,f23])).

fof(f138,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl8_9 ),
    inference(superposition,[],[f124,f45])).

fof(f124,plain,
    ( ! [X4,X3] : ~ r2_hidden(X3,k2_zfmisc_1(sK0,X4))
    | ~ spl8_9 ),
    inference(resolution,[],[f117,f51])).

fof(f117,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK0)
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl8_9
  <=> ! [X1] : ~ r2_hidden(X1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f123,plain,
    ( ! [X2] : r1_tarski(sK0,X2)
    | ~ spl8_9 ),
    inference(resolution,[],[f117,f23])).

fof(f55,plain,
    ( k1_xboole_0 != sK0
    | spl8_1 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl8_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f121,plain,
    ( spl8_9
    | spl8_10
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f82,f68,f119,f116])).

fof(f68,plain,
    ( spl8_4
  <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f82,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(X1,sK0) )
    | ~ spl8_4 ),
    inference(resolution,[],[f73,f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f73,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(sK0,sK1))
        | r2_hidden(X3,sK0) )
    | ~ spl8_4 ),
    inference(superposition,[],[f41,f70])).

fof(f70,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f68])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f108,plain,
    ( spl8_3
    | ~ spl8_8
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f103,f99,f105,f63])).

fof(f63,plain,
    ( spl8_3
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f99,plain,
    ( spl8_7
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f103,plain,
    ( ~ r1_tarski(sK1,sK0)
    | sK0 = sK1
    | ~ spl8_7 ),
    inference(resolution,[],[f101,f21])).

fof(f101,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f99])).

fof(f102,plain,
    ( spl8_7
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f97,f91,f99])).

fof(f91,plain,
    ( spl8_6
  <=> ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f97,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl8_6 ),
    inference(duplicate_literal_removal,[],[f95])).

fof(f95,plain,
    ( r1_tarski(sK0,sK1)
    | r1_tarski(sK0,sK1)
    | ~ spl8_6 ),
    inference(resolution,[],[f94,f23])).

fof(f94,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK2(X0,sK1),sK0)
        | r1_tarski(X0,sK1) )
    | ~ spl8_6 ),
    inference(resolution,[],[f92,f24])).

fof(f92,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f91])).

fof(f93,plain,
    ( spl8_5
    | spl8_6
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f77,f68,f91,f88])).

fof(f77,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,sK1)
        | ~ r2_hidden(X1,sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl8_4 ),
    inference(resolution,[],[f72,f42])).

fof(f72,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1))
        | r2_hidden(X0,sK1) )
    | ~ spl8_4 ),
    inference(superposition,[],[f40,f70])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f71,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f14,f68])).

fof(f14,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) ) ),
    inference(flattening,[],[f10])).

% (25419)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
fof(f10,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)
       => ( X0 = X1
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)
     => ( X0 = X1
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t114_zfmisc_1)).

fof(f66,plain,(
    ~ spl8_3 ),
    inference(avatar_split_clause,[],[f17,f63])).

fof(f17,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f11])).

fof(f61,plain,(
    ~ spl8_2 ),
    inference(avatar_split_clause,[],[f16,f58])).

fof(f16,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f11])).

fof(f56,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f15,f53])).

fof(f15,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:58:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.54  % (25416)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.56  % (25410)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.56  % (25432)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.57  % (25434)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.57  % (25410)Refutation not found, incomplete strategy% (25410)------------------------------
% 0.22/0.57  % (25410)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (25410)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (25410)Memory used [KB]: 1663
% 0.22/0.57  % (25410)Time elapsed: 0.136 s
% 0.22/0.57  % (25410)------------------------------
% 0.22/0.57  % (25410)------------------------------
% 0.22/0.57  % (25424)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.68/0.58  % (25418)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.68/0.58  % (25426)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.68/0.59  % (25412)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.68/0.59  % (25432)Refutation found. Thanks to Tanya!
% 1.68/0.59  % SZS status Theorem for theBenchmark
% 1.68/0.59  % SZS output start Proof for theBenchmark
% 1.68/0.59  fof(f197,plain,(
% 1.68/0.59    $false),
% 1.68/0.59    inference(avatar_sat_refutation,[],[f56,f61,f66,f71,f93,f102,f108,f121,f155,f162,f196])).
% 1.68/0.59  fof(f196,plain,(
% 1.68/0.59    spl8_2 | ~spl8_5),
% 1.68/0.59    inference(avatar_contradiction_clause,[],[f193])).
% 1.68/0.59  fof(f193,plain,(
% 1.68/0.59    $false | (spl8_2 | ~spl8_5)),
% 1.68/0.59    inference(unit_resulting_resolution,[],[f60,f164,f183,f21])).
% 1.68/0.59  fof(f21,plain,(
% 1.68/0.59    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 1.68/0.59    inference(cnf_transformation,[],[f3])).
% 1.68/0.59  fof(f3,axiom,(
% 1.68/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.68/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.68/0.59  fof(f183,plain,(
% 1.68/0.59    ( ! [X2] : (r1_tarski(k1_xboole_0,X2)) ) | ~spl8_5),
% 1.68/0.59    inference(resolution,[],[f179,f23])).
% 1.68/0.59  fof(f23,plain,(
% 1.68/0.59    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.68/0.59    inference(cnf_transformation,[],[f12])).
% 1.68/0.59  fof(f12,plain,(
% 1.68/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.68/0.59    inference(ennf_transformation,[],[f1])).
% 1.68/0.59  fof(f1,axiom,(
% 1.68/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.68/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.68/0.59  fof(f179,plain,(
% 1.68/0.59    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) ) | ~spl8_5),
% 1.68/0.59    inference(superposition,[],[f165,f45])).
% 1.68/0.59  fof(f45,plain,(
% 1.68/0.59    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.68/0.59    inference(equality_resolution,[],[f27])).
% 1.68/0.59  fof(f27,plain,(
% 1.68/0.59    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.68/0.59    inference(cnf_transformation,[],[f7])).
% 1.68/0.59  fof(f7,axiom,(
% 1.68/0.59    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.68/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.68/0.59  fof(f165,plain,(
% 1.68/0.59    ( ! [X4,X3] : (~r2_hidden(X3,k2_zfmisc_1(sK1,X4))) ) | ~spl8_5),
% 1.68/0.59    inference(resolution,[],[f89,f51])).
% 1.68/0.59  fof(f51,plain,(
% 1.68/0.59    ( ! [X0,X3,X1] : (r2_hidden(sK4(X0,X1,X3),X0) | ~r2_hidden(X3,k2_zfmisc_1(X0,X1))) )),
% 1.68/0.59    inference(equality_resolution,[],[f32])).
% 1.68/0.59  fof(f32,plain,(
% 1.68/0.59    ( ! [X2,X0,X3,X1] : (r2_hidden(sK4(X0,X1,X3),X0) | ~r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.68/0.59    inference(cnf_transformation,[],[f5])).
% 1.68/0.59  fof(f5,axiom,(
% 1.68/0.59    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 1.68/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 1.68/0.59  fof(f89,plain,(
% 1.68/0.59    ( ! [X1] : (~r2_hidden(X1,sK1)) ) | ~spl8_5),
% 1.68/0.59    inference(avatar_component_clause,[],[f88])).
% 1.68/0.59  fof(f88,plain,(
% 1.68/0.59    spl8_5 <=> ! [X1] : ~r2_hidden(X1,sK1)),
% 1.68/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 1.68/0.59  fof(f164,plain,(
% 1.68/0.59    ( ! [X2] : (r1_tarski(sK1,X2)) ) | ~spl8_5),
% 1.68/0.59    inference(resolution,[],[f89,f23])).
% 1.68/0.59  fof(f60,plain,(
% 1.68/0.59    k1_xboole_0 != sK1 | spl8_2),
% 1.68/0.59    inference(avatar_component_clause,[],[f58])).
% 1.68/0.59  fof(f58,plain,(
% 1.68/0.59    spl8_2 <=> k1_xboole_0 = sK1),
% 1.68/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 1.68/0.59  fof(f162,plain,(
% 1.68/0.59    spl8_8 | ~spl8_10),
% 1.68/0.59    inference(avatar_split_clause,[],[f161,f119,f105])).
% 1.68/0.59  fof(f105,plain,(
% 1.68/0.59    spl8_8 <=> r1_tarski(sK1,sK0)),
% 1.68/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 1.68/0.59  fof(f119,plain,(
% 1.68/0.59    spl8_10 <=> ! [X0] : (r2_hidden(X0,sK0) | ~r2_hidden(X0,sK1))),
% 1.68/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 1.68/0.59  fof(f161,plain,(
% 1.68/0.59    r1_tarski(sK1,sK0) | ~spl8_10),
% 1.68/0.59    inference(duplicate_literal_removal,[],[f158])).
% 1.68/0.59  fof(f158,plain,(
% 1.68/0.59    r1_tarski(sK1,sK0) | r1_tarski(sK1,sK0) | ~spl8_10),
% 1.68/0.59    inference(resolution,[],[f157,f23])).
% 1.68/0.59  fof(f157,plain,(
% 1.68/0.59    ( ! [X1] : (~r2_hidden(sK2(X1,sK0),sK1) | r1_tarski(X1,sK0)) ) | ~spl8_10),
% 1.68/0.59    inference(resolution,[],[f120,f24])).
% 1.68/0.59  fof(f24,plain,(
% 1.68/0.59    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.68/0.59    inference(cnf_transformation,[],[f12])).
% 1.68/0.59  fof(f120,plain,(
% 1.68/0.59    ( ! [X0] : (r2_hidden(X0,sK0) | ~r2_hidden(X0,sK1)) ) | ~spl8_10),
% 1.68/0.59    inference(avatar_component_clause,[],[f119])).
% 1.68/0.59  fof(f155,plain,(
% 1.68/0.59    spl8_1 | ~spl8_9),
% 1.68/0.59    inference(avatar_contradiction_clause,[],[f152])).
% 1.68/0.59  fof(f152,plain,(
% 1.68/0.59    $false | (spl8_1 | ~spl8_9)),
% 1.68/0.59    inference(unit_resulting_resolution,[],[f55,f123,f142,f21])).
% 1.68/0.59  fof(f142,plain,(
% 1.68/0.59    ( ! [X2] : (r1_tarski(k1_xboole_0,X2)) ) | ~spl8_9),
% 1.68/0.59    inference(resolution,[],[f138,f23])).
% 1.68/0.59  fof(f138,plain,(
% 1.68/0.59    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl8_9),
% 1.68/0.59    inference(superposition,[],[f124,f45])).
% 1.68/0.59  fof(f124,plain,(
% 1.68/0.59    ( ! [X4,X3] : (~r2_hidden(X3,k2_zfmisc_1(sK0,X4))) ) | ~spl8_9),
% 1.68/0.59    inference(resolution,[],[f117,f51])).
% 1.68/0.59  fof(f117,plain,(
% 1.68/0.59    ( ! [X1] : (~r2_hidden(X1,sK0)) ) | ~spl8_9),
% 1.68/0.59    inference(avatar_component_clause,[],[f116])).
% 1.68/0.59  fof(f116,plain,(
% 1.68/0.59    spl8_9 <=> ! [X1] : ~r2_hidden(X1,sK0)),
% 1.68/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 1.68/0.59  fof(f123,plain,(
% 1.68/0.59    ( ! [X2] : (r1_tarski(sK0,X2)) ) | ~spl8_9),
% 1.68/0.59    inference(resolution,[],[f117,f23])).
% 1.68/0.59  fof(f55,plain,(
% 1.68/0.59    k1_xboole_0 != sK0 | spl8_1),
% 1.68/0.59    inference(avatar_component_clause,[],[f53])).
% 1.68/0.59  fof(f53,plain,(
% 1.68/0.59    spl8_1 <=> k1_xboole_0 = sK0),
% 1.68/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.68/0.59  fof(f121,plain,(
% 1.68/0.59    spl8_9 | spl8_10 | ~spl8_4),
% 1.68/0.59    inference(avatar_split_clause,[],[f82,f68,f119,f116])).
% 1.68/0.59  fof(f68,plain,(
% 1.68/0.59    spl8_4 <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0)),
% 1.68/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 1.68/0.59  fof(f82,plain,(
% 1.68/0.59    ( ! [X0,X1] : (r2_hidden(X0,sK0) | ~r2_hidden(X0,sK1) | ~r2_hidden(X1,sK0)) ) | ~spl8_4),
% 1.68/0.59    inference(resolution,[],[f73,f42])).
% 1.68/0.59  fof(f42,plain,(
% 1.68/0.59    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 1.68/0.59    inference(cnf_transformation,[],[f6])).
% 1.68/0.59  fof(f6,axiom,(
% 1.68/0.59    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 1.68/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 1.68/0.59  fof(f73,plain,(
% 1.68/0.59    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(sK0,sK1)) | r2_hidden(X3,sK0)) ) | ~spl8_4),
% 1.68/0.59    inference(superposition,[],[f41,f70])).
% 1.68/0.59  fof(f70,plain,(
% 1.68/0.59    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0) | ~spl8_4),
% 1.68/0.59    inference(avatar_component_clause,[],[f68])).
% 1.68/0.59  fof(f41,plain,(
% 1.68/0.59    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 1.68/0.59    inference(cnf_transformation,[],[f6])).
% 1.68/0.59  fof(f108,plain,(
% 1.68/0.59    spl8_3 | ~spl8_8 | ~spl8_7),
% 1.68/0.59    inference(avatar_split_clause,[],[f103,f99,f105,f63])).
% 1.68/0.59  fof(f63,plain,(
% 1.68/0.59    spl8_3 <=> sK0 = sK1),
% 1.68/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 1.68/0.59  fof(f99,plain,(
% 1.68/0.59    spl8_7 <=> r1_tarski(sK0,sK1)),
% 1.68/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 1.68/0.59  fof(f103,plain,(
% 1.68/0.59    ~r1_tarski(sK1,sK0) | sK0 = sK1 | ~spl8_7),
% 1.68/0.59    inference(resolution,[],[f101,f21])).
% 1.68/0.59  fof(f101,plain,(
% 1.68/0.59    r1_tarski(sK0,sK1) | ~spl8_7),
% 1.68/0.59    inference(avatar_component_clause,[],[f99])).
% 1.68/0.59  fof(f102,plain,(
% 1.68/0.59    spl8_7 | ~spl8_6),
% 1.68/0.59    inference(avatar_split_clause,[],[f97,f91,f99])).
% 1.68/0.59  fof(f91,plain,(
% 1.68/0.59    spl8_6 <=> ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0))),
% 1.68/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 1.68/0.59  fof(f97,plain,(
% 1.68/0.59    r1_tarski(sK0,sK1) | ~spl8_6),
% 1.68/0.59    inference(duplicate_literal_removal,[],[f95])).
% 1.68/0.59  fof(f95,plain,(
% 1.68/0.59    r1_tarski(sK0,sK1) | r1_tarski(sK0,sK1) | ~spl8_6),
% 1.68/0.59    inference(resolution,[],[f94,f23])).
% 1.68/0.59  fof(f94,plain,(
% 1.68/0.59    ( ! [X0] : (~r2_hidden(sK2(X0,sK1),sK0) | r1_tarski(X0,sK1)) ) | ~spl8_6),
% 1.68/0.59    inference(resolution,[],[f92,f24])).
% 1.68/0.59  fof(f92,plain,(
% 1.68/0.59    ( ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0)) ) | ~spl8_6),
% 1.68/0.59    inference(avatar_component_clause,[],[f91])).
% 1.68/0.59  fof(f93,plain,(
% 1.68/0.59    spl8_5 | spl8_6 | ~spl8_4),
% 1.68/0.59    inference(avatar_split_clause,[],[f77,f68,f91,f88])).
% 1.68/0.59  fof(f77,plain,(
% 1.68/0.59    ( ! [X0,X1] : (r2_hidden(X0,sK1) | ~r2_hidden(X1,sK1) | ~r2_hidden(X0,sK0)) ) | ~spl8_4),
% 1.68/0.59    inference(resolution,[],[f72,f42])).
% 1.68/0.59  fof(f72,plain,(
% 1.68/0.59    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1)) | r2_hidden(X0,sK1)) ) | ~spl8_4),
% 1.68/0.59    inference(superposition,[],[f40,f70])).
% 1.68/0.59  fof(f40,plain,(
% 1.68/0.59    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 1.68/0.59    inference(cnf_transformation,[],[f6])).
% 1.68/0.59  fof(f71,plain,(
% 1.68/0.59    spl8_4),
% 1.68/0.59    inference(avatar_split_clause,[],[f14,f68])).
% 1.68/0.59  fof(f14,plain,(
% 1.68/0.59    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0)),
% 1.68/0.59    inference(cnf_transformation,[],[f11])).
% 1.68/0.59  fof(f11,plain,(
% 1.68/0.59    ? [X0,X1] : (X0 != X1 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0))),
% 1.68/0.59    inference(flattening,[],[f10])).
% 1.68/0.59  % (25419)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.68/0.59  fof(f10,plain,(
% 1.68/0.59    ? [X0,X1] : ((X0 != X1 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0))),
% 1.68/0.59    inference(ennf_transformation,[],[f9])).
% 1.68/0.59  fof(f9,negated_conjecture,(
% 1.68/0.59    ~! [X0,X1] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) => (X0 = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.68/0.59    inference(negated_conjecture,[],[f8])).
% 1.68/0.59  fof(f8,conjecture,(
% 1.68/0.59    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) => (X0 = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.68/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t114_zfmisc_1)).
% 1.68/0.59  fof(f66,plain,(
% 1.68/0.59    ~spl8_3),
% 1.68/0.59    inference(avatar_split_clause,[],[f17,f63])).
% 1.68/0.59  fof(f17,plain,(
% 1.68/0.59    sK0 != sK1),
% 1.68/0.59    inference(cnf_transformation,[],[f11])).
% 1.68/0.59  fof(f61,plain,(
% 1.68/0.59    ~spl8_2),
% 1.68/0.59    inference(avatar_split_clause,[],[f16,f58])).
% 1.68/0.59  fof(f16,plain,(
% 1.68/0.59    k1_xboole_0 != sK1),
% 1.68/0.59    inference(cnf_transformation,[],[f11])).
% 1.68/0.59  fof(f56,plain,(
% 1.68/0.59    ~spl8_1),
% 1.68/0.59    inference(avatar_split_clause,[],[f15,f53])).
% 1.68/0.59  fof(f15,plain,(
% 1.68/0.59    k1_xboole_0 != sK0),
% 1.68/0.59    inference(cnf_transformation,[],[f11])).
% 1.68/0.59  % SZS output end Proof for theBenchmark
% 1.68/0.59  % (25432)------------------------------
% 1.68/0.59  % (25432)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.68/0.59  % (25432)Termination reason: Refutation
% 1.68/0.59  
% 1.68/0.59  % (25432)Memory used [KB]: 10746
% 1.68/0.59  % (25432)Time elapsed: 0.155 s
% 1.68/0.59  % (25432)------------------------------
% 1.68/0.59  % (25432)------------------------------
% 1.68/0.59  % (25413)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.68/0.59  % (25409)Success in time 0.227 s
%------------------------------------------------------------------------------
