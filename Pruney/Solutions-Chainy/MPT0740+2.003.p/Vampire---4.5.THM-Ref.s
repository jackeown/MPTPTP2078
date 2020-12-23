%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:18 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 119 expanded)
%              Number of leaves         :   20 (  47 expanded)
%              Depth                    :    8
%              Number of atoms          :  207 ( 287 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f271,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f50,f56,f108,f116,f125,f147,f148,f176,f227,f261])).

% (23775)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
fof(f261,plain,
    ( spl4_4
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f256,f224,f91])).

fof(f91,plain,
    ( spl4_4
  <=> v1_ordinal1(k3_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f224,plain,
    ( spl4_19
  <=> r1_tarski(sK1(k3_tarski(sK0)),k3_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f256,plain,
    ( v1_ordinal1(k3_tarski(sK0))
    | ~ spl4_19 ),
    inference(resolution,[],[f226,f32])).

fof(f32,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1(X0),X0)
      | v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_ordinal1)).

fof(f226,plain,
    ( r1_tarski(sK1(k3_tarski(sK0)),k3_tarski(sK0))
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f224])).

fof(f227,plain,
    ( spl4_19
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f219,f113,f224])).

fof(f113,plain,
    ( spl4_7
  <=> r2_hidden(sK1(k3_tarski(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f219,plain,
    ( r1_tarski(sK1(k3_tarski(sK0)),k3_tarski(sK0))
    | ~ spl4_7 ),
    inference(resolution,[],[f115,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(X0,k3_tarski(X1)) ) ),
    inference(resolution,[],[f40,f62])).

fof(f62,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f39,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k3_tarski(X0),X1)
      | ~ r2_hidden(X2,X0)
      | r1_tarski(X2,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(k3_tarski(X0),X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(k3_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X0)
        & r1_tarski(k3_tarski(X0),X1) )
     => r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_setfam_1)).

fof(f115,plain,
    ( r2_hidden(sK1(k3_tarski(sK0)),sK0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f113])).

fof(f176,plain,
    ( spl4_1
    | ~ spl4_2
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f175,f144,f47,f42])).

fof(f42,plain,
    ( spl4_1
  <=> v3_ordinal1(k3_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f47,plain,
    ( spl4_2
  <=> v3_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f144,plain,
    ( spl4_10
  <=> r2_hidden(k3_tarski(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f175,plain,
    ( ~ v3_ordinal1(sK0)
    | v3_ordinal1(k3_tarski(sK0))
    | ~ spl4_10 ),
    inference(resolution,[],[f146,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
     => ( r2_hidden(X0,X1)
       => v3_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_ordinal1)).

fof(f146,plain,
    ( r2_hidden(k3_tarski(sK0),sK0)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f144])).

fof(f148,plain,
    ( sK0 != k3_tarski(sK0)
    | v3_ordinal1(k3_tarski(sK0))
    | ~ v3_ordinal1(sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f147,plain,
    ( spl4_10
    | ~ spl4_4
    | ~ spl4_2
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f142,f118,f47,f91,f144])).

fof(f118,plain,
    ( spl4_8
  <=> r2_xboole_0(k3_tarski(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f142,plain,
    ( ~ v3_ordinal1(sK0)
    | ~ v1_ordinal1(k3_tarski(sK0))
    | r2_hidden(k3_tarski(sK0),sK0)
    | ~ spl4_8 ),
    inference(resolution,[],[f120,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v1_ordinal1(X0)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X0,X1)
          | ~ r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X0,X1)
          | ~ r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_xboole_0(X0,X1)
           => r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_ordinal1)).

fof(f120,plain,
    ( r2_xboole_0(k3_tarski(sK0),sK0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f118])).

fof(f125,plain,
    ( spl4_8
    | spl4_9
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f111,f105,f122,f118])).

% (23775)Refutation not found, incomplete strategy% (23775)------------------------------
% (23775)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (23775)Termination reason: Refutation not found, incomplete strategy

% (23775)Memory used [KB]: 10618
% (23775)Time elapsed: 0.129 s
% (23775)------------------------------
% (23775)------------------------------
fof(f122,plain,
    ( spl4_9
  <=> sK0 = k3_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f105,plain,
    ( spl4_6
  <=> r1_tarski(k3_tarski(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f111,plain,
    ( sK0 = k3_tarski(sK0)
    | r2_xboole_0(k3_tarski(sK0),sK0)
    | ~ spl4_6 ),
    inference(resolution,[],[f107,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f107,plain,
    ( r1_tarski(k3_tarski(sK0),sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f105])).

fof(f116,plain,
    ( spl4_4
    | spl4_7
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f110,f105,f113,f91])).

fof(f110,plain,
    ( r2_hidden(sK1(k3_tarski(sK0)),sK0)
    | v1_ordinal1(k3_tarski(sK0))
    | ~ spl4_6 ),
    inference(resolution,[],[f107,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(sK1(X0),X1)
      | v1_ordinal1(X0) ) ),
    inference(resolution,[],[f37,f31])).

fof(f31,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f108,plain,
    ( spl4_6
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f103,f53,f105])).

fof(f53,plain,
    ( spl4_3
  <=> v1_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f103,plain,
    ( r1_tarski(k3_tarski(sK0),sK0)
    | ~ spl4_3 ),
    inference(duplicate_literal_removal,[],[f100])).

fof(f100,plain,
    ( r1_tarski(k3_tarski(sK0),sK0)
    | r1_tarski(k3_tarski(sK0),sK0)
    | ~ spl4_3 ),
    inference(resolution,[],[f98,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK2(X0,X1),X1)
      | r1_tarski(k3_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X2,X1) )
     => r1_tarski(k3_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_zfmisc_1)).

fof(f98,plain,
    ( ! [X0] :
        ( r1_tarski(sK2(sK0,X0),sK0)
        | r1_tarski(k3_tarski(sK0),X0) )
    | ~ spl4_3 ),
    inference(resolution,[],[f63,f55])).

fof(f55,plain,
    ( v1_ordinal1(sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f53])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v1_ordinal1(X0)
      | r1_tarski(sK2(X0,X1),X0)
      | r1_tarski(k3_tarski(X0),X1) ) ),
    inference(resolution,[],[f34,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | r1_tarski(X1,X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(k3_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f56,plain,
    ( spl4_3
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f51,f47,f53])).

fof(f51,plain,
    ( v1_ordinal1(sK0)
    | ~ spl4_2 ),
    inference(resolution,[],[f29,f49])).

fof(f49,plain,
    ( v3_ordinal1(sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v1_ordinal1(X0) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_ordinal1)).

fof(f50,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f26,f47])).

fof(f26,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ~ v3_ordinal1(k3_tarski(X0))
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => v3_ordinal1(k3_tarski(X0)) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k3_tarski(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_ordinal1)).

fof(f45,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f27,f42])).

fof(f27,plain,(
    ~ v3_ordinal1(k3_tarski(sK0)) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:51:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (23749)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (23749)Refutation not found, incomplete strategy% (23749)------------------------------
% 0.21/0.50  % (23749)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (23766)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.51  % (23749)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (23749)Memory used [KB]: 10618
% 0.21/0.51  % (23749)Time elapsed: 0.085 s
% 0.21/0.51  % (23749)------------------------------
% 0.21/0.51  % (23749)------------------------------
% 0.21/0.51  % (23748)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (23747)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (23758)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.51  % (23762)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (23764)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.52  % (23772)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (23765)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.52  % (23751)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (23751)Refutation not found, incomplete strategy% (23751)------------------------------
% 0.21/0.52  % (23751)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (23751)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (23751)Memory used [KB]: 6140
% 0.21/0.52  % (23751)Time elapsed: 0.108 s
% 0.21/0.52  % (23751)------------------------------
% 0.21/0.52  % (23751)------------------------------
% 0.21/0.53  % (23756)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  % (23757)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.53  % (23778)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.53  % (23752)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (23769)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  % (23774)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.53  % (23763)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (23750)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (23774)Refutation not found, incomplete strategy% (23774)------------------------------
% 0.21/0.54  % (23774)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (23774)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (23774)Memory used [KB]: 6140
% 0.21/0.54  % (23774)Time elapsed: 0.130 s
% 0.21/0.54  % (23774)------------------------------
% 0.21/0.54  % (23774)------------------------------
% 0.21/0.54  % (23764)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % (23754)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (23756)Refutation not found, incomplete strategy% (23756)------------------------------
% 0.21/0.54  % (23756)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (23756)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (23756)Memory used [KB]: 10618
% 0.21/0.54  % (23756)Time elapsed: 0.130 s
% 0.21/0.54  % (23756)------------------------------
% 0.21/0.54  % (23756)------------------------------
% 0.21/0.54  % (23760)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f271,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f45,f50,f56,f108,f116,f125,f147,f148,f176,f227,f261])).
% 0.21/0.54  % (23775)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  fof(f261,plain,(
% 0.21/0.54    spl4_4 | ~spl4_19),
% 0.21/0.54    inference(avatar_split_clause,[],[f256,f224,f91])).
% 0.21/0.54  fof(f91,plain,(
% 0.21/0.54    spl4_4 <=> v1_ordinal1(k3_tarski(sK0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.54  fof(f224,plain,(
% 0.21/0.54    spl4_19 <=> r1_tarski(sK1(k3_tarski(sK0)),k3_tarski(sK0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.21/0.54  fof(f256,plain,(
% 0.21/0.54    v1_ordinal1(k3_tarski(sK0)) | ~spl4_19),
% 0.21/0.54    inference(resolution,[],[f226,f32])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ( ! [X0] : (~r1_tarski(sK1(X0),X0) | v1_ordinal1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r2_hidden(X1,X0) => r1_tarski(X1,X0)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_ordinal1)).
% 0.21/0.54  fof(f226,plain,(
% 0.21/0.54    r1_tarski(sK1(k3_tarski(sK0)),k3_tarski(sK0)) | ~spl4_19),
% 0.21/0.54    inference(avatar_component_clause,[],[f224])).
% 0.21/0.54  fof(f227,plain,(
% 0.21/0.54    spl4_19 | ~spl4_7),
% 0.21/0.54    inference(avatar_split_clause,[],[f219,f113,f224])).
% 0.21/0.54  fof(f113,plain,(
% 0.21/0.54    spl4_7 <=> r2_hidden(sK1(k3_tarski(sK0)),sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.54  fof(f219,plain,(
% 0.21/0.54    r1_tarski(sK1(k3_tarski(sK0)),k3_tarski(sK0)) | ~spl4_7),
% 0.21/0.54    inference(resolution,[],[f115,f72])).
% 0.21/0.54  fof(f72,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(X0,k3_tarski(X1))) )),
% 0.21/0.54    inference(resolution,[],[f40,f62])).
% 0.21/0.54  fof(f62,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f61])).
% 0.21/0.54  fof(f61,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 0.21/0.54    inference(resolution,[],[f39,f38])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f23])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r1_tarski(k3_tarski(X0),X1) | ~r2_hidden(X2,X0) | r1_tarski(X2,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (r1_tarski(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(k3_tarski(X0),X1))),
% 0.21/0.54    inference(flattening,[],[f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (r1_tarski(X2,X1) | (~r2_hidden(X2,X0) | ~r1_tarski(k3_tarski(X0),X1)))),
% 0.21/0.54    inference(ennf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : ((r2_hidden(X2,X0) & r1_tarski(k3_tarski(X0),X1)) => r1_tarski(X2,X1))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_setfam_1)).
% 0.21/0.54  fof(f115,plain,(
% 0.21/0.54    r2_hidden(sK1(k3_tarski(sK0)),sK0) | ~spl4_7),
% 0.21/0.54    inference(avatar_component_clause,[],[f113])).
% 0.21/0.54  fof(f176,plain,(
% 0.21/0.54    spl4_1 | ~spl4_2 | ~spl4_10),
% 0.21/0.54    inference(avatar_split_clause,[],[f175,f144,f47,f42])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    spl4_1 <=> v3_ordinal1(k3_tarski(sK0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    spl4_2 <=> v3_ordinal1(sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.54  fof(f144,plain,(
% 0.21/0.54    spl4_10 <=> r2_hidden(k3_tarski(sK0),sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.54  fof(f175,plain,(
% 0.21/0.54    ~v3_ordinal1(sK0) | v3_ordinal1(k3_tarski(sK0)) | ~spl4_10),
% 0.21/0.54    inference(resolution,[],[f146,f33])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~v3_ordinal1(X1) | v3_ordinal1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f19])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1))),
% 0.21/0.54    inference(flattening,[],[f18])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ! [X0,X1] : ((v3_ordinal1(X0) | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0,X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => v3_ordinal1(X0)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_ordinal1)).
% 0.21/0.54  fof(f146,plain,(
% 0.21/0.54    r2_hidden(k3_tarski(sK0),sK0) | ~spl4_10),
% 0.21/0.54    inference(avatar_component_clause,[],[f144])).
% 0.21/0.54  fof(f148,plain,(
% 0.21/0.54    sK0 != k3_tarski(sK0) | v3_ordinal1(k3_tarski(sK0)) | ~v3_ordinal1(sK0)),
% 0.21/0.54    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.54  fof(f147,plain,(
% 0.21/0.54    spl4_10 | ~spl4_4 | ~spl4_2 | ~spl4_8),
% 0.21/0.54    inference(avatar_split_clause,[],[f142,f118,f47,f91,f144])).
% 0.21/0.54  fof(f118,plain,(
% 0.21/0.54    spl4_8 <=> r2_xboole_0(k3_tarski(sK0),sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.54  fof(f142,plain,(
% 0.21/0.54    ~v3_ordinal1(sK0) | ~v1_ordinal1(k3_tarski(sK0)) | r2_hidden(k3_tarski(sK0),sK0) | ~spl4_8),
% 0.21/0.54    inference(resolution,[],[f120,f28])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | ~v3_ordinal1(X1) | ~v1_ordinal1(X0) | r2_hidden(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f15])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (r2_hidden(X0,X1) | ~r2_xboole_0(X0,X1) | ~v3_ordinal1(X1)) | ~v1_ordinal1(X0))),
% 0.21/0.54    inference(flattening,[],[f14])).
% 0.21/0.54  fof(f14,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : ((r2_hidden(X0,X1) | ~r2_xboole_0(X0,X1)) | ~v3_ordinal1(X1)) | ~v1_ordinal1(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0] : (v1_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_xboole_0(X0,X1) => r2_hidden(X0,X1))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_ordinal1)).
% 0.21/0.54  fof(f120,plain,(
% 0.21/0.54    r2_xboole_0(k3_tarski(sK0),sK0) | ~spl4_8),
% 0.21/0.54    inference(avatar_component_clause,[],[f118])).
% 0.21/0.54  fof(f125,plain,(
% 0.21/0.54    spl4_8 | spl4_9 | ~spl4_6),
% 0.21/0.54    inference(avatar_split_clause,[],[f111,f105,f122,f118])).
% 0.21/0.54  % (23775)Refutation not found, incomplete strategy% (23775)------------------------------
% 0.21/0.54  % (23775)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (23775)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (23775)Memory used [KB]: 10618
% 0.21/0.54  % (23775)Time elapsed: 0.129 s
% 0.21/0.54  % (23775)------------------------------
% 0.21/0.54  % (23775)------------------------------
% 0.21/0.54  fof(f122,plain,(
% 0.21/0.54    spl4_9 <=> sK0 = k3_tarski(sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.54  fof(f105,plain,(
% 0.21/0.54    spl4_6 <=> r1_tarski(k3_tarski(sK0),sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.54  fof(f111,plain,(
% 0.21/0.54    sK0 = k3_tarski(sK0) | r2_xboole_0(k3_tarski(sK0),sK0) | ~spl4_6),
% 0.21/0.54    inference(resolution,[],[f107,f36])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.54    inference(flattening,[],[f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ! [X0,X1] : (r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1)))),
% 0.21/0.54    inference(ennf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,plain,(
% 0.21/0.54    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) => r2_xboole_0(X0,X1))),
% 0.21/0.54    inference(unused_predicate_definition_removal,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.21/0.54  fof(f107,plain,(
% 0.21/0.54    r1_tarski(k3_tarski(sK0),sK0) | ~spl4_6),
% 0.21/0.54    inference(avatar_component_clause,[],[f105])).
% 0.21/0.54  fof(f116,plain,(
% 0.21/0.54    spl4_4 | spl4_7 | ~spl4_6),
% 0.21/0.54    inference(avatar_split_clause,[],[f110,f105,f113,f91])).
% 0.21/0.54  fof(f110,plain,(
% 0.21/0.54    r2_hidden(sK1(k3_tarski(sK0)),sK0) | v1_ordinal1(k3_tarski(sK0)) | ~spl4_6),
% 0.21/0.54    inference(resolution,[],[f107,f66])).
% 0.21/0.54  fof(f66,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(sK1(X0),X1) | v1_ordinal1(X0)) )),
% 0.21/0.54    inference(resolution,[],[f37,f31])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(sK1(X0),X0) | v1_ordinal1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f23])).
% 0.21/0.54  fof(f108,plain,(
% 0.21/0.54    spl4_6 | ~spl4_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f103,f53,f105])).
% 0.21/0.54  fof(f53,plain,(
% 0.21/0.54    spl4_3 <=> v1_ordinal1(sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.54  fof(f103,plain,(
% 0.21/0.54    r1_tarski(k3_tarski(sK0),sK0) | ~spl4_3),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f100])).
% 0.21/0.54  fof(f100,plain,(
% 0.21/0.54    r1_tarski(k3_tarski(sK0),sK0) | r1_tarski(k3_tarski(sK0),sK0) | ~spl4_3),
% 0.21/0.54    inference(resolution,[],[f98,f35])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(sK2(X0,X1),X1) | r1_tarski(k3_tarski(X0),X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f20])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | ? [X2] : (~r1_tarski(X2,X1) & r2_hidden(X2,X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X2,X1)) => r1_tarski(k3_tarski(X0),X1))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_zfmisc_1)).
% 0.21/0.54  fof(f98,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(sK2(sK0,X0),sK0) | r1_tarski(k3_tarski(sK0),X0)) ) | ~spl4_3),
% 0.21/0.54    inference(resolution,[],[f63,f55])).
% 0.21/0.54  fof(f55,plain,(
% 0.21/0.54    v1_ordinal1(sK0) | ~spl4_3),
% 0.21/0.54    inference(avatar_component_clause,[],[f53])).
% 0.21/0.54  fof(f63,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v1_ordinal1(X0) | r1_tarski(sK2(X0,X1),X0) | r1_tarski(k3_tarski(X0),X1)) )),
% 0.21/0.54    inference(resolution,[],[f34,f30])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r2_hidden(X1,X0) | r1_tarski(X1,X0) | ~v1_ordinal1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(k3_tarski(X0),X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f20])).
% 0.21/0.54  fof(f56,plain,(
% 0.21/0.54    spl4_3 | ~spl4_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f51,f47,f53])).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    v1_ordinal1(sK0) | ~spl4_2),
% 0.21/0.54    inference(resolution,[],[f29,f49])).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    v3_ordinal1(sK0) | ~spl4_2),
% 0.21/0.54    inference(avatar_component_clause,[],[f47])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ( ! [X0] : (~v3_ordinal1(X0) | v1_ordinal1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f16])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ! [X0] : (v1_ordinal1(X0) | ~v3_ordinal1(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,plain,(
% 0.21/0.54    ! [X0] : (v3_ordinal1(X0) => v1_ordinal1(X0))),
% 0.21/0.54    inference(pure_predicate_removal,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0] : (v3_ordinal1(X0) => (v2_ordinal1(X0) & v1_ordinal1(X0)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_ordinal1)).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    spl4_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f26,f47])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    v3_ordinal1(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f13])).
% 0.21/0.54  fof(f13,plain,(
% 0.21/0.54    ? [X0] : (~v3_ordinal1(k3_tarski(X0)) & v3_ordinal1(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,negated_conjecture,(
% 0.21/0.54    ~! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k3_tarski(X0)))),
% 0.21/0.54    inference(negated_conjecture,[],[f9])).
% 0.21/0.54  fof(f9,conjecture,(
% 0.21/0.54    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k3_tarski(X0)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_ordinal1)).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    ~spl4_1),
% 0.21/0.54    inference(avatar_split_clause,[],[f27,f42])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ~v3_ordinal1(k3_tarski(sK0))),
% 0.21/0.54    inference(cnf_transformation,[],[f13])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (23764)------------------------------
% 0.21/0.54  % (23764)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (23764)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (23764)Memory used [KB]: 10874
% 0.21/0.54  % (23764)Time elapsed: 0.136 s
% 0.21/0.54  % (23764)------------------------------
% 0.21/0.54  % (23764)------------------------------
% 0.21/0.54  % (23744)Success in time 0.18 s
%------------------------------------------------------------------------------
