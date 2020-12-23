%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:01 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 140 expanded)
%              Number of leaves         :   16 (  54 expanded)
%              Depth                    :    8
%              Number of atoms          :  199 ( 368 expanded)
%              Number of equality atoms :   45 ( 118 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f286,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f40,f45,f50,f55,f67,f90,f104,f121,f216,f230,f259,f285])).

fof(f285,plain,
    ( spl6_3
    | ~ spl6_10
    | ~ spl6_18 ),
    inference(avatar_contradiction_clause,[],[f284])).

fof(f284,plain,
    ( $false
    | spl6_3
    | ~ spl6_10
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f283,f49])).

fof(f49,plain,
    ( sK0 != sK1
    | spl6_3 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl6_3
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f283,plain,
    ( sK0 = sK1
    | ~ spl6_10
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f281,f103])).

fof(f103,plain,
    ( r2_hidden(sK3(sK1,sK0),sK1)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl6_10
  <=> r2_hidden(sK3(sK1,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f281,plain,
    ( ~ r2_hidden(sK3(sK1,sK0),sK1)
    | sK0 = sK1
    | ~ spl6_18 ),
    inference(resolution,[],[f258,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | ~ r2_hidden(sK3(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(f258,plain,
    ( r2_hidden(sK3(sK1,sK0),sK0)
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f256])).

fof(f256,plain,
    ( spl6_18
  <=> r2_hidden(sK3(sK1,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f259,plain,
    ( spl6_18
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f124,f101,f74,f256])).

fof(f74,plain,
    ( spl6_8
  <=> ! [X0] :
        ( r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f124,plain,
    ( r2_hidden(sK3(sK1,sK0),sK0)
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(resolution,[],[f103,f75])).

fof(f75,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | r2_hidden(X0,sK0) )
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f74])).

fof(f230,plain,
    ( spl6_7
    | spl6_8
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f178,f52,f74,f71])).

fof(f71,plain,
    ( spl6_7
  <=> ! [X1] : ~ r2_hidden(X1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f52,plain,
    ( spl6_4
  <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f178,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(X1,sK0) )
    | ~ spl6_4 ),
    inference(resolution,[],[f57,f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f57,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(sK0,sK1))
        | r2_hidden(X3,sK0) )
    | ~ spl6_4 ),
    inference(superposition,[],[f33,f54])).

fof(f54,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f52])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f216,plain,
    ( spl6_1
    | ~ spl6_9 ),
    inference(avatar_contradiction_clause,[],[f215])).

fof(f215,plain,
    ( $false
    | spl6_1
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f212,f39])).

fof(f39,plain,
    ( k1_xboole_0 != sK0
    | spl6_1 ),
    inference(avatar_component_clause,[],[f37])).

fof(f37,plain,
    ( spl6_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f212,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_9 ),
    inference(resolution,[],[f193,f19])).

fof(f19,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f193,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | sK0 = X0 )
    | ~ spl6_9 ),
    inference(resolution,[],[f89,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f89,plain,
    ( ! [X1] :
        ( r2_hidden(sK3(X1,sK0),X1)
        | sK0 = X1 )
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl6_9
  <=> ! [X1] :
        ( r2_hidden(sK3(X1,sK0),X1)
        | sK0 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f121,plain,
    ( spl6_2
    | ~ spl6_5 ),
    inference(avatar_contradiction_clause,[],[f120])).

fof(f120,plain,
    ( $false
    | spl6_2
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f118,f44])).

fof(f44,plain,
    ( k1_xboole_0 != sK1
    | spl6_2 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl6_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f118,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_5 ),
    inference(resolution,[],[f112,f19])).

fof(f112,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | sK1 = X0 )
    | ~ spl6_5 ),
    inference(resolution,[],[f110,f21])).

fof(f110,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(X0,sK1),X0)
        | sK1 = X0 )
    | ~ spl6_5 ),
    inference(resolution,[],[f63,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r2_hidden(sK3(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f63,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK1)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl6_5
  <=> ! [X1] : ~ r2_hidden(X1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f104,plain,
    ( spl6_10
    | spl6_3
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f97,f65,f47,f101])).

fof(f65,plain,
    ( spl6_6
  <=> ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f97,plain,
    ( r2_hidden(sK3(sK1,sK0),sK1)
    | spl6_3
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f96,f49])).

fof(f96,plain,
    ( r2_hidden(sK3(sK1,sK0),sK1)
    | sK0 = sK1
    | ~ spl6_6 ),
    inference(factoring,[],[f69])).

fof(f69,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(X0,sK0),sK1)
        | r2_hidden(sK3(X0,sK0),X0)
        | sK0 = X0 )
    | ~ spl6_6 ),
    inference(resolution,[],[f66,f22])).

fof(f66,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | r2_hidden(X0,sK1) )
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f65])).

fof(f90,plain,
    ( spl6_9
    | spl6_5
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f79,f71,f52,f62,f88])).

fof(f79,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK1)
        | r2_hidden(sK3(X1,sK0),X1)
        | sK0 = X1 )
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f68,f77])).

fof(f77,plain,
    ( ! [X2,X3] : ~ r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(sK0,sK1))
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f57,f72])).

fof(f72,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK0)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f71])).

fof(f68,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK1)
        | r2_hidden(k4_tarski(X0,sK3(X1,sK0)),k2_zfmisc_1(sK0,sK1))
        | r2_hidden(sK3(X1,sK0),X1)
        | sK0 = X1 )
    | ~ spl6_4 ),
    inference(resolution,[],[f58,f22])).

fof(f58,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(X5,sK0)
        | r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK0,sK1))
        | ~ r2_hidden(X4,sK1) )
    | ~ spl6_4 ),
    inference(superposition,[],[f34,f54])).

fof(f67,plain,
    ( spl6_5
    | spl6_6
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f59,f52,f65,f62])).

fof(f59,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,sK1)
        | ~ r2_hidden(X1,sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl6_4 ),
    inference(resolution,[],[f56,f34])).

fof(f56,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1))
        | r2_hidden(X0,sK1) )
    | ~ spl6_4 ),
    inference(superposition,[],[f32,f54])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f55,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f15,f52])).

fof(f15,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) ) ),
    inference(flattening,[],[f10])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_zfmisc_1)).

fof(f50,plain,(
    ~ spl6_3 ),
    inference(avatar_split_clause,[],[f18,f47])).

fof(f18,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f11])).

fof(f45,plain,(
    ~ spl6_2 ),
    inference(avatar_split_clause,[],[f17,f42])).

fof(f17,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f11])).

fof(f40,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f16,f37])).

fof(f16,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:50:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.45  % (23650)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.48  % (23658)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.49  % (23649)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (23671)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.50  % (23668)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.50  % (23663)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.50  % (23649)Refutation not found, incomplete strategy% (23649)------------------------------
% 0.21/0.50  % (23649)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (23652)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.50  % (23658)Refutation not found, incomplete strategy% (23658)------------------------------
% 0.21/0.50  % (23658)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (23649)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (23649)Memory used [KB]: 10746
% 0.21/0.50  % (23649)Time elapsed: 0.104 s
% 0.21/0.50  % (23649)------------------------------
% 0.21/0.50  % (23649)------------------------------
% 0.21/0.50  % (23651)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (23658)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (23658)Memory used [KB]: 10618
% 0.21/0.50  % (23658)Time elapsed: 0.108 s
% 0.21/0.50  % (23658)------------------------------
% 0.21/0.50  % (23658)------------------------------
% 0.21/0.51  % (23677)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.51  % (23653)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (23672)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.51  % (23657)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.51  % (23660)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (23668)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % (23664)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.52  % (23667)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.52  % (23657)Refutation not found, incomplete strategy% (23657)------------------------------
% 0.21/0.52  % (23657)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (23657)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (23657)Memory used [KB]: 10618
% 0.21/0.52  % (23657)Time elapsed: 0.116 s
% 0.21/0.52  % (23657)------------------------------
% 0.21/0.52  % (23657)------------------------------
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f286,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f40,f45,f50,f55,f67,f90,f104,f121,f216,f230,f259,f285])).
% 0.21/0.52  fof(f285,plain,(
% 0.21/0.52    spl6_3 | ~spl6_10 | ~spl6_18),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f284])).
% 0.21/0.52  fof(f284,plain,(
% 0.21/0.52    $false | (spl6_3 | ~spl6_10 | ~spl6_18)),
% 0.21/0.52    inference(subsumption_resolution,[],[f283,f49])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    sK0 != sK1 | spl6_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f47])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    spl6_3 <=> sK0 = sK1),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.52  fof(f283,plain,(
% 0.21/0.52    sK0 = sK1 | (~spl6_10 | ~spl6_18)),
% 0.21/0.52    inference(subsumption_resolution,[],[f281,f103])).
% 0.21/0.52  fof(f103,plain,(
% 0.21/0.52    r2_hidden(sK3(sK1,sK0),sK1) | ~spl6_10),
% 0.21/0.52    inference(avatar_component_clause,[],[f101])).
% 0.21/0.52  fof(f101,plain,(
% 0.21/0.52    spl6_10 <=> r2_hidden(sK3(sK1,sK0),sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.21/0.52  fof(f281,plain,(
% 0.21/0.52    ~r2_hidden(sK3(sK1,sK0),sK1) | sK0 = sK1 | ~spl6_18),
% 0.21/0.52    inference(resolution,[],[f258,f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | ~r2_hidden(sK3(X0,X1),X0) | X0 = X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).
% 0.21/0.52  fof(f258,plain,(
% 0.21/0.52    r2_hidden(sK3(sK1,sK0),sK0) | ~spl6_18),
% 0.21/0.52    inference(avatar_component_clause,[],[f256])).
% 0.21/0.52  fof(f256,plain,(
% 0.21/0.52    spl6_18 <=> r2_hidden(sK3(sK1,sK0),sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.21/0.52  fof(f259,plain,(
% 0.21/0.52    spl6_18 | ~spl6_8 | ~spl6_10),
% 0.21/0.52    inference(avatar_split_clause,[],[f124,f101,f74,f256])).
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    spl6_8 <=> ! [X0] : (r2_hidden(X0,sK0) | ~r2_hidden(X0,sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.21/0.52  fof(f124,plain,(
% 0.21/0.52    r2_hidden(sK3(sK1,sK0),sK0) | (~spl6_8 | ~spl6_10)),
% 0.21/0.52    inference(resolution,[],[f103,f75])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(X0,sK0)) ) | ~spl6_8),
% 0.21/0.52    inference(avatar_component_clause,[],[f74])).
% 0.21/0.52  fof(f230,plain,(
% 0.21/0.52    spl6_7 | spl6_8 | ~spl6_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f178,f52,f74,f71])).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    spl6_7 <=> ! [X1] : ~r2_hidden(X1,sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    spl6_4 <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.52  fof(f178,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(X0,sK0) | ~r2_hidden(X0,sK1) | ~r2_hidden(X1,sK0)) ) | ~spl6_4),
% 0.21/0.52    inference(resolution,[],[f57,f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(sK0,sK1)) | r2_hidden(X3,sK0)) ) | ~spl6_4),
% 0.21/0.52    inference(superposition,[],[f33,f54])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0) | ~spl6_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f52])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f216,plain,(
% 0.21/0.52    spl6_1 | ~spl6_9),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f215])).
% 0.21/0.52  fof(f215,plain,(
% 0.21/0.52    $false | (spl6_1 | ~spl6_9)),
% 0.21/0.52    inference(subsumption_resolution,[],[f212,f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    k1_xboole_0 != sK0 | spl6_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    spl6_1 <=> k1_xboole_0 = sK0),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.52  fof(f212,plain,(
% 0.21/0.52    k1_xboole_0 = sK0 | ~spl6_9),
% 0.21/0.52    inference(resolution,[],[f193,f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    v1_xboole_0(k1_xboole_0)),
% 0.21/0.52    inference(cnf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    v1_xboole_0(k1_xboole_0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.52  fof(f193,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_xboole_0(X0) | sK0 = X0) ) | ~spl6_9),
% 0.21/0.52    inference(resolution,[],[f89,f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.52  fof(f89,plain,(
% 0.21/0.52    ( ! [X1] : (r2_hidden(sK3(X1,sK0),X1) | sK0 = X1) ) | ~spl6_9),
% 0.21/0.52    inference(avatar_component_clause,[],[f88])).
% 0.21/0.52  fof(f88,plain,(
% 0.21/0.52    spl6_9 <=> ! [X1] : (r2_hidden(sK3(X1,sK0),X1) | sK0 = X1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.21/0.52  fof(f121,plain,(
% 0.21/0.52    spl6_2 | ~spl6_5),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f120])).
% 0.21/0.52  fof(f120,plain,(
% 0.21/0.52    $false | (spl6_2 | ~spl6_5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f118,f44])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    k1_xboole_0 != sK1 | spl6_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    spl6_2 <=> k1_xboole_0 = sK1),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.52  fof(f118,plain,(
% 0.21/0.52    k1_xboole_0 = sK1 | ~spl6_5),
% 0.21/0.52    inference(resolution,[],[f112,f19])).
% 0.21/0.52  fof(f112,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_xboole_0(X0) | sK1 = X0) ) | ~spl6_5),
% 0.21/0.52    inference(resolution,[],[f110,f21])).
% 0.21/0.52  fof(f110,plain,(
% 0.21/0.52    ( ! [X0] : (r2_hidden(sK3(X0,sK1),X0) | sK1 = X0) ) | ~spl6_5),
% 0.21/0.52    inference(resolution,[],[f63,f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | r2_hidden(sK3(X0,X1),X0) | X0 = X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    ( ! [X1] : (~r2_hidden(X1,sK1)) ) | ~spl6_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f62])).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    spl6_5 <=> ! [X1] : ~r2_hidden(X1,sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.52  fof(f104,plain,(
% 0.21/0.52    spl6_10 | spl6_3 | ~spl6_6),
% 0.21/0.52    inference(avatar_split_clause,[],[f97,f65,f47,f101])).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    spl6_6 <=> ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.52  fof(f97,plain,(
% 0.21/0.52    r2_hidden(sK3(sK1,sK0),sK1) | (spl6_3 | ~spl6_6)),
% 0.21/0.52    inference(subsumption_resolution,[],[f96,f49])).
% 0.21/0.52  fof(f96,plain,(
% 0.21/0.52    r2_hidden(sK3(sK1,sK0),sK1) | sK0 = sK1 | ~spl6_6),
% 0.21/0.52    inference(factoring,[],[f69])).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    ( ! [X0] : (r2_hidden(sK3(X0,sK0),sK1) | r2_hidden(sK3(X0,sK0),X0) | sK0 = X0) ) | ~spl6_6),
% 0.21/0.52    inference(resolution,[],[f66,f22])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(X0,sK1)) ) | ~spl6_6),
% 0.21/0.52    inference(avatar_component_clause,[],[f65])).
% 0.21/0.52  fof(f90,plain,(
% 0.21/0.52    spl6_9 | spl6_5 | ~spl6_4 | ~spl6_7),
% 0.21/0.52    inference(avatar_split_clause,[],[f79,f71,f52,f62,f88])).
% 0.21/0.52  fof(f79,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(X0,sK1) | r2_hidden(sK3(X1,sK0),X1) | sK0 = X1) ) | (~spl6_4 | ~spl6_7)),
% 0.21/0.52    inference(subsumption_resolution,[],[f68,f77])).
% 0.21/0.52  fof(f77,plain,(
% 0.21/0.52    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(sK0,sK1))) ) | (~spl6_4 | ~spl6_7)),
% 0.21/0.52    inference(subsumption_resolution,[],[f57,f72])).
% 0.21/0.52  fof(f72,plain,(
% 0.21/0.52    ( ! [X1] : (~r2_hidden(X1,sK0)) ) | ~spl6_7),
% 0.21/0.52    inference(avatar_component_clause,[],[f71])).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(X0,sK1) | r2_hidden(k4_tarski(X0,sK3(X1,sK0)),k2_zfmisc_1(sK0,sK1)) | r2_hidden(sK3(X1,sK0),X1) | sK0 = X1) ) | ~spl6_4),
% 0.21/0.52    inference(resolution,[],[f58,f22])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    ( ! [X4,X5] : (~r2_hidden(X5,sK0) | r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK0,sK1)) | ~r2_hidden(X4,sK1)) ) | ~spl6_4),
% 0.21/0.52    inference(superposition,[],[f34,f54])).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    spl6_5 | spl6_6 | ~spl6_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f59,f52,f65,f62])).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(X0,sK1) | ~r2_hidden(X1,sK1) | ~r2_hidden(X0,sK0)) ) | ~spl6_4),
% 0.21/0.52    inference(resolution,[],[f56,f34])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1)) | r2_hidden(X0,sK1)) ) | ~spl6_4),
% 0.21/0.52    inference(superposition,[],[f32,f54])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    spl6_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f15,f52])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ? [X0,X1] : (X0 != X1 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0))),
% 0.21/0.52    inference(flattening,[],[f10])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    ? [X0,X1] : ((X0 != X1 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) => (X0 = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.52    inference(negated_conjecture,[],[f8])).
% 0.21/0.52  fof(f8,conjecture,(
% 0.21/0.52    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) => (X0 = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_zfmisc_1)).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    ~spl6_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f18,f47])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    sK0 != sK1),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ~spl6_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f17,f42])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    k1_xboole_0 != sK1),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ~spl6_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f16,f37])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    k1_xboole_0 != sK0),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (23668)------------------------------
% 0.21/0.52  % (23668)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (23668)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (23668)Memory used [KB]: 10874
% 0.21/0.52  % (23668)Time elapsed: 0.120 s
% 0.21/0.52  % (23668)------------------------------
% 0.21/0.52  % (23668)------------------------------
% 0.21/0.52  % (23644)Success in time 0.165 s
%------------------------------------------------------------------------------
