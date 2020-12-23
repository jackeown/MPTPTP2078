%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:02 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 118 expanded)
%              Number of leaves         :   16 (  45 expanded)
%              Depth                    :    7
%              Number of atoms          :  163 ( 303 expanded)
%              Number of equality atoms :   30 (  90 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f159,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f58,f63,f68,f82,f101,f111,f118,f132,f142,f157])).

fof(f157,plain,
    ( spl8_2
    | ~ spl8_5 ),
    inference(avatar_contradiction_clause,[],[f154])).

fof(f154,plain,
    ( $false
    | spl8_2
    | ~ spl8_5 ),
    inference(unit_resulting_resolution,[],[f23,f57,f149,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f149,plain,
    ( ! [X7] : ~ r2_xboole_0(X7,sK1)
    | ~ spl8_5 ),
    inference(resolution,[],[f78,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ~ r2_hidden(X2,X0)
              & r2_hidden(X2,X1) )
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_0)).

fof(f78,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK1)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl8_5
  <=> ! [X1] : ~ r2_hidden(X1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f57,plain,
    ( k1_xboole_0 != sK1
    | spl8_2 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl8_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f23,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f142,plain,
    ( spl8_9
    | ~ spl8_11 ),
    inference(avatar_split_clause,[],[f141,f116,f108])).

fof(f108,plain,
    ( spl8_9
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f116,plain,
    ( spl8_11
  <=> ! [X0] :
        ( r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f141,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl8_11 ),
    inference(duplicate_literal_removal,[],[f138])).

fof(f138,plain,
    ( r1_tarski(sK1,sK0)
    | r1_tarski(sK1,sK0)
    | ~ spl8_11 ),
    inference(resolution,[],[f134,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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

fof(f134,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK3(X1,sK0),sK1)
        | r1_tarski(X1,sK0) )
    | ~ spl8_11 ),
    inference(resolution,[],[f117,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f117,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f116])).

fof(f132,plain,
    ( spl8_1
    | ~ spl8_10 ),
    inference(avatar_contradiction_clause,[],[f130])).

fof(f130,plain,
    ( $false
    | spl8_1
    | ~ spl8_10 ),
    inference(unit_resulting_resolution,[],[f23,f52,f125,f30])).

fof(f125,plain,
    ( ! [X7] : ~ r2_xboole_0(X7,sK0)
    | ~ spl8_10 ),
    inference(resolution,[],[f114,f40])).

fof(f114,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK0)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl8_10
  <=> ! [X1] : ~ r2_hidden(X1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f52,plain,
    ( k1_xboole_0 != sK0
    | spl8_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl8_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f118,plain,
    ( spl8_10
    | spl8_11
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f74,f65,f116,f113])).

fof(f65,plain,
    ( spl8_4
  <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f74,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(X1,sK0) )
    | ~ spl8_4 ),
    inference(resolution,[],[f70,f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f70,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(sK0,sK1))
        | r2_hidden(X3,sK0) )
    | ~ spl8_4 ),
    inference(superposition,[],[f43,f67])).

fof(f67,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f65])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f111,plain,
    ( ~ spl8_9
    | spl8_3
    | spl8_8 ),
    inference(avatar_split_clause,[],[f106,f98,f60,f108])).

fof(f60,plain,
    ( spl8_3
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f98,plain,
    ( spl8_8
  <=> r2_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f106,plain,
    ( sK0 = sK1
    | ~ r1_tarski(sK1,sK0)
    | spl8_8 ),
    inference(resolution,[],[f100,f30])).

fof(f100,plain,
    ( ~ r2_xboole_0(sK1,sK0)
    | spl8_8 ),
    inference(avatar_component_clause,[],[f98])).

fof(f101,plain,
    ( ~ spl8_8
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f96,f80,f98])).

fof(f80,plain,
    ( spl8_6
  <=> ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f96,plain,
    ( ~ r2_xboole_0(sK1,sK0)
    | ~ spl8_6 ),
    inference(duplicate_literal_removal,[],[f94])).

fof(f94,plain,
    ( ~ r2_xboole_0(sK1,sK0)
    | ~ r2_xboole_0(sK1,sK0)
    | ~ spl8_6 ),
    inference(resolution,[],[f85,f40])).

fof(f85,plain,
    ( ! [X3] :
        ( ~ r2_hidden(sK7(sK1,X3),sK0)
        | ~ r2_xboole_0(sK1,X3) )
    | ~ spl8_6 ),
    inference(resolution,[],[f81,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK7(X0,X1),X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f81,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f80])).

fof(f82,plain,
    ( spl8_5
    | spl8_6
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f72,f65,f80,f77])).

fof(f72,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,sK1)
        | ~ r2_hidden(X1,sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl8_4 ),
    inference(resolution,[],[f69,f44])).

fof(f69,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1))
        | r2_hidden(X0,sK1) )
    | ~ spl8_4 ),
    inference(superposition,[],[f42,f67])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f68,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f18,f65])).

fof(f18,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)
       => ( X0 = X1
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)
     => ( X0 = X1
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t114_zfmisc_1)).

fof(f63,plain,(
    ~ spl8_3 ),
    inference(avatar_split_clause,[],[f21,f60])).

fof(f21,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f14])).

fof(f58,plain,(
    ~ spl8_2 ),
    inference(avatar_split_clause,[],[f20,f55])).

fof(f20,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f14])).

fof(f53,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f19,f50])).

fof(f19,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:02:01 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.51  % (25989)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.51  % (25981)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.51  % (25973)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (25988)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (25972)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (25990)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.53  % (25970)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (25966)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (25966)Refutation not found, incomplete strategy% (25966)------------------------------
% 0.21/0.53  % (25966)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (25966)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (25966)Memory used [KB]: 1663
% 0.21/0.53  % (25966)Time elapsed: 0.122 s
% 0.21/0.53  % (25966)------------------------------
% 0.21/0.53  % (25966)------------------------------
% 0.21/0.53  % (25969)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (25967)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (25979)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.54  % (25980)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  % (25971)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (25994)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (25993)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.55  % (25991)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  % (25982)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (25988)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f159,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(avatar_sat_refutation,[],[f53,f58,f63,f68,f82,f101,f111,f118,f132,f142,f157])).
% 0.21/0.55  fof(f157,plain,(
% 0.21/0.55    spl8_2 | ~spl8_5),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f154])).
% 0.21/0.55  fof(f154,plain,(
% 0.21/0.55    $false | (spl8_2 | ~spl8_5)),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f23,f57,f149,f30])).
% 0.21/0.55  fof(f30,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f2])).
% 0.21/0.55  fof(f2,axiom,(
% 0.21/0.55    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.21/0.55  fof(f149,plain,(
% 0.21/0.55    ( ! [X7] : (~r2_xboole_0(X7,sK1)) ) | ~spl8_5),
% 0.21/0.55    inference(resolution,[],[f78,f40])).
% 0.21/0.55  fof(f40,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1),X1) | ~r2_xboole_0(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f17])).
% 0.21/0.55  fof(f17,plain,(
% 0.21/0.55    ! [X0,X1] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) | ~r2_xboole_0(X0,X1))),
% 0.21/0.55    inference(ennf_transformation,[],[f4])).
% 0.21/0.55  fof(f4,axiom,(
% 0.21/0.55    ! [X0,X1] : ~(! [X2] : ~(~r2_hidden(X2,X0) & r2_hidden(X2,X1)) & r2_xboole_0(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_0)).
% 0.21/0.55  fof(f78,plain,(
% 0.21/0.55    ( ! [X1] : (~r2_hidden(X1,sK1)) ) | ~spl8_5),
% 0.21/0.55    inference(avatar_component_clause,[],[f77])).
% 0.21/0.55  fof(f77,plain,(
% 0.21/0.55    spl8_5 <=> ! [X1] : ~r2_hidden(X1,sK1)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.21/0.55  fof(f57,plain,(
% 0.21/0.55    k1_xboole_0 != sK1 | spl8_2),
% 0.21/0.55    inference(avatar_component_clause,[],[f55])).
% 0.21/0.55  fof(f55,plain,(
% 0.21/0.55    spl8_2 <=> k1_xboole_0 = sK1),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f5])).
% 0.21/0.55  fof(f5,axiom,(
% 0.21/0.55    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.55  fof(f142,plain,(
% 0.21/0.55    spl8_9 | ~spl8_11),
% 0.21/0.55    inference(avatar_split_clause,[],[f141,f116,f108])).
% 0.21/0.55  fof(f108,plain,(
% 0.21/0.55    spl8_9 <=> r1_tarski(sK1,sK0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.21/0.55  fof(f116,plain,(
% 0.21/0.55    spl8_11 <=> ! [X0] : (r2_hidden(X0,sK0) | ~r2_hidden(X0,sK1))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 0.21/0.55  fof(f141,plain,(
% 0.21/0.55    r1_tarski(sK1,sK0) | ~spl8_11),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f138])).
% 0.21/0.55  fof(f138,plain,(
% 0.21/0.55    r1_tarski(sK1,sK0) | r1_tarski(sK1,sK0) | ~spl8_11),
% 0.21/0.55    inference(resolution,[],[f134,f32])).
% 0.21/0.55  fof(f32,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f16])).
% 0.21/0.55  fof(f16,plain,(
% 0.21/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f1])).
% 0.21/0.55  fof(f1,axiom,(
% 0.21/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.55  fof(f134,plain,(
% 0.21/0.55    ( ! [X1] : (~r2_hidden(sK3(X1,sK0),sK1) | r1_tarski(X1,sK0)) ) | ~spl8_11),
% 0.21/0.55    inference(resolution,[],[f117,f33])).
% 0.21/0.55  fof(f33,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f16])).
% 0.21/0.55  fof(f117,plain,(
% 0.21/0.55    ( ! [X0] : (r2_hidden(X0,sK0) | ~r2_hidden(X0,sK1)) ) | ~spl8_11),
% 0.21/0.55    inference(avatar_component_clause,[],[f116])).
% 0.21/0.55  fof(f132,plain,(
% 0.21/0.55    spl8_1 | ~spl8_10),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f130])).
% 0.21/0.55  fof(f130,plain,(
% 0.21/0.55    $false | (spl8_1 | ~spl8_10)),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f23,f52,f125,f30])).
% 0.21/0.55  fof(f125,plain,(
% 0.21/0.55    ( ! [X7] : (~r2_xboole_0(X7,sK0)) ) | ~spl8_10),
% 0.21/0.55    inference(resolution,[],[f114,f40])).
% 0.21/0.55  fof(f114,plain,(
% 0.21/0.55    ( ! [X1] : (~r2_hidden(X1,sK0)) ) | ~spl8_10),
% 0.21/0.55    inference(avatar_component_clause,[],[f113])).
% 0.21/0.55  fof(f113,plain,(
% 0.21/0.55    spl8_10 <=> ! [X1] : ~r2_hidden(X1,sK0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.21/0.55  fof(f52,plain,(
% 0.21/0.55    k1_xboole_0 != sK0 | spl8_1),
% 0.21/0.55    inference(avatar_component_clause,[],[f50])).
% 0.21/0.55  fof(f50,plain,(
% 0.21/0.55    spl8_1 <=> k1_xboole_0 = sK0),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.55  fof(f118,plain,(
% 0.21/0.55    spl8_10 | spl8_11 | ~spl8_4),
% 0.21/0.55    inference(avatar_split_clause,[],[f74,f65,f116,f113])).
% 0.21/0.55  fof(f65,plain,(
% 0.21/0.55    spl8_4 <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.21/0.55  fof(f74,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r2_hidden(X0,sK0) | ~r2_hidden(X0,sK1) | ~r2_hidden(X1,sK0)) ) | ~spl8_4),
% 0.21/0.55    inference(resolution,[],[f70,f44])).
% 0.21/0.55  fof(f44,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f8])).
% 0.21/0.55  fof(f8,axiom,(
% 0.21/0.55    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.21/0.55  fof(f70,plain,(
% 0.21/0.55    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(sK0,sK1)) | r2_hidden(X3,sK0)) ) | ~spl8_4),
% 0.21/0.55    inference(superposition,[],[f43,f67])).
% 0.21/0.55  fof(f67,plain,(
% 0.21/0.55    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0) | ~spl8_4),
% 0.21/0.55    inference(avatar_component_clause,[],[f65])).
% 0.21/0.55  fof(f43,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f8])).
% 0.21/0.55  fof(f111,plain,(
% 0.21/0.55    ~spl8_9 | spl8_3 | spl8_8),
% 0.21/0.55    inference(avatar_split_clause,[],[f106,f98,f60,f108])).
% 0.21/0.55  fof(f60,plain,(
% 0.21/0.55    spl8_3 <=> sK0 = sK1),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.21/0.55  fof(f98,plain,(
% 0.21/0.55    spl8_8 <=> r2_xboole_0(sK1,sK0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.21/0.55  fof(f106,plain,(
% 0.21/0.55    sK0 = sK1 | ~r1_tarski(sK1,sK0) | spl8_8),
% 0.21/0.55    inference(resolution,[],[f100,f30])).
% 0.21/0.55  fof(f100,plain,(
% 0.21/0.55    ~r2_xboole_0(sK1,sK0) | spl8_8),
% 0.21/0.55    inference(avatar_component_clause,[],[f98])).
% 0.21/0.55  fof(f101,plain,(
% 0.21/0.55    ~spl8_8 | ~spl8_6),
% 0.21/0.55    inference(avatar_split_clause,[],[f96,f80,f98])).
% 0.21/0.55  fof(f80,plain,(
% 0.21/0.55    spl8_6 <=> ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.21/0.55  fof(f96,plain,(
% 0.21/0.55    ~r2_xboole_0(sK1,sK0) | ~spl8_6),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f94])).
% 0.21/0.55  fof(f94,plain,(
% 0.21/0.55    ~r2_xboole_0(sK1,sK0) | ~r2_xboole_0(sK1,sK0) | ~spl8_6),
% 0.21/0.55    inference(resolution,[],[f85,f40])).
% 0.21/0.55  fof(f85,plain,(
% 0.21/0.55    ( ! [X3] : (~r2_hidden(sK7(sK1,X3),sK0) | ~r2_xboole_0(sK1,X3)) ) | ~spl8_6),
% 0.21/0.55    inference(resolution,[],[f81,f41])).
% 0.21/0.55  fof(f41,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r2_hidden(sK7(X0,X1),X0) | ~r2_xboole_0(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f17])).
% 0.21/0.55  fof(f81,plain,(
% 0.21/0.55    ( ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0)) ) | ~spl8_6),
% 0.21/0.55    inference(avatar_component_clause,[],[f80])).
% 0.21/0.55  fof(f82,plain,(
% 0.21/0.55    spl8_5 | spl8_6 | ~spl8_4),
% 0.21/0.55    inference(avatar_split_clause,[],[f72,f65,f80,f77])).
% 0.21/0.55  fof(f72,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r2_hidden(X0,sK1) | ~r2_hidden(X1,sK1) | ~r2_hidden(X0,sK0)) ) | ~spl8_4),
% 0.21/0.55    inference(resolution,[],[f69,f44])).
% 0.21/0.55  fof(f69,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1)) | r2_hidden(X0,sK1)) ) | ~spl8_4),
% 0.21/0.55    inference(superposition,[],[f42,f67])).
% 0.21/0.55  fof(f42,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f8])).
% 0.21/0.55  fof(f68,plain,(
% 0.21/0.55    spl8_4),
% 0.21/0.55    inference(avatar_split_clause,[],[f18,f65])).
% 0.21/0.55  fof(f18,plain,(
% 0.21/0.55    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0)),
% 0.21/0.55    inference(cnf_transformation,[],[f14])).
% 0.21/0.55  fof(f14,plain,(
% 0.21/0.55    ? [X0,X1] : (X0 != X1 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0))),
% 0.21/0.55    inference(flattening,[],[f13])).
% 0.21/0.55  fof(f13,plain,(
% 0.21/0.55    ? [X0,X1] : ((X0 != X1 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f11])).
% 0.21/0.55  fof(f11,negated_conjecture,(
% 0.21/0.55    ~! [X0,X1] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) => (X0 = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.55    inference(negated_conjecture,[],[f10])).
% 0.21/0.55  fof(f10,conjecture,(
% 0.21/0.55    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) => (X0 = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t114_zfmisc_1)).
% 0.21/0.55  fof(f63,plain,(
% 0.21/0.55    ~spl8_3),
% 0.21/0.55    inference(avatar_split_clause,[],[f21,f60])).
% 0.21/0.55  fof(f21,plain,(
% 0.21/0.55    sK0 != sK1),
% 0.21/0.55    inference(cnf_transformation,[],[f14])).
% 0.21/0.55  fof(f58,plain,(
% 0.21/0.55    ~spl8_2),
% 0.21/0.55    inference(avatar_split_clause,[],[f20,f55])).
% 0.21/0.55  fof(f20,plain,(
% 0.21/0.55    k1_xboole_0 != sK1),
% 0.21/0.55    inference(cnf_transformation,[],[f14])).
% 0.21/0.55  fof(f53,plain,(
% 0.21/0.55    ~spl8_1),
% 0.21/0.55    inference(avatar_split_clause,[],[f19,f50])).
% 0.21/0.55  fof(f19,plain,(
% 0.21/0.55    k1_xboole_0 != sK0),
% 0.21/0.55    inference(cnf_transformation,[],[f14])).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (25988)------------------------------
% 0.21/0.55  % (25988)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (25988)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (25988)Memory used [KB]: 10746
% 0.21/0.55  % (25988)Time elapsed: 0.153 s
% 0.21/0.55  % (25988)------------------------------
% 0.21/0.55  % (25988)------------------------------
% 0.21/0.55  % (25965)Success in time 0.19 s
%------------------------------------------------------------------------------
