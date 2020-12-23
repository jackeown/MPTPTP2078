%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:00 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
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
fof(f201,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f60,f65,f70,f75,f97,f106,f112,f125,f159,f166,f200])).

fof(f200,plain,
    ( spl8_2
    | ~ spl8_5 ),
    inference(avatar_contradiction_clause,[],[f197])).

fof(f197,plain,
    ( $false
    | spl8_2
    | ~ spl8_5 ),
    inference(unit_resulting_resolution,[],[f64,f168,f187,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f187,plain,
    ( ! [X2] : r1_tarski(k1_xboole_0,X2)
    | ~ spl8_5 ),
    inference(resolution,[],[f183,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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

fof(f183,plain,
    ( ! [X1] : ~ r2_hidden(X1,k1_xboole_0)
    | ~ spl8_5 ),
    inference(superposition,[],[f169,f48])).

fof(f48,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
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

fof(f169,plain,
    ( ! [X4,X3] : ~ r2_hidden(X3,k2_zfmisc_1(sK1,X4))
    | ~ spl8_5 ),
    inference(resolution,[],[f93,f54])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK4(X0,X1,X3),X0)
      | ~ r2_hidden(X3,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
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

fof(f93,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK1)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl8_5
  <=> ! [X1] : ~ r2_hidden(X1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f168,plain,
    ( ! [X2] : r1_tarski(sK1,X2)
    | ~ spl8_5 ),
    inference(resolution,[],[f93,f24])).

fof(f64,plain,
    ( k1_xboole_0 != sK1
    | spl8_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl8_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f166,plain,
    ( spl8_8
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f165,f123,f109])).

fof(f109,plain,
    ( spl8_8
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f123,plain,
    ( spl8_10
  <=> ! [X0] :
        ( r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f165,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl8_10 ),
    inference(duplicate_literal_removal,[],[f162])).

fof(f162,plain,
    ( r1_tarski(sK1,sK0)
    | r1_tarski(sK1,sK0)
    | ~ spl8_10 ),
    inference(resolution,[],[f161,f24])).

fof(f161,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK2(X1,sK0),sK1)
        | r1_tarski(X1,sK0) )
    | ~ spl8_10 ),
    inference(resolution,[],[f124,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f124,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f123])).

fof(f159,plain,
    ( spl8_1
    | ~ spl8_9 ),
    inference(avatar_contradiction_clause,[],[f156])).

fof(f156,plain,
    ( $false
    | spl8_1
    | ~ spl8_9 ),
    inference(unit_resulting_resolution,[],[f59,f127,f146,f22])).

fof(f146,plain,
    ( ! [X2] : r1_tarski(k1_xboole_0,X2)
    | ~ spl8_9 ),
    inference(resolution,[],[f142,f24])).

fof(f142,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl8_9 ),
    inference(superposition,[],[f128,f48])).

fof(f128,plain,
    ( ! [X4,X3] : ~ r2_hidden(X3,k2_zfmisc_1(sK0,X4))
    | ~ spl8_9 ),
    inference(resolution,[],[f121,f54])).

fof(f121,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK0)
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl8_9
  <=> ! [X1] : ~ r2_hidden(X1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f127,plain,
    ( ! [X2] : r1_tarski(sK0,X2)
    | ~ spl8_9 ),
    inference(resolution,[],[f121,f24])).

fof(f59,plain,
    ( k1_xboole_0 != sK0
    | spl8_1 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl8_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f125,plain,
    ( spl8_9
    | spl8_10
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f86,f72,f123,f120])).

fof(f72,plain,
    ( spl8_4
  <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f86,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(X1,sK0) )
    | ~ spl8_4 ),
    inference(resolution,[],[f77,f42])).

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

fof(f77,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(sK0,sK1))
        | r2_hidden(X3,sK0) )
    | ~ spl8_4 ),
    inference(superposition,[],[f41,f74])).

fof(f74,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f72])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f112,plain,
    ( spl8_3
    | ~ spl8_8
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f107,f103,f109,f67])).

fof(f67,plain,
    ( spl8_3
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f103,plain,
    ( spl8_7
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f107,plain,
    ( ~ r1_tarski(sK1,sK0)
    | sK0 = sK1
    | ~ spl8_7 ),
    inference(resolution,[],[f105,f22])).

fof(f105,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f103])).

fof(f106,plain,
    ( spl8_7
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f101,f95,f103])).

fof(f95,plain,
    ( spl8_6
  <=> ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f101,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl8_6 ),
    inference(duplicate_literal_removal,[],[f99])).

fof(f99,plain,
    ( r1_tarski(sK0,sK1)
    | r1_tarski(sK0,sK1)
    | ~ spl8_6 ),
    inference(resolution,[],[f98,f24])).

fof(f98,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK2(X0,sK1),sK0)
        | r1_tarski(X0,sK1) )
    | ~ spl8_6 ),
    inference(resolution,[],[f96,f25])).

fof(f96,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f95])).

fof(f97,plain,
    ( spl8_5
    | spl8_6
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f81,f72,f95,f92])).

fof(f81,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,sK1)
        | ~ r2_hidden(X1,sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl8_4 ),
    inference(resolution,[],[f76,f42])).

fof(f76,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1))
        | r2_hidden(X0,sK1) )
    | ~ spl8_4 ),
    inference(superposition,[],[f40,f74])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f75,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f14,f72])).

fof(f14,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)
       => ( X0 = X1
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)
     => ( X0 = X1
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t114_zfmisc_1)).

fof(f70,plain,(
    ~ spl8_3 ),
    inference(avatar_split_clause,[],[f17,f67])).

fof(f17,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f12])).

fof(f65,plain,(
    ~ spl8_2 ),
    inference(avatar_split_clause,[],[f16,f62])).

fof(f16,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f12])).

fof(f60,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f15,f57])).

fof(f15,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:01:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.50  % (8096)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.50  % (8088)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.51  % (8103)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.51  % (8080)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.51  % (8078)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.51  % (8079)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.51  % (8095)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.51  % (8075)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.51  % (8087)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.52  % (8096)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % (8081)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f201,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(avatar_sat_refutation,[],[f60,f65,f70,f75,f97,f106,f112,f125,f159,f166,f200])).
% 0.22/0.52  fof(f200,plain,(
% 0.22/0.52    spl8_2 | ~spl8_5),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f197])).
% 0.22/0.52  fof(f197,plain,(
% 0.22/0.52    $false | (spl8_2 | ~spl8_5)),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f64,f168,f187,f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.22/0.52    inference(cnf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.52  fof(f187,plain,(
% 0.22/0.52    ( ! [X2] : (r1_tarski(k1_xboole_0,X2)) ) | ~spl8_5),
% 0.22/0.52    inference(resolution,[],[f183,f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f13])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.52  fof(f183,plain,(
% 0.22/0.52    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) ) | ~spl8_5),
% 0.22/0.52    inference(superposition,[],[f169,f48])).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.52    inference(equality_resolution,[],[f28])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.52  fof(f169,plain,(
% 0.22/0.52    ( ! [X4,X3] : (~r2_hidden(X3,k2_zfmisc_1(sK1,X4))) ) | ~spl8_5),
% 0.22/0.52    inference(resolution,[],[f93,f54])).
% 0.22/0.52  fof(f54,plain,(
% 0.22/0.52    ( ! [X0,X3,X1] : (r2_hidden(sK4(X0,X1,X3),X0) | ~r2_hidden(X3,k2_zfmisc_1(X0,X1))) )),
% 0.22/0.52    inference(equality_resolution,[],[f33])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (r2_hidden(sK4(X0,X1,X3),X0) | ~r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.22/0.52    inference(cnf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 0.22/0.52  fof(f93,plain,(
% 0.22/0.52    ( ! [X1] : (~r2_hidden(X1,sK1)) ) | ~spl8_5),
% 0.22/0.52    inference(avatar_component_clause,[],[f92])).
% 0.22/0.52  fof(f92,plain,(
% 0.22/0.52    spl8_5 <=> ! [X1] : ~r2_hidden(X1,sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.22/0.52  fof(f168,plain,(
% 0.22/0.52    ( ! [X2] : (r1_tarski(sK1,X2)) ) | ~spl8_5),
% 0.22/0.52    inference(resolution,[],[f93,f24])).
% 0.22/0.52  fof(f64,plain,(
% 0.22/0.52    k1_xboole_0 != sK1 | spl8_2),
% 0.22/0.52    inference(avatar_component_clause,[],[f62])).
% 0.22/0.52  fof(f62,plain,(
% 0.22/0.52    spl8_2 <=> k1_xboole_0 = sK1),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.22/0.52  fof(f166,plain,(
% 0.22/0.52    spl8_8 | ~spl8_10),
% 0.22/0.52    inference(avatar_split_clause,[],[f165,f123,f109])).
% 0.22/0.52  fof(f109,plain,(
% 0.22/0.52    spl8_8 <=> r1_tarski(sK1,sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.22/0.52  fof(f123,plain,(
% 0.22/0.52    spl8_10 <=> ! [X0] : (r2_hidden(X0,sK0) | ~r2_hidden(X0,sK1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.22/0.52  fof(f165,plain,(
% 0.22/0.52    r1_tarski(sK1,sK0) | ~spl8_10),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f162])).
% 0.22/0.52  fof(f162,plain,(
% 0.22/0.52    r1_tarski(sK1,sK0) | r1_tarski(sK1,sK0) | ~spl8_10),
% 0.22/0.52    inference(resolution,[],[f161,f24])).
% 0.22/0.52  fof(f161,plain,(
% 0.22/0.52    ( ! [X1] : (~r2_hidden(sK2(X1,sK0),sK1) | r1_tarski(X1,sK0)) ) | ~spl8_10),
% 0.22/0.52    inference(resolution,[],[f124,f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f13])).
% 0.22/0.52  fof(f124,plain,(
% 0.22/0.52    ( ! [X0] : (r2_hidden(X0,sK0) | ~r2_hidden(X0,sK1)) ) | ~spl8_10),
% 0.22/0.52    inference(avatar_component_clause,[],[f123])).
% 0.22/0.52  fof(f159,plain,(
% 0.22/0.52    spl8_1 | ~spl8_9),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f156])).
% 0.22/0.52  fof(f156,plain,(
% 0.22/0.52    $false | (spl8_1 | ~spl8_9)),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f59,f127,f146,f22])).
% 0.22/0.52  fof(f146,plain,(
% 0.22/0.52    ( ! [X2] : (r1_tarski(k1_xboole_0,X2)) ) | ~spl8_9),
% 0.22/0.52    inference(resolution,[],[f142,f24])).
% 0.22/0.52  fof(f142,plain,(
% 0.22/0.52    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl8_9),
% 0.22/0.52    inference(superposition,[],[f128,f48])).
% 0.22/0.52  fof(f128,plain,(
% 0.22/0.52    ( ! [X4,X3] : (~r2_hidden(X3,k2_zfmisc_1(sK0,X4))) ) | ~spl8_9),
% 0.22/0.52    inference(resolution,[],[f121,f54])).
% 0.22/0.52  fof(f121,plain,(
% 0.22/0.52    ( ! [X1] : (~r2_hidden(X1,sK0)) ) | ~spl8_9),
% 0.22/0.52    inference(avatar_component_clause,[],[f120])).
% 0.22/0.52  fof(f120,plain,(
% 0.22/0.52    spl8_9 <=> ! [X1] : ~r2_hidden(X1,sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.22/0.52  fof(f127,plain,(
% 0.22/0.52    ( ! [X2] : (r1_tarski(sK0,X2)) ) | ~spl8_9),
% 0.22/0.52    inference(resolution,[],[f121,f24])).
% 0.22/0.52  fof(f59,plain,(
% 0.22/0.52    k1_xboole_0 != sK0 | spl8_1),
% 0.22/0.52    inference(avatar_component_clause,[],[f57])).
% 0.22/0.52  fof(f57,plain,(
% 0.22/0.52    spl8_1 <=> k1_xboole_0 = sK0),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.22/0.52  fof(f125,plain,(
% 0.22/0.52    spl8_9 | spl8_10 | ~spl8_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f86,f72,f123,f120])).
% 0.22/0.52  fof(f72,plain,(
% 0.22/0.52    spl8_4 <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.22/0.52  fof(f86,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r2_hidden(X0,sK0) | ~r2_hidden(X0,sK1) | ~r2_hidden(X1,sK0)) ) | ~spl8_4),
% 0.22/0.52    inference(resolution,[],[f77,f42])).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.22/0.52  fof(f77,plain,(
% 0.22/0.52    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(sK0,sK1)) | r2_hidden(X3,sK0)) ) | ~spl8_4),
% 0.22/0.52    inference(superposition,[],[f41,f74])).
% 0.22/0.52  fof(f74,plain,(
% 0.22/0.52    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0) | ~spl8_4),
% 0.22/0.52    inference(avatar_component_clause,[],[f72])).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f6])).
% 0.22/0.52  fof(f112,plain,(
% 0.22/0.52    spl8_3 | ~spl8_8 | ~spl8_7),
% 0.22/0.52    inference(avatar_split_clause,[],[f107,f103,f109,f67])).
% 0.22/0.52  fof(f67,plain,(
% 0.22/0.52    spl8_3 <=> sK0 = sK1),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.22/0.52  fof(f103,plain,(
% 0.22/0.52    spl8_7 <=> r1_tarski(sK0,sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.22/0.52  fof(f107,plain,(
% 0.22/0.52    ~r1_tarski(sK1,sK0) | sK0 = sK1 | ~spl8_7),
% 0.22/0.52    inference(resolution,[],[f105,f22])).
% 0.22/0.52  fof(f105,plain,(
% 0.22/0.52    r1_tarski(sK0,sK1) | ~spl8_7),
% 0.22/0.52    inference(avatar_component_clause,[],[f103])).
% 0.22/0.52  fof(f106,plain,(
% 0.22/0.52    spl8_7 | ~spl8_6),
% 0.22/0.52    inference(avatar_split_clause,[],[f101,f95,f103])).
% 0.22/0.52  fof(f95,plain,(
% 0.22/0.52    spl8_6 <=> ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.22/0.52  fof(f101,plain,(
% 0.22/0.52    r1_tarski(sK0,sK1) | ~spl8_6),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f99])).
% 0.22/0.52  fof(f99,plain,(
% 0.22/0.52    r1_tarski(sK0,sK1) | r1_tarski(sK0,sK1) | ~spl8_6),
% 0.22/0.52    inference(resolution,[],[f98,f24])).
% 0.22/0.52  fof(f98,plain,(
% 0.22/0.52    ( ! [X0] : (~r2_hidden(sK2(X0,sK1),sK0) | r1_tarski(X0,sK1)) ) | ~spl8_6),
% 0.22/0.52    inference(resolution,[],[f96,f25])).
% 0.22/0.52  fof(f96,plain,(
% 0.22/0.52    ( ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0)) ) | ~spl8_6),
% 0.22/0.52    inference(avatar_component_clause,[],[f95])).
% 0.22/0.52  fof(f97,plain,(
% 0.22/0.52    spl8_5 | spl8_6 | ~spl8_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f81,f72,f95,f92])).
% 0.22/0.52  fof(f81,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r2_hidden(X0,sK1) | ~r2_hidden(X1,sK1) | ~r2_hidden(X0,sK0)) ) | ~spl8_4),
% 0.22/0.52    inference(resolution,[],[f76,f42])).
% 0.22/0.52  fof(f76,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1)) | r2_hidden(X0,sK1)) ) | ~spl8_4),
% 0.22/0.52    inference(superposition,[],[f40,f74])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f6])).
% 0.22/0.52  fof(f75,plain,(
% 0.22/0.52    spl8_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f14,f72])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f12])).
% 0.22/0.52  fof(f12,plain,(
% 0.22/0.52    ? [X0,X1] : (X0 != X1 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0))),
% 0.22/0.52    inference(flattening,[],[f11])).
% 0.22/0.52  fof(f11,plain,(
% 0.22/0.52    ? [X0,X1] : ((X0 != X1 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f10])).
% 0.22/0.52  fof(f10,negated_conjecture,(
% 0.22/0.52    ~! [X0,X1] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) => (X0 = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.52    inference(negated_conjecture,[],[f9])).
% 0.22/0.52  fof(f9,conjecture,(
% 0.22/0.52    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) => (X0 = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t114_zfmisc_1)).
% 0.22/0.52  fof(f70,plain,(
% 0.22/0.52    ~spl8_3),
% 0.22/0.52    inference(avatar_split_clause,[],[f17,f67])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    sK0 != sK1),
% 0.22/0.52    inference(cnf_transformation,[],[f12])).
% 0.22/0.52  fof(f65,plain,(
% 0.22/0.52    ~spl8_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f16,f62])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    k1_xboole_0 != sK1),
% 0.22/0.52    inference(cnf_transformation,[],[f12])).
% 0.22/0.52  fof(f60,plain,(
% 0.22/0.52    ~spl8_1),
% 0.22/0.52    inference(avatar_split_clause,[],[f15,f57])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    k1_xboole_0 != sK0),
% 0.22/0.52    inference(cnf_transformation,[],[f12])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (8096)------------------------------
% 0.22/0.52  % (8096)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (8096)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (8096)Memory used [KB]: 10874
% 0.22/0.52  % (8096)Time elapsed: 0.064 s
% 0.22/0.52  % (8096)------------------------------
% 0.22/0.52  % (8096)------------------------------
% 0.22/0.52  % (8069)Success in time 0.163 s
%------------------------------------------------------------------------------
