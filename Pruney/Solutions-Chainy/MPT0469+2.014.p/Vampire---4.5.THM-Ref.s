%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:35 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   54 (  74 expanded)
%              Number of leaves         :   15 (  29 expanded)
%              Depth                    :    7
%              Number of atoms          :  106 ( 143 expanded)
%              Number of equality atoms :   28 (  41 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f89,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f43,f48,f54,f72,f78,f86,f88])).

fof(f88,plain,(
    ~ spl5_7 ),
    inference(avatar_contradiction_clause,[],[f87])).

fof(f87,plain,
    ( $false
    | ~ spl5_7 ),
    inference(resolution,[],[f85,f55])).

fof(f55,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f21,f33])).

fof(f33,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f21,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f85,plain,
    ( r2_hidden(sK1(k1_xboole_0),k1_xboole_0)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl5_7
  <=> r2_hidden(sK1(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f86,plain,
    ( spl5_7
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f81,f69,f40,f83])).

fof(f40,plain,
    ( spl5_2
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

% (12498)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
fof(f69,plain,
    ( spl5_6
  <=> r2_hidden(sK1(k1_xboole_0),k1_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f81,plain,
    ( r2_hidden(sK1(k1_xboole_0),k1_xboole_0)
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(forward_demodulation,[],[f71,f41])).

fof(f41,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f40])).

% (12499)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
fof(f71,plain,
    ( r2_hidden(sK1(k1_xboole_0),k1_relat_1(k1_xboole_0))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f69])).

fof(f78,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f75,f40])).

fof(f75,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f66,f55])).

fof(f66,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK0(k1_relat_1(X0)),sK3(X0,sK0(k1_relat_1(X0)))),X0)
      | k1_xboole_0 = k1_relat_1(X0) ) ),
    inference(resolution,[],[f31,f20])).

fof(f20,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f13])).

% (12500)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
fof(f13,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f31,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_relat_1(X0))
      | r2_hidden(k4_tarski(X2,sK3(X0,X2)),X0) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X2,sK3(X0,X2)),X0)
      | ~ r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f72,plain,
    ( spl5_1
    | spl5_6
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f67,f51,f69,f36])).

fof(f36,plain,
    ( spl5_1
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f51,plain,
    ( spl5_4
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f67,plain,
    ( r2_hidden(sK1(k1_xboole_0),k1_relat_1(k1_xboole_0))
    | k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl5_4 ),
    inference(resolution,[],[f63,f53])).

fof(f53,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f51])).

fof(f63,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK1(X0),k1_relat_1(X0))
      | k1_xboole_0 = k2_relat_1(X0) ) ),
    inference(resolution,[],[f22,f20])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | r2_hidden(sK1(X1),k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( ! [X2] : ~ r2_hidden(X2,k1_relat_1(X1))
          & r2_hidden(X0,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relat_1)).

fof(f54,plain,
    ( spl5_4
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f49,f45,f51])).

fof(f45,plain,
    ( spl5_3
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f49,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl5_3 ),
    inference(resolution,[],[f19,f47])).

fof(f47,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f45])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f48,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f30,f45])).

fof(f30,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(definition_unfolding,[],[f17,f18])).

fof(f18,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(f17,plain,(
    ! [X0] : v1_xboole_0(k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : v1_xboole_0(k1_subset_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc13_subset_1)).

fof(f43,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f16,f40,f36])).

fof(f16,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
      & k1_xboole_0 = k1_relat_1(k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:06:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.49  % (12501)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.19/0.50  % (12494)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.19/0.50  % (12506)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.19/0.50  % (12490)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.19/0.50  % (12506)Refutation found. Thanks to Tanya!
% 0.19/0.50  % SZS status Theorem for theBenchmark
% 0.19/0.51  % (12514)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.19/0.51  % (12497)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.19/0.51  % (12501)Refutation not found, incomplete strategy% (12501)------------------------------
% 0.19/0.51  % (12501)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % SZS output start Proof for theBenchmark
% 0.19/0.51  fof(f89,plain,(
% 0.19/0.51    $false),
% 0.19/0.51    inference(avatar_sat_refutation,[],[f43,f48,f54,f72,f78,f86,f88])).
% 0.19/0.51  fof(f88,plain,(
% 0.19/0.51    ~spl5_7),
% 0.19/0.51    inference(avatar_contradiction_clause,[],[f87])).
% 0.19/0.51  fof(f87,plain,(
% 0.19/0.51    $false | ~spl5_7),
% 0.19/0.51    inference(resolution,[],[f85,f55])).
% 0.19/0.51  fof(f55,plain,(
% 0.19/0.51    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.19/0.51    inference(superposition,[],[f21,f33])).
% 0.19/0.51  fof(f33,plain,(
% 0.19/0.51    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.19/0.51    inference(equality_resolution,[],[f29])).
% 0.19/0.51  fof(f29,plain,(
% 0.19/0.51    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f2])).
% 0.19/0.51  fof(f2,axiom,(
% 0.19/0.51    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.19/0.51  fof(f21,plain,(
% 0.19/0.51    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.19/0.51    inference(cnf_transformation,[],[f3])).
% 0.19/0.51  fof(f3,axiom,(
% 0.19/0.51    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.19/0.51  fof(f85,plain,(
% 0.19/0.51    r2_hidden(sK1(k1_xboole_0),k1_xboole_0) | ~spl5_7),
% 0.19/0.51    inference(avatar_component_clause,[],[f83])).
% 0.19/0.51  fof(f83,plain,(
% 0.19/0.51    spl5_7 <=> r2_hidden(sK1(k1_xboole_0),k1_xboole_0)),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.19/0.51  fof(f86,plain,(
% 0.19/0.51    spl5_7 | ~spl5_2 | ~spl5_6),
% 0.19/0.51    inference(avatar_split_clause,[],[f81,f69,f40,f83])).
% 0.19/0.51  fof(f40,plain,(
% 0.19/0.51    spl5_2 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.19/0.51  % (12498)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.19/0.51  fof(f69,plain,(
% 0.19/0.51    spl5_6 <=> r2_hidden(sK1(k1_xboole_0),k1_relat_1(k1_xboole_0))),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.19/0.51  fof(f81,plain,(
% 0.19/0.51    r2_hidden(sK1(k1_xboole_0),k1_xboole_0) | (~spl5_2 | ~spl5_6)),
% 0.19/0.51    inference(forward_demodulation,[],[f71,f41])).
% 0.19/0.51  fof(f41,plain,(
% 0.19/0.51    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl5_2),
% 0.19/0.51    inference(avatar_component_clause,[],[f40])).
% 0.19/0.51  % (12499)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.19/0.51  fof(f71,plain,(
% 0.19/0.51    r2_hidden(sK1(k1_xboole_0),k1_relat_1(k1_xboole_0)) | ~spl5_6),
% 0.19/0.51    inference(avatar_component_clause,[],[f69])).
% 0.19/0.51  fof(f78,plain,(
% 0.19/0.51    spl5_2),
% 0.19/0.51    inference(avatar_split_clause,[],[f75,f40])).
% 0.19/0.51  fof(f75,plain,(
% 0.19/0.51    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.19/0.51    inference(resolution,[],[f66,f55])).
% 0.19/0.51  fof(f66,plain,(
% 0.19/0.51    ( ! [X0] : (r2_hidden(k4_tarski(sK0(k1_relat_1(X0)),sK3(X0,sK0(k1_relat_1(X0)))),X0) | k1_xboole_0 = k1_relat_1(X0)) )),
% 0.19/0.51    inference(resolution,[],[f31,f20])).
% 0.19/0.51  fof(f20,plain,(
% 0.19/0.51    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 0.19/0.51    inference(cnf_transformation,[],[f13])).
% 0.19/0.51  % (12500)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.19/0.51  fof(f13,plain,(
% 0.19/0.51    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.19/0.51    inference(ennf_transformation,[],[f1])).
% 0.19/0.51  fof(f1,axiom,(
% 0.19/0.51    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.19/0.51  fof(f31,plain,(
% 0.19/0.51    ( ! [X2,X0] : (~r2_hidden(X2,k1_relat_1(X0)) | r2_hidden(k4_tarski(X2,sK3(X0,X2)),X0)) )),
% 0.19/0.51    inference(equality_resolution,[],[f24])).
% 0.19/0.51  fof(f24,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X2,sK3(X0,X2)),X0) | ~r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 0.19/0.51    inference(cnf_transformation,[],[f7])).
% 0.19/0.51  fof(f7,axiom,(
% 0.19/0.51    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 0.19/0.51  fof(f72,plain,(
% 0.19/0.51    spl5_1 | spl5_6 | ~spl5_4),
% 0.19/0.51    inference(avatar_split_clause,[],[f67,f51,f69,f36])).
% 0.19/0.51  fof(f36,plain,(
% 0.19/0.51    spl5_1 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.19/0.51  fof(f51,plain,(
% 0.19/0.51    spl5_4 <=> v1_relat_1(k1_xboole_0)),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.19/0.51  fof(f67,plain,(
% 0.19/0.51    r2_hidden(sK1(k1_xboole_0),k1_relat_1(k1_xboole_0)) | k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl5_4),
% 0.19/0.51    inference(resolution,[],[f63,f53])).
% 0.19/0.51  fof(f53,plain,(
% 0.19/0.51    v1_relat_1(k1_xboole_0) | ~spl5_4),
% 0.19/0.51    inference(avatar_component_clause,[],[f51])).
% 0.19/0.51  fof(f63,plain,(
% 0.19/0.51    ( ! [X0] : (~v1_relat_1(X0) | r2_hidden(sK1(X0),k1_relat_1(X0)) | k1_xboole_0 = k2_relat_1(X0)) )),
% 0.19/0.51    inference(resolution,[],[f22,f20])).
% 0.19/0.51  fof(f22,plain,(
% 0.19/0.51    ( ! [X0,X1] : (~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1) | r2_hidden(sK1(X1),k1_relat_1(X1))) )),
% 0.19/0.51    inference(cnf_transformation,[],[f15])).
% 0.19/0.51  fof(f15,plain,(
% 0.19/0.51    ! [X0,X1] : (? [X2] : r2_hidden(X2,k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.19/0.51    inference(flattening,[],[f14])).
% 0.19/0.51  fof(f14,plain,(
% 0.19/0.51    ! [X0,X1] : ((? [X2] : r2_hidden(X2,k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.19/0.51    inference(ennf_transformation,[],[f8])).
% 0.19/0.51  fof(f8,axiom,(
% 0.19/0.51    ! [X0,X1] : (v1_relat_1(X1) => ~(! [X2] : ~r2_hidden(X2,k1_relat_1(X1)) & r2_hidden(X0,k2_relat_1(X1))))),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relat_1)).
% 0.19/0.51  fof(f54,plain,(
% 0.19/0.51    spl5_4 | ~spl5_3),
% 0.19/0.51    inference(avatar_split_clause,[],[f49,f45,f51])).
% 0.19/0.51  fof(f45,plain,(
% 0.19/0.51    spl5_3 <=> v1_xboole_0(k1_xboole_0)),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.19/0.51  fof(f49,plain,(
% 0.19/0.51    v1_relat_1(k1_xboole_0) | ~spl5_3),
% 0.19/0.51    inference(resolution,[],[f19,f47])).
% 0.19/0.51  fof(f47,plain,(
% 0.19/0.51    v1_xboole_0(k1_xboole_0) | ~spl5_3),
% 0.19/0.51    inference(avatar_component_clause,[],[f45])).
% 0.19/0.51  fof(f19,plain,(
% 0.19/0.51    ( ! [X0] : (~v1_xboole_0(X0) | v1_relat_1(X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f12])).
% 0.19/0.51  fof(f12,plain,(
% 0.19/0.51    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.19/0.51    inference(ennf_transformation,[],[f6])).
% 0.19/0.51  fof(f6,axiom,(
% 0.19/0.51    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.19/0.51  fof(f48,plain,(
% 0.19/0.51    spl5_3),
% 0.19/0.51    inference(avatar_split_clause,[],[f30,f45])).
% 0.19/0.51  fof(f30,plain,(
% 0.19/0.51    v1_xboole_0(k1_xboole_0)),
% 0.19/0.51    inference(definition_unfolding,[],[f17,f18])).
% 0.19/0.51  fof(f18,plain,(
% 0.19/0.51    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f4])).
% 0.19/0.51  fof(f4,axiom,(
% 0.19/0.51    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).
% 0.19/0.51  fof(f17,plain,(
% 0.19/0.51    ( ! [X0] : (v1_xboole_0(k1_subset_1(X0))) )),
% 0.19/0.51    inference(cnf_transformation,[],[f5])).
% 0.19/0.51  fof(f5,axiom,(
% 0.19/0.51    ! [X0] : v1_xboole_0(k1_subset_1(X0))),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc13_subset_1)).
% 0.19/0.51  fof(f43,plain,(
% 0.19/0.51    ~spl5_1 | ~spl5_2),
% 0.19/0.51    inference(avatar_split_clause,[],[f16,f40,f36])).
% 0.19/0.51  fof(f16,plain,(
% 0.19/0.51    k1_xboole_0 != k1_relat_1(k1_xboole_0) | k1_xboole_0 != k2_relat_1(k1_xboole_0)),
% 0.19/0.51    inference(cnf_transformation,[],[f11])).
% 0.19/0.51  fof(f11,plain,(
% 0.19/0.51    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 0.19/0.51    inference(ennf_transformation,[],[f10])).
% 0.19/0.51  fof(f10,negated_conjecture,(
% 0.19/0.51    ~(k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0))),
% 0.19/0.51    inference(negated_conjecture,[],[f9])).
% 0.19/0.51  fof(f9,conjecture,(
% 0.19/0.51    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.19/0.51  % SZS output end Proof for theBenchmark
% 0.19/0.51  % (12506)------------------------------
% 0.19/0.51  % (12506)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (12506)Termination reason: Refutation
% 0.19/0.51  
% 0.19/0.51  % (12506)Memory used [KB]: 10746
% 0.19/0.51  % (12506)Time elapsed: 0.098 s
% 0.19/0.51  % (12506)------------------------------
% 0.19/0.51  % (12506)------------------------------
% 0.19/0.51  % (12498)Refutation not found, incomplete strategy% (12498)------------------------------
% 0.19/0.51  % (12498)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (12498)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.51  
% 0.19/0.51  % (12498)Memory used [KB]: 10618
% 0.19/0.51  % (12498)Time elapsed: 0.107 s
% 0.19/0.51  % (12498)------------------------------
% 0.19/0.51  % (12498)------------------------------
% 0.19/0.51  % (12500)Refutation not found, incomplete strategy% (12500)------------------------------
% 0.19/0.51  % (12500)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (12500)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.51  
% 0.19/0.51  % (12500)Memory used [KB]: 10618
% 0.19/0.51  % (12500)Time elapsed: 0.108 s
% 0.19/0.51  % (12500)------------------------------
% 0.19/0.51  % (12500)------------------------------
% 0.19/0.51  % (12499)Refutation not found, incomplete strategy% (12499)------------------------------
% 0.19/0.51  % (12499)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (12499)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.51  
% 0.19/0.51  % (12499)Memory used [KB]: 10618
% 0.19/0.51  % (12499)Time elapsed: 0.107 s
% 0.19/0.51  % (12499)------------------------------
% 0.19/0.51  % (12499)------------------------------
% 0.19/0.51  % (12501)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.51  
% 0.19/0.51  % (12501)Memory used [KB]: 10618
% 0.19/0.51  % (12501)Time elapsed: 0.105 s
% 0.19/0.51  % (12501)------------------------------
% 0.19/0.51  % (12501)------------------------------
% 0.19/0.51  % (12511)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.19/0.52  % (12489)Success in time 0.161 s
%------------------------------------------------------------------------------
