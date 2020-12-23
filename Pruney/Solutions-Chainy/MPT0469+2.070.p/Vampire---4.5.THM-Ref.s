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
% DateTime   : Thu Dec  3 12:47:43 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   66 (  95 expanded)
%              Number of leaves         :   19 (  45 expanded)
%              Depth                    :    5
%              Number of atoms          :  153 ( 221 expanded)
%              Number of equality atoms :   28 (  39 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f150,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35,f39,f43,f47,f59,f63,f71,f76,f84,f95,f116,f135,f147])).

fof(f147,plain,
    ( spl5_2
    | ~ spl5_8
    | ~ spl5_19 ),
    inference(avatar_contradiction_clause,[],[f146])).

fof(f146,plain,
    ( $false
    | spl5_2
    | ~ spl5_8
    | ~ spl5_19 ),
    inference(subsumption_resolution,[],[f142,f34])).

fof(f34,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f33])).

fof(f33,plain,
    ( spl5_2
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f142,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl5_8
    | ~ spl5_19 ),
    inference(resolution,[],[f134,f62])).

fof(f62,plain,
    ( ! [X0] :
        ( r2_hidden(sK0(X0),X0)
        | k1_xboole_0 = X0 )
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl5_8
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | r2_hidden(sK0(X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f134,plain,
    ( ! [X3] : ~ r2_hidden(X3,k1_relat_1(k1_xboole_0))
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl5_19
  <=> ! [X3] : ~ r2_hidden(X3,k1_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f135,plain,
    ( spl5_19
    | ~ spl5_7
    | ~ spl5_11
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f105,f93,f74,f57,f133])).

fof(f57,plain,
    ( spl5_7
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f74,plain,
    ( spl5_11
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X1)
        | ~ r2_hidden(X0,k1_relat_1(X1))
        | r2_hidden(sK1(X1),k2_relat_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

% (30901)Termination reason: Refutation not found, incomplete strategy
fof(f93,plain,
    ( spl5_15
  <=> ! [X0] : ~ r2_hidden(X0,k2_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

% (30901)Memory used [KB]: 10490
fof(f105,plain,
    ( ! [X3] : ~ r2_hidden(X3,k1_relat_1(k1_xboole_0))
    | ~ spl5_7
    | ~ spl5_11
    | ~ spl5_15 ),
    inference(subsumption_resolution,[],[f101,f58])).

% (30901)Time elapsed: 0.060 s
% (30901)------------------------------
% (30901)------------------------------
fof(f58,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f57])).

fof(f101,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k1_relat_1(k1_xboole_0))
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl5_11
    | ~ spl5_15 ),
    inference(resolution,[],[f94,f75])).

fof(f75,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK1(X1),k2_relat_1(X1))
        | ~ r2_hidden(X0,k1_relat_1(X1))
        | ~ v1_relat_1(X1) )
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f74])).

fof(f94,plain,
    ( ! [X0] : ~ r2_hidden(X0,k2_relat_1(k1_xboole_0))
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f93])).

fof(f116,plain,
    ( spl5_1
    | ~ spl5_8
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f100,f93,f61,f30])).

fof(f30,plain,
    ( spl5_1
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f100,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl5_8
    | ~ spl5_15 ),
    inference(resolution,[],[f94,f62])).

fof(f95,plain,
    ( spl5_15
    | ~ spl5_10
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f87,f82,f69,f93])).

fof(f69,plain,
    ( spl5_10
  <=> ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f82,plain,
    ( spl5_13
  <=> ! [X0,X2] :
        ( r2_hidden(k4_tarski(sK3(X0,X2),X2),X0)
        | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f87,plain,
    ( ! [X0] : ~ r2_hidden(X0,k2_relat_1(k1_xboole_0))
    | ~ spl5_10
    | ~ spl5_13 ),
    inference(resolution,[],[f83,f70])).

% (30913)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
fof(f70,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f69])).

fof(f83,plain,
    ( ! [X2,X0] :
        ( r2_hidden(k4_tarski(sK3(X0,X2),X2),X0)
        | ~ r2_hidden(X2,k2_relat_1(X0)) )
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f82])).

fof(f84,plain,(
    spl5_13 ),
    inference(avatar_split_clause,[],[f25,f82])).

fof(f25,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(sK3(X0,X2),X2),X0)
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f19])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X2),X2),X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f76,plain,(
    spl5_11 ),
    inference(avatar_split_clause,[],[f17,f74])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | r2_hidden(sK1(X1),k2_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( ! [X2] : ~ r2_hidden(X2,k2_relat_1(X1))
          & r2_hidden(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_relat_1)).

fof(f71,plain,
    ( spl5_10
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f52,f45,f41,f69])).

fof(f41,plain,
    ( spl5_4
  <=> ! [X1,X0] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f45,plain,
    ( spl5_5
  <=> ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f52,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(superposition,[],[f42,f46])).

fof(f46,plain,
    ( ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f45])).

fof(f42,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f41])).

fof(f63,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f14,f61])).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f59,plain,
    ( spl5_7
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f53,f45,f37,f57])).

fof(f37,plain,
    ( spl5_3
  <=> ! [X1,X0] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f53,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(superposition,[],[f38,f46])).

fof(f38,plain,
    ( ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f37])).

fof(f47,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f27,f45])).

fof(f27,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
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

fof(f43,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f16,f41])).

fof(f16,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

% (30913)Refutation not found, incomplete strategy% (30913)------------------------------
% (30913)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (30913)Termination reason: Refutation not found, incomplete strategy

% (30913)Memory used [KB]: 1535
% (30913)Time elapsed: 0.033 s
% (30913)------------------------------
% (30913)------------------------------
fof(f3,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f39,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f15,f37])).

fof(f15,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f35,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f13,f33,f30])).

fof(f13,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
      & k1_xboole_0 = k1_relat_1(k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:18:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.47  % (30909)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.47  % (30909)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.48  % (30901)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.48  % (30901)Refutation not found, incomplete strategy% (30901)------------------------------
% 0.20/0.48  % (30901)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f150,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f35,f39,f43,f47,f59,f63,f71,f76,f84,f95,f116,f135,f147])).
% 0.20/0.48  fof(f147,plain,(
% 0.20/0.48    spl5_2 | ~spl5_8 | ~spl5_19),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f146])).
% 0.20/0.48  fof(f146,plain,(
% 0.20/0.48    $false | (spl5_2 | ~spl5_8 | ~spl5_19)),
% 0.20/0.48    inference(subsumption_resolution,[],[f142,f34])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    k1_xboole_0 != k1_relat_1(k1_xboole_0) | spl5_2),
% 0.20/0.48    inference(avatar_component_clause,[],[f33])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    spl5_2 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.48  fof(f142,plain,(
% 0.20/0.48    k1_xboole_0 = k1_relat_1(k1_xboole_0) | (~spl5_8 | ~spl5_19)),
% 0.20/0.48    inference(resolution,[],[f134,f62])).
% 0.20/0.48  fof(f62,plain,(
% 0.20/0.48    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) ) | ~spl5_8),
% 0.20/0.48    inference(avatar_component_clause,[],[f61])).
% 0.20/0.48  fof(f61,plain,(
% 0.20/0.48    spl5_8 <=> ! [X0] : (k1_xboole_0 = X0 | r2_hidden(sK0(X0),X0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.20/0.48  fof(f134,plain,(
% 0.20/0.48    ( ! [X3] : (~r2_hidden(X3,k1_relat_1(k1_xboole_0))) ) | ~spl5_19),
% 0.20/0.48    inference(avatar_component_clause,[],[f133])).
% 0.20/0.48  fof(f133,plain,(
% 0.20/0.48    spl5_19 <=> ! [X3] : ~r2_hidden(X3,k1_relat_1(k1_xboole_0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.20/0.48  fof(f135,plain,(
% 0.20/0.48    spl5_19 | ~spl5_7 | ~spl5_11 | ~spl5_15),
% 0.20/0.48    inference(avatar_split_clause,[],[f105,f93,f74,f57,f133])).
% 0.20/0.48  fof(f57,plain,(
% 0.20/0.48    spl5_7 <=> v1_relat_1(k1_xboole_0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.20/0.48  fof(f74,plain,(
% 0.20/0.48    spl5_11 <=> ! [X1,X0] : (~v1_relat_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | r2_hidden(sK1(X1),k2_relat_1(X1)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.20/0.48  % (30901)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  fof(f93,plain,(
% 0.20/0.48    spl5_15 <=> ! [X0] : ~r2_hidden(X0,k2_relat_1(k1_xboole_0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.20/0.48  
% 0.20/0.48  % (30901)Memory used [KB]: 10490
% 0.20/0.48  fof(f105,plain,(
% 0.20/0.48    ( ! [X3] : (~r2_hidden(X3,k1_relat_1(k1_xboole_0))) ) | (~spl5_7 | ~spl5_11 | ~spl5_15)),
% 0.20/0.48    inference(subsumption_resolution,[],[f101,f58])).
% 0.20/0.48  % (30901)Time elapsed: 0.060 s
% 0.20/0.48  % (30901)------------------------------
% 0.20/0.48  % (30901)------------------------------
% 0.20/0.48  fof(f58,plain,(
% 0.20/0.48    v1_relat_1(k1_xboole_0) | ~spl5_7),
% 0.20/0.48    inference(avatar_component_clause,[],[f57])).
% 0.20/0.48  fof(f101,plain,(
% 0.20/0.48    ( ! [X3] : (~r2_hidden(X3,k1_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)) ) | (~spl5_11 | ~spl5_15)),
% 0.20/0.48    inference(resolution,[],[f94,f75])).
% 0.20/0.48  fof(f75,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r2_hidden(sK1(X1),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) ) | ~spl5_11),
% 0.20/0.48    inference(avatar_component_clause,[],[f74])).
% 0.20/0.48  fof(f94,plain,(
% 0.20/0.48    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(k1_xboole_0))) ) | ~spl5_15),
% 0.20/0.48    inference(avatar_component_clause,[],[f93])).
% 0.20/0.48  fof(f116,plain,(
% 0.20/0.48    spl5_1 | ~spl5_8 | ~spl5_15),
% 0.20/0.48    inference(avatar_split_clause,[],[f100,f93,f61,f30])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    spl5_1 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.48  fof(f100,plain,(
% 0.20/0.48    k1_xboole_0 = k2_relat_1(k1_xboole_0) | (~spl5_8 | ~spl5_15)),
% 0.20/0.48    inference(resolution,[],[f94,f62])).
% 0.20/0.48  fof(f95,plain,(
% 0.20/0.48    spl5_15 | ~spl5_10 | ~spl5_13),
% 0.20/0.48    inference(avatar_split_clause,[],[f87,f82,f69,f93])).
% 0.20/0.48  fof(f69,plain,(
% 0.20/0.48    spl5_10 <=> ! [X0] : ~r2_hidden(X0,k1_xboole_0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.20/0.48  fof(f82,plain,(
% 0.20/0.48    spl5_13 <=> ! [X0,X2] : (r2_hidden(k4_tarski(sK3(X0,X2),X2),X0) | ~r2_hidden(X2,k2_relat_1(X0)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.20/0.48  fof(f87,plain,(
% 0.20/0.48    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(k1_xboole_0))) ) | (~spl5_10 | ~spl5_13)),
% 0.20/0.48    inference(resolution,[],[f83,f70])).
% 0.20/0.48  % (30913)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.48  fof(f70,plain,(
% 0.20/0.48    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl5_10),
% 0.20/0.48    inference(avatar_component_clause,[],[f69])).
% 0.20/0.48  fof(f83,plain,(
% 0.20/0.48    ( ! [X2,X0] : (r2_hidden(k4_tarski(sK3(X0,X2),X2),X0) | ~r2_hidden(X2,k2_relat_1(X0))) ) | ~spl5_13),
% 0.20/0.48    inference(avatar_component_clause,[],[f82])).
% 0.20/0.48  fof(f84,plain,(
% 0.20/0.48    spl5_13),
% 0.20/0.48    inference(avatar_split_clause,[],[f25,f82])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ( ! [X2,X0] : (r2_hidden(k4_tarski(sK3(X0,X2),X2),X0) | ~r2_hidden(X2,k2_relat_1(X0))) )),
% 0.20/0.48    inference(equality_resolution,[],[f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK3(X0,X2),X2),X0) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.20/0.48    inference(cnf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).
% 0.20/0.48  fof(f76,plain,(
% 0.20/0.48    spl5_11),
% 0.20/0.48    inference(avatar_split_clause,[],[f17,f74])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | r2_hidden(sK1(X1),k2_relat_1(X1))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ! [X0,X1] : (? [X2] : r2_hidden(X2,k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(flattening,[],[f11])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    ! [X0,X1] : ((? [X2] : r2_hidden(X2,k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,axiom,(
% 0.20/0.48    ! [X0,X1] : (v1_relat_1(X1) => ~(! [X2] : ~r2_hidden(X2,k2_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X1))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_relat_1)).
% 0.20/0.48  fof(f71,plain,(
% 0.20/0.48    spl5_10 | ~spl5_4 | ~spl5_5),
% 0.20/0.48    inference(avatar_split_clause,[],[f52,f45,f41,f69])).
% 0.20/0.48  fof(f41,plain,(
% 0.20/0.48    spl5_4 <=> ! [X1,X0] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.20/0.48  fof(f45,plain,(
% 0.20/0.48    spl5_5 <=> ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.20/0.48  fof(f52,plain,(
% 0.20/0.48    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | (~spl5_4 | ~spl5_5)),
% 0.20/0.48    inference(superposition,[],[f42,f46])).
% 0.20/0.48  fof(f46,plain,(
% 0.20/0.48    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) ) | ~spl5_5),
% 0.20/0.48    inference(avatar_component_clause,[],[f45])).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) ) | ~spl5_4),
% 0.20/0.48    inference(avatar_component_clause,[],[f41])).
% 0.20/0.48  fof(f63,plain,(
% 0.20/0.48    spl5_8),
% 0.20/0.48    inference(avatar_split_clause,[],[f14,f61])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ( ! [X0] : (k1_xboole_0 = X0 | r2_hidden(sK0(X0),X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f10])).
% 0.20/0.48  fof(f10,plain,(
% 0.20/0.48    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.20/0.48    inference(ennf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.20/0.48  fof(f59,plain,(
% 0.20/0.48    spl5_7 | ~spl5_3 | ~spl5_5),
% 0.20/0.48    inference(avatar_split_clause,[],[f53,f45,f37,f57])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    spl5_3 <=> ! [X1,X0] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.48  fof(f53,plain,(
% 0.20/0.48    v1_relat_1(k1_xboole_0) | (~spl5_3 | ~spl5_5)),
% 0.20/0.48    inference(superposition,[],[f38,f46])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) ) | ~spl5_3),
% 0.20/0.48    inference(avatar_component_clause,[],[f37])).
% 0.20/0.48  fof(f47,plain,(
% 0.20/0.48    spl5_5),
% 0.20/0.48    inference(avatar_split_clause,[],[f27,f45])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.48    inference(equality_resolution,[],[f24])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.48  fof(f43,plain,(
% 0.20/0.48    spl5_4),
% 0.20/0.48    inference(avatar_split_clause,[],[f16,f41])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f3])).
% 0.20/0.48  % (30913)Refutation not found, incomplete strategy% (30913)------------------------------
% 0.20/0.48  % (30913)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (30913)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (30913)Memory used [KB]: 1535
% 0.20/0.48  % (30913)Time elapsed: 0.033 s
% 0.20/0.48  % (30913)------------------------------
% 0.20/0.48  % (30913)------------------------------
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    spl5_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f15,f37])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    ~spl5_1 | ~spl5_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f13,f33,f30])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    k1_xboole_0 != k1_relat_1(k1_xboole_0) | k1_xboole_0 != k2_relat_1(k1_xboole_0)),
% 0.20/0.48    inference(cnf_transformation,[],[f9])).
% 0.20/0.48  fof(f9,plain,(
% 0.20/0.48    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 0.20/0.48    inference(ennf_transformation,[],[f8])).
% 0.20/0.48  fof(f8,negated_conjecture,(
% 0.20/0.48    ~(k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0))),
% 0.20/0.48    inference(negated_conjecture,[],[f7])).
% 0.20/0.48  fof(f7,conjecture,(
% 0.20/0.48    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (30909)------------------------------
% 0.20/0.48  % (30909)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (30909)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (30909)Memory used [KB]: 10618
% 0.20/0.48  % (30909)Time elapsed: 0.057 s
% 0.20/0.48  % (30909)------------------------------
% 0.20/0.48  % (30909)------------------------------
% 0.20/0.49  % (30897)Success in time 0.124 s
%------------------------------------------------------------------------------
