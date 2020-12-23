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
% DateTime   : Thu Dec  3 12:55:00 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 108 expanded)
%              Number of leaves         :   21 (  45 expanded)
%              Depth                    :    8
%              Number of atoms          :  217 ( 299 expanded)
%              Number of equality atoms :   15 (  19 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f136,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f38,f42,f46,f50,f54,f62,f66,f70,f78,f84,f102,f118,f128,f135])).

fof(f135,plain,
    ( ~ spl5_11
    | ~ spl5_12
    | spl5_19 ),
    inference(avatar_contradiction_clause,[],[f134])).

fof(f134,plain,
    ( $false
    | ~ spl5_11
    | ~ spl5_12
    | spl5_19 ),
    inference(subsumption_resolution,[],[f132,f83])).

fof(f83,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl5_12
  <=> ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f132,plain,
    ( r2_hidden(sK2(k1_xboole_0),k1_xboole_0)
    | ~ spl5_11
    | spl5_19 ),
    inference(resolution,[],[f117,f77])).

fof(f77,plain,
    ( ! [X0] :
        ( v1_relat_1(X0)
        | r2_hidden(sK2(X0),X0) )
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl5_11
  <=> ! [X0] :
        ( r2_hidden(sK2(X0),X0)
        | v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f117,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl5_19 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl5_19
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f128,plain,
    ( ~ spl5_4
    | ~ spl5_7
    | spl5_18 ),
    inference(avatar_contradiction_clause,[],[f127])).

fof(f127,plain,
    ( $false
    | ~ spl5_4
    | ~ spl5_7
    | spl5_18 ),
    inference(subsumption_resolution,[],[f125,f49])).

fof(f49,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl5_4
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f125,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl5_7
    | spl5_18 ),
    inference(resolution,[],[f114,f61])).

fof(f61,plain,
    ( ! [X0] :
        ( v1_funct_1(X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl5_7
  <=> ! [X0] :
        ( ~ v1_xboole_0(X0)
        | v1_funct_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f114,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | spl5_18 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl5_18
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f118,plain,
    ( ~ spl5_18
    | ~ spl5_19
    | ~ spl5_1
    | ~ spl5_2
    | spl5_3
    | ~ spl5_5
    | ~ spl5_12
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f107,f100,f82,f52,f44,f40,f36,f116,f113])).

fof(f36,plain,
    ( spl5_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f40,plain,
    ( spl5_2
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f44,plain,
    ( spl5_3
  <=> v5_funct_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f52,plain,
    ( spl5_5
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f100,plain,
    ( spl5_16
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | r2_hidden(sK1(X0,X1),k1_relat_1(X1))
        | v5_funct_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f107,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ spl5_1
    | ~ spl5_2
    | spl5_3
    | ~ spl5_5
    | ~ spl5_12
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f106,f83])).

fof(f106,plain,
    ( r2_hidden(sK1(sK0,k1_xboole_0),k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ spl5_1
    | ~ spl5_2
    | spl5_3
    | ~ spl5_5
    | ~ spl5_16 ),
    inference(forward_demodulation,[],[f105,f53])).

fof(f53,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f52])).

fof(f105,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | r2_hidden(sK1(sK0,k1_xboole_0),k1_relat_1(k1_xboole_0))
    | ~ spl5_1
    | ~ spl5_2
    | spl5_3
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f104,f37])).

fof(f37,plain,
    ( v1_relat_1(sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f36])).

fof(f104,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | r2_hidden(sK1(sK0,k1_xboole_0),k1_relat_1(k1_xboole_0))
    | ~ v1_relat_1(sK0)
    | ~ spl5_2
    | spl5_3
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f103,f41])).

fof(f41,plain,
    ( v1_funct_1(sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f40])).

fof(f103,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | r2_hidden(sK1(sK0,k1_xboole_0),k1_relat_1(k1_xboole_0))
    | ~ v1_relat_1(sK0)
    | spl5_3
    | ~ spl5_16 ),
    inference(resolution,[],[f101,f45])).

fof(f45,plain,
    ( ~ v5_funct_1(k1_xboole_0,sK0)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f44])).

fof(f101,plain,
    ( ! [X0,X1] :
        ( v5_funct_1(X1,X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | r2_hidden(sK1(X0,X1),k1_relat_1(X1))
        | ~ v1_relat_1(X0) )
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f100])).

fof(f102,plain,(
    spl5_16 ),
    inference(avatar_split_clause,[],[f24,f100])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | r2_hidden(sK1(X0,X1),k1_relat_1(X1))
      | v5_funct_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(X2,k1_relat_1(X1))
               => r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_funct_1)).

fof(f84,plain,
    ( spl5_12
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f79,f68,f64,f82])).

fof(f64,plain,
    ( spl5_8
  <=> ! [X1,X0] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f68,plain,
    ( spl5_9
  <=> ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f79,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(superposition,[],[f65,f69])).

fof(f69,plain,
    ( ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f68])).

fof(f65,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f64])).

fof(f78,plain,(
    spl5_11 ),
    inference(avatar_split_clause,[],[f27,f76])).

fof(f27,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

fof(f70,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f33,f68])).

fof(f33,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
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

fof(f66,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f29,f64])).

fof(f29,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f62,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f22,f60])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).

fof(f54,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f20,f52])).

fof(f20,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f50,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f19,f48])).

fof(f19,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f46,plain,(
    ~ spl5_3 ),
    inference(avatar_split_clause,[],[f18,f44])).

fof(f18,plain,(
    ~ v5_funct_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ~ v5_funct_1(k1_xboole_0,X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ~ v5_funct_1(k1_xboole_0,X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => v5_funct_1(k1_xboole_0,X0) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => v5_funct_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_funct_1)).

fof(f42,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f17,f40])).

fof(f17,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f38,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f16,f36])).

fof(f16,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:56:35 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.47  % (5606)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.48  % (5614)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.48  % (5614)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % (5606)Refutation not found, incomplete strategy% (5606)------------------------------
% 0.22/0.48  % (5606)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f136,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f38,f42,f46,f50,f54,f62,f66,f70,f78,f84,f102,f118,f128,f135])).
% 0.22/0.48  fof(f135,plain,(
% 0.22/0.48    ~spl5_11 | ~spl5_12 | spl5_19),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f134])).
% 0.22/0.48  fof(f134,plain,(
% 0.22/0.48    $false | (~spl5_11 | ~spl5_12 | spl5_19)),
% 0.22/0.48    inference(subsumption_resolution,[],[f132,f83])).
% 0.22/0.48  fof(f83,plain,(
% 0.22/0.48    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl5_12),
% 0.22/0.48    inference(avatar_component_clause,[],[f82])).
% 0.22/0.48  fof(f82,plain,(
% 0.22/0.48    spl5_12 <=> ! [X0] : ~r2_hidden(X0,k1_xboole_0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.22/0.48  fof(f132,plain,(
% 0.22/0.48    r2_hidden(sK2(k1_xboole_0),k1_xboole_0) | (~spl5_11 | spl5_19)),
% 0.22/0.48    inference(resolution,[],[f117,f77])).
% 0.22/0.48  fof(f77,plain,(
% 0.22/0.48    ( ! [X0] : (v1_relat_1(X0) | r2_hidden(sK2(X0),X0)) ) | ~spl5_11),
% 0.22/0.48    inference(avatar_component_clause,[],[f76])).
% 0.22/0.48  fof(f76,plain,(
% 0.22/0.48    spl5_11 <=> ! [X0] : (r2_hidden(sK2(X0),X0) | v1_relat_1(X0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.22/0.48  fof(f117,plain,(
% 0.22/0.48    ~v1_relat_1(k1_xboole_0) | spl5_19),
% 0.22/0.48    inference(avatar_component_clause,[],[f116])).
% 0.22/0.48  fof(f116,plain,(
% 0.22/0.48    spl5_19 <=> v1_relat_1(k1_xboole_0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.22/0.48  fof(f128,plain,(
% 0.22/0.48    ~spl5_4 | ~spl5_7 | spl5_18),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f127])).
% 0.22/0.48  fof(f127,plain,(
% 0.22/0.48    $false | (~spl5_4 | ~spl5_7 | spl5_18)),
% 0.22/0.48    inference(subsumption_resolution,[],[f125,f49])).
% 0.22/0.48  fof(f49,plain,(
% 0.22/0.48    v1_xboole_0(k1_xboole_0) | ~spl5_4),
% 0.22/0.48    inference(avatar_component_clause,[],[f48])).
% 0.22/0.48  fof(f48,plain,(
% 0.22/0.48    spl5_4 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.22/0.48  fof(f125,plain,(
% 0.22/0.48    ~v1_xboole_0(k1_xboole_0) | (~spl5_7 | spl5_18)),
% 0.22/0.48    inference(resolution,[],[f114,f61])).
% 0.22/0.49  fof(f61,plain,(
% 0.22/0.49    ( ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0)) ) | ~spl5_7),
% 0.22/0.49    inference(avatar_component_clause,[],[f60])).
% 0.22/0.49  fof(f60,plain,(
% 0.22/0.49    spl5_7 <=> ! [X0] : (~v1_xboole_0(X0) | v1_funct_1(X0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.22/0.49  fof(f114,plain,(
% 0.22/0.49    ~v1_funct_1(k1_xboole_0) | spl5_18),
% 0.22/0.49    inference(avatar_component_clause,[],[f113])).
% 0.22/0.49  fof(f113,plain,(
% 0.22/0.49    spl5_18 <=> v1_funct_1(k1_xboole_0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.22/0.49  fof(f118,plain,(
% 0.22/0.49    ~spl5_18 | ~spl5_19 | ~spl5_1 | ~spl5_2 | spl5_3 | ~spl5_5 | ~spl5_12 | ~spl5_16),
% 0.22/0.49    inference(avatar_split_clause,[],[f107,f100,f82,f52,f44,f40,f36,f116,f113])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    spl5_1 <=> v1_relat_1(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    spl5_2 <=> v1_funct_1(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    spl5_3 <=> v5_funct_1(k1_xboole_0,sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.49  fof(f52,plain,(
% 0.22/0.49    spl5_5 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.22/0.49  fof(f100,plain,(
% 0.22/0.49    spl5_16 <=> ! [X1,X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | r2_hidden(sK1(X0,X1),k1_relat_1(X1)) | v5_funct_1(X1,X0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.22/0.49  fof(f107,plain,(
% 0.22/0.49    ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | (~spl5_1 | ~spl5_2 | spl5_3 | ~spl5_5 | ~spl5_12 | ~spl5_16)),
% 0.22/0.49    inference(subsumption_resolution,[],[f106,f83])).
% 0.22/0.49  fof(f106,plain,(
% 0.22/0.49    r2_hidden(sK1(sK0,k1_xboole_0),k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | (~spl5_1 | ~spl5_2 | spl5_3 | ~spl5_5 | ~spl5_16)),
% 0.22/0.49    inference(forward_demodulation,[],[f105,f53])).
% 0.22/0.49  fof(f53,plain,(
% 0.22/0.49    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl5_5),
% 0.22/0.49    inference(avatar_component_clause,[],[f52])).
% 0.22/0.49  fof(f105,plain,(
% 0.22/0.49    ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | r2_hidden(sK1(sK0,k1_xboole_0),k1_relat_1(k1_xboole_0)) | (~spl5_1 | ~spl5_2 | spl5_3 | ~spl5_16)),
% 0.22/0.49    inference(subsumption_resolution,[],[f104,f37])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    v1_relat_1(sK0) | ~spl5_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f36])).
% 0.22/0.49  fof(f104,plain,(
% 0.22/0.49    ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | r2_hidden(sK1(sK0,k1_xboole_0),k1_relat_1(k1_xboole_0)) | ~v1_relat_1(sK0) | (~spl5_2 | spl5_3 | ~spl5_16)),
% 0.22/0.49    inference(subsumption_resolution,[],[f103,f41])).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    v1_funct_1(sK0) | ~spl5_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f40])).
% 0.22/0.49  fof(f103,plain,(
% 0.22/0.49    ~v1_funct_1(sK0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | r2_hidden(sK1(sK0,k1_xboole_0),k1_relat_1(k1_xboole_0)) | ~v1_relat_1(sK0) | (spl5_3 | ~spl5_16)),
% 0.22/0.49    inference(resolution,[],[f101,f45])).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    ~v5_funct_1(k1_xboole_0,sK0) | spl5_3),
% 0.22/0.49    inference(avatar_component_clause,[],[f44])).
% 0.22/0.49  fof(f101,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v5_funct_1(X1,X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | r2_hidden(sK1(X0,X1),k1_relat_1(X1)) | ~v1_relat_1(X0)) ) | ~spl5_16),
% 0.22/0.49    inference(avatar_component_clause,[],[f100])).
% 0.22/0.49  fof(f102,plain,(
% 0.22/0.49    spl5_16),
% 0.22/0.49    inference(avatar_split_clause,[],[f24,f100])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | r2_hidden(sK1(X0,X1),k1_relat_1(X1)) | v5_funct_1(X1,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : ((v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1)))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(flattening,[],[f13])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : ((v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_funct_1)).
% 0.22/0.49  fof(f84,plain,(
% 0.22/0.49    spl5_12 | ~spl5_8 | ~spl5_9),
% 0.22/0.49    inference(avatar_split_clause,[],[f79,f68,f64,f82])).
% 0.22/0.49  fof(f64,plain,(
% 0.22/0.49    spl5_8 <=> ! [X1,X0] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.22/0.49  fof(f68,plain,(
% 0.22/0.49    spl5_9 <=> ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.22/0.49  fof(f79,plain,(
% 0.22/0.49    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | (~spl5_8 | ~spl5_9)),
% 0.22/0.49    inference(superposition,[],[f65,f69])).
% 0.22/0.49  fof(f69,plain,(
% 0.22/0.49    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) ) | ~spl5_9),
% 0.22/0.49    inference(avatar_component_clause,[],[f68])).
% 0.22/0.49  fof(f65,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) ) | ~spl5_8),
% 0.22/0.49    inference(avatar_component_clause,[],[f64])).
% 0.22/0.49  fof(f78,plain,(
% 0.22/0.49    spl5_11),
% 0.22/0.49    inference(avatar_split_clause,[],[f27,f76])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ( ! [X0] : (r2_hidden(sK2(X0),X0) | v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).
% 0.22/0.49  fof(f70,plain,(
% 0.22/0.49    spl5_9),
% 0.22/0.49    inference(avatar_split_clause,[],[f33,f68])).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.49    inference(equality_resolution,[],[f32])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.49  fof(f66,plain,(
% 0.22/0.49    spl5_8),
% 0.22/0.49    inference(avatar_split_clause,[],[f29,f64])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.22/0.49  fof(f62,plain,(
% 0.22/0.49    spl5_7),
% 0.22/0.49    inference(avatar_split_clause,[],[f22,f60])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_xboole_0(X0) | v1_funct_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f12])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0] : (v1_xboole_0(X0) => v1_funct_1(X0))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).
% 0.22/0.49  fof(f54,plain,(
% 0.22/0.49    spl5_5),
% 0.22/0.49    inference(avatar_split_clause,[],[f20,f52])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.49    inference(cnf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    spl5_4),
% 0.22/0.49    inference(avatar_split_clause,[],[f19,f48])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    v1_xboole_0(k1_xboole_0)),
% 0.22/0.49    inference(cnf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    v1_xboole_0(k1_xboole_0)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    ~spl5_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f18,f44])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ~v5_funct_1(k1_xboole_0,sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f11])).
% 0.22/0.49  fof(f11,plain,(
% 0.22/0.49    ? [X0] : (~v5_funct_1(k1_xboole_0,X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.22/0.49    inference(flattening,[],[f10])).
% 0.22/0.49  fof(f10,plain,(
% 0.22/0.49    ? [X0] : (~v5_funct_1(k1_xboole_0,X0) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,negated_conjecture,(
% 0.22/0.49    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => v5_funct_1(k1_xboole_0,X0))),
% 0.22/0.49    inference(negated_conjecture,[],[f8])).
% 0.22/0.49  fof(f8,conjecture,(
% 0.22/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => v5_funct_1(k1_xboole_0,X0))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_funct_1)).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    spl5_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f17,f40])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    v1_funct_1(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f11])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    spl5_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f16,f36])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    v1_relat_1(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f11])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (5614)------------------------------
% 0.22/0.49  % (5614)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (5614)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (5614)Memory used [KB]: 10618
% 0.22/0.49  % (5614)Time elapsed: 0.065 s
% 0.22/0.49  % (5614)------------------------------
% 0.22/0.49  % (5614)------------------------------
% 0.22/0.49  % (5604)Success in time 0.123 s
%------------------------------------------------------------------------------
