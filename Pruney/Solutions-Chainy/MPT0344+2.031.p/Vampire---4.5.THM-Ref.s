%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:47 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 100 expanded)
%              Number of leaves         :   17 (  44 expanded)
%              Depth                    :    6
%              Number of atoms          :  181 ( 289 expanded)
%              Number of equality atoms :   14 (  30 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f128,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f26,f30,f34,f38,f42,f54,f63,f68,f72,f80,f107,f113,f127])).

fof(f127,plain,
    ( spl3_1
    | ~ spl3_5
    | spl3_20 ),
    inference(avatar_contradiction_clause,[],[f126])).

fof(f126,plain,
    ( $false
    | spl3_1
    | ~ spl3_5
    | spl3_20 ),
    inference(subsumption_resolution,[],[f122,f25])).

fof(f25,plain,
    ( k1_xboole_0 != sK1
    | spl3_1 ),
    inference(avatar_component_clause,[],[f24])).

fof(f24,plain,
    ( spl3_1
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f122,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_5
    | spl3_20 ),
    inference(resolution,[],[f112,f41])).

fof(f41,plain,
    ( ! [X0] :
        ( r2_hidden(sK2(X0),X0)
        | k1_xboole_0 = X0 )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl3_5
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | r2_hidden(sK2(X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f112,plain,
    ( ~ r2_hidden(sK2(sK1),sK1)
    | spl3_20 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl3_20
  <=> r2_hidden(sK2(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f113,plain,
    ( ~ spl3_20
    | ~ spl3_2
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f108,f105,f28,f111])).

fof(f28,plain,
    ( spl3_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f105,plain,
    ( spl3_19
  <=> ! [X0] :
        ( ~ r2_hidden(sK2(sK1),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f108,plain,
    ( ~ r2_hidden(sK2(sK1),sK1)
    | ~ spl3_2
    | ~ spl3_19 ),
    inference(resolution,[],[f106,f29])).

fof(f29,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f28])).

fof(f106,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | ~ r2_hidden(sK2(sK1),X0) )
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f105])).

fof(f107,plain,
    ( spl3_19
    | ~ spl3_12
    | spl3_13 ),
    inference(avatar_split_clause,[],[f81,f78,f70,f105])).

fof(f70,plain,
    ( spl3_12
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ r2_hidden(X2,X1)
        | r2_hidden(X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f78,plain,
    ( spl3_13
  <=> r2_hidden(sK2(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f81,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK2(sK1),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) )
    | ~ spl3_12
    | spl3_13 ),
    inference(resolution,[],[f79,f71])).

fof(f71,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(X2,X0)
        | ~ r2_hidden(X2,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f70])).

fof(f79,plain,
    ( ~ r2_hidden(sK2(sK1),sK0)
    | spl3_13 ),
    inference(avatar_component_clause,[],[f78])).

fof(f80,plain,
    ( ~ spl3_13
    | spl3_1
    | ~ spl3_5
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f75,f66,f40,f24,f78])).

fof(f66,plain,
    ( spl3_11
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f75,plain,
    ( ~ r2_hidden(sK2(sK1),sK0)
    | spl3_1
    | ~ spl3_5
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f73,f25])).

fof(f73,plain,
    ( ~ r2_hidden(sK2(sK1),sK0)
    | k1_xboole_0 = sK1
    | ~ spl3_5
    | ~ spl3_11 ),
    inference(resolution,[],[f67,f41])).

fof(f67,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f66])).

fof(f72,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f21,f70])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f68,plain,
    ( spl3_11
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f64,f61,f32,f66])).

fof(f32,plain,
    ( spl3_3
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,sK0)
        | ~ r2_hidden(X2,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f61,plain,
    ( spl3_10
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X1,X0)
        | m1_subset_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f64,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(resolution,[],[f62,f33])).

fof(f33,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK0)
        | ~ r2_hidden(X2,sK1) )
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f32])).

fof(f62,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X1,X0)
        | ~ r2_hidden(X1,X0) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f61])).

fof(f63,plain,
    ( spl3_10
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f55,f52,f36,f61])).

fof(f36,plain,
    ( spl3_4
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,X1)
        | ~ v1_xboole_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f52,plain,
    ( spl3_8
  <=> ! [X1,X0] :
        ( v1_xboole_0(X0)
        | ~ r2_hidden(X1,X0)
        | m1_subset_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f55,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | m1_subset_1(X1,X0) )
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f53,f37])).

fof(f37,plain,
    ( ! [X0,X1] :
        ( ~ v1_xboole_0(X1)
        | ~ r2_hidden(X0,X1) )
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f36])).

fof(f53,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(X0)
        | ~ r2_hidden(X1,X0)
        | m1_subset_1(X1,X0) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f52])).

fof(f54,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f19,f52])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f42,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f16,f40])).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(sK2(X0),X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f38,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f22,f36])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(f34,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f13,f32])).

fof(f13,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,sK0)
      | ~ r2_hidden(X2,sK1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r2_hidden(X2,X1)
          | ~ m1_subset_1(X2,X0) )
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r2_hidden(X2,X1)
          | ~ m1_subset_1(X2,X0) )
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ~ ( ! [X2] :
                ( m1_subset_1(X2,X0)
               => ~ r2_hidden(X2,X1) )
            & k1_xboole_0 != X1 ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ~ ( ! [X2] :
              ( m1_subset_1(X2,X0)
             => ~ r2_hidden(X2,X1) )
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_subset_1)).

fof(f30,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f14,f28])).

fof(f14,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f26,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f15,f24])).

fof(f15,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:01:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.46  % (9146)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.47  % (9146)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f128,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(avatar_sat_refutation,[],[f26,f30,f34,f38,f42,f54,f63,f68,f72,f80,f107,f113,f127])).
% 0.22/0.47  fof(f127,plain,(
% 0.22/0.47    spl3_1 | ~spl3_5 | spl3_20),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f126])).
% 0.22/0.47  fof(f126,plain,(
% 0.22/0.47    $false | (spl3_1 | ~spl3_5 | spl3_20)),
% 0.22/0.47    inference(subsumption_resolution,[],[f122,f25])).
% 0.22/0.47  fof(f25,plain,(
% 0.22/0.47    k1_xboole_0 != sK1 | spl3_1),
% 0.22/0.47    inference(avatar_component_clause,[],[f24])).
% 0.22/0.47  fof(f24,plain,(
% 0.22/0.47    spl3_1 <=> k1_xboole_0 = sK1),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.47  fof(f122,plain,(
% 0.22/0.47    k1_xboole_0 = sK1 | (~spl3_5 | spl3_20)),
% 0.22/0.47    inference(resolution,[],[f112,f41])).
% 0.22/0.47  fof(f41,plain,(
% 0.22/0.47    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) ) | ~spl3_5),
% 0.22/0.47    inference(avatar_component_clause,[],[f40])).
% 0.22/0.47  fof(f40,plain,(
% 0.22/0.47    spl3_5 <=> ! [X0] : (k1_xboole_0 = X0 | r2_hidden(sK2(X0),X0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.47  fof(f112,plain,(
% 0.22/0.47    ~r2_hidden(sK2(sK1),sK1) | spl3_20),
% 0.22/0.47    inference(avatar_component_clause,[],[f111])).
% 0.22/0.47  fof(f111,plain,(
% 0.22/0.47    spl3_20 <=> r2_hidden(sK2(sK1),sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.22/0.47  fof(f113,plain,(
% 0.22/0.47    ~spl3_20 | ~spl3_2 | ~spl3_19),
% 0.22/0.47    inference(avatar_split_clause,[],[f108,f105,f28,f111])).
% 0.22/0.47  fof(f28,plain,(
% 0.22/0.47    spl3_2 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.47  fof(f105,plain,(
% 0.22/0.47    spl3_19 <=> ! [X0] : (~r2_hidden(sK2(sK1),X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.22/0.47  fof(f108,plain,(
% 0.22/0.47    ~r2_hidden(sK2(sK1),sK1) | (~spl3_2 | ~spl3_19)),
% 0.22/0.47    inference(resolution,[],[f106,f29])).
% 0.22/0.47  fof(f29,plain,(
% 0.22/0.47    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl3_2),
% 0.22/0.47    inference(avatar_component_clause,[],[f28])).
% 0.22/0.47  fof(f106,plain,(
% 0.22/0.47    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~r2_hidden(sK2(sK1),X0)) ) | ~spl3_19),
% 0.22/0.47    inference(avatar_component_clause,[],[f105])).
% 0.22/0.47  fof(f107,plain,(
% 0.22/0.47    spl3_19 | ~spl3_12 | spl3_13),
% 0.22/0.47    inference(avatar_split_clause,[],[f81,f78,f70,f105])).
% 0.22/0.47  fof(f70,plain,(
% 0.22/0.47    spl3_12 <=> ! [X1,X0,X2] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.47  fof(f78,plain,(
% 0.22/0.47    spl3_13 <=> r2_hidden(sK2(sK1),sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.47  fof(f81,plain,(
% 0.22/0.47    ( ! [X0] : (~r2_hidden(sK2(sK1),X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0))) ) | (~spl3_12 | spl3_13)),
% 0.22/0.47    inference(resolution,[],[f79,f71])).
% 0.22/0.47  fof(f71,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl3_12),
% 0.22/0.47    inference(avatar_component_clause,[],[f70])).
% 0.22/0.47  fof(f79,plain,(
% 0.22/0.47    ~r2_hidden(sK2(sK1),sK0) | spl3_13),
% 0.22/0.47    inference(avatar_component_clause,[],[f78])).
% 0.22/0.47  fof(f80,plain,(
% 0.22/0.47    ~spl3_13 | spl3_1 | ~spl3_5 | ~spl3_11),
% 0.22/0.47    inference(avatar_split_clause,[],[f75,f66,f40,f24,f78])).
% 0.22/0.47  fof(f66,plain,(
% 0.22/0.47    spl3_11 <=> ! [X0] : (~r2_hidden(X0,sK0) | ~r2_hidden(X0,sK1))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.47  fof(f75,plain,(
% 0.22/0.47    ~r2_hidden(sK2(sK1),sK0) | (spl3_1 | ~spl3_5 | ~spl3_11)),
% 0.22/0.47    inference(subsumption_resolution,[],[f73,f25])).
% 0.22/0.47  fof(f73,plain,(
% 0.22/0.47    ~r2_hidden(sK2(sK1),sK0) | k1_xboole_0 = sK1 | (~spl3_5 | ~spl3_11)),
% 0.22/0.47    inference(resolution,[],[f67,f41])).
% 0.22/0.47  fof(f67,plain,(
% 0.22/0.47    ( ! [X0] : (~r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0)) ) | ~spl3_11),
% 0.22/0.47    inference(avatar_component_clause,[],[f66])).
% 0.22/0.47  fof(f72,plain,(
% 0.22/0.47    spl3_12),
% 0.22/0.47    inference(avatar_split_clause,[],[f21,f70])).
% 0.22/0.47  fof(f21,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f11])).
% 0.22/0.47  fof(f11,plain,(
% 0.22/0.47    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f4])).
% 0.22/0.47  fof(f4,axiom,(
% 0.22/0.47    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.22/0.47  fof(f68,plain,(
% 0.22/0.47    spl3_11 | ~spl3_3 | ~spl3_10),
% 0.22/0.47    inference(avatar_split_clause,[],[f64,f61,f32,f66])).
% 0.22/0.47  fof(f32,plain,(
% 0.22/0.47    spl3_3 <=> ! [X2] : (~m1_subset_1(X2,sK0) | ~r2_hidden(X2,sK1))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.47  fof(f61,plain,(
% 0.22/0.47    spl3_10 <=> ! [X1,X0] : (~r2_hidden(X1,X0) | m1_subset_1(X1,X0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.47  fof(f64,plain,(
% 0.22/0.47    ( ! [X0] : (~r2_hidden(X0,sK0) | ~r2_hidden(X0,sK1)) ) | (~spl3_3 | ~spl3_10)),
% 0.22/0.47    inference(resolution,[],[f62,f33])).
% 0.22/0.47  fof(f33,plain,(
% 0.22/0.47    ( ! [X2] : (~m1_subset_1(X2,sK0) | ~r2_hidden(X2,sK1)) ) | ~spl3_3),
% 0.22/0.47    inference(avatar_component_clause,[],[f32])).
% 0.22/0.47  fof(f62,plain,(
% 0.22/0.47    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) ) | ~spl3_10),
% 0.22/0.47    inference(avatar_component_clause,[],[f61])).
% 0.22/0.47  fof(f63,plain,(
% 0.22/0.47    spl3_10 | ~spl3_4 | ~spl3_8),
% 0.22/0.47    inference(avatar_split_clause,[],[f55,f52,f36,f61])).
% 0.22/0.47  fof(f36,plain,(
% 0.22/0.47    spl3_4 <=> ! [X1,X0] : (~r2_hidden(X0,X1) | ~v1_xboole_0(X1))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.47  fof(f52,plain,(
% 0.22/0.47    spl3_8 <=> ! [X1,X0] : (v1_xboole_0(X0) | ~r2_hidden(X1,X0) | m1_subset_1(X1,X0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.47  fof(f55,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~r2_hidden(X1,X0) | m1_subset_1(X1,X0)) ) | (~spl3_4 | ~spl3_8)),
% 0.22/0.47    inference(subsumption_resolution,[],[f53,f37])).
% 0.22/0.47  fof(f37,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1)) ) | ~spl3_4),
% 0.22/0.47    inference(avatar_component_clause,[],[f36])).
% 0.22/0.47  fof(f53,plain,(
% 0.22/0.47    ( ! [X0,X1] : (v1_xboole_0(X0) | ~r2_hidden(X1,X0) | m1_subset_1(X1,X0)) ) | ~spl3_8),
% 0.22/0.47    inference(avatar_component_clause,[],[f52])).
% 0.22/0.47  fof(f54,plain,(
% 0.22/0.47    spl3_8),
% 0.22/0.47    inference(avatar_split_clause,[],[f19,f52])).
% 0.22/0.47  fof(f19,plain,(
% 0.22/0.47    ( ! [X0,X1] : (v1_xboole_0(X0) | ~r2_hidden(X1,X0) | m1_subset_1(X1,X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f10])).
% 0.22/0.47  fof(f10,plain,(
% 0.22/0.47    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f3])).
% 0.22/0.47  fof(f3,axiom,(
% 0.22/0.47    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.22/0.47  fof(f42,plain,(
% 0.22/0.47    spl3_5),
% 0.22/0.47    inference(avatar_split_clause,[],[f16,f40])).
% 0.22/0.47  fof(f16,plain,(
% 0.22/0.47    ( ! [X0] : (k1_xboole_0 = X0 | r2_hidden(sK2(X0),X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f9])).
% 0.22/0.47  fof(f9,plain,(
% 0.22/0.47    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.22/0.47    inference(ennf_transformation,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.22/0.47  fof(f38,plain,(
% 0.22/0.47    spl3_4),
% 0.22/0.47    inference(avatar_split_clause,[],[f22,f36])).
% 0.22/0.47  fof(f22,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~v1_xboole_0(X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f12])).
% 0.22/0.47  fof(f12,plain,(
% 0.22/0.47    ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0,X1] : ~(v1_xboole_0(X1) & r2_hidden(X0,X1))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).
% 0.22/0.47  fof(f34,plain,(
% 0.22/0.47    spl3_3),
% 0.22/0.47    inference(avatar_split_clause,[],[f13,f32])).
% 0.22/0.47  fof(f13,plain,(
% 0.22/0.47    ( ! [X2] : (~m1_subset_1(X2,sK0) | ~r2_hidden(X2,sK1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f8])).
% 0.22/0.47  fof(f8,plain,(
% 0.22/0.47    ? [X0,X1] : (! [X2] : (~r2_hidden(X2,X1) | ~m1_subset_1(X2,X0)) & k1_xboole_0 != X1 & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.47    inference(flattening,[],[f7])).
% 0.22/0.47  fof(f7,plain,(
% 0.22/0.47    ? [X0,X1] : ((! [X2] : (~r2_hidden(X2,X1) | ~m1_subset_1(X2,X0)) & k1_xboole_0 != X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f6])).
% 0.22/0.47  fof(f6,negated_conjecture,(
% 0.22/0.47    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~(! [X2] : (m1_subset_1(X2,X0) => ~r2_hidden(X2,X1)) & k1_xboole_0 != X1))),
% 0.22/0.47    inference(negated_conjecture,[],[f5])).
% 0.22/0.47  fof(f5,conjecture,(
% 0.22/0.47    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~(! [X2] : (m1_subset_1(X2,X0) => ~r2_hidden(X2,X1)) & k1_xboole_0 != X1))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_subset_1)).
% 0.22/0.47  fof(f30,plain,(
% 0.22/0.47    spl3_2),
% 0.22/0.47    inference(avatar_split_clause,[],[f14,f28])).
% 0.22/0.47  fof(f14,plain,(
% 0.22/0.47    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.47    inference(cnf_transformation,[],[f8])).
% 0.22/0.47  fof(f26,plain,(
% 0.22/0.47    ~spl3_1),
% 0.22/0.47    inference(avatar_split_clause,[],[f15,f24])).
% 0.22/0.47  fof(f15,plain,(
% 0.22/0.47    k1_xboole_0 != sK1),
% 0.22/0.47    inference(cnf_transformation,[],[f8])).
% 0.22/0.47  % SZS output end Proof for theBenchmark
% 0.22/0.47  % (9146)------------------------------
% 0.22/0.47  % (9146)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (9146)Termination reason: Refutation
% 0.22/0.47  
% 0.22/0.47  % (9146)Memory used [KB]: 10618
% 0.22/0.47  % (9146)Time elapsed: 0.032 s
% 0.22/0.47  % (9146)------------------------------
% 0.22/0.47  % (9146)------------------------------
% 0.22/0.47  % (9136)Success in time 0.117 s
%------------------------------------------------------------------------------
