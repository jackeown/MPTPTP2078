%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:39 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 127 expanded)
%              Number of leaves         :   25 (  54 expanded)
%              Depth                    :    6
%              Number of atoms          :  243 ( 339 expanded)
%              Number of equality atoms :   16 (  21 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f210,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f52,f57,f61,f65,f73,f80,f84,f105,f110,f140,f176,f178,f193,f198,f208])).

fof(f208,plain,
    ( ~ spl5_6
    | ~ spl5_8
    | ~ spl5_25
    | spl5_26 ),
    inference(avatar_contradiction_clause,[],[f207])).

fof(f207,plain,
    ( $false
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_25
    | spl5_26 ),
    inference(subsumption_resolution,[],[f197,f206])).

fof(f206,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_25 ),
    inference(forward_demodulation,[],[f200,f201])).

fof(f201,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)
    | ~ spl5_8
    | ~ spl5_25 ),
    inference(unit_resulting_resolution,[],[f192,f83])).

fof(f83,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(X0),X0)
        | k1_xboole_0 = X0 )
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl5_8
  <=> ! [X0] :
        ( r2_hidden(sK3(X0),X0)
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f192,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0))
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl5_25
  <=> ! [X1,X0] : ~ r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f200,plain,
    ( ! [X0] : v1_xboole_0(k3_xboole_0(X0,k1_xboole_0))
    | ~ spl5_6
    | ~ spl5_25 ),
    inference(unit_resulting_resolution,[],[f192,f72])).

fof(f72,plain,
    ( ! [X0] :
        ( r2_hidden(sK2(X0),X0)
        | v1_xboole_0(X0) )
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl5_6
  <=> ! [X0] :
        ( v1_xboole_0(X0)
        | r2_hidden(sK2(X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f197,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl5_26 ),
    inference(avatar_component_clause,[],[f195])).

fof(f195,plain,
    ( spl5_26
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f198,plain,
    ( ~ spl5_26
    | spl5_7
    | ~ spl5_23 ),
    inference(avatar_split_clause,[],[f181,f173,f77,f195])).

fof(f77,plain,
    ( spl5_7
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f173,plain,
    ( spl5_23
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f181,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl5_7
    | ~ spl5_23 ),
    inference(superposition,[],[f79,f175])).

fof(f175,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f173])).

fof(f79,plain,
    ( ~ v1_xboole_0(sK1)
    | spl5_7 ),
    inference(avatar_component_clause,[],[f77])).

fof(f193,plain,
    ( spl5_25
    | ~ spl5_3
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f121,f108,f59,f191])).

fof(f59,plain,
    ( spl5_3
  <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f108,plain,
    ( spl5_14
  <=> ! [X1,X0,X2] :
        ( ~ r1_xboole_0(X0,X1)
        | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f121,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0))
    | ~ spl5_3
    | ~ spl5_14 ),
    inference(unit_resulting_resolution,[],[f60,f109])).

fof(f109,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f108])).

fof(f60,plain,
    ( ! [X0] : r1_xboole_0(X0,k1_xboole_0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f59])).

fof(f178,plain,
    ( ~ spl5_1
    | spl5_7
    | ~ spl5_13
    | spl5_22 ),
    inference(avatar_contradiction_clause,[],[f177])).

fof(f177,plain,
    ( $false
    | ~ spl5_1
    | spl5_7
    | ~ spl5_13
    | spl5_22 ),
    inference(subsumption_resolution,[],[f116,f171])).

fof(f171,plain,
    ( ~ m1_subset_1(sK0,sK1)
    | spl5_22 ),
    inference(avatar_component_clause,[],[f169])).

fof(f169,plain,
    ( spl5_22
  <=> m1_subset_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f116,plain,
    ( m1_subset_1(sK0,sK1)
    | ~ spl5_1
    | spl5_7
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f79,f51,f104])).

fof(f104,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | m1_subset_1(X1,X0)
        | v1_xboole_0(X0) )
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl5_13
  <=> ! [X1,X0] :
        ( m1_subset_1(X1,X0)
        | ~ r2_hidden(X1,X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f51,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl5_1
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f176,plain,
    ( ~ spl5_22
    | spl5_23
    | spl5_2
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f149,f138,f54,f173,f169])).

fof(f54,plain,
    ( spl5_2
  <=> m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

% (31804)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% (31806)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% (31810)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% (31806)Refutation not found, incomplete strategy% (31806)------------------------------
% (31806)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (31806)Termination reason: Refutation not found, incomplete strategy

% (31806)Memory used [KB]: 10618
% (31806)Time elapsed: 0.062 s
% (31806)------------------------------
% (31806)------------------------------
fof(f138,plain,
    ( spl5_18
  <=> ! [X1,X0] :
        ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
        | k1_xboole_0 = X0
        | ~ m1_subset_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f149,plain,
    ( k1_xboole_0 = sK1
    | ~ m1_subset_1(sK0,sK1)
    | spl5_2
    | ~ spl5_18 ),
    inference(resolution,[],[f139,f56])).

fof(f56,plain,
    ( ~ m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f139,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
        | k1_xboole_0 = X0
        | ~ m1_subset_1(X1,X0) )
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f138])).

fof(f140,plain,(
    spl5_18 ),
    inference(avatar_split_clause,[],[f45,f138])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ( k1_xboole_0 != X0
       => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_subset_1)).

fof(f110,plain,(
    spl5_14 ),
    inference(avatar_split_clause,[],[f44,f108])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f17,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f105,plain,(
    spl5_13 ),
    inference(avatar_split_clause,[],[f40,f103])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f84,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f37,f82])).

fof(f37,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f26])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f80,plain,
    ( ~ spl5_7
    | ~ spl5_1
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f74,f63,f49,f77])).

fof(f63,plain,
    ( spl5_4
  <=> ! [X0,X2] :
        ( ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f74,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl5_1
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f51,f64])).

fof(f64,plain,
    ( ! [X2,X0] :
        ( ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f63])).

fof(f73,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f36,f71])).

fof(f36,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK2(X0),X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK2(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f23,f24])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f65,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f35,f63])).

fof(f35,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f61,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f33,f59])).

fof(f33,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f57,plain,(
    ~ spl5_2 ),
    inference(avatar_split_clause,[],[f32,f54])).

fof(f32,plain,(
    ~ m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ~ m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1))
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f20])).

fof(f20,plain,
    ( ? [X0,X1] :
        ( ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
        & r2_hidden(X0,X1) )
   => ( ~ m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1))
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

fof(f52,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f31,f49])).

fof(f31,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:44:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.47  % (31803)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.47  % (31800)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.47  % (31811)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.47  % (31799)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.47  % (31796)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.47  % (31800)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f210,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f52,f57,f61,f65,f73,f80,f84,f105,f110,f140,f176,f178,f193,f198,f208])).
% 0.20/0.47  fof(f208,plain,(
% 0.20/0.47    ~spl5_6 | ~spl5_8 | ~spl5_25 | spl5_26),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f207])).
% 0.20/0.47  fof(f207,plain,(
% 0.20/0.47    $false | (~spl5_6 | ~spl5_8 | ~spl5_25 | spl5_26)),
% 0.20/0.47    inference(subsumption_resolution,[],[f197,f206])).
% 0.20/0.47  fof(f206,plain,(
% 0.20/0.47    v1_xboole_0(k1_xboole_0) | (~spl5_6 | ~spl5_8 | ~spl5_25)),
% 0.20/0.47    inference(forward_demodulation,[],[f200,f201])).
% 0.20/0.47  fof(f201,plain,(
% 0.20/0.47    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) ) | (~spl5_8 | ~spl5_25)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f192,f83])).
% 0.20/0.47  fof(f83,plain,(
% 0.20/0.47    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) ) | ~spl5_8),
% 0.20/0.47    inference(avatar_component_clause,[],[f82])).
% 0.20/0.47  fof(f82,plain,(
% 0.20/0.47    spl5_8 <=> ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.20/0.47  fof(f192,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0))) ) | ~spl5_25),
% 0.20/0.47    inference(avatar_component_clause,[],[f191])).
% 0.20/0.47  fof(f191,plain,(
% 0.20/0.47    spl5_25 <=> ! [X1,X0] : ~r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 0.20/0.47  fof(f200,plain,(
% 0.20/0.47    ( ! [X0] : (v1_xboole_0(k3_xboole_0(X0,k1_xboole_0))) ) | (~spl5_6 | ~spl5_25)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f192,f72])).
% 0.20/0.47  fof(f72,plain,(
% 0.20/0.47    ( ! [X0] : (r2_hidden(sK2(X0),X0) | v1_xboole_0(X0)) ) | ~spl5_6),
% 0.20/0.47    inference(avatar_component_clause,[],[f71])).
% 0.20/0.47  fof(f71,plain,(
% 0.20/0.47    spl5_6 <=> ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK2(X0),X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.20/0.47  fof(f197,plain,(
% 0.20/0.47    ~v1_xboole_0(k1_xboole_0) | spl5_26),
% 0.20/0.47    inference(avatar_component_clause,[],[f195])).
% 0.20/0.47  fof(f195,plain,(
% 0.20/0.47    spl5_26 <=> v1_xboole_0(k1_xboole_0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 0.20/0.47  fof(f198,plain,(
% 0.20/0.47    ~spl5_26 | spl5_7 | ~spl5_23),
% 0.20/0.47    inference(avatar_split_clause,[],[f181,f173,f77,f195])).
% 0.20/0.47  fof(f77,plain,(
% 0.20/0.47    spl5_7 <=> v1_xboole_0(sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.20/0.47  fof(f173,plain,(
% 0.20/0.47    spl5_23 <=> k1_xboole_0 = sK1),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 0.20/0.47  fof(f181,plain,(
% 0.20/0.47    ~v1_xboole_0(k1_xboole_0) | (spl5_7 | ~spl5_23)),
% 0.20/0.47    inference(superposition,[],[f79,f175])).
% 0.20/0.47  fof(f175,plain,(
% 0.20/0.47    k1_xboole_0 = sK1 | ~spl5_23),
% 0.20/0.47    inference(avatar_component_clause,[],[f173])).
% 0.20/0.47  fof(f79,plain,(
% 0.20/0.47    ~v1_xboole_0(sK1) | spl5_7),
% 0.20/0.47    inference(avatar_component_clause,[],[f77])).
% 0.20/0.47  fof(f193,plain,(
% 0.20/0.47    spl5_25 | ~spl5_3 | ~spl5_14),
% 0.20/0.47    inference(avatar_split_clause,[],[f121,f108,f59,f191])).
% 0.20/0.47  fof(f59,plain,(
% 0.20/0.47    spl5_3 <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.47  fof(f108,plain,(
% 0.20/0.47    spl5_14 <=> ! [X1,X0,X2] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.20/0.47  fof(f121,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0))) ) | (~spl5_3 | ~spl5_14)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f60,f109])).
% 0.20/0.47  fof(f109,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) ) | ~spl5_14),
% 0.20/0.47    inference(avatar_component_clause,[],[f108])).
% 0.20/0.47  fof(f60,plain,(
% 0.20/0.47    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) ) | ~spl5_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f59])).
% 0.20/0.47  fof(f178,plain,(
% 0.20/0.47    ~spl5_1 | spl5_7 | ~spl5_13 | spl5_22),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f177])).
% 0.20/0.47  fof(f177,plain,(
% 0.20/0.47    $false | (~spl5_1 | spl5_7 | ~spl5_13 | spl5_22)),
% 0.20/0.47    inference(subsumption_resolution,[],[f116,f171])).
% 0.20/0.47  fof(f171,plain,(
% 0.20/0.47    ~m1_subset_1(sK0,sK1) | spl5_22),
% 0.20/0.47    inference(avatar_component_clause,[],[f169])).
% 0.20/0.47  fof(f169,plain,(
% 0.20/0.47    spl5_22 <=> m1_subset_1(sK0,sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 0.20/0.47  fof(f116,plain,(
% 0.20/0.47    m1_subset_1(sK0,sK1) | (~spl5_1 | spl5_7 | ~spl5_13)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f79,f51,f104])).
% 0.20/0.47  fof(f104,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r2_hidden(X1,X0) | m1_subset_1(X1,X0) | v1_xboole_0(X0)) ) | ~spl5_13),
% 0.20/0.47    inference(avatar_component_clause,[],[f103])).
% 0.20/0.47  fof(f103,plain,(
% 0.20/0.47    spl5_13 <=> ! [X1,X0] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.20/0.47  fof(f51,plain,(
% 0.20/0.47    r2_hidden(sK0,sK1) | ~spl5_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f49])).
% 0.20/0.47  fof(f49,plain,(
% 0.20/0.47    spl5_1 <=> r2_hidden(sK0,sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.47  fof(f176,plain,(
% 0.20/0.47    ~spl5_22 | spl5_23 | spl5_2 | ~spl5_18),
% 0.20/0.47    inference(avatar_split_clause,[],[f149,f138,f54,f173,f169])).
% 0.20/0.47  fof(f54,plain,(
% 0.20/0.47    spl5_2 <=> m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.48  % (31804)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.48  % (31806)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.48  % (31810)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.48  % (31806)Refutation not found, incomplete strategy% (31806)------------------------------
% 0.20/0.48  % (31806)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (31806)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (31806)Memory used [KB]: 10618
% 0.20/0.48  % (31806)Time elapsed: 0.062 s
% 0.20/0.48  % (31806)------------------------------
% 0.20/0.48  % (31806)------------------------------
% 0.20/0.48  fof(f138,plain,(
% 0.20/0.48    spl5_18 <=> ! [X1,X0] : (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X1,X0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.20/0.48  fof(f149,plain,(
% 0.20/0.48    k1_xboole_0 = sK1 | ~m1_subset_1(sK0,sK1) | (spl5_2 | ~spl5_18)),
% 0.20/0.48    inference(resolution,[],[f139,f56])).
% 0.20/0.48  fof(f56,plain,(
% 0.20/0.48    ~m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1)) | spl5_2),
% 0.20/0.48    inference(avatar_component_clause,[],[f54])).
% 0.20/0.48  fof(f139,plain,(
% 0.20/0.48    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X1,X0)) ) | ~spl5_18),
% 0.20/0.48    inference(avatar_component_clause,[],[f138])).
% 0.20/0.48  fof(f140,plain,(
% 0.20/0.48    spl5_18),
% 0.20/0.48    inference(avatar_split_clause,[],[f45,f138])).
% 0.20/0.48  fof(f45,plain,(
% 0.20/0.48    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X1,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X1,X0))),
% 0.20/0.48    inference(flattening,[],[f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ! [X0,X1] : ((m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0) | ~m1_subset_1(X1,X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f10])).
% 0.20/0.48  fof(f10,axiom,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(X1,X0) => (k1_xboole_0 != X0 => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_subset_1)).
% 0.20/0.48  fof(f110,plain,(
% 0.20/0.48    spl5_14),
% 0.20/0.48    inference(avatar_split_clause,[],[f44,f108])).
% 0.20/0.48  fof(f44,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f30])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f17,f29])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.20/0.48    inference(ennf_transformation,[],[f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.48    inference(rectify,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.20/0.48  fof(f105,plain,(
% 0.20/0.48    spl5_13),
% 0.20/0.48    inference(avatar_split_clause,[],[f40,f103])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f28])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.20/0.48    inference(nnf_transformation,[],[f16])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f9])).
% 0.20/0.48  fof(f9,axiom,(
% 0.20/0.48    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.20/0.48  fof(f84,plain,(
% 0.20/0.48    spl5_8),
% 0.20/0.48    inference(avatar_split_clause,[],[f37,f82])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f27])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f26])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.20/0.48    inference(ennf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.20/0.48  fof(f80,plain,(
% 0.20/0.48    ~spl5_7 | ~spl5_1 | ~spl5_4),
% 0.20/0.48    inference(avatar_split_clause,[],[f74,f63,f49,f77])).
% 0.20/0.48  fof(f63,plain,(
% 0.20/0.48    spl5_4 <=> ! [X0,X2] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.20/0.48  fof(f74,plain,(
% 0.20/0.48    ~v1_xboole_0(sK1) | (~spl5_1 | ~spl5_4)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f51,f64])).
% 0.20/0.48  fof(f64,plain,(
% 0.20/0.48    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) ) | ~spl5_4),
% 0.20/0.48    inference(avatar_component_clause,[],[f63])).
% 0.20/0.48  fof(f73,plain,(
% 0.20/0.48    spl5_6),
% 0.20/0.48    inference(avatar_split_clause,[],[f36,f71])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK2(X0),X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f25])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK2(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f23,f24])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.48    inference(rectify,[],[f22])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.48    inference(nnf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.48  fof(f65,plain,(
% 0.20/0.48    spl5_4),
% 0.20/0.48    inference(avatar_split_clause,[],[f35,f63])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f25])).
% 0.20/0.48  fof(f61,plain,(
% 0.20/0.48    spl5_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f33,f59])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.20/0.48  fof(f57,plain,(
% 0.20/0.48    ~spl5_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f32,f54])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    ~m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1))),
% 0.20/0.48    inference(cnf_transformation,[],[f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ~m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1)) & r2_hidden(sK0,sK1)),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ? [X0,X1] : (~m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) & r2_hidden(X0,X1)) => (~m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1)) & r2_hidden(sK0,sK1))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ? [X0,X1] : (~m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) & r2_hidden(X0,X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f12])).
% 0.20/0.48  fof(f12,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 0.20/0.48    inference(negated_conjecture,[],[f11])).
% 0.20/0.48  fof(f11,conjecture,(
% 0.20/0.48    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).
% 0.20/0.48  fof(f52,plain,(
% 0.20/0.48    spl5_1),
% 0.20/0.48    inference(avatar_split_clause,[],[f31,f49])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    r2_hidden(sK0,sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f21])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (31800)------------------------------
% 0.20/0.48  % (31800)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (31800)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (31800)Memory used [KB]: 6140
% 0.20/0.48  % (31800)Time elapsed: 0.052 s
% 0.20/0.48  % (31800)------------------------------
% 0.20/0.48  % (31800)------------------------------
% 0.20/0.48  % (31794)Success in time 0.125 s
%------------------------------------------------------------------------------
