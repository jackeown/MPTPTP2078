%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:03 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 154 expanded)
%              Number of leaves         :   29 (  70 expanded)
%              Depth                    :    7
%              Number of atoms          :  266 ( 421 expanded)
%              Number of equality atoms :   13 (  21 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f258,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f58,f63,f68,f72,f80,f84,f107,f121,f125,f131,f135,f143,f167,f199,f217,f229,f254,f257])).

fof(f257,plain,
    ( ~ spl2_2
    | ~ spl2_20
    | spl2_26
    | ~ spl2_29
    | ~ spl2_31 ),
    inference(avatar_contradiction_clause,[],[f256])).

fof(f256,plain,
    ( $false
    | ~ spl2_2
    | ~ spl2_20
    | spl2_26
    | ~ spl2_29
    | ~ spl2_31 ),
    inference(subsumption_resolution,[],[f62,f255])).

fof(f255,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl2_20
    | spl2_26
    | ~ spl2_29
    | ~ spl2_31 ),
    inference(subsumption_resolution,[],[f230,f253])).

fof(f253,plain,
    ( ! [X2,X0] : r1_tarski(k3_xboole_0(X2,X0),X0)
    | ~ spl2_31 ),
    inference(avatar_component_clause,[],[f252])).

fof(f252,plain,
    ( spl2_31
  <=> ! [X0,X2] : r1_tarski(k3_xboole_0(X2,X0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).

fof(f230,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK1),sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl2_20
    | spl2_26
    | ~ spl2_29 ),
    inference(subsumption_resolution,[],[f208,f228])).

fof(f228,plain,
    ( ! [X0] : v1_relat_1(k3_xboole_0(sK0,X0))
    | ~ spl2_29 ),
    inference(avatar_component_clause,[],[f227])).

fof(f227,plain,
    ( spl2_29
  <=> ! [X0] : v1_relat_1(k3_xboole_0(sK0,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).

fof(f208,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK1),sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k3_xboole_0(sK0,sK1))
    | ~ spl2_20
    | spl2_26 ),
    inference(resolution,[],[f198,f142])).

fof(f142,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl2_20
  <=> ! [X1,X0] :
        ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f198,plain,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK1))
    | spl2_26 ),
    inference(avatar_component_clause,[],[f196])).

fof(f196,plain,
    ( spl2_26
  <=> r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f62,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl2_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f254,plain,
    ( spl2_31
    | ~ spl2_12
    | ~ spl2_15
    | ~ spl2_16
    | ~ spl2_17 ),
    inference(avatar_split_clause,[],[f177,f129,f123,f119,f105,f252])).

fof(f105,plain,
    ( spl2_12
  <=> ! [X1,X0] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f119,plain,
    ( spl2_15
  <=> ! [X1,X0,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f123,plain,
    ( spl2_16
  <=> ! [X1,X0,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f129,plain,
    ( spl2_17
  <=> ! [X1,X0,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f177,plain,
    ( ! [X2,X0] : r1_tarski(k3_xboole_0(X2,X0),X0)
    | ~ spl2_12
    | ~ spl2_15
    | ~ spl2_16
    | ~ spl2_17 ),
    inference(forward_demodulation,[],[f176,f154])).

fof(f154,plain,
    ( ! [X2,X0,X1] : k3_xboole_0(X0,X1) = k2_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,X2)),k4_xboole_0(k3_xboole_0(X0,X1),X2))
    | ~ spl2_12
    | ~ spl2_16 ),
    inference(superposition,[],[f106,f124])).

fof(f124,plain,
    ( ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f123])).

fof(f106,plain,
    ( ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f105])).

fof(f176,plain,
    ( ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X2,k3_xboole_0(X0,X1)),k4_xboole_0(k3_xboole_0(X2,X0),X1)),X0)
    | ~ spl2_12
    | ~ spl2_15
    | ~ spl2_17 ),
    inference(forward_demodulation,[],[f173,f120])).

fof(f120,plain,
    ( ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f119])).

fof(f173,plain,
    ( ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X2,k3_xboole_0(X0,X1)),k3_xboole_0(X2,k4_xboole_0(X0,X1))),X0)
    | ~ spl2_12
    | ~ spl2_17 ),
    inference(superposition,[],[f130,f106])).

fof(f130,plain,
    ( ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f129])).

fof(f229,plain,
    ( spl2_29
    | ~ spl2_1
    | ~ spl2_7
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f209,f165,f82,f55,f227])).

fof(f55,plain,
    ( spl2_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f82,plain,
    ( spl2_7
  <=> ! [X1,X0] :
        ( v1_relat_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f165,plain,
    ( spl2_22
  <=> ! [X1,X0] : m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f209,plain,
    ( ! [X0] : v1_relat_1(k3_xboole_0(sK0,X0))
    | ~ spl2_1
    | ~ spl2_7
    | ~ spl2_22 ),
    inference(unit_resulting_resolution,[],[f57,f166,f83])).

fof(f83,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f82])).

fof(f166,plain,
    ( ! [X0,X1] : m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(X0))
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f165])).

fof(f57,plain,
    ( v1_relat_1(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f55])).

fof(f217,plain,
    ( ~ spl2_1
    | ~ spl2_4
    | ~ spl2_7
    | ~ spl2_20
    | ~ spl2_22
    | spl2_25 ),
    inference(avatar_contradiction_clause,[],[f216])).

fof(f216,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_7
    | ~ spl2_20
    | ~ spl2_22
    | spl2_25 ),
    inference(subsumption_resolution,[],[f204,f209])).

fof(f204,plain,
    ( ~ v1_relat_1(k3_xboole_0(sK0,sK1))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_20
    | spl2_25 ),
    inference(unit_resulting_resolution,[],[f57,f71,f194,f142])).

fof(f194,plain,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK0))
    | spl2_25 ),
    inference(avatar_component_clause,[],[f192])).

fof(f192,plain,
    ( spl2_25
  <=> r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).

fof(f71,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl2_4
  <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f199,plain,
    ( ~ spl2_25
    | ~ spl2_26
    | spl2_3
    | ~ spl2_18 ),
    inference(avatar_split_clause,[],[f180,f133,f65,f196,f192])).

fof(f65,plain,
    ( spl2_3
  <=> r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f133,plain,
    ( spl2_18
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,k3_xboole_0(X1,X2))
        | ~ r1_tarski(X0,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f180,plain,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK1))
    | ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK0))
    | spl2_3
    | ~ spl2_18 ),
    inference(resolution,[],[f134,f67])).

fof(f67,plain,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f65])).

fof(f134,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(X0,k3_xboole_0(X1,X2))
        | ~ r1_tarski(X0,X2)
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f133])).

fof(f167,plain,
    ( spl2_22
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f98,f78,f70,f165])).

fof(f78,plain,
    ( spl2_6
  <=> ! [X1,X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f98,plain,
    ( ! [X0,X1] : m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(X0))
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(unit_resulting_resolution,[],[f71,f79])).

fof(f79,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f78])).

fof(f143,plain,(
    spl2_20 ),
    inference(avatar_split_clause,[],[f35,f141])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(f135,plain,(
    spl2_18 ),
    inference(avatar_split_clause,[],[f49,f133])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f131,plain,(
    spl2_17 ),
    inference(avatar_split_clause,[],[f48,f129])).

fof(f48,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).

fof(f125,plain,(
    spl2_16 ),
    inference(avatar_split_clause,[],[f47,f123])).

fof(f47,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f121,plain,(
    spl2_15 ),
    inference(avatar_split_clause,[],[f46,f119])).

fof(f46,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f107,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f42,f105])).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

% (8305)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% (8313)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% (8312)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
fof(f84,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f36,f82])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f80,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f44,f78])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f72,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f37,f70])).

fof(f37,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f68,plain,(
    ~ spl2_3 ),
    inference(avatar_split_clause,[],[f33,f65])).

fof(f33,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f28,f27])).

% (8311)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
fof(f27,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(X1)))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_relat_1)).

fof(f63,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f32,f60])).

fof(f32,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f29])).

% (8310)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
fof(f58,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f31,f55])).

fof(f31,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:57:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.46  % (8301)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.46  % (8304)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.46  % (8314)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.46  % (8306)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.47  % (8303)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.47  % (8307)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.47  % (8304)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f258,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f58,f63,f68,f72,f80,f84,f107,f121,f125,f131,f135,f143,f167,f199,f217,f229,f254,f257])).
% 0.20/0.47  fof(f257,plain,(
% 0.20/0.47    ~spl2_2 | ~spl2_20 | spl2_26 | ~spl2_29 | ~spl2_31),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f256])).
% 0.20/0.47  fof(f256,plain,(
% 0.20/0.47    $false | (~spl2_2 | ~spl2_20 | spl2_26 | ~spl2_29 | ~spl2_31)),
% 0.20/0.47    inference(subsumption_resolution,[],[f62,f255])).
% 0.20/0.47  fof(f255,plain,(
% 0.20/0.47    ~v1_relat_1(sK1) | (~spl2_20 | spl2_26 | ~spl2_29 | ~spl2_31)),
% 0.20/0.47    inference(subsumption_resolution,[],[f230,f253])).
% 0.20/0.47  fof(f253,plain,(
% 0.20/0.47    ( ! [X2,X0] : (r1_tarski(k3_xboole_0(X2,X0),X0)) ) | ~spl2_31),
% 0.20/0.47    inference(avatar_component_clause,[],[f252])).
% 0.20/0.47  fof(f252,plain,(
% 0.20/0.47    spl2_31 <=> ! [X0,X2] : r1_tarski(k3_xboole_0(X2,X0),X0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).
% 0.20/0.47  fof(f230,plain,(
% 0.20/0.47    ~r1_tarski(k3_xboole_0(sK0,sK1),sK1) | ~v1_relat_1(sK1) | (~spl2_20 | spl2_26 | ~spl2_29)),
% 0.20/0.47    inference(subsumption_resolution,[],[f208,f228])).
% 0.20/0.47  fof(f228,plain,(
% 0.20/0.47    ( ! [X0] : (v1_relat_1(k3_xboole_0(sK0,X0))) ) | ~spl2_29),
% 0.20/0.47    inference(avatar_component_clause,[],[f227])).
% 0.20/0.47  fof(f227,plain,(
% 0.20/0.47    spl2_29 <=> ! [X0] : v1_relat_1(k3_xboole_0(sK0,X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).
% 0.20/0.47  fof(f208,plain,(
% 0.20/0.47    ~r1_tarski(k3_xboole_0(sK0,sK1),sK1) | ~v1_relat_1(sK1) | ~v1_relat_1(k3_xboole_0(sK0,sK1)) | (~spl2_20 | spl2_26)),
% 0.20/0.47    inference(resolution,[],[f198,f142])).
% 0.20/0.47  fof(f142,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl2_20),
% 0.20/0.47    inference(avatar_component_clause,[],[f141])).
% 0.20/0.47  fof(f141,plain,(
% 0.20/0.47    spl2_20 <=> ! [X1,X0] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 0.20/0.47  fof(f198,plain,(
% 0.20/0.47    ~r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK1)) | spl2_26),
% 0.20/0.47    inference(avatar_component_clause,[],[f196])).
% 0.20/0.47  fof(f196,plain,(
% 0.20/0.47    spl2_26 <=> r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).
% 0.20/0.47  fof(f62,plain,(
% 0.20/0.47    v1_relat_1(sK1) | ~spl2_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f60])).
% 0.20/0.47  fof(f60,plain,(
% 0.20/0.47    spl2_2 <=> v1_relat_1(sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.47  fof(f254,plain,(
% 0.20/0.47    spl2_31 | ~spl2_12 | ~spl2_15 | ~spl2_16 | ~spl2_17),
% 0.20/0.47    inference(avatar_split_clause,[],[f177,f129,f123,f119,f105,f252])).
% 0.20/0.47  fof(f105,plain,(
% 0.20/0.47    spl2_12 <=> ! [X1,X0] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.20/0.47  fof(f119,plain,(
% 0.20/0.47    spl2_15 <=> ! [X1,X0,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.20/0.47  fof(f123,plain,(
% 0.20/0.47    spl2_16 <=> ! [X1,X0,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.20/0.47  fof(f129,plain,(
% 0.20/0.47    spl2_17 <=> ! [X1,X0,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.20/0.47  fof(f177,plain,(
% 0.20/0.47    ( ! [X2,X0] : (r1_tarski(k3_xboole_0(X2,X0),X0)) ) | (~spl2_12 | ~spl2_15 | ~spl2_16 | ~spl2_17)),
% 0.20/0.47    inference(forward_demodulation,[],[f176,f154])).
% 0.20/0.47  fof(f154,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = k2_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,X2)),k4_xboole_0(k3_xboole_0(X0,X1),X2))) ) | (~spl2_12 | ~spl2_16)),
% 0.20/0.47    inference(superposition,[],[f106,f124])).
% 0.20/0.47  fof(f124,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) ) | ~spl2_16),
% 0.20/0.47    inference(avatar_component_clause,[],[f123])).
% 0.20/0.47  fof(f106,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) ) | ~spl2_12),
% 0.20/0.47    inference(avatar_component_clause,[],[f105])).
% 0.20/0.47  fof(f176,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X2,k3_xboole_0(X0,X1)),k4_xboole_0(k3_xboole_0(X2,X0),X1)),X0)) ) | (~spl2_12 | ~spl2_15 | ~spl2_17)),
% 0.20/0.47    inference(forward_demodulation,[],[f173,f120])).
% 0.20/0.47  fof(f120,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) ) | ~spl2_15),
% 0.20/0.47    inference(avatar_component_clause,[],[f119])).
% 0.20/0.47  fof(f173,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X2,k3_xboole_0(X0,X1)),k3_xboole_0(X2,k4_xboole_0(X0,X1))),X0)) ) | (~spl2_12 | ~spl2_17)),
% 0.20/0.47    inference(superposition,[],[f130,f106])).
% 0.20/0.47  fof(f130,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))) ) | ~spl2_17),
% 0.20/0.47    inference(avatar_component_clause,[],[f129])).
% 0.20/0.47  fof(f229,plain,(
% 0.20/0.47    spl2_29 | ~spl2_1 | ~spl2_7 | ~spl2_22),
% 0.20/0.47    inference(avatar_split_clause,[],[f209,f165,f82,f55,f227])).
% 0.20/0.47  fof(f55,plain,(
% 0.20/0.47    spl2_1 <=> v1_relat_1(sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.47  fof(f82,plain,(
% 0.20/0.47    spl2_7 <=> ! [X1,X0] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.20/0.47  fof(f165,plain,(
% 0.20/0.47    spl2_22 <=> ! [X1,X0] : m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 0.20/0.47  fof(f209,plain,(
% 0.20/0.47    ( ! [X0] : (v1_relat_1(k3_xboole_0(sK0,X0))) ) | (~spl2_1 | ~spl2_7 | ~spl2_22)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f57,f166,f83])).
% 0.20/0.47  fof(f83,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl2_7),
% 0.20/0.47    inference(avatar_component_clause,[],[f82])).
% 0.20/0.47  fof(f166,plain,(
% 0.20/0.47    ( ! [X0,X1] : (m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(X0))) ) | ~spl2_22),
% 0.20/0.47    inference(avatar_component_clause,[],[f165])).
% 0.20/0.47  fof(f57,plain,(
% 0.20/0.47    v1_relat_1(sK0) | ~spl2_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f55])).
% 0.20/0.47  fof(f217,plain,(
% 0.20/0.47    ~spl2_1 | ~spl2_4 | ~spl2_7 | ~spl2_20 | ~spl2_22 | spl2_25),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f216])).
% 0.20/0.47  fof(f216,plain,(
% 0.20/0.47    $false | (~spl2_1 | ~spl2_4 | ~spl2_7 | ~spl2_20 | ~spl2_22 | spl2_25)),
% 0.20/0.47    inference(subsumption_resolution,[],[f204,f209])).
% 0.20/0.47  fof(f204,plain,(
% 0.20/0.47    ~v1_relat_1(k3_xboole_0(sK0,sK1)) | (~spl2_1 | ~spl2_4 | ~spl2_20 | spl2_25)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f57,f71,f194,f142])).
% 0.20/0.47  fof(f194,plain,(
% 0.20/0.47    ~r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK0)) | spl2_25),
% 0.20/0.47    inference(avatar_component_clause,[],[f192])).
% 0.20/0.47  fof(f192,plain,(
% 0.20/0.47    spl2_25 <=> r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).
% 0.20/0.47  fof(f71,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) ) | ~spl2_4),
% 0.20/0.47    inference(avatar_component_clause,[],[f70])).
% 0.20/0.47  fof(f70,plain,(
% 0.20/0.47    spl2_4 <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.47  fof(f199,plain,(
% 0.20/0.47    ~spl2_25 | ~spl2_26 | spl2_3 | ~spl2_18),
% 0.20/0.47    inference(avatar_split_clause,[],[f180,f133,f65,f196,f192])).
% 0.20/0.47  fof(f65,plain,(
% 0.20/0.47    spl2_3 <=> r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.47  fof(f133,plain,(
% 0.20/0.47    spl2_18 <=> ! [X1,X0,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.20/0.47  fof(f180,plain,(
% 0.20/0.47    ~r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK1)) | ~r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK0)) | (spl2_3 | ~spl2_18)),
% 0.20/0.47    inference(resolution,[],[f134,f67])).
% 0.20/0.47  fof(f67,plain,(
% 0.20/0.47    ~r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))) | spl2_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f65])).
% 0.20/0.47  fof(f134,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) ) | ~spl2_18),
% 0.20/0.47    inference(avatar_component_clause,[],[f133])).
% 0.20/0.47  fof(f167,plain,(
% 0.20/0.47    spl2_22 | ~spl2_4 | ~spl2_6),
% 0.20/0.47    inference(avatar_split_clause,[],[f98,f78,f70,f165])).
% 0.20/0.47  fof(f78,plain,(
% 0.20/0.47    spl2_6 <=> ! [X1,X0] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.20/0.47  fof(f98,plain,(
% 0.20/0.47    ( ! [X0,X1] : (m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(X0))) ) | (~spl2_4 | ~spl2_6)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f71,f79])).
% 0.20/0.47  fof(f79,plain,(
% 0.20/0.47    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) ) | ~spl2_6),
% 0.20/0.47    inference(avatar_component_clause,[],[f78])).
% 0.20/0.47  fof(f143,plain,(
% 0.20/0.47    spl2_20),
% 0.20/0.47    inference(avatar_split_clause,[],[f35,f141])).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f23])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(flattening,[],[f22])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f18])).
% 0.20/0.47  fof(f18,axiom,(
% 0.20/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).
% 0.20/0.47  fof(f135,plain,(
% 0.20/0.47    spl2_18),
% 0.20/0.47    inference(avatar_split_clause,[],[f49,f133])).
% 0.20/0.47  fof(f49,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f26])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.47    inference(flattening,[],[f25])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.47    inference(ennf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.20/0.47  fof(f131,plain,(
% 0.20/0.47    spl2_17),
% 0.20/0.47    inference(avatar_split_clause,[],[f48,f129])).
% 0.20/0.47  fof(f48,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).
% 0.20/0.47  fof(f125,plain,(
% 0.20/0.47    spl2_16),
% 0.20/0.47    inference(avatar_split_clause,[],[f47,f123])).
% 0.20/0.47  fof(f47,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).
% 0.20/0.47  fof(f121,plain,(
% 0.20/0.47    spl2_15),
% 0.20/0.47    inference(avatar_split_clause,[],[f46,f119])).
% 0.20/0.47  fof(f46,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 0.20/0.47  fof(f107,plain,(
% 0.20/0.47    spl2_12),
% 0.20/0.47    inference(avatar_split_clause,[],[f42,f105])).
% 0.20/0.47  fof(f42,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 0.20/0.47    inference(cnf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,axiom,(
% 0.20/0.47    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 0.20/0.48  % (8305)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.48  % (8313)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.48  % (8312)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.48  fof(f84,plain,(
% 0.20/0.48    spl2_7),
% 0.20/0.48    inference(avatar_split_clause,[],[f36,f82])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f24])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f17])).
% 0.20/0.48  fof(f17,axiom,(
% 0.20/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.48  fof(f80,plain,(
% 0.20/0.48    spl2_6),
% 0.20/0.48    inference(avatar_split_clause,[],[f44,f78])).
% 0.20/0.48  fof(f44,plain,(
% 0.20/0.48    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f30])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.48    inference(nnf_transformation,[],[f16])).
% 0.20/0.48  fof(f16,axiom,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.48  fof(f72,plain,(
% 0.20/0.48    spl2_4),
% 0.20/0.48    inference(avatar_split_clause,[],[f37,f70])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.20/0.48  fof(f68,plain,(
% 0.20/0.48    ~spl2_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f33,f65])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    ~r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))),
% 0.20/0.48    inference(cnf_transformation,[],[f29])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    (~r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f28,f27])).
% 0.20/0.48  % (8311)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : (~r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k2_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    ? [X1] : (~r1_tarski(k2_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(X1))) & v1_relat_1(X1)) => (~r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))) & v1_relat_1(sK1))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : (~r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f20])).
% 0.20/0.48  fof(f20,negated_conjecture,(
% 0.20/0.48    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))))),
% 0.20/0.48    inference(negated_conjecture,[],[f19])).
% 0.20/0.48  fof(f19,conjecture,(
% 0.20/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_relat_1)).
% 0.20/0.48  fof(f63,plain,(
% 0.20/0.48    spl2_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f32,f60])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    v1_relat_1(sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f29])).
% 0.20/0.48  % (8310)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.48  fof(f58,plain,(
% 0.20/0.48    spl2_1),
% 0.20/0.48    inference(avatar_split_clause,[],[f31,f55])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    v1_relat_1(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f29])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (8304)------------------------------
% 0.20/0.48  % (8304)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (8304)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (8304)Memory used [KB]: 6268
% 0.20/0.48  % (8304)Time elapsed: 0.059 s
% 0.20/0.48  % (8304)------------------------------
% 0.20/0.48  % (8304)------------------------------
% 0.20/0.48  % (8298)Success in time 0.119 s
%------------------------------------------------------------------------------
