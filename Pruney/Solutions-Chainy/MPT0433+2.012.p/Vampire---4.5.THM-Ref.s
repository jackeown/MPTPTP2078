%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:53 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 176 expanded)
%              Number of leaves         :   31 (  84 expanded)
%              Depth                    :    6
%              Number of atoms          :  295 ( 488 expanded)
%              Number of equality atoms :   18 (  27 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f505,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f50,f55,f59,f63,f67,f75,f79,f95,f101,f122,f134,f189,f219,f230,f242,f246,f325,f361,f470,f503])).

fof(f503,plain,
    ( ~ spl2_2
    | ~ spl2_13
    | ~ spl2_14
    | spl2_25
    | ~ spl2_34
    | ~ spl2_39 ),
    inference(avatar_contradiction_clause,[],[f502])).

fof(f502,plain,
    ( $false
    | ~ spl2_2
    | ~ spl2_13
    | ~ spl2_14
    | spl2_25
    | ~ spl2_34
    | ~ spl2_39 ),
    inference(subsumption_resolution,[],[f188,f501])).

fof(f501,plain,
    ( ! [X0] : r1_tarski(k1_relat_1(k3_xboole_0(X0,sK1)),k1_relat_1(sK1))
    | ~ spl2_2
    | ~ spl2_13
    | ~ spl2_14
    | ~ spl2_34
    | ~ spl2_39 ),
    inference(forward_demodulation,[],[f494,f198])).

fof(f198,plain,
    ( ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),X1) = X1
    | ~ spl2_13
    | ~ spl2_14 ),
    inference(unit_resulting_resolution,[],[f100,f94])).

fof(f94,plain,
    ( ! [X0,X1] :
        ( k2_xboole_0(X0,X1) = X1
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl2_13
  <=> ! [X1,X0] :
        ( k2_xboole_0(X0,X1) = X1
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f100,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0)
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl2_14
  <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X1,X0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f494,plain,
    ( ! [X0] : r1_tarski(k1_relat_1(k3_xboole_0(X0,sK1)),k1_relat_1(k2_xboole_0(k3_xboole_0(X0,sK1),sK1)))
    | ~ spl2_2
    | ~ spl2_34
    | ~ spl2_39 ),
    inference(unit_resulting_resolution,[],[f49,f469,f324])).

fof(f324,plain,
    ( ! [X2,X3] :
        ( r1_tarski(k1_relat_1(X2),k1_relat_1(k2_xboole_0(X2,X3)))
        | ~ v1_relat_1(X3)
        | ~ v1_relat_1(X2) )
    | ~ spl2_34 ),
    inference(avatar_component_clause,[],[f323])).

fof(f323,plain,
    ( spl2_34
  <=> ! [X3,X2] :
        ( r1_tarski(k1_relat_1(X2),k1_relat_1(k2_xboole_0(X2,X3)))
        | ~ v1_relat_1(X3)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).

fof(f469,plain,
    ( ! [X0] : v1_relat_1(k3_xboole_0(X0,sK1))
    | ~ spl2_39 ),
    inference(avatar_component_clause,[],[f468])).

fof(f468,plain,
    ( spl2_39
  <=> ! [X0] : v1_relat_1(k3_xboole_0(X0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_39])])).

fof(f49,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl2_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f188,plain,
    ( ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK1))
    | spl2_25 ),
    inference(avatar_component_clause,[],[f186])).

fof(f186,plain,
    ( spl2_25
  <=> r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).

fof(f470,plain,
    ( spl2_39
    | ~ spl2_2
    | ~ spl2_14
    | ~ spl2_28 ),
    inference(avatar_split_clause,[],[f234,f228,f99,f47,f468])).

fof(f228,plain,
    ( spl2_28
  <=> ! [X1,X0] :
        ( v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).

fof(f234,plain,
    ( ! [X0] : v1_relat_1(k3_xboole_0(X0,sK1))
    | ~ spl2_2
    | ~ spl2_14
    | ~ spl2_28 ),
    inference(unit_resulting_resolution,[],[f49,f100,f229])).

fof(f229,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X1)
        | v1_relat_1(X0) )
    | ~ spl2_28 ),
    inference(avatar_component_clause,[],[f228])).

fof(f361,plain,
    ( ~ spl2_1
    | spl2_24
    | ~ spl2_29
    | ~ spl2_30
    | ~ spl2_34 ),
    inference(avatar_contradiction_clause,[],[f360])).

fof(f360,plain,
    ( $false
    | ~ spl2_1
    | spl2_24
    | ~ spl2_29
    | ~ spl2_30
    | ~ spl2_34 ),
    inference(subsumption_resolution,[],[f184,f359])).

fof(f359,plain,
    ( ! [X0] : r1_tarski(k1_relat_1(k3_xboole_0(sK0,X0)),k1_relat_1(sK0))
    | ~ spl2_1
    | ~ spl2_29
    | ~ spl2_30
    | ~ spl2_34 ),
    inference(forward_demodulation,[],[f341,f241])).

fof(f241,plain,
    ( ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0
    | ~ spl2_29 ),
    inference(avatar_component_clause,[],[f240])).

fof(f240,plain,
    ( spl2_29
  <=> ! [X1,X0] : k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).

fof(f341,plain,
    ( ! [X0] : r1_tarski(k1_relat_1(k3_xboole_0(sK0,X0)),k1_relat_1(k2_xboole_0(k3_xboole_0(sK0,X0),sK0)))
    | ~ spl2_1
    | ~ spl2_30
    | ~ spl2_34 ),
    inference(unit_resulting_resolution,[],[f245,f44,f324])).

fof(f44,plain,
    ( v1_relat_1(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl2_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f245,plain,
    ( ! [X0] : v1_relat_1(k3_xboole_0(sK0,X0))
    | ~ spl2_30 ),
    inference(avatar_component_clause,[],[f244])).

fof(f244,plain,
    ( spl2_30
  <=> ! [X0] : v1_relat_1(k3_xboole_0(sK0,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).

fof(f184,plain,
    ( ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0))
    | spl2_24 ),
    inference(avatar_component_clause,[],[f182])).

fof(f182,plain,
    ( spl2_24
  <=> r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f325,plain,
    ( spl2_34
    | ~ spl2_4
    | ~ spl2_18 ),
    inference(avatar_split_clause,[],[f141,f132,f57,f323])).

fof(f57,plain,
    ( spl2_4
  <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f132,plain,
    ( spl2_18
  <=> ! [X1,X0] :
        ( k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f141,plain,
    ( ! [X2,X3] :
        ( r1_tarski(k1_relat_1(X2),k1_relat_1(k2_xboole_0(X2,X3)))
        | ~ v1_relat_1(X3)
        | ~ v1_relat_1(X2) )
    | ~ spl2_4
    | ~ spl2_18 ),
    inference(superposition,[],[f58,f133])).

fof(f133,plain,
    ( ! [X0,X1] :
        ( k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f132])).

fof(f58,plain,
    ( ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f57])).

fof(f246,plain,
    ( spl2_30
    | ~ spl2_1
    | ~ spl2_9
    | ~ spl2_27 ),
    inference(avatar_split_clause,[],[f220,f217,f77,f42,f244])).

fof(f77,plain,
    ( spl2_9
  <=> ! [X1,X0] :
        ( v1_relat_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f217,plain,
    ( spl2_27
  <=> ! [X1,X0] : m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).

fof(f220,plain,
    ( ! [X0] : v1_relat_1(k3_xboole_0(sK0,X0))
    | ~ spl2_1
    | ~ spl2_9
    | ~ spl2_27 ),
    inference(unit_resulting_resolution,[],[f44,f218,f78])).

fof(f78,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f77])).

fof(f218,plain,
    ( ! [X0,X1] : m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(X0))
    | ~ spl2_27 ),
    inference(avatar_component_clause,[],[f217])).

fof(f242,plain,
    ( spl2_29
    | ~ spl2_5
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f108,f93,f61,f240])).

fof(f61,plain,
    ( spl2_5
  <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f108,plain,
    ( ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0
    | ~ spl2_5
    | ~ spl2_13 ),
    inference(unit_resulting_resolution,[],[f62,f94])).

fof(f62,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f61])).

fof(f230,plain,
    ( spl2_28
    | ~ spl2_8
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f106,f77,f73,f228])).

fof(f73,plain,
    ( spl2_8
  <=> ! [X1,X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f106,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_8
    | ~ spl2_9 ),
    inference(resolution,[],[f78,f74])).

fof(f74,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f73])).

fof(f219,plain,
    ( spl2_27
    | ~ spl2_5
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f104,f73,f61,f217])).

fof(f104,plain,
    ( ! [X0,X1] : m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(X0))
    | ~ spl2_5
    | ~ spl2_8 ),
    inference(unit_resulting_resolution,[],[f62,f74])).

fof(f189,plain,
    ( ~ spl2_24
    | ~ spl2_25
    | spl2_3
    | ~ spl2_17 ),
    inference(avatar_split_clause,[],[f127,f120,f52,f186,f182])).

fof(f52,plain,
    ( spl2_3
  <=> r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f120,plain,
    ( spl2_17
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,k3_xboole_0(X1,X2))
        | ~ r1_tarski(X0,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f127,plain,
    ( ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK1))
    | ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0))
    | spl2_3
    | ~ spl2_17 ),
    inference(resolution,[],[f121,f54])).

fof(f54,plain,
    ( ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f52])).

fof(f121,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(X0,k3_xboole_0(X1,X2))
        | ~ r1_tarski(X0,X2)
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f120])).

fof(f134,plain,(
    spl2_18 ),
    inference(avatar_split_clause,[],[f28,f132])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relat_1)).

fof(f122,plain,(
    spl2_17 ),
    inference(avatar_split_clause,[],[f40,f120])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
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

fof(f101,plain,
    ( spl2_14
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f96,f65,f61,f99])).

fof(f65,plain,
    ( spl2_6
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f96,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0)
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(superposition,[],[f62,f66])).

fof(f66,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f65])).

fof(f95,plain,(
    spl2_13 ),
    inference(avatar_split_clause,[],[f36,f93])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f79,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f29,f77])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f75,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f38,f73])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f67,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f32,f65])).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f63,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f31,f61])).

fof(f31,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f59,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f30,f57])).

fof(f30,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f55,plain,(
    ~ spl2_3 ),
    inference(avatar_split_clause,[],[f27,f52])).

fof(f27,plain,(
    ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f22,f21])).

fof(f21,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(X1)))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relat_1)).

fof(f50,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f26,f47])).

fof(f26,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f45,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f25,f42])).

fof(f25,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:19:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.41  % (12948)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.43  % (12934)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.45  % (12938)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (12950)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.47  % (12944)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (12940)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.48  % (12943)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.48  % (12938)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f505,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f45,f50,f55,f59,f63,f67,f75,f79,f95,f101,f122,f134,f189,f219,f230,f242,f246,f325,f361,f470,f503])).
% 0.21/0.48  fof(f503,plain,(
% 0.21/0.48    ~spl2_2 | ~spl2_13 | ~spl2_14 | spl2_25 | ~spl2_34 | ~spl2_39),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f502])).
% 0.21/0.48  fof(f502,plain,(
% 0.21/0.48    $false | (~spl2_2 | ~spl2_13 | ~spl2_14 | spl2_25 | ~spl2_34 | ~spl2_39)),
% 0.21/0.48    inference(subsumption_resolution,[],[f188,f501])).
% 0.21/0.48  fof(f501,plain,(
% 0.21/0.48    ( ! [X0] : (r1_tarski(k1_relat_1(k3_xboole_0(X0,sK1)),k1_relat_1(sK1))) ) | (~spl2_2 | ~spl2_13 | ~spl2_14 | ~spl2_34 | ~spl2_39)),
% 0.21/0.48    inference(forward_demodulation,[],[f494,f198])).
% 0.21/0.48  fof(f198,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),X1) = X1) ) | (~spl2_13 | ~spl2_14)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f100,f94])).
% 0.21/0.48  fof(f94,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) ) | ~spl2_13),
% 0.21/0.48    inference(avatar_component_clause,[],[f93])).
% 0.21/0.48  fof(f93,plain,(
% 0.21/0.48    spl2_13 <=> ! [X1,X0] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.21/0.48  fof(f100,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) ) | ~spl2_14),
% 0.21/0.48    inference(avatar_component_clause,[],[f99])).
% 0.21/0.48  fof(f99,plain,(
% 0.21/0.48    spl2_14 <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X1,X0),X0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.21/0.48  fof(f494,plain,(
% 0.21/0.48    ( ! [X0] : (r1_tarski(k1_relat_1(k3_xboole_0(X0,sK1)),k1_relat_1(k2_xboole_0(k3_xboole_0(X0,sK1),sK1)))) ) | (~spl2_2 | ~spl2_34 | ~spl2_39)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f49,f469,f324])).
% 0.21/0.48  fof(f324,plain,(
% 0.21/0.48    ( ! [X2,X3] : (r1_tarski(k1_relat_1(X2),k1_relat_1(k2_xboole_0(X2,X3))) | ~v1_relat_1(X3) | ~v1_relat_1(X2)) ) | ~spl2_34),
% 0.21/0.48    inference(avatar_component_clause,[],[f323])).
% 0.21/0.48  fof(f323,plain,(
% 0.21/0.48    spl2_34 <=> ! [X3,X2] : (r1_tarski(k1_relat_1(X2),k1_relat_1(k2_xboole_0(X2,X3))) | ~v1_relat_1(X3) | ~v1_relat_1(X2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).
% 0.21/0.48  fof(f469,plain,(
% 0.21/0.48    ( ! [X0] : (v1_relat_1(k3_xboole_0(X0,sK1))) ) | ~spl2_39),
% 0.21/0.48    inference(avatar_component_clause,[],[f468])).
% 0.21/0.48  fof(f468,plain,(
% 0.21/0.48    spl2_39 <=> ! [X0] : v1_relat_1(k3_xboole_0(X0,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_39])])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    v1_relat_1(sK1) | ~spl2_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f47])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    spl2_2 <=> v1_relat_1(sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.48  fof(f188,plain,(
% 0.21/0.48    ~r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK1)) | spl2_25),
% 0.21/0.48    inference(avatar_component_clause,[],[f186])).
% 0.21/0.48  fof(f186,plain,(
% 0.21/0.48    spl2_25 <=> r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).
% 0.21/0.48  fof(f470,plain,(
% 0.21/0.48    spl2_39 | ~spl2_2 | ~spl2_14 | ~spl2_28),
% 0.21/0.48    inference(avatar_split_clause,[],[f234,f228,f99,f47,f468])).
% 0.21/0.48  fof(f228,plain,(
% 0.21/0.48    spl2_28 <=> ! [X1,X0] : (v1_relat_1(X0) | ~v1_relat_1(X1) | ~r1_tarski(X0,X1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).
% 0.21/0.48  fof(f234,plain,(
% 0.21/0.48    ( ! [X0] : (v1_relat_1(k3_xboole_0(X0,sK1))) ) | (~spl2_2 | ~spl2_14 | ~spl2_28)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f49,f100,f229])).
% 0.21/0.48  fof(f229,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~v1_relat_1(X1) | v1_relat_1(X0)) ) | ~spl2_28),
% 0.21/0.48    inference(avatar_component_clause,[],[f228])).
% 0.21/0.48  fof(f361,plain,(
% 0.21/0.48    ~spl2_1 | spl2_24 | ~spl2_29 | ~spl2_30 | ~spl2_34),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f360])).
% 0.21/0.48  fof(f360,plain,(
% 0.21/0.48    $false | (~spl2_1 | spl2_24 | ~spl2_29 | ~spl2_30 | ~spl2_34)),
% 0.21/0.48    inference(subsumption_resolution,[],[f184,f359])).
% 0.21/0.48  fof(f359,plain,(
% 0.21/0.48    ( ! [X0] : (r1_tarski(k1_relat_1(k3_xboole_0(sK0,X0)),k1_relat_1(sK0))) ) | (~spl2_1 | ~spl2_29 | ~spl2_30 | ~spl2_34)),
% 0.21/0.48    inference(forward_demodulation,[],[f341,f241])).
% 0.21/0.48  fof(f241,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0) ) | ~spl2_29),
% 0.21/0.48    inference(avatar_component_clause,[],[f240])).
% 0.21/0.48  fof(f240,plain,(
% 0.21/0.48    spl2_29 <=> ! [X1,X0] : k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).
% 0.21/0.48  fof(f341,plain,(
% 0.21/0.48    ( ! [X0] : (r1_tarski(k1_relat_1(k3_xboole_0(sK0,X0)),k1_relat_1(k2_xboole_0(k3_xboole_0(sK0,X0),sK0)))) ) | (~spl2_1 | ~spl2_30 | ~spl2_34)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f245,f44,f324])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    v1_relat_1(sK0) | ~spl2_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    spl2_1 <=> v1_relat_1(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.48  fof(f245,plain,(
% 0.21/0.48    ( ! [X0] : (v1_relat_1(k3_xboole_0(sK0,X0))) ) | ~spl2_30),
% 0.21/0.48    inference(avatar_component_clause,[],[f244])).
% 0.21/0.48  fof(f244,plain,(
% 0.21/0.48    spl2_30 <=> ! [X0] : v1_relat_1(k3_xboole_0(sK0,X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).
% 0.21/0.48  fof(f184,plain,(
% 0.21/0.48    ~r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0)) | spl2_24),
% 0.21/0.48    inference(avatar_component_clause,[],[f182])).
% 0.21/0.48  fof(f182,plain,(
% 0.21/0.48    spl2_24 <=> r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 0.21/0.48  fof(f325,plain,(
% 0.21/0.48    spl2_34 | ~spl2_4 | ~spl2_18),
% 0.21/0.48    inference(avatar_split_clause,[],[f141,f132,f57,f323])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    spl2_4 <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.48  fof(f132,plain,(
% 0.21/0.48    spl2_18 <=> ! [X1,X0] : (k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.21/0.48  fof(f141,plain,(
% 0.21/0.48    ( ! [X2,X3] : (r1_tarski(k1_relat_1(X2),k1_relat_1(k2_xboole_0(X2,X3))) | ~v1_relat_1(X3) | ~v1_relat_1(X2)) ) | (~spl2_4 | ~spl2_18)),
% 0.21/0.48    inference(superposition,[],[f58,f133])).
% 0.21/0.48  fof(f133,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl2_18),
% 0.21/0.48    inference(avatar_component_clause,[],[f132])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) ) | ~spl2_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f57])).
% 0.21/0.48  fof(f246,plain,(
% 0.21/0.48    spl2_30 | ~spl2_1 | ~spl2_9 | ~spl2_27),
% 0.21/0.48    inference(avatar_split_clause,[],[f220,f217,f77,f42,f244])).
% 0.21/0.48  fof(f77,plain,(
% 0.21/0.48    spl2_9 <=> ! [X1,X0] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.48  fof(f217,plain,(
% 0.21/0.48    spl2_27 <=> ! [X1,X0] : m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).
% 0.21/0.48  fof(f220,plain,(
% 0.21/0.48    ( ! [X0] : (v1_relat_1(k3_xboole_0(sK0,X0))) ) | (~spl2_1 | ~spl2_9 | ~spl2_27)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f44,f218,f78])).
% 0.21/0.48  fof(f78,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl2_9),
% 0.21/0.48    inference(avatar_component_clause,[],[f77])).
% 0.21/0.48  fof(f218,plain,(
% 0.21/0.48    ( ! [X0,X1] : (m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(X0))) ) | ~spl2_27),
% 0.21/0.48    inference(avatar_component_clause,[],[f217])).
% 0.21/0.48  fof(f242,plain,(
% 0.21/0.48    spl2_29 | ~spl2_5 | ~spl2_13),
% 0.21/0.48    inference(avatar_split_clause,[],[f108,f93,f61,f240])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    spl2_5 <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.48  fof(f108,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0) ) | (~spl2_5 | ~spl2_13)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f62,f94])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) ) | ~spl2_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f61])).
% 0.21/0.48  fof(f230,plain,(
% 0.21/0.48    spl2_28 | ~spl2_8 | ~spl2_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f106,f77,f73,f228])).
% 0.21/0.48  fof(f73,plain,(
% 0.21/0.48    spl2_8 <=> ! [X1,X0] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.48  fof(f106,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v1_relat_1(X0) | ~v1_relat_1(X1) | ~r1_tarski(X0,X1)) ) | (~spl2_8 | ~spl2_9)),
% 0.21/0.48    inference(resolution,[],[f78,f74])).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) ) | ~spl2_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f73])).
% 0.21/0.48  fof(f219,plain,(
% 0.21/0.48    spl2_27 | ~spl2_5 | ~spl2_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f104,f73,f61,f217])).
% 0.21/0.48  fof(f104,plain,(
% 0.21/0.48    ( ! [X0,X1] : (m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(X0))) ) | (~spl2_5 | ~spl2_8)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f62,f74])).
% 0.21/0.48  fof(f189,plain,(
% 0.21/0.48    ~spl2_24 | ~spl2_25 | spl2_3 | ~spl2_17),
% 0.21/0.48    inference(avatar_split_clause,[],[f127,f120,f52,f186,f182])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    spl2_3 <=> r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.48  fof(f120,plain,(
% 0.21/0.48    spl2_17 <=> ! [X1,X0,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.21/0.48  fof(f127,plain,(
% 0.21/0.48    ~r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK1)) | ~r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0)) | (spl2_3 | ~spl2_17)),
% 0.21/0.48    inference(resolution,[],[f121,f54])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    ~r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))) | spl2_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f52])).
% 0.21/0.48  fof(f121,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) ) | ~spl2_17),
% 0.21/0.48    inference(avatar_component_clause,[],[f120])).
% 0.21/0.48  fof(f134,plain,(
% 0.21/0.48    spl2_18),
% 0.21/0.48    inference(avatar_split_clause,[],[f28,f132])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,axiom,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relat_1)).
% 0.21/0.48  fof(f122,plain,(
% 0.21/0.48    spl2_17),
% 0.21/0.48    inference(avatar_split_clause,[],[f40,f120])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.48    inference(flattening,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.21/0.48  fof(f101,plain,(
% 0.21/0.48    spl2_14 | ~spl2_5 | ~spl2_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f96,f65,f61,f99])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    spl2_6 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.48  fof(f96,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) ) | (~spl2_5 | ~spl2_6)),
% 0.21/0.48    inference(superposition,[],[f62,f66])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl2_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f65])).
% 0.21/0.48  fof(f95,plain,(
% 0.21/0.48    spl2_13),
% 0.21/0.48    inference(avatar_split_clause,[],[f36,f93])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.48  fof(f79,plain,(
% 0.21/0.48    spl2_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f29,f77])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,axiom,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.48  fof(f75,plain,(
% 0.21/0.48    spl2_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f38,f73])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.48    inference(nnf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    spl2_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f32,f65])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    spl2_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f31,f61])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    spl2_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f30,f57])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    ~spl2_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f27,f52])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ~r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    (~r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f22,f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (~r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k1_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ? [X1] : (~r1_tarski(k1_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(X1))) & v1_relat_1(X1)) => (~r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))) & v1_relat_1(sK1))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (~r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,negated_conjecture,(
% 0.21/0.48    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))))),
% 0.21/0.48    inference(negated_conjecture,[],[f13])).
% 0.21/0.48  fof(f13,conjecture,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relat_1)).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    spl2_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f26,f47])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    v1_relat_1(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    spl2_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f25,f42])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    v1_relat_1(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (12938)------------------------------
% 0.21/0.48  % (12938)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (12938)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (12938)Memory used [KB]: 6524
% 0.21/0.48  % (12938)Time elapsed: 0.073 s
% 0.21/0.48  % (12938)------------------------------
% 0.21/0.48  % (12938)------------------------------
% 0.21/0.48  % (12942)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.48  % (12932)Success in time 0.125 s
%------------------------------------------------------------------------------
