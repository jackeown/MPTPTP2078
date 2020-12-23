%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:51 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 212 expanded)
%              Number of leaves         :   31 ( 100 expanded)
%              Depth                    :    7
%              Number of atoms          :  353 ( 762 expanded)
%              Number of equality atoms :    9 (  16 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f485,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f60,f65,f70,f75,f80,f88,f92,f96,f124,f128,f132,f153,f157,f161,f184,f200,f308,f314,f358,f372,f476,f484])).

fof(f484,plain,
    ( spl3_6
    | ~ spl3_17
    | spl3_25
    | ~ spl3_34
    | ~ spl3_37
    | ~ spl3_39
    | ~ spl3_45 ),
    inference(avatar_contradiction_clause,[],[f483])).

fof(f483,plain,
    ( $false
    | spl3_6
    | ~ spl3_17
    | spl3_25
    | ~ spl3_34
    | ~ spl3_37
    | ~ spl3_39
    | ~ spl3_45 ),
    inference(subsumption_resolution,[],[f361,f477])).

fof(f477,plain,
    ( ~ r2_hidden(sK0,k2_xboole_0(sK1,sK2))
    | spl3_25
    | ~ spl3_39
    | ~ spl3_45 ),
    inference(unit_resulting_resolution,[],[f199,f475,f371])).

fof(f371,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,k2_xboole_0(X2,X1))
        | r1_tarski(k1_tarski(X0),X2)
        | ~ r1_xboole_0(k1_tarski(X0),X1) )
    | ~ spl3_39 ),
    inference(avatar_component_clause,[],[f370])).

fof(f370,plain,
    ( spl3_39
  <=> ! [X1,X0,X2] :
        ( ~ r1_xboole_0(k1_tarski(X0),X1)
        | r1_tarski(k1_tarski(X0),X2)
        | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f475,plain,
    ( r1_xboole_0(k1_tarski(sK0),sK2)
    | ~ spl3_45 ),
    inference(avatar_component_clause,[],[f473])).

fof(f473,plain,
    ( spl3_45
  <=> r1_xboole_0(k1_tarski(sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).

fof(f199,plain,
    ( ~ r1_tarski(k1_tarski(sK0),sK1)
    | spl3_25 ),
    inference(avatar_component_clause,[],[f197])).

fof(f197,plain,
    ( spl3_25
  <=> r1_tarski(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f361,plain,
    ( r2_hidden(sK0,k2_xboole_0(sK1,sK2))
    | spl3_6
    | ~ spl3_17
    | ~ spl3_34
    | ~ spl3_37 ),
    inference(subsumption_resolution,[],[f339,f359])).

fof(f359,plain,
    ( ~ v3_setfam_1(k2_xboole_0(sK1,sK2),sK0)
    | spl3_6
    | ~ spl3_37 ),
    inference(superposition,[],[f79,f357])).

fof(f357,plain,
    ( k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2)
    | ~ spl3_37 ),
    inference(avatar_component_clause,[],[f355])).

fof(f355,plain,
    ( spl3_37
  <=> k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f79,plain,
    ( ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2),sK0)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl3_6
  <=> v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f339,plain,
    ( r2_hidden(sK0,k2_xboole_0(sK1,sK2))
    | v3_setfam_1(k2_xboole_0(sK1,sK2),sK0)
    | ~ spl3_17
    | ~ spl3_34 ),
    inference(resolution,[],[f313,f127])).

fof(f127,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | r2_hidden(X0,X1)
        | v3_setfam_1(X1,X0) )
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl3_17
  <=> ! [X1,X0] :
        ( v3_setfam_1(X1,X0)
        | r2_hidden(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f313,plain,
    ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_34 ),
    inference(avatar_component_clause,[],[f311])).

fof(f311,plain,
    ( spl3_34
  <=> m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f476,plain,
    ( spl3_45
    | ~ spl3_8
    | spl3_23 ),
    inference(avatar_split_clause,[],[f189,f181,f86,f473])).

fof(f86,plain,
    ( spl3_8
  <=> ! [X1,X0] :
        ( r1_xboole_0(k1_tarski(X0),X1)
        | r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f181,plain,
    ( spl3_23
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f189,plain,
    ( r1_xboole_0(k1_tarski(sK0),sK2)
    | ~ spl3_8
    | spl3_23 ),
    inference(unit_resulting_resolution,[],[f183,f87])).

fof(f87,plain,
    ( ! [X0,X1] :
        ( r1_xboole_0(k1_tarski(X0),X1)
        | r2_hidden(X0,X1) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f86])).

fof(f183,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl3_23 ),
    inference(avatar_component_clause,[],[f181])).

fof(f372,plain,
    ( spl3_39
    | ~ spl3_10
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f143,f130,f94,f370])).

fof(f94,plain,
    ( spl3_10
  <=> ! [X1,X0] :
        ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f130,plain,
    ( spl3_18
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,X1)
        | ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f143,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(k1_tarski(X0),X1)
        | r1_tarski(k1_tarski(X0),X2)
        | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) )
    | ~ spl3_10
    | ~ spl3_18 ),
    inference(resolution,[],[f131,f95])).

fof(f95,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f94])).

fof(f131,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
        | ~ r1_xboole_0(X0,X2)
        | r1_tarski(X0,X1) )
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f130])).

fof(f358,plain,
    ( spl3_37
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f170,f159,f72,f67,f355])).

fof(f67,plain,
    ( spl3_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f72,plain,
    ( spl3_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f159,plain,
    ( spl3_22
  <=> ! [X1,X0,X2] :
        ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f170,plain,
    ( k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2)
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_22 ),
    inference(unit_resulting_resolution,[],[f69,f74,f160])).

fof(f160,plain,
    ( ! [X2,X0,X1] :
        ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f159])).

fof(f74,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f72])).

fof(f69,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f67])).

fof(f314,plain,
    ( spl3_34
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_22
    | ~ spl3_33 ),
    inference(avatar_split_clause,[],[f309,f305,f159,f72,f67,f311])).

fof(f305,plain,
    ( spl3_33
  <=> m1_subset_1(k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f309,plain,
    ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_22
    | ~ spl3_33 ),
    inference(forward_demodulation,[],[f307,f170])).

fof(f307,plain,
    ( m1_subset_1(k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f305])).

fof(f308,plain,
    ( spl3_33
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f164,f155,f72,f67,f305])).

fof(f155,plain,
    ( spl3_21
  <=> ! [X1,X0,X2] :
        ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f164,plain,
    ( m1_subset_1(k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_21 ),
    inference(unit_resulting_resolution,[],[f69,f74,f156])).

fof(f156,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f155])).

fof(f200,plain,
    ( ~ spl3_25
    | ~ spl3_9
    | spl3_20 ),
    inference(avatar_split_clause,[],[f178,f150,f90,f197])).

fof(f90,plain,
    ( spl3_9
  <=> ! [X1,X0] :
        ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f150,plain,
    ( spl3_20
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f178,plain,
    ( ~ r1_tarski(k1_tarski(sK0),sK1)
    | ~ spl3_9
    | spl3_20 ),
    inference(unit_resulting_resolution,[],[f152,f91])).

fof(f91,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k1_tarski(X0),X1)
        | r2_hidden(X0,X1) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f90])).

fof(f152,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl3_20 ),
    inference(avatar_component_clause,[],[f150])).

fof(f184,plain,
    ( ~ spl3_23
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f138,f122,f72,f62,f181])).

fof(f62,plain,
    ( spl3_3
  <=> v3_setfam_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f122,plain,
    ( spl3_16
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,X1)
        | ~ v3_setfam_1(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f138,plain,
    ( ~ r2_hidden(sK0,sK2)
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_16 ),
    inference(unit_resulting_resolution,[],[f64,f74,f123])).

fof(f123,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | ~ v3_setfam_1(X1,X0)
        | ~ r2_hidden(X0,X1) )
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f122])).

fof(f64,plain,
    ( v3_setfam_1(sK2,sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f62])).

fof(f161,plain,(
    spl3_22 ),
    inference(avatar_split_clause,[],[f46,f159])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f157,plain,(
    spl3_21 ),
    inference(avatar_split_clause,[],[f45,f155])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f153,plain,
    ( ~ spl3_20
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f137,f122,f67,f57,f150])).

fof(f57,plain,
    ( spl3_2
  <=> v3_setfam_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f137,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_16 ),
    inference(unit_resulting_resolution,[],[f59,f69,f123])).

fof(f59,plain,
    ( v3_setfam_1(sK1,sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f57])).

fof(f132,plain,(
    spl3_18 ),
    inference(avatar_split_clause,[],[f47,f130])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

fof(f128,plain,(
    spl3_17 ),
    inference(avatar_split_clause,[],[f42,f126])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v3_setfam_1(X1,X0)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ( v3_setfam_1(X1,X0)
          | r2_hidden(X0,X1) )
        & ( ~ r2_hidden(X0,X1)
          | ~ v3_setfam_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( v3_setfam_1(X1,X0)
      <=> ~ r2_hidden(X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( v3_setfam_1(X1,X0)
      <=> ~ r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_setfam_1)).

fof(f124,plain,(
    spl3_16 ),
    inference(avatar_split_clause,[],[f41,f122])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v3_setfam_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f96,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f44,f94])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f92,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f43,f90])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f88,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f40,f86])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f80,plain,(
    ~ spl3_6 ),
    inference(avatar_split_clause,[],[f36,f77])).

fof(f36,plain,(
    ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2),sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    & v3_setfam_1(sK2,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    & v3_setfam_1(sK1,sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f25,f24,f23])).

fof(f23,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0)
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
                & v3_setfam_1(X2,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
            & v3_setfam_1(X1,X0) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK0),X1,X2),sK0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
              & v3_setfam_1(X2,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
          & v3_setfam_1(X1,sK0) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK0),X1,X2),sK0)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
            & v3_setfam_1(X2,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
        & v3_setfam_1(X1,sK0) )
   => ( ? [X2] :
          ( ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK0),sK1,X2),sK0)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
          & v3_setfam_1(X2,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
      & v3_setfam_1(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X2] :
        ( ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK0),sK1,X2),sK0)
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
        & v3_setfam_1(X2,sK0) )
   => ( ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2),sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
      & v3_setfam_1(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
              & v3_setfam_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
          & v3_setfam_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
              & v3_setfam_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
          & v3_setfam_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
              & v3_setfam_1(X1,X0) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
                  & v3_setfam_1(X2,X0) )
               => v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
            & v3_setfam_1(X1,X0) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
                & v3_setfam_1(X2,X0) )
             => v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_setfam_1)).

fof(f75,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f35,f72])).

fof(f35,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f70,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f33,f67])).

fof(f33,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f65,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f34,f62])).

fof(f34,plain,(
    v3_setfam_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f60,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f32,f57])).

fof(f32,plain,(
    v3_setfam_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:21:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.47  % (20692)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.48  % (20690)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.48  % (20693)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.48  % (20692)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (20697)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.48  % (20695)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.49  % (20689)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.49  % (20691)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.49  % (20700)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f485,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f60,f65,f70,f75,f80,f88,f92,f96,f124,f128,f132,f153,f157,f161,f184,f200,f308,f314,f358,f372,f476,f484])).
% 0.21/0.49  fof(f484,plain,(
% 0.21/0.49    spl3_6 | ~spl3_17 | spl3_25 | ~spl3_34 | ~spl3_37 | ~spl3_39 | ~spl3_45),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f483])).
% 0.21/0.49  fof(f483,plain,(
% 0.21/0.49    $false | (spl3_6 | ~spl3_17 | spl3_25 | ~spl3_34 | ~spl3_37 | ~spl3_39 | ~spl3_45)),
% 0.21/0.49    inference(subsumption_resolution,[],[f361,f477])).
% 0.21/0.49  fof(f477,plain,(
% 0.21/0.49    ~r2_hidden(sK0,k2_xboole_0(sK1,sK2)) | (spl3_25 | ~spl3_39 | ~spl3_45)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f199,f475,f371])).
% 0.21/0.49  fof(f371,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_xboole_0(X2,X1)) | r1_tarski(k1_tarski(X0),X2) | ~r1_xboole_0(k1_tarski(X0),X1)) ) | ~spl3_39),
% 0.21/0.49    inference(avatar_component_clause,[],[f370])).
% 0.21/0.49  fof(f370,plain,(
% 0.21/0.49    spl3_39 <=> ! [X1,X0,X2] : (~r1_xboole_0(k1_tarski(X0),X1) | r1_tarski(k1_tarski(X0),X2) | ~r2_hidden(X0,k2_xboole_0(X2,X1)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 0.21/0.49  fof(f475,plain,(
% 0.21/0.49    r1_xboole_0(k1_tarski(sK0),sK2) | ~spl3_45),
% 0.21/0.49    inference(avatar_component_clause,[],[f473])).
% 0.21/0.49  fof(f473,plain,(
% 0.21/0.49    spl3_45 <=> r1_xboole_0(k1_tarski(sK0),sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).
% 0.21/0.49  fof(f199,plain,(
% 0.21/0.49    ~r1_tarski(k1_tarski(sK0),sK1) | spl3_25),
% 0.21/0.49    inference(avatar_component_clause,[],[f197])).
% 0.21/0.49  fof(f197,plain,(
% 0.21/0.49    spl3_25 <=> r1_tarski(k1_tarski(sK0),sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.21/0.49  fof(f361,plain,(
% 0.21/0.49    r2_hidden(sK0,k2_xboole_0(sK1,sK2)) | (spl3_6 | ~spl3_17 | ~spl3_34 | ~spl3_37)),
% 0.21/0.49    inference(subsumption_resolution,[],[f339,f359])).
% 0.21/0.49  fof(f359,plain,(
% 0.21/0.49    ~v3_setfam_1(k2_xboole_0(sK1,sK2),sK0) | (spl3_6 | ~spl3_37)),
% 0.21/0.49    inference(superposition,[],[f79,f357])).
% 0.21/0.49  fof(f357,plain,(
% 0.21/0.49    k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2) | ~spl3_37),
% 0.21/0.49    inference(avatar_component_clause,[],[f355])).
% 0.21/0.49  fof(f355,plain,(
% 0.21/0.49    spl3_37 <=> k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    ~v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2),sK0) | spl3_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f77])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    spl3_6 <=> v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2),sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.49  fof(f339,plain,(
% 0.21/0.49    r2_hidden(sK0,k2_xboole_0(sK1,sK2)) | v3_setfam_1(k2_xboole_0(sK1,sK2),sK0) | (~spl3_17 | ~spl3_34)),
% 0.21/0.49    inference(resolution,[],[f313,f127])).
% 0.21/0.49  fof(f127,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | r2_hidden(X0,X1) | v3_setfam_1(X1,X0)) ) | ~spl3_17),
% 0.21/0.49    inference(avatar_component_clause,[],[f126])).
% 0.21/0.49  fof(f126,plain,(
% 0.21/0.49    spl3_17 <=> ! [X1,X0] : (v3_setfam_1(X1,X0) | r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.49  fof(f313,plain,(
% 0.21/0.49    m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl3_34),
% 0.21/0.49    inference(avatar_component_clause,[],[f311])).
% 0.21/0.49  fof(f311,plain,(
% 0.21/0.49    spl3_34 <=> m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 0.21/0.49  fof(f476,plain,(
% 0.21/0.49    spl3_45 | ~spl3_8 | spl3_23),
% 0.21/0.49    inference(avatar_split_clause,[],[f189,f181,f86,f473])).
% 0.21/0.49  fof(f86,plain,(
% 0.21/0.49    spl3_8 <=> ! [X1,X0] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.49  fof(f181,plain,(
% 0.21/0.49    spl3_23 <=> r2_hidden(sK0,sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.21/0.49  fof(f189,plain,(
% 0.21/0.49    r1_xboole_0(k1_tarski(sK0),sK2) | (~spl3_8 | spl3_23)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f183,f87])).
% 0.21/0.49  fof(f87,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) ) | ~spl3_8),
% 0.21/0.49    inference(avatar_component_clause,[],[f86])).
% 0.21/0.49  fof(f183,plain,(
% 0.21/0.49    ~r2_hidden(sK0,sK2) | spl3_23),
% 0.21/0.49    inference(avatar_component_clause,[],[f181])).
% 0.21/0.49  fof(f372,plain,(
% 0.21/0.49    spl3_39 | ~spl3_10 | ~spl3_18),
% 0.21/0.49    inference(avatar_split_clause,[],[f143,f130,f94,f370])).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    spl3_10 <=> ! [X1,X0] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.49  fof(f130,plain,(
% 0.21/0.49    spl3_18 <=> ! [X1,X0,X2] : (r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.49  fof(f143,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r1_xboole_0(k1_tarski(X0),X1) | r1_tarski(k1_tarski(X0),X2) | ~r2_hidden(X0,k2_xboole_0(X2,X1))) ) | (~spl3_10 | ~spl3_18)),
% 0.21/0.49    inference(resolution,[],[f131,f95])).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) ) | ~spl3_10),
% 0.21/0.49    inference(avatar_component_clause,[],[f94])).
% 0.21/0.49  fof(f131,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | r1_tarski(X0,X1)) ) | ~spl3_18),
% 0.21/0.49    inference(avatar_component_clause,[],[f130])).
% 0.21/0.49  fof(f358,plain,(
% 0.21/0.49    spl3_37 | ~spl3_4 | ~spl3_5 | ~spl3_22),
% 0.21/0.49    inference(avatar_split_clause,[],[f170,f159,f72,f67,f355])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    spl3_4 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    spl3_5 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.49  fof(f159,plain,(
% 0.21/0.49    spl3_22 <=> ! [X1,X0,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.21/0.49  fof(f170,plain,(
% 0.21/0.49    k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2) | (~spl3_4 | ~spl3_5 | ~spl3_22)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f69,f74,f160])).
% 0.21/0.49  fof(f160,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl3_22),
% 0.21/0.49    inference(avatar_component_clause,[],[f159])).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl3_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f72])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl3_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f67])).
% 0.21/0.49  fof(f314,plain,(
% 0.21/0.49    spl3_34 | ~spl3_4 | ~spl3_5 | ~spl3_22 | ~spl3_33),
% 0.21/0.49    inference(avatar_split_clause,[],[f309,f305,f159,f72,f67,f311])).
% 0.21/0.49  fof(f305,plain,(
% 0.21/0.49    spl3_33 <=> m1_subset_1(k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.21/0.49  fof(f309,plain,(
% 0.21/0.49    m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(sK0))) | (~spl3_4 | ~spl3_5 | ~spl3_22 | ~spl3_33)),
% 0.21/0.49    inference(forward_demodulation,[],[f307,f170])).
% 0.21/0.49  fof(f307,plain,(
% 0.21/0.49    m1_subset_1(k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl3_33),
% 0.21/0.49    inference(avatar_component_clause,[],[f305])).
% 0.21/0.49  fof(f308,plain,(
% 0.21/0.49    spl3_33 | ~spl3_4 | ~spl3_5 | ~spl3_21),
% 0.21/0.49    inference(avatar_split_clause,[],[f164,f155,f72,f67,f305])).
% 0.21/0.49  fof(f155,plain,(
% 0.21/0.49    spl3_21 <=> ! [X1,X0,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.21/0.49  fof(f164,plain,(
% 0.21/0.49    m1_subset_1(k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(sK0))) | (~spl3_4 | ~spl3_5 | ~spl3_21)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f69,f74,f156])).
% 0.21/0.49  fof(f156,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl3_21),
% 0.21/0.49    inference(avatar_component_clause,[],[f155])).
% 0.21/0.49  fof(f200,plain,(
% 0.21/0.49    ~spl3_25 | ~spl3_9 | spl3_20),
% 0.21/0.49    inference(avatar_split_clause,[],[f178,f150,f90,f197])).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    spl3_9 <=> ! [X1,X0] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.49  fof(f150,plain,(
% 0.21/0.49    spl3_20 <=> r2_hidden(sK0,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.49  fof(f178,plain,(
% 0.21/0.49    ~r1_tarski(k1_tarski(sK0),sK1) | (~spl3_9 | spl3_20)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f152,f91])).
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X0),X1) | r2_hidden(X0,X1)) ) | ~spl3_9),
% 0.21/0.49    inference(avatar_component_clause,[],[f90])).
% 0.21/0.49  fof(f152,plain,(
% 0.21/0.49    ~r2_hidden(sK0,sK1) | spl3_20),
% 0.21/0.49    inference(avatar_component_clause,[],[f150])).
% 0.21/0.49  fof(f184,plain,(
% 0.21/0.49    ~spl3_23 | ~spl3_3 | ~spl3_5 | ~spl3_16),
% 0.21/0.49    inference(avatar_split_clause,[],[f138,f122,f72,f62,f181])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    spl3_3 <=> v3_setfam_1(sK2,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.49  fof(f122,plain,(
% 0.21/0.49    spl3_16 <=> ! [X1,X0] : (~r2_hidden(X0,X1) | ~v3_setfam_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.49  fof(f138,plain,(
% 0.21/0.49    ~r2_hidden(sK0,sK2) | (~spl3_3 | ~spl3_5 | ~spl3_16)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f64,f74,f123])).
% 0.21/0.49  fof(f123,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~v3_setfam_1(X1,X0) | ~r2_hidden(X0,X1)) ) | ~spl3_16),
% 0.21/0.49    inference(avatar_component_clause,[],[f122])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    v3_setfam_1(sK2,sK0) | ~spl3_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f62])).
% 0.21/0.49  fof(f161,plain,(
% 0.21/0.49    spl3_22),
% 0.21/0.49    inference(avatar_split_clause,[],[f46,f159])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.49    inference(flattening,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.21/0.49  fof(f157,plain,(
% 0.21/0.49    spl3_21),
% 0.21/0.49    inference(avatar_split_clause,[],[f45,f155])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.49    inference(flattening,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).
% 0.21/0.49  fof(f153,plain,(
% 0.21/0.49    ~spl3_20 | ~spl3_2 | ~spl3_4 | ~spl3_16),
% 0.21/0.49    inference(avatar_split_clause,[],[f137,f122,f67,f57,f150])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    spl3_2 <=> v3_setfam_1(sK1,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.49  fof(f137,plain,(
% 0.21/0.49    ~r2_hidden(sK0,sK1) | (~spl3_2 | ~spl3_4 | ~spl3_16)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f59,f69,f123])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    v3_setfam_1(sK1,sK0) | ~spl3_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f57])).
% 0.21/0.49  fof(f132,plain,(
% 0.21/0.49    spl3_18),
% 0.21/0.49    inference(avatar_split_clause,[],[f47,f130])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.21/0.49    inference(flattening,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (r1_tarski(X0,X1) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).
% 0.21/0.49  fof(f128,plain,(
% 0.21/0.49    spl3_17),
% 0.21/0.49    inference(avatar_split_clause,[],[f42,f126])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v3_setfam_1(X1,X0) | r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X0,X1] : (((v3_setfam_1(X1,X0) | r2_hidden(X0,X1)) & (~r2_hidden(X0,X1) | ~v3_setfam_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.49    inference(nnf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0,X1] : ((v3_setfam_1(X1,X0) <=> ~r2_hidden(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.49    inference(ennf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (v3_setfam_1(X1,X0) <=> ~r2_hidden(X0,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_setfam_1)).
% 0.21/0.49  fof(f124,plain,(
% 0.21/0.49    spl3_16),
% 0.21/0.49    inference(avatar_split_clause,[],[f41,f122])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~v3_setfam_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f27])).
% 0.21/0.49  fof(f96,plain,(
% 0.21/0.49    spl3_10),
% 0.21/0.49    inference(avatar_split_clause,[],[f44,f94])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.21/0.49    inference(nnf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.21/0.49  fof(f92,plain,(
% 0.21/0.49    spl3_9),
% 0.21/0.49    inference(avatar_split_clause,[],[f43,f90])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f28])).
% 0.21/0.49  fof(f88,plain,(
% 0.21/0.49    spl3_8),
% 0.21/0.49    inference(avatar_split_clause,[],[f40,f86])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    ~spl3_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f36,f77])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ~v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2),sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ((~v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2),sK0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) & v3_setfam_1(sK2,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) & v3_setfam_1(sK1,sK0)) & ~v1_xboole_0(sK0)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f25,f24,f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (~v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X1,X0)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (~v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK0),X1,X2),sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0))) & v3_setfam_1(X2,sK0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(sK0))) & v3_setfam_1(X1,sK0)) & ~v1_xboole_0(sK0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ? [X1] : (? [X2] : (~v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK0),X1,X2),sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0))) & v3_setfam_1(X2,sK0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(sK0))) & v3_setfam_1(X1,sK0)) => (? [X2] : (~v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK0),sK1,X2),sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0))) & v3_setfam_1(X2,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) & v3_setfam_1(sK1,sK0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ? [X2] : (~v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK0),sK1,X2),sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0))) & v3_setfam_1(X2,sK0)) => (~v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2),sK0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) & v3_setfam_1(sK2,sK0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (~v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.21/0.49    inference(flattening,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (~v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0) & (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X2,X0))) & (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X1,X0))) & ~v1_xboole_0(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,negated_conjecture,(
% 0.21/0.49    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X1,X0)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X2,X0)) => v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0))))),
% 0.21/0.49    inference(negated_conjecture,[],[f11])).
% 0.21/0.49  fof(f11,conjecture,(
% 0.21/0.49    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X1,X0)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X2,X0)) => v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_setfam_1)).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    spl3_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f35,f72])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    spl3_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f33,f67])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    spl3_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f34,f62])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    v3_setfam_1(sK2,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    spl3_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f32,f57])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    v3_setfam_1(sK1,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (20692)------------------------------
% 0.21/0.49  % (20692)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (20692)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (20692)Memory used [KB]: 6396
% 0.21/0.49  % (20692)Time elapsed: 0.066 s
% 0.21/0.49  % (20692)------------------------------
% 0.21/0.49  % (20692)------------------------------
% 0.21/0.49  % (20688)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.49  % (20698)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.50  % (20687)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.50  % (20701)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.50  % (20699)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.50  % (20686)Success in time 0.144 s
%------------------------------------------------------------------------------
