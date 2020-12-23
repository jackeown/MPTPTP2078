%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:20 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 203 expanded)
%              Number of leaves         :   35 (  94 expanded)
%              Depth                    :    7
%              Number of atoms          :  338 ( 509 expanded)
%              Number of equality atoms :   11 (  25 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f246,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f52,f57,f61,f67,f71,f79,f87,f91,f95,f112,f119,f125,f129,f133,f139,f163,f196,f206,f212,f219,f229,f235,f241,f245])).

fof(f245,plain,
    ( spl3_2
    | ~ spl3_18
    | ~ spl3_37 ),
    inference(avatar_contradiction_clause,[],[f244])).

fof(f244,plain,
    ( $false
    | spl3_2
    | ~ spl3_18
    | ~ spl3_37 ),
    inference(subsumption_resolution,[],[f242,f56])).

fof(f56,plain,
    ( ~ r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1)))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl3_2
  <=> r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f242,plain,
    ( r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1)))
    | ~ spl3_18
    | ~ spl3_37 ),
    inference(resolution,[],[f240,f132])).

fof(f132,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k4_xboole_0(X0,X1),X2)
        | r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) )
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl3_18
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))
        | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f240,plain,
    ( r1_tarski(k4_xboole_0(k3_relat_1(sK2),sK0),sK1)
    | ~ spl3_37 ),
    inference(avatar_component_clause,[],[f238])).

fof(f238,plain,
    ( spl3_37
  <=> r1_tarski(k4_xboole_0(k3_relat_1(sK2),sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f241,plain,
    ( spl3_37
    | ~ spl3_15
    | ~ spl3_36 ),
    inference(avatar_split_clause,[],[f236,f233,f116,f238])).

fof(f116,plain,
    ( spl3_15
  <=> v5_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f233,plain,
    ( spl3_36
  <=> ! [X0] :
        ( r1_tarski(k4_xboole_0(k3_relat_1(sK2),sK0),X0)
        | ~ v5_relat_1(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f236,plain,
    ( r1_tarski(k4_xboole_0(k3_relat_1(sK2),sK0),sK1)
    | ~ spl3_15
    | ~ spl3_36 ),
    inference(resolution,[],[f234,f118])).

fof(f118,plain,
    ( v5_relat_1(sK2,sK1)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f116])).

fof(f234,plain,
    ( ! [X0] :
        ( ~ v5_relat_1(sK2,X0)
        | r1_tarski(k4_xboole_0(k3_relat_1(sK2),sK0),X0) )
    | ~ spl3_36 ),
    inference(avatar_component_clause,[],[f233])).

fof(f235,plain,
    ( spl3_36
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_35 ),
    inference(avatar_split_clause,[],[f231,f227,f69,f64,f233])).

fof(f64,plain,
    ( spl3_4
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f69,plain,
    ( spl3_5
  <=> ! [X1,X0] :
        ( r1_tarski(k2_relat_1(X1),X0)
        | ~ v5_relat_1(X1,X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f227,plain,
    ( spl3_35
  <=> ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK2),X0)
        | r1_tarski(k4_xboole_0(k3_relat_1(sK2),sK0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f231,plain,
    ( ! [X0] :
        ( r1_tarski(k4_xboole_0(k3_relat_1(sK2),sK0),X0)
        | ~ v5_relat_1(sK2,X0) )
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_35 ),
    inference(subsumption_resolution,[],[f230,f66])).

fof(f66,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f64])).

fof(f230,plain,
    ( ! [X0] :
        ( r1_tarski(k4_xboole_0(k3_relat_1(sK2),sK0),X0)
        | ~ v5_relat_1(sK2,X0)
        | ~ v1_relat_1(sK2) )
    | ~ spl3_5
    | ~ spl3_35 ),
    inference(resolution,[],[f228,f70])).

fof(f70,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k2_relat_1(X1),X0)
        | ~ v5_relat_1(X1,X0)
        | ~ v1_relat_1(X1) )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f69])).

fof(f228,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK2),X0)
        | r1_tarski(k4_xboole_0(k3_relat_1(sK2),sK0),X0) )
    | ~ spl3_35 ),
    inference(avatar_component_clause,[],[f227])).

fof(f229,plain,
    ( spl3_35
    | ~ spl3_11
    | ~ spl3_33 ),
    inference(avatar_split_clause,[],[f225,f216,f93,f227])).

fof(f93,plain,
    ( spl3_11
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,X2)
        | ~ r1_tarski(X1,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f216,plain,
    ( spl3_33
  <=> r1_tarski(k4_xboole_0(k3_relat_1(sK2),sK0),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f225,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK2),X0)
        | r1_tarski(k4_xboole_0(k3_relat_1(sK2),sK0),X0) )
    | ~ spl3_11
    | ~ spl3_33 ),
    inference(resolution,[],[f218,f94])).

fof(f94,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ r1_tarski(X1,X2)
        | r1_tarski(X0,X2) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f93])).

fof(f218,plain,
    ( r1_tarski(k4_xboole_0(k3_relat_1(sK2),sK0),k2_relat_1(sK2))
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f216])).

fof(f219,plain,
    ( spl3_33
    | ~ spl3_17
    | ~ spl3_32 ),
    inference(avatar_split_clause,[],[f213,f209,f127,f216])).

fof(f127,plain,
    ( spl3_17
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k4_xboole_0(X0,X1),X2)
        | ~ r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f209,plain,
    ( spl3_32
  <=> r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(sK0,k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f213,plain,
    ( r1_tarski(k4_xboole_0(k3_relat_1(sK2),sK0),k2_relat_1(sK2))
    | ~ spl3_17
    | ~ spl3_32 ),
    inference(resolution,[],[f211,f128])).

fof(f128,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))
        | r1_tarski(k4_xboole_0(X0,X1),X2) )
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f127])).

fof(f211,plain,
    ( r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(sK0,k2_relat_1(sK2))))
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f209])).

fof(f212,plain,
    ( spl3_32
    | ~ spl3_14
    | ~ spl3_31 ),
    inference(avatar_split_clause,[],[f207,f204,f109,f209])).

fof(f109,plain,
    ( spl3_14
  <=> v4_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f204,plain,
    ( spl3_31
  <=> ! [X0] :
        ( r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(X0,k2_relat_1(sK2))))
        | ~ v4_relat_1(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f207,plain,
    ( r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(sK0,k2_relat_1(sK2))))
    | ~ spl3_14
    | ~ spl3_31 ),
    inference(resolution,[],[f205,f111])).

fof(f111,plain,
    ( v4_relat_1(sK2,sK0)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f109])).

fof(f205,plain,
    ( ! [X0] :
        ( ~ v4_relat_1(sK2,X0)
        | r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(X0,k2_relat_1(sK2)))) )
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f204])).

fof(f206,plain,
    ( spl3_31
    | ~ spl3_4
    | ~ spl3_7
    | ~ spl3_29 ),
    inference(avatar_split_clause,[],[f202,f194,f77,f64,f204])).

fof(f77,plain,
    ( spl3_7
  <=> ! [X1,X0] :
        ( r1_tarski(k1_relat_1(X1),X0)
        | ~ v4_relat_1(X1,X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f194,plain,
    ( spl3_29
  <=> ! [X0] :
        ( r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(X0,k2_relat_1(sK2))))
        | ~ r1_tarski(k1_relat_1(sK2),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f202,plain,
    ( ! [X0] :
        ( r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(X0,k2_relat_1(sK2))))
        | ~ v4_relat_1(sK2,X0) )
    | ~ spl3_4
    | ~ spl3_7
    | ~ spl3_29 ),
    inference(subsumption_resolution,[],[f201,f66])).

fof(f201,plain,
    ( ! [X0] :
        ( r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(X0,k2_relat_1(sK2))))
        | ~ v4_relat_1(sK2,X0)
        | ~ v1_relat_1(sK2) )
    | ~ spl3_7
    | ~ spl3_29 ),
    inference(resolution,[],[f195,f78])).

fof(f78,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k1_relat_1(X1),X0)
        | ~ v4_relat_1(X1,X0)
        | ~ v1_relat_1(X1) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f77])).

fof(f195,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(sK2),X0)
        | r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(X0,k2_relat_1(sK2)))) )
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f194])).

fof(f196,plain,
    ( spl3_29
    | ~ spl3_19
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f191,f161,f136,f194])).

fof(f136,plain,
    ( spl3_19
  <=> k3_relat_1(sK2) = k3_tarski(k2_tarski(k1_relat_1(sK2),k2_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f161,plain,
    ( spl3_23
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k3_tarski(k2_tarski(X0,X2)),k3_tarski(k2_tarski(X1,X2)))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f191,plain,
    ( ! [X0] :
        ( r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(X0,k2_relat_1(sK2))))
        | ~ r1_tarski(k1_relat_1(sK2),X0) )
    | ~ spl3_19
    | ~ spl3_23 ),
    inference(superposition,[],[f162,f138])).

fof(f138,plain,
    ( k3_relat_1(sK2) = k3_tarski(k2_tarski(k1_relat_1(sK2),k2_relat_1(sK2)))
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f136])).

fof(f162,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k3_tarski(k2_tarski(X0,X2)),k3_tarski(k2_tarski(X1,X2)))
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f161])).

fof(f163,plain,(
    spl3_23 ),
    inference(avatar_split_clause,[],[f45,f161])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k2_tarski(X0,X2)),k3_tarski(k2_tarski(X1,X2)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f36,f31,f31])).

fof(f31,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_xboole_1)).

fof(f139,plain,
    ( spl3_19
    | ~ spl3_4
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f134,f123,f64,f136])).

fof(f123,plain,
    ( spl3_16
  <=> ! [X0] :
        ( k3_relat_1(X0) = k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0)))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f134,plain,
    ( k3_relat_1(sK2) = k3_tarski(k2_tarski(k1_relat_1(sK2),k2_relat_1(sK2)))
    | ~ spl3_4
    | ~ spl3_16 ),
    inference(resolution,[],[f124,f66])).

fof(f124,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k3_relat_1(X0) = k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))) )
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f123])).

fof(f133,plain,(
    spl3_18 ),
    inference(avatar_split_clause,[],[f47,f131])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f38,f31])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f129,plain,(
    spl3_17 ),
    inference(avatar_split_clause,[],[f46,f127])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) ) ),
    inference(definition_unfolding,[],[f37,f31])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f125,plain,(
    spl3_16 ),
    inference(avatar_split_clause,[],[f44,f123])).

fof(f44,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f30,f31])).

fof(f30,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(f119,plain,
    ( spl3_15
    | ~ spl3_1
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f114,f89,f49,f116])).

fof(f49,plain,
    ( spl3_1
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f89,plain,
    ( spl3_10
  <=> ! [X1,X0,X2] :
        ( v5_relat_1(X2,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f114,plain,
    ( v5_relat_1(sK2,sK1)
    | ~ spl3_1
    | ~ spl3_10 ),
    inference(resolution,[],[f90,f51])).

fof(f51,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f49])).

fof(f90,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v5_relat_1(X2,X1) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f89])).

fof(f112,plain,
    ( spl3_14
    | ~ spl3_1
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f107,f85,f49,f109])).

fof(f85,plain,
    ( spl3_9
  <=> ! [X1,X0,X2] :
        ( v4_relat_1(X2,X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f107,plain,
    ( v4_relat_1(sK2,sK0)
    | ~ spl3_1
    | ~ spl3_9 ),
    inference(resolution,[],[f86,f51])).

fof(f86,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v4_relat_1(X2,X0) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f85])).

fof(f95,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f42,f93])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f91,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f41,f89])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f87,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f40,f85])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f79,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f34,f77])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f71,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f32,f69])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f67,plain,
    ( spl3_4
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f62,f59,f49,f64])).

fof(f59,plain,
    ( spl3_3
  <=> ! [X1,X0,X2] :
        ( v1_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f62,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(resolution,[],[f60,f51])).

fof(f60,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_relat_1(X2) )
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f59])).

fof(f61,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f39,f59])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f57,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f43,f54])).

fof(f43,plain,(
    ~ r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1))) ),
    inference(definition_unfolding,[],[f29,f31])).

fof(f29,plain,(
    ~ r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ~ r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f24])).

fof(f24,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ~ r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1))
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1))
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_relset_1)).

fof(f52,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f28,f49])).

fof(f28,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:09:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.45  % (2570)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.46  % (2570)Refutation found. Thanks to Tanya!
% 0.22/0.46  % SZS status Theorem for theBenchmark
% 0.22/0.46  % SZS output start Proof for theBenchmark
% 0.22/0.46  fof(f246,plain,(
% 0.22/0.46    $false),
% 0.22/0.46    inference(avatar_sat_refutation,[],[f52,f57,f61,f67,f71,f79,f87,f91,f95,f112,f119,f125,f129,f133,f139,f163,f196,f206,f212,f219,f229,f235,f241,f245])).
% 0.22/0.46  fof(f245,plain,(
% 0.22/0.46    spl3_2 | ~spl3_18 | ~spl3_37),
% 0.22/0.46    inference(avatar_contradiction_clause,[],[f244])).
% 0.22/0.46  fof(f244,plain,(
% 0.22/0.46    $false | (spl3_2 | ~spl3_18 | ~spl3_37)),
% 0.22/0.46    inference(subsumption_resolution,[],[f242,f56])).
% 0.22/0.46  fof(f56,plain,(
% 0.22/0.46    ~r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1))) | spl3_2),
% 0.22/0.46    inference(avatar_component_clause,[],[f54])).
% 0.22/0.46  fof(f54,plain,(
% 0.22/0.46    spl3_2 <=> r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1)))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.46  fof(f242,plain,(
% 0.22/0.46    r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1))) | (~spl3_18 | ~spl3_37)),
% 0.22/0.46    inference(resolution,[],[f240,f132])).
% 0.22/0.46  fof(f132,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X2) | r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))) ) | ~spl3_18),
% 0.22/0.46    inference(avatar_component_clause,[],[f131])).
% 0.22/0.46  fof(f131,plain,(
% 0.22/0.46    spl3_18 <=> ! [X1,X0,X2] : (r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.22/0.46  fof(f240,plain,(
% 0.22/0.46    r1_tarski(k4_xboole_0(k3_relat_1(sK2),sK0),sK1) | ~spl3_37),
% 0.22/0.46    inference(avatar_component_clause,[],[f238])).
% 0.22/0.46  fof(f238,plain,(
% 0.22/0.46    spl3_37 <=> r1_tarski(k4_xboole_0(k3_relat_1(sK2),sK0),sK1)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 0.22/0.46  fof(f241,plain,(
% 0.22/0.46    spl3_37 | ~spl3_15 | ~spl3_36),
% 0.22/0.46    inference(avatar_split_clause,[],[f236,f233,f116,f238])).
% 0.22/0.46  fof(f116,plain,(
% 0.22/0.46    spl3_15 <=> v5_relat_1(sK2,sK1)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.22/0.46  fof(f233,plain,(
% 0.22/0.46    spl3_36 <=> ! [X0] : (r1_tarski(k4_xboole_0(k3_relat_1(sK2),sK0),X0) | ~v5_relat_1(sK2,X0))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 0.22/0.46  fof(f236,plain,(
% 0.22/0.46    r1_tarski(k4_xboole_0(k3_relat_1(sK2),sK0),sK1) | (~spl3_15 | ~spl3_36)),
% 0.22/0.46    inference(resolution,[],[f234,f118])).
% 0.22/0.46  fof(f118,plain,(
% 0.22/0.46    v5_relat_1(sK2,sK1) | ~spl3_15),
% 0.22/0.46    inference(avatar_component_clause,[],[f116])).
% 0.22/0.46  fof(f234,plain,(
% 0.22/0.46    ( ! [X0] : (~v5_relat_1(sK2,X0) | r1_tarski(k4_xboole_0(k3_relat_1(sK2),sK0),X0)) ) | ~spl3_36),
% 0.22/0.46    inference(avatar_component_clause,[],[f233])).
% 0.22/0.46  fof(f235,plain,(
% 0.22/0.46    spl3_36 | ~spl3_4 | ~spl3_5 | ~spl3_35),
% 0.22/0.46    inference(avatar_split_clause,[],[f231,f227,f69,f64,f233])).
% 0.22/0.46  fof(f64,plain,(
% 0.22/0.46    spl3_4 <=> v1_relat_1(sK2)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.46  fof(f69,plain,(
% 0.22/0.46    spl3_5 <=> ! [X1,X0] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.46  fof(f227,plain,(
% 0.22/0.46    spl3_35 <=> ! [X0] : (~r1_tarski(k2_relat_1(sK2),X0) | r1_tarski(k4_xboole_0(k3_relat_1(sK2),sK0),X0))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 0.22/0.46  fof(f231,plain,(
% 0.22/0.46    ( ! [X0] : (r1_tarski(k4_xboole_0(k3_relat_1(sK2),sK0),X0) | ~v5_relat_1(sK2,X0)) ) | (~spl3_4 | ~spl3_5 | ~spl3_35)),
% 0.22/0.46    inference(subsumption_resolution,[],[f230,f66])).
% 0.22/0.46  fof(f66,plain,(
% 0.22/0.46    v1_relat_1(sK2) | ~spl3_4),
% 0.22/0.46    inference(avatar_component_clause,[],[f64])).
% 0.22/0.46  fof(f230,plain,(
% 0.22/0.46    ( ! [X0] : (r1_tarski(k4_xboole_0(k3_relat_1(sK2),sK0),X0) | ~v5_relat_1(sK2,X0) | ~v1_relat_1(sK2)) ) | (~spl3_5 | ~spl3_35)),
% 0.22/0.46    inference(resolution,[],[f228,f70])).
% 0.22/0.46  fof(f70,plain,(
% 0.22/0.46    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) ) | ~spl3_5),
% 0.22/0.46    inference(avatar_component_clause,[],[f69])).
% 0.22/0.46  fof(f228,plain,(
% 0.22/0.46    ( ! [X0] : (~r1_tarski(k2_relat_1(sK2),X0) | r1_tarski(k4_xboole_0(k3_relat_1(sK2),sK0),X0)) ) | ~spl3_35),
% 0.22/0.46    inference(avatar_component_clause,[],[f227])).
% 0.22/0.46  fof(f229,plain,(
% 0.22/0.46    spl3_35 | ~spl3_11 | ~spl3_33),
% 0.22/0.46    inference(avatar_split_clause,[],[f225,f216,f93,f227])).
% 0.22/0.46  fof(f93,plain,(
% 0.22/0.46    spl3_11 <=> ! [X1,X0,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.46  fof(f216,plain,(
% 0.22/0.46    spl3_33 <=> r1_tarski(k4_xboole_0(k3_relat_1(sK2),sK0),k2_relat_1(sK2))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.22/0.46  fof(f225,plain,(
% 0.22/0.46    ( ! [X0] : (~r1_tarski(k2_relat_1(sK2),X0) | r1_tarski(k4_xboole_0(k3_relat_1(sK2),sK0),X0)) ) | (~spl3_11 | ~spl3_33)),
% 0.22/0.46    inference(resolution,[],[f218,f94])).
% 0.22/0.46  fof(f94,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) ) | ~spl3_11),
% 0.22/0.46    inference(avatar_component_clause,[],[f93])).
% 0.22/0.46  fof(f218,plain,(
% 0.22/0.46    r1_tarski(k4_xboole_0(k3_relat_1(sK2),sK0),k2_relat_1(sK2)) | ~spl3_33),
% 0.22/0.46    inference(avatar_component_clause,[],[f216])).
% 0.22/0.46  fof(f219,plain,(
% 0.22/0.46    spl3_33 | ~spl3_17 | ~spl3_32),
% 0.22/0.46    inference(avatar_split_clause,[],[f213,f209,f127,f216])).
% 0.22/0.46  fof(f127,plain,(
% 0.22/0.46    spl3_17 <=> ! [X1,X0,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.22/0.46  fof(f209,plain,(
% 0.22/0.46    spl3_32 <=> r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(sK0,k2_relat_1(sK2))))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.22/0.46  fof(f213,plain,(
% 0.22/0.46    r1_tarski(k4_xboole_0(k3_relat_1(sK2),sK0),k2_relat_1(sK2)) | (~spl3_17 | ~spl3_32)),
% 0.22/0.46    inference(resolution,[],[f211,f128])).
% 0.22/0.46  fof(f128,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) | r1_tarski(k4_xboole_0(X0,X1),X2)) ) | ~spl3_17),
% 0.22/0.46    inference(avatar_component_clause,[],[f127])).
% 0.22/0.46  fof(f211,plain,(
% 0.22/0.46    r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(sK0,k2_relat_1(sK2)))) | ~spl3_32),
% 0.22/0.46    inference(avatar_component_clause,[],[f209])).
% 0.22/0.46  fof(f212,plain,(
% 0.22/0.46    spl3_32 | ~spl3_14 | ~spl3_31),
% 0.22/0.46    inference(avatar_split_clause,[],[f207,f204,f109,f209])).
% 0.22/0.46  fof(f109,plain,(
% 0.22/0.46    spl3_14 <=> v4_relat_1(sK2,sK0)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.22/0.46  fof(f204,plain,(
% 0.22/0.46    spl3_31 <=> ! [X0] : (r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(X0,k2_relat_1(sK2)))) | ~v4_relat_1(sK2,X0))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.22/0.46  fof(f207,plain,(
% 0.22/0.46    r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(sK0,k2_relat_1(sK2)))) | (~spl3_14 | ~spl3_31)),
% 0.22/0.46    inference(resolution,[],[f205,f111])).
% 0.22/0.46  fof(f111,plain,(
% 0.22/0.46    v4_relat_1(sK2,sK0) | ~spl3_14),
% 0.22/0.46    inference(avatar_component_clause,[],[f109])).
% 0.22/0.46  fof(f205,plain,(
% 0.22/0.46    ( ! [X0] : (~v4_relat_1(sK2,X0) | r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(X0,k2_relat_1(sK2))))) ) | ~spl3_31),
% 0.22/0.46    inference(avatar_component_clause,[],[f204])).
% 0.22/0.46  fof(f206,plain,(
% 0.22/0.46    spl3_31 | ~spl3_4 | ~spl3_7 | ~spl3_29),
% 0.22/0.46    inference(avatar_split_clause,[],[f202,f194,f77,f64,f204])).
% 0.22/0.46  fof(f77,plain,(
% 0.22/0.46    spl3_7 <=> ! [X1,X0] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.46  fof(f194,plain,(
% 0.22/0.46    spl3_29 <=> ! [X0] : (r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(X0,k2_relat_1(sK2)))) | ~r1_tarski(k1_relat_1(sK2),X0))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.22/0.46  fof(f202,plain,(
% 0.22/0.46    ( ! [X0] : (r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(X0,k2_relat_1(sK2)))) | ~v4_relat_1(sK2,X0)) ) | (~spl3_4 | ~spl3_7 | ~spl3_29)),
% 0.22/0.46    inference(subsumption_resolution,[],[f201,f66])).
% 0.22/0.46  fof(f201,plain,(
% 0.22/0.46    ( ! [X0] : (r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(X0,k2_relat_1(sK2)))) | ~v4_relat_1(sK2,X0) | ~v1_relat_1(sK2)) ) | (~spl3_7 | ~spl3_29)),
% 0.22/0.46    inference(resolution,[],[f195,f78])).
% 0.22/0.46  fof(f78,plain,(
% 0.22/0.46    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) ) | ~spl3_7),
% 0.22/0.46    inference(avatar_component_clause,[],[f77])).
% 0.22/0.46  fof(f195,plain,(
% 0.22/0.46    ( ! [X0] : (~r1_tarski(k1_relat_1(sK2),X0) | r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(X0,k2_relat_1(sK2))))) ) | ~spl3_29),
% 0.22/0.46    inference(avatar_component_clause,[],[f194])).
% 0.22/0.46  fof(f196,plain,(
% 0.22/0.46    spl3_29 | ~spl3_19 | ~spl3_23),
% 0.22/0.46    inference(avatar_split_clause,[],[f191,f161,f136,f194])).
% 0.22/0.46  fof(f136,plain,(
% 0.22/0.46    spl3_19 <=> k3_relat_1(sK2) = k3_tarski(k2_tarski(k1_relat_1(sK2),k2_relat_1(sK2)))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.22/0.46  fof(f161,plain,(
% 0.22/0.46    spl3_23 <=> ! [X1,X0,X2] : (r1_tarski(k3_tarski(k2_tarski(X0,X2)),k3_tarski(k2_tarski(X1,X2))) | ~r1_tarski(X0,X1))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.22/0.46  fof(f191,plain,(
% 0.22/0.46    ( ! [X0] : (r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(X0,k2_relat_1(sK2)))) | ~r1_tarski(k1_relat_1(sK2),X0)) ) | (~spl3_19 | ~spl3_23)),
% 0.22/0.46    inference(superposition,[],[f162,f138])).
% 0.22/0.46  fof(f138,plain,(
% 0.22/0.46    k3_relat_1(sK2) = k3_tarski(k2_tarski(k1_relat_1(sK2),k2_relat_1(sK2))) | ~spl3_19),
% 0.22/0.46    inference(avatar_component_clause,[],[f136])).
% 0.22/0.46  fof(f162,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k2_tarski(X0,X2)),k3_tarski(k2_tarski(X1,X2))) | ~r1_tarski(X0,X1)) ) | ~spl3_23),
% 0.22/0.46    inference(avatar_component_clause,[],[f161])).
% 0.22/0.46  fof(f163,plain,(
% 0.22/0.46    spl3_23),
% 0.22/0.46    inference(avatar_split_clause,[],[f45,f161])).
% 0.22/0.46  fof(f45,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k2_tarski(X0,X2)),k3_tarski(k2_tarski(X1,X2))) | ~r1_tarski(X0,X1)) )),
% 0.22/0.46    inference(definition_unfolding,[],[f36,f31,f31])).
% 0.22/0.46  fof(f31,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f5])).
% 0.22/0.46  fof(f5,axiom,(
% 0.22/0.46    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.22/0.46  fof(f36,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f17])).
% 0.22/0.46  fof(f17,plain,(
% 0.22/0.46    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) | ~r1_tarski(X0,X1))),
% 0.22/0.46    inference(ennf_transformation,[],[f4])).
% 0.22/0.46  fof(f4,axiom,(
% 0.22/0.46    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_xboole_1)).
% 0.22/0.46  fof(f139,plain,(
% 0.22/0.46    spl3_19 | ~spl3_4 | ~spl3_16),
% 0.22/0.46    inference(avatar_split_clause,[],[f134,f123,f64,f136])).
% 0.22/0.46  fof(f123,plain,(
% 0.22/0.46    spl3_16 <=> ! [X0] : (k3_relat_1(X0) = k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.22/0.46  fof(f134,plain,(
% 0.22/0.46    k3_relat_1(sK2) = k3_tarski(k2_tarski(k1_relat_1(sK2),k2_relat_1(sK2))) | (~spl3_4 | ~spl3_16)),
% 0.22/0.46    inference(resolution,[],[f124,f66])).
% 0.22/0.46  fof(f124,plain,(
% 0.22/0.46    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0)))) ) | ~spl3_16),
% 0.22/0.46    inference(avatar_component_clause,[],[f123])).
% 0.22/0.46  fof(f133,plain,(
% 0.22/0.46    spl3_18),
% 0.22/0.46    inference(avatar_split_clause,[],[f47,f131])).
% 0.22/0.46  fof(f47,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 0.22/0.46    inference(definition_unfolding,[],[f38,f31])).
% 0.22/0.46  fof(f38,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f19])).
% 0.22/0.46  fof(f19,plain,(
% 0.22/0.46    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.22/0.46    inference(ennf_transformation,[],[f3])).
% 0.22/0.46  fof(f3,axiom,(
% 0.22/0.46    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).
% 0.22/0.46  fof(f129,plain,(
% 0.22/0.46    spl3_17),
% 0.22/0.46    inference(avatar_split_clause,[],[f46,f127])).
% 0.22/0.46  fof(f46,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))) )),
% 0.22/0.46    inference(definition_unfolding,[],[f37,f31])).
% 0.22/0.46  fof(f37,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 0.22/0.46    inference(cnf_transformation,[],[f18])).
% 0.22/0.46  fof(f18,plain,(
% 0.22/0.46    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.22/0.46    inference(ennf_transformation,[],[f2])).
% 0.22/0.46  fof(f2,axiom,(
% 0.22/0.46    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).
% 0.22/0.46  fof(f125,plain,(
% 0.22/0.46    spl3_16),
% 0.22/0.46    inference(avatar_split_clause,[],[f44,f123])).
% 0.22/0.46  fof(f44,plain,(
% 0.22/0.46    ( ! [X0] : (k3_relat_1(X0) = k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 0.22/0.46    inference(definition_unfolding,[],[f30,f31])).
% 0.22/0.46  fof(f30,plain,(
% 0.22/0.46    ( ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f14])).
% 0.22/0.46  fof(f14,plain,(
% 0.22/0.46    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.46    inference(ennf_transformation,[],[f8])).
% 0.22/0.46  fof(f8,axiom,(
% 0.22/0.46    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).
% 0.22/0.46  fof(f119,plain,(
% 0.22/0.46    spl3_15 | ~spl3_1 | ~spl3_10),
% 0.22/0.46    inference(avatar_split_clause,[],[f114,f89,f49,f116])).
% 0.22/0.46  fof(f49,plain,(
% 0.22/0.46    spl3_1 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.46  fof(f89,plain,(
% 0.22/0.46    spl3_10 <=> ! [X1,X0,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.46  fof(f114,plain,(
% 0.22/0.46    v5_relat_1(sK2,sK1) | (~spl3_1 | ~spl3_10)),
% 0.22/0.46    inference(resolution,[],[f90,f51])).
% 0.22/0.46  fof(f51,plain,(
% 0.22/0.46    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl3_1),
% 0.22/0.46    inference(avatar_component_clause,[],[f49])).
% 0.22/0.46  fof(f90,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) ) | ~spl3_10),
% 0.22/0.46    inference(avatar_component_clause,[],[f89])).
% 0.22/0.46  fof(f112,plain,(
% 0.22/0.46    spl3_14 | ~spl3_1 | ~spl3_9),
% 0.22/0.46    inference(avatar_split_clause,[],[f107,f85,f49,f109])).
% 0.22/0.46  fof(f85,plain,(
% 0.22/0.46    spl3_9 <=> ! [X1,X0,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.46  fof(f107,plain,(
% 0.22/0.46    v4_relat_1(sK2,sK0) | (~spl3_1 | ~spl3_9)),
% 0.22/0.46    inference(resolution,[],[f86,f51])).
% 0.22/0.46  fof(f86,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) ) | ~spl3_9),
% 0.22/0.46    inference(avatar_component_clause,[],[f85])).
% 0.22/0.46  fof(f95,plain,(
% 0.22/0.46    spl3_11),
% 0.22/0.46    inference(avatar_split_clause,[],[f42,f93])).
% 0.22/0.46  fof(f42,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f23])).
% 0.22/0.46  fof(f23,plain,(
% 0.22/0.46    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.46    inference(flattening,[],[f22])).
% 0.22/0.46  fof(f22,plain,(
% 0.22/0.46    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.46    inference(ennf_transformation,[],[f1])).
% 0.22/0.46  fof(f1,axiom,(
% 0.22/0.46    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.22/0.46  fof(f91,plain,(
% 0.22/0.46    spl3_10),
% 0.22/0.46    inference(avatar_split_clause,[],[f41,f89])).
% 0.22/0.46  fof(f41,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.46    inference(cnf_transformation,[],[f21])).
% 0.22/0.46  fof(f21,plain,(
% 0.22/0.46    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.46    inference(ennf_transformation,[],[f10])).
% 0.22/0.46  fof(f10,axiom,(
% 0.22/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.46  fof(f87,plain,(
% 0.22/0.46    spl3_9),
% 0.22/0.46    inference(avatar_split_clause,[],[f40,f85])).
% 0.22/0.46  fof(f40,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.46    inference(cnf_transformation,[],[f21])).
% 0.22/0.46  fof(f79,plain,(
% 0.22/0.46    spl3_7),
% 0.22/0.46    inference(avatar_split_clause,[],[f34,f77])).
% 0.22/0.46  fof(f34,plain,(
% 0.22/0.46    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f27])).
% 0.22/0.46  fof(f27,plain,(
% 0.22/0.46    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.22/0.46    inference(nnf_transformation,[],[f16])).
% 0.22/0.46  fof(f16,plain,(
% 0.22/0.46    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.46    inference(ennf_transformation,[],[f6])).
% 0.22/0.46  fof(f6,axiom,(
% 0.22/0.46    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 0.22/0.46  fof(f71,plain,(
% 0.22/0.46    spl3_5),
% 0.22/0.46    inference(avatar_split_clause,[],[f32,f69])).
% 0.22/0.46  fof(f32,plain,(
% 0.22/0.46    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f26])).
% 0.22/0.46  fof(f26,plain,(
% 0.22/0.46    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.22/0.46    inference(nnf_transformation,[],[f15])).
% 0.22/0.46  fof(f15,plain,(
% 0.22/0.46    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.46    inference(ennf_transformation,[],[f7])).
% 0.22/0.46  fof(f7,axiom,(
% 0.22/0.46    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.22/0.46  fof(f67,plain,(
% 0.22/0.46    spl3_4 | ~spl3_1 | ~spl3_3),
% 0.22/0.46    inference(avatar_split_clause,[],[f62,f59,f49,f64])).
% 0.22/0.46  fof(f59,plain,(
% 0.22/0.46    spl3_3 <=> ! [X1,X0,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.46  fof(f62,plain,(
% 0.22/0.46    v1_relat_1(sK2) | (~spl3_1 | ~spl3_3)),
% 0.22/0.46    inference(resolution,[],[f60,f51])).
% 0.22/0.46  fof(f60,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) ) | ~spl3_3),
% 0.22/0.46    inference(avatar_component_clause,[],[f59])).
% 0.22/0.46  fof(f61,plain,(
% 0.22/0.46    spl3_3),
% 0.22/0.46    inference(avatar_split_clause,[],[f39,f59])).
% 0.22/0.46  fof(f39,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.46    inference(cnf_transformation,[],[f20])).
% 0.22/0.46  fof(f20,plain,(
% 0.22/0.46    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.46    inference(ennf_transformation,[],[f9])).
% 0.22/0.46  fof(f9,axiom,(
% 0.22/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.46  fof(f57,plain,(
% 0.22/0.46    ~spl3_2),
% 0.22/0.46    inference(avatar_split_clause,[],[f43,f54])).
% 0.22/0.46  fof(f43,plain,(
% 0.22/0.46    ~r1_tarski(k3_relat_1(sK2),k3_tarski(k2_tarski(sK0,sK1)))),
% 0.22/0.46    inference(definition_unfolding,[],[f29,f31])).
% 0.22/0.46  fof(f29,plain,(
% 0.22/0.46    ~r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1))),
% 0.22/0.46    inference(cnf_transformation,[],[f25])).
% 0.22/0.46  fof(f25,plain,(
% 0.22/0.46    ~r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f24])).
% 0.22/0.46  fof(f24,plain,(
% 0.22/0.46    ? [X0,X1,X2] : (~r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (~r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 0.22/0.46    introduced(choice_axiom,[])).
% 0.22/0.46  fof(f13,plain,(
% 0.22/0.46    ? [X0,X1,X2] : (~r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.46    inference(ennf_transformation,[],[f12])).
% 0.22/0.46  fof(f12,negated_conjecture,(
% 0.22/0.46    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)))),
% 0.22/0.46    inference(negated_conjecture,[],[f11])).
% 0.22/0.46  fof(f11,conjecture,(
% 0.22/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_relset_1)).
% 0.22/0.46  fof(f52,plain,(
% 0.22/0.46    spl3_1),
% 0.22/0.46    inference(avatar_split_clause,[],[f28,f49])).
% 0.22/0.46  fof(f28,plain,(
% 0.22/0.46    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.46    inference(cnf_transformation,[],[f25])).
% 0.22/0.46  % SZS output end Proof for theBenchmark
% 0.22/0.46  % (2570)------------------------------
% 0.22/0.46  % (2570)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.46  % (2570)Termination reason: Refutation
% 0.22/0.46  
% 0.22/0.46  % (2570)Memory used [KB]: 6268
% 0.22/0.46  % (2570)Time elapsed: 0.011 s
% 0.22/0.46  % (2570)------------------------------
% 0.22/0.46  % (2570)------------------------------
% 0.22/0.47  % (2562)Success in time 0.106 s
%------------------------------------------------------------------------------
