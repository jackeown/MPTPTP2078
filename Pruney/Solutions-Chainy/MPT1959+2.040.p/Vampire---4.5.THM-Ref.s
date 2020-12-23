%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:56 EST 2020

% Result     : Theorem 1.61s
% Output     : Refutation 1.78s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 294 expanded)
%              Number of leaves         :   39 ( 125 expanded)
%              Depth                    :    8
%              Number of atoms          :  513 (1211 expanded)
%              Number of equality atoms :   25 (  42 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f388,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f73,f78,f93,f98,f103,f113,f118,f130,f139,f140,f147,f172,f187,f194,f206,f212,f223,f232,f248,f259,f264,f275,f313,f347,f362,f365,f374,f377,f378,f387])).

fof(f387,plain,
    ( ~ spl8_15
    | ~ spl8_17 ),
    inference(avatar_contradiction_clause,[],[f381])).

fof(f381,plain,
    ( $false
    | ~ spl8_15
    | ~ spl8_17 ),
    inference(unit_resulting_resolution,[],[f160,f171,f66])).

fof(f66,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X1))
      | ~ v1_subset_1(X1,X1) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 != X1
      | ~ v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(f171,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f169])).

fof(f169,plain,
    ( spl8_17
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f160,plain,
    ( v1_subset_1(sK1,sK1)
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl8_15
  <=> v1_subset_1(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f378,plain,
    ( sK1 != u1_struct_0(sK0)
    | v1_subset_1(sK1,sK1)
    | ~ v1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f377,plain,
    ( ~ spl8_31
    | spl8_39 ),
    inference(avatar_contradiction_clause,[],[f375])).

fof(f375,plain,
    ( $false
    | ~ spl8_31
    | spl8_39 ),
    inference(unit_resulting_resolution,[],[f312,f373,f68])).

fof(f68,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,k1_zfmisc_1(X0))
      | ~ r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f373,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl8_39 ),
    inference(avatar_component_clause,[],[f371])).

fof(f371,plain,
    ( spl8_39
  <=> r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_39])])).

fof(f312,plain,
    ( r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl8_31 ),
    inference(avatar_component_clause,[],[f310])).

fof(f310,plain,
    ( spl8_31
  <=> r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).

fof(f374,plain,
    ( spl8_11
    | ~ spl8_39
    | spl8_38 ),
    inference(avatar_split_clause,[],[f367,f359,f371,f127])).

fof(f127,plain,
    ( spl8_11
  <=> v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f359,plain,
    ( spl8_38
  <=> m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).

fof(f367,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | spl8_38 ),
    inference(resolution,[],[f361,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f361,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl8_38 ),
    inference(avatar_component_clause,[],[f359])).

fof(f365,plain,
    ( spl8_14
    | ~ spl8_38
    | ~ spl8_10
    | ~ spl8_24
    | spl8_37 ),
    inference(avatar_split_clause,[],[f363,f355,f221,f115,f359,f144])).

fof(f144,plain,
    ( spl8_14
  <=> sK1 = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f115,plain,
    ( spl8_10
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f221,plain,
    ( spl8_24
  <=> ! [X1] :
        ( r2_hidden(X1,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f355,plain,
    ( spl8_37
  <=> r2_hidden(sK5(u1_struct_0(sK0),u1_struct_0(sK0),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).

fof(f363,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = u1_struct_0(sK0)
    | ~ spl8_24
    | spl8_37 ),
    inference(resolution,[],[f357,f241])).

fof(f241,plain,
    ( ! [X4,X3] :
        ( r2_hidden(sK5(u1_struct_0(sK0),X3,X4),sK1)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | X3 = X4 )
    | ~ spl8_24 ),
    inference(resolution,[],[f222,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X1 = X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                <=> r2_hidden(X3,X2) ) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_subset_1)).

fof(f222,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_hidden(X1,sK1) )
    | ~ spl8_24 ),
    inference(avatar_component_clause,[],[f221])).

fof(f357,plain,
    ( ~ r2_hidden(sK5(u1_struct_0(sK0),u1_struct_0(sK0),sK1),sK1)
    | spl8_37 ),
    inference(avatar_component_clause,[],[f355])).

fof(f362,plain,
    ( ~ spl8_37
    | spl8_14
    | ~ spl8_38
    | ~ spl8_19
    | ~ spl8_36 ),
    inference(avatar_split_clause,[],[f351,f345,f191,f359,f144,f355])).

fof(f191,plain,
    ( spl8_19
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f345,plain,
    ( spl8_36
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK5(u1_struct_0(sK0),X0,sK1),X0)
        | sK1 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).

fof(f351,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = u1_struct_0(sK0)
    | ~ r2_hidden(sK5(u1_struct_0(sK0),u1_struct_0(sK0),sK1),sK1)
    | ~ spl8_19
    | ~ spl8_36 ),
    inference(resolution,[],[f346,f195])).

fof(f195,plain,
    ( ! [X0] :
        ( r2_hidden(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK1) )
    | ~ spl8_19 ),
    inference(resolution,[],[f193,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f193,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f191])).

fof(f346,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5(u1_struct_0(sK0),X0,sK1),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | sK1 = X0 )
    | ~ spl8_36 ),
    inference(avatar_component_clause,[],[f345])).

fof(f347,plain,
    ( spl8_36
    | ~ spl8_10
    | ~ spl8_24 ),
    inference(avatar_split_clause,[],[f343,f221,f115,f345])).

fof(f343,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | sK1 = X0
        | ~ r2_hidden(sK5(u1_struct_0(sK0),X0,sK1),X0) )
    | ~ spl8_24 ),
    inference(duplicate_literal_removal,[],[f341])).

fof(f341,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | sK1 = X0
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK5(u1_struct_0(sK0),X0,sK1),X0)
        | sK1 = X0 )
    | ~ spl8_24 ),
    inference(resolution,[],[f241,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(sK5(X0,X1,X2),X1)
      | X1 = X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f313,plain,
    ( spl8_31
    | ~ spl8_19
    | ~ spl8_26 ),
    inference(avatar_split_clause,[],[f302,f262,f191,f310])).

fof(f262,plain,
    ( spl8_26
  <=> ! [X6] :
        ( r2_hidden(X6,sK1)
        | ~ r2_hidden(X6,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f302,plain,
    ( r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl8_19
    | ~ spl8_26 ),
    inference(duplicate_literal_removal,[],[f298])).

fof(f298,plain,
    ( r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0))
    | r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl8_19
    | ~ spl8_26 ),
    inference(resolution,[],[f269,f198])).

fof(f198,plain,
    ( ! [X3] :
        ( ~ r2_hidden(sK6(X3,u1_struct_0(sK0)),sK1)
        | r1_tarski(X3,u1_struct_0(sK0)) )
    | ~ spl8_19 ),
    inference(resolution,[],[f195,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f269,plain,
    ( ! [X3] :
        ( r2_hidden(sK6(u1_struct_0(sK0),X3),sK1)
        | r1_tarski(u1_struct_0(sK0),X3) )
    | ~ spl8_26 ),
    inference(resolution,[],[f263,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f263,plain,
    ( ! [X6] :
        ( ~ r2_hidden(X6,u1_struct_0(sK0))
        | r2_hidden(X6,sK1) )
    | ~ spl8_26 ),
    inference(avatar_component_clause,[],[f262])).

fof(f275,plain,
    ( sK1 != u1_struct_0(sK0)
    | r2_hidden(k3_yellow_0(sK0),sK1)
    | ~ r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f264,plain,
    ( spl8_20
    | spl8_26
    | ~ spl8_24 ),
    inference(avatar_split_clause,[],[f243,f221,f262,f200])).

fof(f200,plain,
    ( spl8_20
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f243,plain,
    ( ! [X6] :
        ( r2_hidden(X6,sK1)
        | ~ r2_hidden(X6,u1_struct_0(sK0))
        | v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl8_24 ),
    inference(resolution,[],[f222,f51])).

fof(f259,plain,
    ( spl8_1
    | ~ spl8_21 ),
    inference(avatar_contradiction_clause,[],[f251])).

fof(f251,plain,
    ( $false
    | spl8_1
    | ~ spl8_21 ),
    inference(unit_resulting_resolution,[],[f72,f205,f47])).

fof(f47,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f205,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK1)
    | ~ spl8_21 ),
    inference(avatar_component_clause,[],[f204])).

fof(f204,plain,
    ( spl8_21
  <=> ! [X0] : ~ r2_hidden(X0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f72,plain,
    ( ~ v1_xboole_0(sK1)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl8_1
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f248,plain,
    ( spl8_20
    | spl8_25
    | ~ spl8_23 ),
    inference(avatar_split_clause,[],[f235,f217,f245,f200])).

fof(f245,plain,
    ( spl8_25
  <=> r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f217,plain,
    ( spl8_23
  <=> m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f235,plain,
    ( r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl8_23 ),
    inference(resolution,[],[f218,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f218,plain,
    ( m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))
    | ~ spl8_23 ),
    inference(avatar_component_clause,[],[f217])).

fof(f232,plain,
    ( ~ spl8_7
    | spl8_23 ),
    inference(avatar_contradiction_clause,[],[f225])).

fof(f225,plain,
    ( $false
    | ~ spl8_7
    | spl8_23 ),
    inference(unit_resulting_resolution,[],[f102,f219,f39])).

fof(f39,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow_0)).

fof(f219,plain,
    ( ~ m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))
    | spl8_23 ),
    inference(avatar_component_clause,[],[f217])).

fof(f102,plain,
    ( l1_orders_2(sK0)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl8_7
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f223,plain,
    ( spl8_2
    | ~ spl8_7
    | ~ spl8_6
    | ~ spl8_5
    | ~ spl8_13
    | ~ spl8_23
    | spl8_24
    | ~ spl8_22 ),
    inference(avatar_split_clause,[],[f215,f210,f221,f217,f136,f90,f95,f100,f75])).

fof(f75,plain,
    ( spl8_2
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f95,plain,
    ( spl8_6
  <=> v1_yellow_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f90,plain,
    ( spl8_5
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f136,plain,
    ( spl8_13
  <=> r2_hidden(k3_yellow_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f210,plain,
    ( spl8_22
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X1,sK1)
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f215,plain,
    ( ! [X1] :
        ( r2_hidden(X1,sK1)
        | ~ m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))
        | ~ r2_hidden(k3_yellow_0(sK0),sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v5_orders_2(sK0)
        | ~ v1_yellow_0(sK0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_22 ),
    inference(duplicate_literal_removal,[],[f214])).

fof(f214,plain,
    ( ! [X1] :
        ( r2_hidden(X1,sK1)
        | ~ m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))
        | ~ r2_hidden(k3_yellow_0(sK0),sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v5_orders_2(sK0)
        | ~ v1_yellow_0(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl8_22 ),
    inference(resolution,[],[f211,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_orders_2(X0,k3_yellow_0(X0),X1)
      | ~ v5_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,k3_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,k3_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,k3_yellow_0(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_yellow_0)).

fof(f211,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | r2_hidden(X1,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl8_22 ),
    inference(avatar_component_clause,[],[f210])).

fof(f212,plain,
    ( ~ spl8_9
    | spl8_22
    | ~ spl8_7
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f121,f115,f100,f210,f110])).

fof(f110,plain,
    ( spl8_9
  <=> v13_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f121,plain,
    ( ! [X0,X1] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK1)
        | ~ r1_orders_2(sK0,X0,X1)
        | r2_hidden(X1,sK1)
        | ~ v13_waybel_0(sK1,sK0) )
    | ~ spl8_10 ),
    inference(resolution,[],[f117,f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(X2,X1)
      | ~ r1_orders_2(X0,X2,X3)
      | r2_hidden(X3,X1)
      | ~ v13_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r1_orders_2(X0,X2,X3)
                        & r2_hidden(X2,X1) )
                     => r2_hidden(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_waybel_0)).

fof(f117,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f115])).

fof(f206,plain,
    ( ~ spl8_20
    | spl8_21
    | ~ spl8_19 ),
    inference(avatar_split_clause,[],[f196,f191,f204,f200])).

fof(f196,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl8_19 ),
    inference(resolution,[],[f195,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f194,plain,
    ( spl8_19
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f188,f184,f191])).

fof(f184,plain,
    ( spl8_18
  <=> r2_hidden(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f188,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl8_18 ),
    inference(resolution,[],[f186,f67])).

fof(f67,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f186,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f184])).

fof(f187,plain,
    ( spl8_11
    | spl8_18
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f125,f115,f184,f127])).

fof(f125,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_10 ),
    inference(resolution,[],[f117,f52])).

fof(f172,plain,
    ( spl8_17
    | ~ spl8_10
    | ~ spl8_14 ),
    inference(avatar_split_clause,[],[f151,f144,f115,f169])).

fof(f151,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl8_10
    | ~ spl8_14 ),
    inference(backward_demodulation,[],[f117,f146])).

fof(f146,plain,
    ( sK1 = u1_struct_0(sK0)
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f144])).

fof(f147,plain,
    ( spl8_12
    | spl8_14
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f123,f115,f144,f132])).

fof(f132,plain,
    ( spl8_12
  <=> v1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f123,plain,
    ( sK1 = u1_struct_0(sK0)
    | v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl8_10 ),
    inference(resolution,[],[f117,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f140,plain,
    ( ~ spl8_12
    | spl8_13 ),
    inference(avatar_split_clause,[],[f28,f136,f132])).

fof(f28,plain,
    ( r2_hidden(k3_yellow_0(sK0),sK1)
    | ~ v1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <~> ~ r2_hidden(k3_yellow_0(X0),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <~> ~ r2_hidden(k3_yellow_0(X0),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & v2_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,u1_struct_0(X0))
            <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ( v1_subset_1(X1,u1_struct_0(X0))
          <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_7)).

fof(f139,plain,
    ( spl8_12
    | ~ spl8_13 ),
    inference(avatar_split_clause,[],[f27,f136,f132])).

fof(f27,plain,
    ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
    | v1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f130,plain,
    ( ~ spl8_11
    | spl8_1
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f124,f115,f70,f127])).

fof(f124,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_10 ),
    inference(resolution,[],[f117,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f118,plain,(
    spl8_10 ),
    inference(avatar_split_clause,[],[f32,f115])).

fof(f32,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f113,plain,(
    spl8_9 ),
    inference(avatar_split_clause,[],[f31,f110])).

fof(f31,plain,(
    v13_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f103,plain,(
    spl8_7 ),
    inference(avatar_split_clause,[],[f38,f100])).

fof(f38,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f98,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f37,f95])).

fof(f37,plain,(
    v1_yellow_0(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f93,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f36,f90])).

fof(f36,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f78,plain,(
    ~ spl8_2 ),
    inference(avatar_split_clause,[],[f33,f75])).

fof(f33,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f73,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f29,f70])).

fof(f29,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:39:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.49  % (5909)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.51  % (5901)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.51  % (5902)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.51  % (5921)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.52  % (5906)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (5914)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.53  % (5919)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.53  % (5924)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.53  % (5922)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.53  % (5913)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (5915)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.53  % (5905)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.53  % (5912)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.54  % (5907)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.54  % (5927)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.54  % (5910)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.54  % (5928)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.54  % (5927)Refutation not found, incomplete strategy% (5927)------------------------------
% 0.20/0.54  % (5927)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (5927)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (5927)Memory used [KB]: 10746
% 0.20/0.54  % (5927)Time elapsed: 0.134 s
% 0.20/0.54  % (5927)------------------------------
% 0.20/0.54  % (5927)------------------------------
% 0.20/0.54  % (5920)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.55  % (5930)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.55  % (5926)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.55  % (5904)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.56  % (5908)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.56  % (5918)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.56  % (5917)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.57  % (5903)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.57  % (5923)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.57  % (5925)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.57  % (5911)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.57  % (5929)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.61/0.59  % (5916)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.61/0.59  % (5923)Refutation found. Thanks to Tanya!
% 1.61/0.59  % SZS status Theorem for theBenchmark
% 1.61/0.59  % SZS output start Proof for theBenchmark
% 1.78/0.59  fof(f388,plain,(
% 1.78/0.59    $false),
% 1.78/0.59    inference(avatar_sat_refutation,[],[f73,f78,f93,f98,f103,f113,f118,f130,f139,f140,f147,f172,f187,f194,f206,f212,f223,f232,f248,f259,f264,f275,f313,f347,f362,f365,f374,f377,f378,f387])).
% 1.78/0.59  fof(f387,plain,(
% 1.78/0.59    ~spl8_15 | ~spl8_17),
% 1.78/0.59    inference(avatar_contradiction_clause,[],[f381])).
% 1.78/0.59  fof(f381,plain,(
% 1.78/0.59    $false | (~spl8_15 | ~spl8_17)),
% 1.78/0.59    inference(unit_resulting_resolution,[],[f160,f171,f66])).
% 1.78/0.59  fof(f66,plain,(
% 1.78/0.59    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(X1)) | ~v1_subset_1(X1,X1)) )),
% 1.78/0.59    inference(equality_resolution,[],[f54])).
% 1.78/0.59  fof(f54,plain,(
% 1.78/0.59    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 != X1 | ~v1_subset_1(X1,X0)) )),
% 1.78/0.59    inference(cnf_transformation,[],[f21])).
% 1.78/0.59  fof(f21,plain,(
% 1.78/0.59    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.78/0.59    inference(ennf_transformation,[],[f10])).
% 1.78/0.59  fof(f10,axiom,(
% 1.78/0.59    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 1.78/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).
% 1.78/0.59  fof(f171,plain,(
% 1.78/0.59    m1_subset_1(sK1,k1_zfmisc_1(sK1)) | ~spl8_17),
% 1.78/0.59    inference(avatar_component_clause,[],[f169])).
% 1.78/0.59  fof(f169,plain,(
% 1.78/0.59    spl8_17 <=> m1_subset_1(sK1,k1_zfmisc_1(sK1))),
% 1.78/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 1.78/0.59  fof(f160,plain,(
% 1.78/0.59    v1_subset_1(sK1,sK1) | ~spl8_15),
% 1.78/0.59    inference(avatar_component_clause,[],[f159])).
% 1.78/0.59  fof(f159,plain,(
% 1.78/0.59    spl8_15 <=> v1_subset_1(sK1,sK1)),
% 1.78/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 1.78/0.59  fof(f378,plain,(
% 1.78/0.59    sK1 != u1_struct_0(sK0) | v1_subset_1(sK1,sK1) | ~v1_subset_1(sK1,u1_struct_0(sK0))),
% 1.78/0.59    introduced(theory_tautology_sat_conflict,[])).
% 1.78/0.59  fof(f377,plain,(
% 1.78/0.59    ~spl8_31 | spl8_39),
% 1.78/0.59    inference(avatar_contradiction_clause,[],[f375])).
% 1.78/0.59  fof(f375,plain,(
% 1.78/0.59    $false | (~spl8_31 | spl8_39)),
% 1.78/0.59    inference(unit_resulting_resolution,[],[f312,f373,f68])).
% 1.78/0.59  fof(f68,plain,(
% 1.78/0.59    ( ! [X2,X0] : (r2_hidden(X2,k1_zfmisc_1(X0)) | ~r1_tarski(X2,X0)) )),
% 1.78/0.59    inference(equality_resolution,[],[f61])).
% 1.78/0.59  fof(f61,plain,(
% 1.78/0.59    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.78/0.59    inference(cnf_transformation,[],[f3])).
% 1.78/0.59  fof(f3,axiom,(
% 1.78/0.59    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.78/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.78/0.59  fof(f373,plain,(
% 1.78/0.59    ~r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | spl8_39),
% 1.78/0.59    inference(avatar_component_clause,[],[f371])).
% 1.78/0.59  fof(f371,plain,(
% 1.78/0.59    spl8_39 <=> r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.78/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_39])])).
% 1.78/0.59  fof(f312,plain,(
% 1.78/0.59    r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) | ~spl8_31),
% 1.78/0.59    inference(avatar_component_clause,[],[f310])).
% 1.78/0.59  fof(f310,plain,(
% 1.78/0.59    spl8_31 <=> r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0))),
% 1.78/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).
% 1.78/0.59  fof(f374,plain,(
% 1.78/0.59    spl8_11 | ~spl8_39 | spl8_38),
% 1.78/0.59    inference(avatar_split_clause,[],[f367,f359,f371,f127])).
% 1.78/0.59  fof(f127,plain,(
% 1.78/0.59    spl8_11 <=> v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.78/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 1.78/0.59  fof(f359,plain,(
% 1.78/0.59    spl8_38 <=> m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.78/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).
% 1.78/0.59  fof(f367,plain,(
% 1.78/0.59    ~r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) | spl8_38),
% 1.78/0.59    inference(resolution,[],[f361,f51])).
% 1.78/0.59  fof(f51,plain,(
% 1.78/0.59    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.78/0.59    inference(cnf_transformation,[],[f20])).
% 1.78/0.59  fof(f20,plain,(
% 1.78/0.59    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.78/0.59    inference(ennf_transformation,[],[f4])).
% 1.78/0.59  fof(f4,axiom,(
% 1.78/0.59    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.78/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 1.78/0.59  fof(f361,plain,(
% 1.78/0.59    ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | spl8_38),
% 1.78/0.59    inference(avatar_component_clause,[],[f359])).
% 1.78/0.59  fof(f365,plain,(
% 1.78/0.59    spl8_14 | ~spl8_38 | ~spl8_10 | ~spl8_24 | spl8_37),
% 1.78/0.59    inference(avatar_split_clause,[],[f363,f355,f221,f115,f359,f144])).
% 1.78/0.59  fof(f144,plain,(
% 1.78/0.59    spl8_14 <=> sK1 = u1_struct_0(sK0)),
% 1.78/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 1.78/0.59  fof(f115,plain,(
% 1.78/0.59    spl8_10 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.78/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 1.78/0.59  fof(f221,plain,(
% 1.78/0.59    spl8_24 <=> ! [X1] : (r2_hidden(X1,sK1) | ~m1_subset_1(X1,u1_struct_0(sK0)))),
% 1.78/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).
% 1.78/0.59  fof(f355,plain,(
% 1.78/0.59    spl8_37 <=> r2_hidden(sK5(u1_struct_0(sK0),u1_struct_0(sK0),sK1),sK1)),
% 1.78/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).
% 1.78/0.59  fof(f363,plain,(
% 1.78/0.59    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = u1_struct_0(sK0) | (~spl8_24 | spl8_37)),
% 1.78/0.59    inference(resolution,[],[f357,f241])).
% 1.78/0.59  fof(f241,plain,(
% 1.78/0.59    ( ! [X4,X3] : (r2_hidden(sK5(u1_struct_0(sK0),X3,X4),sK1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | X3 = X4) ) | ~spl8_24),
% 1.78/0.59    inference(resolution,[],[f222,f57])).
% 1.78/0.59  fof(f57,plain,(
% 1.78/0.59    ( ! [X2,X0,X1] : (m1_subset_1(sK5(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | X1 = X2) )),
% 1.78/0.59    inference(cnf_transformation,[],[f23])).
% 1.78/0.59  fof(f23,plain,(
% 1.78/0.59    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.78/0.59    inference(flattening,[],[f22])).
% 1.78/0.59  fof(f22,plain,(
% 1.78/0.59    ! [X0,X1] : (! [X2] : ((X1 = X2 | ? [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.78/0.59    inference(ennf_transformation,[],[f5])).
% 1.78/0.59  fof(f5,axiom,(
% 1.78/0.59    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 1.78/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_subset_1)).
% 1.78/0.59  fof(f222,plain,(
% 1.78/0.59    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | r2_hidden(X1,sK1)) ) | ~spl8_24),
% 1.78/0.59    inference(avatar_component_clause,[],[f221])).
% 1.78/0.59  fof(f357,plain,(
% 1.78/0.59    ~r2_hidden(sK5(u1_struct_0(sK0),u1_struct_0(sK0),sK1),sK1) | spl8_37),
% 1.78/0.59    inference(avatar_component_clause,[],[f355])).
% 1.78/0.59  fof(f362,plain,(
% 1.78/0.59    ~spl8_37 | spl8_14 | ~spl8_38 | ~spl8_19 | ~spl8_36),
% 1.78/0.59    inference(avatar_split_clause,[],[f351,f345,f191,f359,f144,f355])).
% 1.78/0.59  fof(f191,plain,(
% 1.78/0.59    spl8_19 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 1.78/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).
% 1.78/0.59  fof(f345,plain,(
% 1.78/0.59    spl8_36 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK5(u1_struct_0(sK0),X0,sK1),X0) | sK1 = X0)),
% 1.78/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).
% 1.78/0.59  fof(f351,plain,(
% 1.78/0.59    ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = u1_struct_0(sK0) | ~r2_hidden(sK5(u1_struct_0(sK0),u1_struct_0(sK0),sK1),sK1) | (~spl8_19 | ~spl8_36)),
% 1.78/0.59    inference(resolution,[],[f346,f195])).
% 1.78/0.59  fof(f195,plain,(
% 1.78/0.59    ( ! [X0] : (r2_hidden(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,sK1)) ) | ~spl8_19),
% 1.78/0.59    inference(resolution,[],[f193,f58])).
% 1.78/0.59  fof(f58,plain,(
% 1.78/0.59    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.78/0.59    inference(cnf_transformation,[],[f24])).
% 1.78/0.59  fof(f24,plain,(
% 1.78/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.78/0.59    inference(ennf_transformation,[],[f2])).
% 1.78/0.59  fof(f2,axiom,(
% 1.78/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.78/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.78/0.59  fof(f193,plain,(
% 1.78/0.59    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl8_19),
% 1.78/0.59    inference(avatar_component_clause,[],[f191])).
% 1.78/0.59  fof(f346,plain,(
% 1.78/0.59    ( ! [X0] : (~r2_hidden(sK5(u1_struct_0(sK0),X0,sK1),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = X0) ) | ~spl8_36),
% 1.78/0.59    inference(avatar_component_clause,[],[f345])).
% 1.78/0.59  fof(f347,plain,(
% 1.78/0.59    spl8_36 | ~spl8_10 | ~spl8_24),
% 1.78/0.59    inference(avatar_split_clause,[],[f343,f221,f115,f345])).
% 1.78/0.59  fof(f343,plain,(
% 1.78/0.59    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = X0 | ~r2_hidden(sK5(u1_struct_0(sK0),X0,sK1),X0)) ) | ~spl8_24),
% 1.78/0.59    inference(duplicate_literal_removal,[],[f341])).
% 1.78/0.59  fof(f341,plain,(
% 1.78/0.59    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = X0 | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK5(u1_struct_0(sK0),X0,sK1),X0) | sK1 = X0) ) | ~spl8_24),
% 1.78/0.59    inference(resolution,[],[f241,f56])).
% 1.78/0.59  fof(f56,plain,(
% 1.78/0.59    ( ! [X2,X0,X1] : (~r2_hidden(sK5(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(sK5(X0,X1,X2),X1) | X1 = X2) )),
% 1.78/0.59    inference(cnf_transformation,[],[f23])).
% 1.78/0.59  fof(f313,plain,(
% 1.78/0.59    spl8_31 | ~spl8_19 | ~spl8_26),
% 1.78/0.59    inference(avatar_split_clause,[],[f302,f262,f191,f310])).
% 1.78/0.59  fof(f262,plain,(
% 1.78/0.59    spl8_26 <=> ! [X6] : (r2_hidden(X6,sK1) | ~r2_hidden(X6,u1_struct_0(sK0)))),
% 1.78/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).
% 1.78/0.59  fof(f302,plain,(
% 1.78/0.59    r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) | (~spl8_19 | ~spl8_26)),
% 1.78/0.59    inference(duplicate_literal_removal,[],[f298])).
% 1.78/0.59  fof(f298,plain,(
% 1.78/0.59    r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) | r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) | (~spl8_19 | ~spl8_26)),
% 1.78/0.59    inference(resolution,[],[f269,f198])).
% 1.78/0.59  fof(f198,plain,(
% 1.78/0.59    ( ! [X3] : (~r2_hidden(sK6(X3,u1_struct_0(sK0)),sK1) | r1_tarski(X3,u1_struct_0(sK0))) ) | ~spl8_19),
% 1.78/0.59    inference(resolution,[],[f195,f60])).
% 1.78/0.59  fof(f60,plain,(
% 1.78/0.59    ( ! [X0,X1] : (~r2_hidden(sK6(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.78/0.59    inference(cnf_transformation,[],[f24])).
% 1.78/0.59  fof(f269,plain,(
% 1.78/0.59    ( ! [X3] : (r2_hidden(sK6(u1_struct_0(sK0),X3),sK1) | r1_tarski(u1_struct_0(sK0),X3)) ) | ~spl8_26),
% 1.78/0.59    inference(resolution,[],[f263,f59])).
% 1.78/0.59  fof(f59,plain,(
% 1.78/0.59    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.78/0.59    inference(cnf_transformation,[],[f24])).
% 1.78/0.59  fof(f263,plain,(
% 1.78/0.59    ( ! [X6] : (~r2_hidden(X6,u1_struct_0(sK0)) | r2_hidden(X6,sK1)) ) | ~spl8_26),
% 1.78/0.59    inference(avatar_component_clause,[],[f262])).
% 1.78/0.61  fof(f275,plain,(
% 1.78/0.61    sK1 != u1_struct_0(sK0) | r2_hidden(k3_yellow_0(sK0),sK1) | ~r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0))),
% 1.78/0.61    introduced(theory_tautology_sat_conflict,[])).
% 1.78/0.61  fof(f264,plain,(
% 1.78/0.61    spl8_20 | spl8_26 | ~spl8_24),
% 1.78/0.61    inference(avatar_split_clause,[],[f243,f221,f262,f200])).
% 1.78/0.61  fof(f200,plain,(
% 1.78/0.61    spl8_20 <=> v1_xboole_0(u1_struct_0(sK0))),
% 1.78/0.61    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).
% 1.78/0.61  fof(f243,plain,(
% 1.78/0.61    ( ! [X6] : (r2_hidden(X6,sK1) | ~r2_hidden(X6,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))) ) | ~spl8_24),
% 1.78/0.61    inference(resolution,[],[f222,f51])).
% 1.78/0.61  fof(f259,plain,(
% 1.78/0.61    spl8_1 | ~spl8_21),
% 1.78/0.61    inference(avatar_contradiction_clause,[],[f251])).
% 1.78/0.61  fof(f251,plain,(
% 1.78/0.61    $false | (spl8_1 | ~spl8_21)),
% 1.78/0.61    inference(unit_resulting_resolution,[],[f72,f205,f47])).
% 1.78/0.61  fof(f47,plain,(
% 1.78/0.61    ( ! [X0] : (r2_hidden(sK4(X0),X0) | v1_xboole_0(X0)) )),
% 1.78/0.61    inference(cnf_transformation,[],[f1])).
% 1.78/0.61  fof(f1,axiom,(
% 1.78/0.61    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.78/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.78/0.61  fof(f205,plain,(
% 1.78/0.61    ( ! [X0] : (~r2_hidden(X0,sK1)) ) | ~spl8_21),
% 1.78/0.61    inference(avatar_component_clause,[],[f204])).
% 1.78/0.61  fof(f204,plain,(
% 1.78/0.61    spl8_21 <=> ! [X0] : ~r2_hidden(X0,sK1)),
% 1.78/0.61    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).
% 1.78/0.61  fof(f72,plain,(
% 1.78/0.61    ~v1_xboole_0(sK1) | spl8_1),
% 1.78/0.61    inference(avatar_component_clause,[],[f70])).
% 1.78/0.61  fof(f70,plain,(
% 1.78/0.61    spl8_1 <=> v1_xboole_0(sK1)),
% 1.78/0.61    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.78/0.61  fof(f248,plain,(
% 1.78/0.61    spl8_20 | spl8_25 | ~spl8_23),
% 1.78/0.61    inference(avatar_split_clause,[],[f235,f217,f245,f200])).
% 1.78/0.61  fof(f245,plain,(
% 1.78/0.61    spl8_25 <=> r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0))),
% 1.78/0.61    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).
% 1.78/0.61  fof(f217,plain,(
% 1.78/0.61    spl8_23 <=> m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))),
% 1.78/0.61    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).
% 1.78/0.61  fof(f235,plain,(
% 1.78/0.61    r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | ~spl8_23),
% 1.78/0.61    inference(resolution,[],[f218,f52])).
% 1.78/0.61  fof(f52,plain,(
% 1.78/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.78/0.61    inference(cnf_transformation,[],[f20])).
% 1.78/0.61  fof(f218,plain,(
% 1.78/0.61    m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) | ~spl8_23),
% 1.78/0.61    inference(avatar_component_clause,[],[f217])).
% 1.78/0.61  fof(f232,plain,(
% 1.78/0.61    ~spl8_7 | spl8_23),
% 1.78/0.61    inference(avatar_contradiction_clause,[],[f225])).
% 1.78/0.61  fof(f225,plain,(
% 1.78/0.61    $false | (~spl8_7 | spl8_23)),
% 1.78/0.61    inference(unit_resulting_resolution,[],[f102,f219,f39])).
% 1.78/0.61  fof(f39,plain,(
% 1.78/0.61    ( ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.78/0.61    inference(cnf_transformation,[],[f15])).
% 1.78/0.61  fof(f15,plain,(
% 1.78/0.61    ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 1.78/0.61    inference(ennf_transformation,[],[f7])).
% 1.78/0.61  fof(f7,axiom,(
% 1.78/0.61    ! [X0] : (l1_orders_2(X0) => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)))),
% 1.78/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow_0)).
% 1.78/0.61  fof(f219,plain,(
% 1.78/0.61    ~m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) | spl8_23),
% 1.78/0.61    inference(avatar_component_clause,[],[f217])).
% 1.78/0.61  fof(f102,plain,(
% 1.78/0.61    l1_orders_2(sK0) | ~spl8_7),
% 1.78/0.61    inference(avatar_component_clause,[],[f100])).
% 1.78/0.61  fof(f100,plain,(
% 1.78/0.61    spl8_7 <=> l1_orders_2(sK0)),
% 1.78/0.61    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 1.78/0.61  fof(f223,plain,(
% 1.78/0.61    spl8_2 | ~spl8_7 | ~spl8_6 | ~spl8_5 | ~spl8_13 | ~spl8_23 | spl8_24 | ~spl8_22),
% 1.78/0.61    inference(avatar_split_clause,[],[f215,f210,f221,f217,f136,f90,f95,f100,f75])).
% 1.78/0.61  fof(f75,plain,(
% 1.78/0.61    spl8_2 <=> v2_struct_0(sK0)),
% 1.78/0.61    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 1.78/0.61  fof(f95,plain,(
% 1.78/0.61    spl8_6 <=> v1_yellow_0(sK0)),
% 1.78/0.61    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 1.78/0.61  fof(f90,plain,(
% 1.78/0.61    spl8_5 <=> v5_orders_2(sK0)),
% 1.78/0.61    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 1.78/0.61  fof(f136,plain,(
% 1.78/0.61    spl8_13 <=> r2_hidden(k3_yellow_0(sK0),sK1)),
% 1.78/0.61    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 1.78/0.61  fof(f210,plain,(
% 1.78/0.61    spl8_22 <=> ! [X1,X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X1,sK1) | ~r1_orders_2(sK0,X0,X1) | ~r2_hidden(X0,sK1) | ~m1_subset_1(X1,u1_struct_0(sK0)))),
% 1.78/0.61    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).
% 1.78/0.61  fof(f215,plain,(
% 1.78/0.61    ( ! [X1] : (r2_hidden(X1,sK1) | ~m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) | ~r2_hidden(k3_yellow_0(sK0),sK1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v5_orders_2(sK0) | ~v1_yellow_0(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl8_22),
% 1.78/0.61    inference(duplicate_literal_removal,[],[f214])).
% 1.78/0.61  fof(f214,plain,(
% 1.78/0.61    ( ! [X1] : (r2_hidden(X1,sK1) | ~m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) | ~r2_hidden(k3_yellow_0(sK0),sK1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v5_orders_2(sK0) | ~v1_yellow_0(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | v2_struct_0(sK0)) ) | ~spl8_22),
% 1.78/0.61    inference(resolution,[],[f211,f46])).
% 1.78/0.61  fof(f46,plain,(
% 1.78/0.61    ( ! [X0,X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~v5_orders_2(X0) | ~v1_yellow_0(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0)) )),
% 1.78/0.61    inference(cnf_transformation,[],[f19])).
% 1.78/0.61  fof(f19,plain,(
% 1.78/0.61    ! [X0] : (! [X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 1.78/0.61    inference(flattening,[],[f18])).
% 1.78/0.61  fof(f18,plain,(
% 1.78/0.61    ! [X0] : (! [X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 1.78/0.61    inference(ennf_transformation,[],[f8])).
% 1.78/0.61  fof(f8,axiom,(
% 1.78/0.61    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_orders_2(X0,k3_yellow_0(X0),X1)))),
% 1.78/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_yellow_0)).
% 1.78/0.61  fof(f211,plain,(
% 1.78/0.61    ( ! [X0,X1] : (~r1_orders_2(sK0,X0,X1) | r2_hidden(X1,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,sK1) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl8_22),
% 1.78/0.61    inference(avatar_component_clause,[],[f210])).
% 1.78/0.61  fof(f212,plain,(
% 1.78/0.61    ~spl8_9 | spl8_22 | ~spl8_7 | ~spl8_10),
% 1.78/0.61    inference(avatar_split_clause,[],[f121,f115,f100,f210,f110])).
% 1.78/0.61  fof(f110,plain,(
% 1.78/0.61    spl8_9 <=> v13_waybel_0(sK1,sK0)),
% 1.78/0.61    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 1.78/0.61  fof(f121,plain,(
% 1.78/0.61    ( ! [X0,X1] : (~l1_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X0,sK1) | ~r1_orders_2(sK0,X0,X1) | r2_hidden(X1,sK1) | ~v13_waybel_0(sK1,sK0)) ) | ~spl8_10),
% 1.78/0.61    inference(resolution,[],[f117,f44])).
% 1.78/0.61  fof(f44,plain,(
% 1.78/0.61    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_hidden(X2,X1) | ~r1_orders_2(X0,X2,X3) | r2_hidden(X3,X1) | ~v13_waybel_0(X1,X0)) )),
% 1.78/0.61    inference(cnf_transformation,[],[f17])).
% 1.78/0.61  fof(f17,plain,(
% 1.78/0.61    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.78/0.61    inference(flattening,[],[f16])).
% 1.78/0.61  fof(f16,plain,(
% 1.78/0.61    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : ((r2_hidden(X3,X1) | (~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.78/0.61    inference(ennf_transformation,[],[f9])).
% 1.78/0.61  fof(f9,axiom,(
% 1.78/0.61    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v13_waybel_0(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)))))))),
% 1.78/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_waybel_0)).
% 1.78/0.61  fof(f117,plain,(
% 1.78/0.61    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl8_10),
% 1.78/0.61    inference(avatar_component_clause,[],[f115])).
% 1.78/0.61  fof(f206,plain,(
% 1.78/0.61    ~spl8_20 | spl8_21 | ~spl8_19),
% 1.78/0.61    inference(avatar_split_clause,[],[f196,f191,f204,f200])).
% 1.78/0.61  fof(f196,plain,(
% 1.78/0.61    ( ! [X0] : (~r2_hidden(X0,sK1) | ~v1_xboole_0(u1_struct_0(sK0))) ) | ~spl8_19),
% 1.78/0.61    inference(resolution,[],[f195,f48])).
% 1.78/0.61  fof(f48,plain,(
% 1.78/0.61    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.78/0.61    inference(cnf_transformation,[],[f1])).
% 1.78/0.62  fof(f194,plain,(
% 1.78/0.62    spl8_19 | ~spl8_18),
% 1.78/0.62    inference(avatar_split_clause,[],[f188,f184,f191])).
% 1.78/0.62  fof(f184,plain,(
% 1.78/0.62    spl8_18 <=> r2_hidden(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.78/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 1.78/0.62  fof(f188,plain,(
% 1.78/0.62    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl8_18),
% 1.78/0.62    inference(resolution,[],[f186,f67])).
% 1.78/0.62  fof(f67,plain,(
% 1.78/0.62    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 1.78/0.62    inference(equality_resolution,[],[f62])).
% 1.78/0.62  fof(f62,plain,(
% 1.78/0.62    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.78/0.62    inference(cnf_transformation,[],[f3])).
% 1.78/0.62  fof(f186,plain,(
% 1.78/0.62    r2_hidden(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl8_18),
% 1.78/0.62    inference(avatar_component_clause,[],[f184])).
% 1.78/0.62  fof(f187,plain,(
% 1.78/0.62    spl8_11 | spl8_18 | ~spl8_10),
% 1.78/0.62    inference(avatar_split_clause,[],[f125,f115,f184,f127])).
% 1.78/0.62  fof(f125,plain,(
% 1.78/0.62    r2_hidden(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) | ~spl8_10),
% 1.78/0.62    inference(resolution,[],[f117,f52])).
% 1.78/0.62  fof(f172,plain,(
% 1.78/0.62    spl8_17 | ~spl8_10 | ~spl8_14),
% 1.78/0.62    inference(avatar_split_clause,[],[f151,f144,f115,f169])).
% 1.78/0.62  fof(f151,plain,(
% 1.78/0.62    m1_subset_1(sK1,k1_zfmisc_1(sK1)) | (~spl8_10 | ~spl8_14)),
% 1.78/0.62    inference(backward_demodulation,[],[f117,f146])).
% 1.78/0.62  fof(f146,plain,(
% 1.78/0.62    sK1 = u1_struct_0(sK0) | ~spl8_14),
% 1.78/0.62    inference(avatar_component_clause,[],[f144])).
% 1.78/0.62  fof(f147,plain,(
% 1.78/0.62    spl8_12 | spl8_14 | ~spl8_10),
% 1.78/0.62    inference(avatar_split_clause,[],[f123,f115,f144,f132])).
% 1.78/0.62  fof(f132,plain,(
% 1.78/0.62    spl8_12 <=> v1_subset_1(sK1,u1_struct_0(sK0))),
% 1.78/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 1.78/0.62  fof(f123,plain,(
% 1.78/0.62    sK1 = u1_struct_0(sK0) | v1_subset_1(sK1,u1_struct_0(sK0)) | ~spl8_10),
% 1.78/0.62    inference(resolution,[],[f117,f53])).
% 1.78/0.62  fof(f53,plain,(
% 1.78/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 1.78/0.62    inference(cnf_transformation,[],[f21])).
% 1.78/0.62  fof(f140,plain,(
% 1.78/0.62    ~spl8_12 | spl8_13),
% 1.78/0.62    inference(avatar_split_clause,[],[f28,f136,f132])).
% 1.78/0.62  fof(f28,plain,(
% 1.78/0.62    r2_hidden(k3_yellow_0(sK0),sK1) | ~v1_subset_1(sK1,u1_struct_0(sK0))),
% 1.78/0.62    inference(cnf_transformation,[],[f14])).
% 1.78/0.62  fof(f14,plain,(
% 1.78/0.62    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.78/0.62    inference(flattening,[],[f13])).
% 1.78/0.62  fof(f13,plain,(
% 1.78/0.62    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1))) & (l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.78/0.62    inference(ennf_transformation,[],[f12])).
% 1.78/0.62  fof(f12,negated_conjecture,(
% 1.78/0.62    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 1.78/0.62    inference(negated_conjecture,[],[f11])).
% 1.78/0.62  fof(f11,conjecture,(
% 1.78/0.62    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 1.78/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_7)).
% 1.78/0.62  fof(f139,plain,(
% 1.78/0.62    spl8_12 | ~spl8_13),
% 1.78/0.62    inference(avatar_split_clause,[],[f27,f136,f132])).
% 1.78/0.62  fof(f27,plain,(
% 1.78/0.62    ~r2_hidden(k3_yellow_0(sK0),sK1) | v1_subset_1(sK1,u1_struct_0(sK0))),
% 1.78/0.62    inference(cnf_transformation,[],[f14])).
% 1.78/0.62  fof(f130,plain,(
% 1.78/0.62    ~spl8_11 | spl8_1 | ~spl8_10),
% 1.78/0.62    inference(avatar_split_clause,[],[f124,f115,f70,f127])).
% 1.78/0.62  fof(f124,plain,(
% 1.78/0.62    v1_xboole_0(sK1) | ~v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) | ~spl8_10),
% 1.78/0.62    inference(resolution,[],[f117,f50])).
% 1.78/0.62  fof(f50,plain,(
% 1.78/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 1.78/0.62    inference(cnf_transformation,[],[f20])).
% 1.78/0.62  fof(f118,plain,(
% 1.78/0.62    spl8_10),
% 1.78/0.62    inference(avatar_split_clause,[],[f32,f115])).
% 1.78/0.62  fof(f32,plain,(
% 1.78/0.62    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.78/0.62    inference(cnf_transformation,[],[f14])).
% 1.78/0.62  fof(f113,plain,(
% 1.78/0.62    spl8_9),
% 1.78/0.62    inference(avatar_split_clause,[],[f31,f110])).
% 1.78/0.62  fof(f31,plain,(
% 1.78/0.62    v13_waybel_0(sK1,sK0)),
% 1.78/0.62    inference(cnf_transformation,[],[f14])).
% 1.78/0.62  fof(f103,plain,(
% 1.78/0.62    spl8_7),
% 1.78/0.62    inference(avatar_split_clause,[],[f38,f100])).
% 1.78/0.62  fof(f38,plain,(
% 1.78/0.62    l1_orders_2(sK0)),
% 1.78/0.62    inference(cnf_transformation,[],[f14])).
% 1.78/0.62  fof(f98,plain,(
% 1.78/0.62    spl8_6),
% 1.78/0.62    inference(avatar_split_clause,[],[f37,f95])).
% 1.78/0.62  fof(f37,plain,(
% 1.78/0.62    v1_yellow_0(sK0)),
% 1.78/0.62    inference(cnf_transformation,[],[f14])).
% 1.78/0.62  fof(f93,plain,(
% 1.78/0.62    spl8_5),
% 1.78/0.62    inference(avatar_split_clause,[],[f36,f90])).
% 1.78/0.62  fof(f36,plain,(
% 1.78/0.62    v5_orders_2(sK0)),
% 1.78/0.62    inference(cnf_transformation,[],[f14])).
% 1.78/0.62  fof(f78,plain,(
% 1.78/0.62    ~spl8_2),
% 1.78/0.62    inference(avatar_split_clause,[],[f33,f75])).
% 1.78/0.62  fof(f33,plain,(
% 1.78/0.62    ~v2_struct_0(sK0)),
% 1.78/0.62    inference(cnf_transformation,[],[f14])).
% 1.78/0.62  fof(f73,plain,(
% 1.78/0.62    ~spl8_1),
% 1.78/0.62    inference(avatar_split_clause,[],[f29,f70])).
% 1.78/0.62  fof(f29,plain,(
% 1.78/0.62    ~v1_xboole_0(sK1)),
% 1.78/0.62    inference(cnf_transformation,[],[f14])).
% 1.78/0.62  % SZS output end Proof for theBenchmark
% 1.78/0.62  % (5923)------------------------------
% 1.78/0.62  % (5923)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.78/0.62  % (5923)Termination reason: Refutation
% 1.78/0.62  
% 1.78/0.62  % (5923)Memory used [KB]: 11001
% 1.78/0.62  % (5923)Time elapsed: 0.184 s
% 1.78/0.62  % (5923)------------------------------
% 1.78/0.62  % (5923)------------------------------
% 1.78/0.62  % (5900)Success in time 0.249 s
%------------------------------------------------------------------------------
