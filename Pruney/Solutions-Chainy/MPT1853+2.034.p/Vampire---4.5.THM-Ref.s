%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:46 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  171 ( 326 expanded)
%              Number of leaves         :   31 ( 126 expanded)
%              Depth                    :   12
%              Number of atoms          :  614 (1026 expanded)
%              Number of equality atoms :   24 (  45 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f382,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f82,f86,f91,f95,f111,f118,f123,f139,f153,f164,f168,f176,f191,f195,f210,f228,f300,f311,f381])).

fof(f381,plain,
    ( ~ spl4_4
    | spl4_5
    | ~ spl4_8
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_16
    | ~ spl4_22 ),
    inference(avatar_contradiction_clause,[],[f380])).

fof(f380,plain,
    ( $false
    | ~ spl4_4
    | spl4_5
    | ~ spl4_8
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_16
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f379,f94])).

fof(f94,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl4_4
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f379,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | spl4_5
    | ~ spl4_8
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_16
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f378,f175])).

fof(f175,plain,
    ( v1_subset_1(k1_tarski(sK1),u1_struct_0(sK0))
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl4_15
  <=> v1_subset_1(k1_tarski(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f378,plain,
    ( ~ v1_subset_1(k1_tarski(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | spl4_5
    | ~ spl4_8
    | ~ spl4_14
    | ~ spl4_16
    | ~ spl4_22 ),
    inference(superposition,[],[f353,f163])).

fof(f163,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl4_14
  <=> k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f353,plain,
    ( ! [X5] :
        ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),X5),u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
    | spl4_5
    | ~ spl4_8
    | ~ spl4_16
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f352,f122])).

fof(f122,plain,
    ( v7_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl4_8
  <=> v7_struct_0(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f352,plain,
    ( ! [X5] :
        ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),X5),u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ v7_struct_0(k1_tex_2(sK0,sK1)) )
    | spl4_5
    | ~ spl4_16
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f351,f110])).

fof(f110,plain,
    ( ~ v2_struct_0(k1_tex_2(sK0,sK1))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl4_5
  <=> v2_struct_0(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f351,plain,
    ( ! [X5] :
        ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),X5),u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | v2_struct_0(k1_tex_2(sK0,sK1))
        | ~ v7_struct_0(k1_tex_2(sK0,sK1)) )
    | ~ spl4_16
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f341,f190])).

fof(f190,plain,
    ( l1_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f189])).

fof(f189,plain,
    ( spl4_16
  <=> l1_struct_0(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f341,plain,
    ( ! [X5] :
        ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),X5),u1_struct_0(sK0))
        | ~ l1_struct_0(k1_tex_2(sK0,sK1))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | v2_struct_0(k1_tex_2(sK0,sK1))
        | ~ v7_struct_0(k1_tex_2(sK0,sK1)) )
    | ~ spl4_22 ),
    inference(superposition,[],[f75,f227])).

fof(f227,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f226])).

fof(f226,plain,
    ( spl4_22
  <=> u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v7_struct_0(X0)
          | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v7_struct_0(X0)
          | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ~ ( v7_struct_0(X0)
              & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_tex_2)).

fof(f311,plain,
    ( spl4_5
    | ~ spl4_16
    | ~ spl4_28 ),
    inference(avatar_contradiction_clause,[],[f310])).

fof(f310,plain,
    ( $false
    | spl4_5
    | ~ spl4_16
    | ~ spl4_28 ),
    inference(subsumption_resolution,[],[f309,f110])).

fof(f309,plain,
    ( v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl4_16
    | ~ spl4_28 ),
    inference(subsumption_resolution,[],[f308,f190])).

fof(f308,plain,
    ( ~ l1_struct_0(k1_tex_2(sK0,sK1))
    | v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl4_28 ),
    inference(resolution,[],[f299,f70])).

fof(f70,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f299,plain,
    ( v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f298])).

fof(f298,plain,
    ( spl4_28
  <=> v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f300,plain,
    ( spl4_28
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | spl4_13
    | ~ spl4_14
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f292,f193,f162,f158,f137,f113,f93,f84,f298])).

fof(f84,plain,
    ( spl4_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f113,plain,
    ( spl4_6
  <=> v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f137,plain,
    ( spl4_10
  <=> m1_pre_topc(k1_tex_2(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f158,plain,
    ( spl4_13
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f193,plain,
    ( spl4_17
  <=> m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f292,plain,
    ( v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | spl4_13
    | ~ spl4_14
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f290,f291])).

fof(f291,plain,
    ( v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl4_2
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f277,f114])).

fof(f114,plain,
    ( v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f113])).

fof(f277,plain,
    ( v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ spl4_2
    | ~ spl4_10
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f276,f85])).

fof(f85,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f84])).

fof(f276,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ spl4_10
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f196,f138])).

fof(f138,plain,
    ( m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f137])).

fof(f196,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ spl4_17 ),
    inference(resolution,[],[f194,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_tex_2(X1,X0) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | v1_subset_1(X2,u1_struct_0(X0))
      | ~ v1_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tex_2)).

fof(f194,plain,
    ( m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f193])).

fof(f290,plain,
    ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))
    | ~ spl4_4
    | ~ spl4_6
    | spl4_13
    | ~ spl4_14
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f289,f255])).

fof(f255,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl4_13 ),
    inference(avatar_component_clause,[],[f158])).

fof(f289,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))
    | ~ spl4_4
    | ~ spl4_6
    | spl4_13
    | ~ spl4_14
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f198,f286])).

fof(f286,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl4_4
    | ~ spl4_6
    | spl4_13
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f280,f180])).

fof(f180,plain,
    ( ~ v1_subset_1(k1_tarski(sK1),u1_struct_0(sK0))
    | ~ spl4_6
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f179,f114])).

fof(f179,plain,
    ( ~ v1_subset_1(k1_tarski(sK1),u1_struct_0(sK0))
    | ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ spl4_14 ),
    inference(forward_demodulation,[],[f51,f163])).

fof(f51,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( v1_tex_2(k1_tex_2(X0,X1),X0)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_tex_2)).

fof(f280,plain,
    ( v1_subset_1(k1_tarski(sK1),u1_struct_0(sK0))
    | v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl4_4
    | spl4_13
    | ~ spl4_14 ),
    inference(forward_demodulation,[],[f279,f163])).

fof(f279,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl4_4
    | spl4_13 ),
    inference(subsumption_resolution,[],[f101,f255])).

fof(f101,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl4_4 ),
    inference(resolution,[],[f94,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0)
      | v1_subset_1(k6_domain_1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( ~ v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tex_2)).

fof(f198,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))
    | ~ spl4_17 ),
    inference(resolution,[],[f194,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0)
      | ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( v1_subset_1(X1,X0)
           => v1_xboole_0(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tex_2)).

fof(f228,plain,
    ( spl4_22
    | ~ spl4_2
    | spl4_6
    | ~ spl4_10
    | ~ spl4_17
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f215,f208,f193,f137,f113,f84,f226])).

fof(f208,plain,
    ( spl4_19
  <=> u1_struct_0(k1_tex_2(sK0,sK1)) = sK3(sK0,k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f215,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl4_2
    | spl4_6
    | ~ spl4_10
    | ~ spl4_17
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f197,f214])).

fof(f214,plain,
    ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl4_2
    | spl4_6
    | ~ spl4_10
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f213,f124])).

fof(f124,plain,
    ( ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f113])).

fof(f213,plain,
    ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ spl4_2
    | ~ spl4_10
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f212,f85])).

fof(f212,plain,
    ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ spl4_10
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f211,f138])).

fof(f211,plain,
    ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ spl4_19 ),
    inference(superposition,[],[f63,f209])).

fof(f209,plain,
    ( u1_struct_0(k1_tex_2(sK0,sK1)) = sK3(sK0,k1_tex_2(sK0,sK1))
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f208])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(sK3(X0,X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v1_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f197,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))
    | v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl4_17 ),
    inference(resolution,[],[f194,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

fof(f210,plain,
    ( spl4_19
    | ~ spl4_2
    | ~ spl4_10
    | ~ spl4_14
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f184,f174,f162,f137,f84,f208])).

fof(f184,plain,
    ( u1_struct_0(k1_tex_2(sK0,sK1)) = sK3(sK0,k1_tex_2(sK0,sK1))
    | ~ spl4_2
    | ~ spl4_10
    | ~ spl4_14
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f148,f183])).

fof(f183,plain,
    ( ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ spl4_14
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f179,f175])).

fof(f148,plain,
    ( u1_struct_0(k1_tex_2(sK0,sK1)) = sK3(sK0,k1_tex_2(sK0,sK1))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ spl4_2
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f143,f85])).

fof(f143,plain,
    ( ~ l1_pre_topc(sK0)
    | u1_struct_0(k1_tex_2(sK0,sK1)) = sK3(sK0,k1_tex_2(sK0,sK1))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ spl4_10 ),
    inference(resolution,[],[f138,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | u1_struct_0(X1) = sK3(X0,X1)
      | v1_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f195,plain,
    ( spl4_17
    | ~ spl4_2
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f145,f137,f84,f193])).

fof(f145,plain,
    ( m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_2
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f141,f85])).

fof(f141,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_10 ),
    inference(resolution,[],[f138,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l17_tex_2)).

fof(f191,plain,
    ( spl4_16
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f172,f151,f189])).

fof(f151,plain,
    ( spl4_11
  <=> l1_pre_topc(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f172,plain,
    ( l1_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl4_11 ),
    inference(resolution,[],[f152,f76])).

fof(f76,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f152,plain,
    ( l1_pre_topc(k1_tex_2(sK0,sK1))
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f151])).

fof(f176,plain,
    ( spl4_15
    | ~ spl4_7
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f169,f162,f116,f174])).

fof(f116,plain,
    ( spl4_7
  <=> v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f169,plain,
    ( v1_subset_1(k1_tarski(sK1),u1_struct_0(sK0))
    | ~ spl4_7
    | ~ spl4_14 ),
    inference(superposition,[],[f117,f163])).

fof(f117,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f116])).

fof(f168,plain,
    ( spl4_1
    | ~ spl4_3
    | ~ spl4_13 ),
    inference(avatar_contradiction_clause,[],[f167])).

fof(f167,plain,
    ( $false
    | spl4_1
    | ~ spl4_3
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f166,f81])).

fof(f81,plain,
    ( ~ v2_struct_0(sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl4_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f166,plain,
    ( v2_struct_0(sK0)
    | ~ spl4_3
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f165,f90])).

fof(f90,plain,
    ( l1_struct_0(sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl4_3
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f165,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_13 ),
    inference(resolution,[],[f159,f70])).

fof(f159,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f158])).

fof(f164,plain,
    ( spl4_14
    | spl4_13
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f100,f93,f158,f162])).

fof(f100,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)
    | ~ spl4_4 ),
    inference(resolution,[],[f94,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f153,plain,
    ( spl4_11
    | ~ spl4_2
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f144,f137,f84,f151])).

fof(f144,plain,
    ( l1_pre_topc(k1_tex_2(sK0,sK1))
    | ~ spl4_2
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f140,f85])).

fof(f140,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(k1_tex_2(sK0,sK1))
    | ~ spl4_10 ),
    inference(resolution,[],[f138,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f139,plain,
    ( spl4_10
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f107,f93,f84,f80,f137])).

fof(f107,plain,
    ( m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f106,f81])).

fof(f106,plain,
    ( v2_struct_0(sK0)
    | m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f99,f85])).

fof(f99,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ spl4_4 ),
    inference(resolution,[],[f94,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | m1_pre_topc(k1_tex_2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).

fof(f123,plain,
    ( spl4_8
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f105,f93,f84,f80,f121])).

fof(f105,plain,
    ( v7_struct_0(k1_tex_2(sK0,sK1))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f104,f81])).

fof(f104,plain,
    ( v2_struct_0(sK0)
    | v7_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f97,f85])).

fof(f97,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v7_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl4_4 ),
    inference(resolution,[],[f94,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v7_struct_0(k1_tex_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).

fof(f118,plain,
    ( spl4_6
    | spl4_7 ),
    inference(avatar_split_clause,[],[f50,f116,f113])).

fof(f50,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f111,plain,
    ( ~ spl4_5
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f103,f93,f84,f80,f109])).

fof(f103,plain,
    ( ~ v2_struct_0(k1_tex_2(sK0,sK1))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f102,f81])).

fof(f102,plain,
    ( v2_struct_0(sK0)
    | ~ v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f96,f85])).

fof(f96,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl4_4 ),
    inference(resolution,[],[f94,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v2_struct_0(k1_tex_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f95,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f52,f93])).

fof(f52,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f91,plain,
    ( spl4_3
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f87,f84,f89])).

fof(f87,plain,
    ( l1_struct_0(sK0)
    | ~ spl4_2 ),
    inference(resolution,[],[f85,f76])).

fof(f86,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f54,f84])).

fof(f54,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f82,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f53,f80])).

fof(f53,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:23:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.45  % (17620)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.47  % (17633)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.48  % (17629)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.49  % (17617)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.49  % (17619)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.49  % (17625)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.50  % (17631)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.50  % (17630)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.50  % (17623)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.50  % (17627)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.50  % (17615)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (17621)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.50  % (17636)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.50  % (17616)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (17626)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.50  % (17626)Refutation not found, incomplete strategy% (17626)------------------------------
% 0.21/0.50  % (17626)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (17626)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (17626)Memory used [KB]: 6140
% 0.21/0.50  % (17626)Time elapsed: 0.096 s
% 0.21/0.50  % (17626)------------------------------
% 0.21/0.50  % (17626)------------------------------
% 0.21/0.50  % (17636)Refutation not found, incomplete strategy% (17636)------------------------------
% 0.21/0.50  % (17636)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (17636)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (17636)Memory used [KB]: 10618
% 0.21/0.50  % (17636)Time elapsed: 0.097 s
% 0.21/0.50  % (17636)------------------------------
% 0.21/0.50  % (17636)------------------------------
% 0.21/0.50  % (17616)Refutation not found, incomplete strategy% (17616)------------------------------
% 0.21/0.50  % (17616)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (17616)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (17616)Memory used [KB]: 10618
% 0.21/0.50  % (17616)Time elapsed: 0.091 s
% 0.21/0.50  % (17616)------------------------------
% 0.21/0.50  % (17616)------------------------------
% 0.21/0.51  % (17618)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (17615)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f382,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f82,f86,f91,f95,f111,f118,f123,f139,f153,f164,f168,f176,f191,f195,f210,f228,f300,f311,f381])).
% 0.21/0.51  fof(f381,plain,(
% 0.21/0.51    ~spl4_4 | spl4_5 | ~spl4_8 | ~spl4_14 | ~spl4_15 | ~spl4_16 | ~spl4_22),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f380])).
% 0.21/0.51  fof(f380,plain,(
% 0.21/0.51    $false | (~spl4_4 | spl4_5 | ~spl4_8 | ~spl4_14 | ~spl4_15 | ~spl4_16 | ~spl4_22)),
% 0.21/0.51    inference(subsumption_resolution,[],[f379,f94])).
% 0.21/0.51  fof(f94,plain,(
% 0.21/0.51    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl4_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f93])).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    spl4_4 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.51  fof(f379,plain,(
% 0.21/0.51    ~m1_subset_1(sK1,u1_struct_0(sK0)) | (spl4_5 | ~spl4_8 | ~spl4_14 | ~spl4_15 | ~spl4_16 | ~spl4_22)),
% 0.21/0.51    inference(subsumption_resolution,[],[f378,f175])).
% 0.21/0.51  fof(f175,plain,(
% 0.21/0.51    v1_subset_1(k1_tarski(sK1),u1_struct_0(sK0)) | ~spl4_15),
% 0.21/0.51    inference(avatar_component_clause,[],[f174])).
% 0.21/0.51  fof(f174,plain,(
% 0.21/0.51    spl4_15 <=> v1_subset_1(k1_tarski(sK1),u1_struct_0(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.21/0.51  fof(f378,plain,(
% 0.21/0.51    ~v1_subset_1(k1_tarski(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | (spl4_5 | ~spl4_8 | ~spl4_14 | ~spl4_16 | ~spl4_22)),
% 0.21/0.51    inference(superposition,[],[f353,f163])).
% 0.21/0.51  fof(f163,plain,(
% 0.21/0.51    k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) | ~spl4_14),
% 0.21/0.51    inference(avatar_component_clause,[],[f162])).
% 0.21/0.51  fof(f162,plain,(
% 0.21/0.51    spl4_14 <=> k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.21/0.51  fof(f353,plain,(
% 0.21/0.51    ( ! [X5] : (~v1_subset_1(k6_domain_1(u1_struct_0(sK0),X5),u1_struct_0(sK0)) | ~m1_subset_1(X5,u1_struct_0(sK0))) ) | (spl4_5 | ~spl4_8 | ~spl4_16 | ~spl4_22)),
% 0.21/0.51    inference(subsumption_resolution,[],[f352,f122])).
% 0.21/0.51  fof(f122,plain,(
% 0.21/0.51    v7_struct_0(k1_tex_2(sK0,sK1)) | ~spl4_8),
% 0.21/0.51    inference(avatar_component_clause,[],[f121])).
% 0.21/0.51  fof(f121,plain,(
% 0.21/0.51    spl4_8 <=> v7_struct_0(k1_tex_2(sK0,sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.51  fof(f352,plain,(
% 0.21/0.51    ( ! [X5] : (~v1_subset_1(k6_domain_1(u1_struct_0(sK0),X5),u1_struct_0(sK0)) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~v7_struct_0(k1_tex_2(sK0,sK1))) ) | (spl4_5 | ~spl4_16 | ~spl4_22)),
% 0.21/0.51    inference(subsumption_resolution,[],[f351,f110])).
% 0.21/0.51  fof(f110,plain,(
% 0.21/0.51    ~v2_struct_0(k1_tex_2(sK0,sK1)) | spl4_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f109])).
% 0.21/0.51  fof(f109,plain,(
% 0.21/0.51    spl4_5 <=> v2_struct_0(k1_tex_2(sK0,sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.51  fof(f351,plain,(
% 0.21/0.51    ( ! [X5] : (~v1_subset_1(k6_domain_1(u1_struct_0(sK0),X5),u1_struct_0(sK0)) | ~m1_subset_1(X5,u1_struct_0(sK0)) | v2_struct_0(k1_tex_2(sK0,sK1)) | ~v7_struct_0(k1_tex_2(sK0,sK1))) ) | (~spl4_16 | ~spl4_22)),
% 0.21/0.51    inference(subsumption_resolution,[],[f341,f190])).
% 0.21/0.51  fof(f190,plain,(
% 0.21/0.51    l1_struct_0(k1_tex_2(sK0,sK1)) | ~spl4_16),
% 0.21/0.51    inference(avatar_component_clause,[],[f189])).
% 0.21/0.51  fof(f189,plain,(
% 0.21/0.51    spl4_16 <=> l1_struct_0(k1_tex_2(sK0,sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.21/0.51  fof(f341,plain,(
% 0.21/0.51    ( ! [X5] : (~v1_subset_1(k6_domain_1(u1_struct_0(sK0),X5),u1_struct_0(sK0)) | ~l1_struct_0(k1_tex_2(sK0,sK1)) | ~m1_subset_1(X5,u1_struct_0(sK0)) | v2_struct_0(k1_tex_2(sK0,sK1)) | ~v7_struct_0(k1_tex_2(sK0,sK1))) ) | ~spl4_22),
% 0.21/0.51    inference(superposition,[],[f75,f227])).
% 0.21/0.51  fof(f227,plain,(
% 0.21/0.51    u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) | ~spl4_22),
% 0.21/0.51    inference(avatar_component_clause,[],[f226])).
% 0.21/0.51  fof(f226,plain,(
% 0.21/0.51    spl4_22 <=> u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.21/0.51  fof(f75,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~l1_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | ~v7_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f48])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f47])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f19])).
% 0.21/0.51  fof(f19,axiom,(
% 0.21/0.51    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~(v7_struct_0(X0) & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_tex_2)).
% 0.21/0.51  fof(f311,plain,(
% 0.21/0.51    spl4_5 | ~spl4_16 | ~spl4_28),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f310])).
% 0.21/0.51  fof(f310,plain,(
% 0.21/0.51    $false | (spl4_5 | ~spl4_16 | ~spl4_28)),
% 0.21/0.51    inference(subsumption_resolution,[],[f309,f110])).
% 0.21/0.51  fof(f309,plain,(
% 0.21/0.51    v2_struct_0(k1_tex_2(sK0,sK1)) | (~spl4_16 | ~spl4_28)),
% 0.21/0.51    inference(subsumption_resolution,[],[f308,f190])).
% 0.21/0.51  fof(f308,plain,(
% 0.21/0.51    ~l1_struct_0(k1_tex_2(sK0,sK1)) | v2_struct_0(k1_tex_2(sK0,sK1)) | ~spl4_28),
% 0.21/0.51    inference(resolution,[],[f299,f70])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f41])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.51  fof(f299,plain,(
% 0.21/0.51    v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) | ~spl4_28),
% 0.21/0.51    inference(avatar_component_clause,[],[f298])).
% 0.21/0.51  fof(f298,plain,(
% 0.21/0.51    spl4_28 <=> v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 0.21/0.51  fof(f300,plain,(
% 0.21/0.51    spl4_28 | ~spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | spl4_13 | ~spl4_14 | ~spl4_17),
% 0.21/0.51    inference(avatar_split_clause,[],[f292,f193,f162,f158,f137,f113,f93,f84,f298])).
% 0.21/0.51  fof(f84,plain,(
% 0.21/0.51    spl4_2 <=> l1_pre_topc(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.51  fof(f113,plain,(
% 0.21/0.51    spl4_6 <=> v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.51  fof(f137,plain,(
% 0.21/0.51    spl4_10 <=> m1_pre_topc(k1_tex_2(sK0,sK1),sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.51  fof(f158,plain,(
% 0.21/0.51    spl4_13 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.51  fof(f193,plain,(
% 0.21/0.51    spl4_17 <=> m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.21/0.51  fof(f292,plain,(
% 0.21/0.51    v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) | (~spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | spl4_13 | ~spl4_14 | ~spl4_17)),
% 0.21/0.51    inference(subsumption_resolution,[],[f290,f291])).
% 0.21/0.51  fof(f291,plain,(
% 0.21/0.51    v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | (~spl4_2 | ~spl4_6 | ~spl4_10 | ~spl4_17)),
% 0.21/0.51    inference(subsumption_resolution,[],[f277,f114])).
% 0.21/0.51  fof(f114,plain,(
% 0.21/0.51    v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~spl4_6),
% 0.21/0.51    inference(avatar_component_clause,[],[f113])).
% 0.21/0.51  fof(f277,plain,(
% 0.21/0.51    v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,sK1),sK0) | (~spl4_2 | ~spl4_10 | ~spl4_17)),
% 0.21/0.51    inference(subsumption_resolution,[],[f276,f85])).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    l1_pre_topc(sK0) | ~spl4_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f84])).
% 0.21/0.51  fof(f276,plain,(
% 0.21/0.51    ~l1_pre_topc(sK0) | v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,sK1),sK0) | (~spl4_10 | ~spl4_17)),
% 0.21/0.51    inference(subsumption_resolution,[],[f196,f138])).
% 0.21/0.51  fof(f138,plain,(
% 0.21/0.51    m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | ~spl4_10),
% 0.21/0.51    inference(avatar_component_clause,[],[f137])).
% 0.21/0.51  fof(f196,plain,(
% 0.21/0.51    ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~spl4_17),
% 0.21/0.51    inference(resolution,[],[f194,f77])).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) | ~v1_tex_2(X1,X0)) )),
% 0.21/0.51    inference(equality_resolution,[],[f60])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X2 | v1_subset_1(X2,u1_struct_0(X0)) | ~v1_tex_2(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : ((v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v1_subset_1(X2,u1_struct_0(X0)))))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tex_2)).
% 0.21/0.51  fof(f194,plain,(
% 0.21/0.51    m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_17),
% 0.21/0.51    inference(avatar_component_clause,[],[f193])).
% 0.21/0.51  fof(f290,plain,(
% 0.21/0.51    ~v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) | (~spl4_4 | ~spl4_6 | spl4_13 | ~spl4_14 | ~spl4_17)),
% 0.21/0.51    inference(subsumption_resolution,[],[f289,f255])).
% 0.21/0.51  fof(f255,plain,(
% 0.21/0.51    ~v1_xboole_0(u1_struct_0(sK0)) | spl4_13),
% 0.21/0.51    inference(avatar_component_clause,[],[f158])).
% 0.21/0.51  fof(f289,plain,(
% 0.21/0.51    v1_xboole_0(u1_struct_0(sK0)) | ~v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) | (~spl4_4 | ~spl4_6 | spl4_13 | ~spl4_14 | ~spl4_17)),
% 0.21/0.51    inference(subsumption_resolution,[],[f198,f286])).
% 0.21/0.51  fof(f286,plain,(
% 0.21/0.51    v1_zfmisc_1(u1_struct_0(sK0)) | (~spl4_4 | ~spl4_6 | spl4_13 | ~spl4_14)),
% 0.21/0.51    inference(subsumption_resolution,[],[f280,f180])).
% 0.21/0.51  fof(f180,plain,(
% 0.21/0.51    ~v1_subset_1(k1_tarski(sK1),u1_struct_0(sK0)) | (~spl4_6 | ~spl4_14)),
% 0.21/0.51    inference(subsumption_resolution,[],[f179,f114])).
% 0.21/0.51  fof(f179,plain,(
% 0.21/0.51    ~v1_subset_1(k1_tarski(sK1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~spl4_14),
% 0.21/0.51    inference(forward_demodulation,[],[f51,f163])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f21])).
% 0.21/0.51  fof(f21,negated_conjecture,(
% 0.21/0.51    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 0.21/0.51    inference(negated_conjecture,[],[f20])).
% 0.21/0.51  fof(f20,conjecture,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_tex_2)).
% 0.21/0.51  fof(f280,plain,(
% 0.21/0.51    v1_subset_1(k1_tarski(sK1),u1_struct_0(sK0)) | v1_zfmisc_1(u1_struct_0(sK0)) | (~spl4_4 | spl4_13 | ~spl4_14)),
% 0.21/0.51    inference(forward_demodulation,[],[f279,f163])).
% 0.21/0.51  fof(f279,plain,(
% 0.21/0.51    v1_zfmisc_1(u1_struct_0(sK0)) | v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | (~spl4_4 | spl4_13)),
% 0.21/0.51    inference(subsumption_resolution,[],[f101,f255])).
% 0.21/0.51  fof(f101,plain,(
% 0.21/0.51    v1_zfmisc_1(u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~spl4_4),
% 0.21/0.51    inference(resolution,[],[f94,f58])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | v1_zfmisc_1(X0) | v1_xboole_0(X0) | v1_subset_1(k6_domain_1(X0,X1),X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 0.21/0.51    inference(flattening,[],[f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | (v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,axiom,(
% 0.21/0.51    ! [X0] : ((~v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,X0) => v1_subset_1(k6_domain_1(X0,X1),X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tex_2)).
% 0.21/0.51  fof(f198,plain,(
% 0.21/0.51    ~v1_zfmisc_1(u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | ~v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) | ~spl4_17),
% 0.21/0.51    inference(resolution,[],[f194,f71])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0) | ~v1_subset_1(X1,X0) | v1_xboole_0(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f43])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 0.21/0.51    inference(flattening,[],[f42])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((v1_xboole_0(X1) | ~v1_subset_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | (~v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,axiom,(
% 0.21/0.51    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) => v1_xboole_0(X1))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tex_2)).
% 0.21/0.51  fof(f228,plain,(
% 0.21/0.51    spl4_22 | ~spl4_2 | spl4_6 | ~spl4_10 | ~spl4_17 | ~spl4_19),
% 0.21/0.51    inference(avatar_split_clause,[],[f215,f208,f193,f137,f113,f84,f226])).
% 0.21/0.51  fof(f208,plain,(
% 0.21/0.51    spl4_19 <=> u1_struct_0(k1_tex_2(sK0,sK1)) = sK3(sK0,k1_tex_2(sK0,sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.21/0.51  fof(f215,plain,(
% 0.21/0.51    u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) | (~spl4_2 | spl4_6 | ~spl4_10 | ~spl4_17 | ~spl4_19)),
% 0.21/0.51    inference(subsumption_resolution,[],[f197,f214])).
% 0.21/0.51  fof(f214,plain,(
% 0.21/0.51    ~v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | (~spl4_2 | spl4_6 | ~spl4_10 | ~spl4_19)),
% 0.21/0.51    inference(subsumption_resolution,[],[f213,f124])).
% 0.21/0.51  fof(f124,plain,(
% 0.21/0.51    ~v1_tex_2(k1_tex_2(sK0,sK1),sK0) | spl4_6),
% 0.21/0.51    inference(avatar_component_clause,[],[f113])).
% 0.21/0.51  fof(f213,plain,(
% 0.21/0.51    ~v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0) | (~spl4_2 | ~spl4_10 | ~spl4_19)),
% 0.21/0.51    inference(subsumption_resolution,[],[f212,f85])).
% 0.21/0.51  fof(f212,plain,(
% 0.21/0.51    ~v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | v1_tex_2(k1_tex_2(sK0,sK1),sK0) | (~spl4_10 | ~spl4_19)),
% 0.21/0.51    inference(subsumption_resolution,[],[f211,f138])).
% 0.21/0.51  fof(f211,plain,(
% 0.21/0.51    ~v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~spl4_19),
% 0.21/0.51    inference(superposition,[],[f63,f209])).
% 0.21/0.51  fof(f209,plain,(
% 0.21/0.51    u1_struct_0(k1_tex_2(sK0,sK1)) = sK3(sK0,k1_tex_2(sK0,sK1)) | ~spl4_19),
% 0.21/0.51    inference(avatar_component_clause,[],[f208])).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_subset_1(sK3(X0,X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v1_tex_2(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  fof(f197,plain,(
% 0.21/0.51    u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) | v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | ~spl4_17),
% 0.21/0.51    inference(resolution,[],[f194,f73])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f46])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).
% 0.21/0.51  fof(f210,plain,(
% 0.21/0.51    spl4_19 | ~spl4_2 | ~spl4_10 | ~spl4_14 | ~spl4_15),
% 0.21/0.51    inference(avatar_split_clause,[],[f184,f174,f162,f137,f84,f208])).
% 0.21/0.51  fof(f184,plain,(
% 0.21/0.51    u1_struct_0(k1_tex_2(sK0,sK1)) = sK3(sK0,k1_tex_2(sK0,sK1)) | (~spl4_2 | ~spl4_10 | ~spl4_14 | ~spl4_15)),
% 0.21/0.51    inference(subsumption_resolution,[],[f148,f183])).
% 0.21/0.51  fof(f183,plain,(
% 0.21/0.51    ~v1_tex_2(k1_tex_2(sK0,sK1),sK0) | (~spl4_14 | ~spl4_15)),
% 0.21/0.51    inference(subsumption_resolution,[],[f179,f175])).
% 0.21/0.51  fof(f148,plain,(
% 0.21/0.51    u1_struct_0(k1_tex_2(sK0,sK1)) = sK3(sK0,k1_tex_2(sK0,sK1)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0) | (~spl4_2 | ~spl4_10)),
% 0.21/0.51    inference(subsumption_resolution,[],[f143,f85])).
% 0.21/0.51  fof(f143,plain,(
% 0.21/0.51    ~l1_pre_topc(sK0) | u1_struct_0(k1_tex_2(sK0,sK1)) = sK3(sK0,k1_tex_2(sK0,sK1)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~spl4_10),
% 0.21/0.51    inference(resolution,[],[f138,f62])).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | u1_struct_0(X1) = sK3(X0,X1) | v1_tex_2(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  fof(f195,plain,(
% 0.21/0.51    spl4_17 | ~spl4_2 | ~spl4_10),
% 0.21/0.51    inference(avatar_split_clause,[],[f145,f137,f84,f193])).
% 0.21/0.51  fof(f145,plain,(
% 0.21/0.51    m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_2 | ~spl4_10)),
% 0.21/0.51    inference(subsumption_resolution,[],[f141,f85])).
% 0.21/0.51  fof(f141,plain,(
% 0.21/0.51    ~l1_pre_topc(sK0) | m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_10),
% 0.21/0.51    inference(resolution,[],[f138,f68])).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l17_tex_2)).
% 0.21/0.51  fof(f191,plain,(
% 0.21/0.51    spl4_16 | ~spl4_11),
% 0.21/0.51    inference(avatar_split_clause,[],[f172,f151,f189])).
% 0.21/0.51  fof(f151,plain,(
% 0.21/0.51    spl4_11 <=> l1_pre_topc(k1_tex_2(sK0,sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.51  fof(f172,plain,(
% 0.21/0.51    l1_struct_0(k1_tex_2(sK0,sK1)) | ~spl4_11),
% 0.21/0.51    inference(resolution,[],[f152,f76])).
% 0.21/0.51  fof(f76,plain,(
% 0.21/0.51    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f49])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.51  fof(f152,plain,(
% 0.21/0.51    l1_pre_topc(k1_tex_2(sK0,sK1)) | ~spl4_11),
% 0.21/0.51    inference(avatar_component_clause,[],[f151])).
% 0.21/0.51  fof(f176,plain,(
% 0.21/0.51    spl4_15 | ~spl4_7 | ~spl4_14),
% 0.21/0.51    inference(avatar_split_clause,[],[f169,f162,f116,f174])).
% 0.21/0.51  fof(f116,plain,(
% 0.21/0.51    spl4_7 <=> v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.51  fof(f169,plain,(
% 0.21/0.51    v1_subset_1(k1_tarski(sK1),u1_struct_0(sK0)) | (~spl4_7 | ~spl4_14)),
% 0.21/0.51    inference(superposition,[],[f117,f163])).
% 0.21/0.51  fof(f117,plain,(
% 0.21/0.51    v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~spl4_7),
% 0.21/0.51    inference(avatar_component_clause,[],[f116])).
% 0.21/0.51  fof(f168,plain,(
% 0.21/0.51    spl4_1 | ~spl4_3 | ~spl4_13),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f167])).
% 0.21/0.51  fof(f167,plain,(
% 0.21/0.51    $false | (spl4_1 | ~spl4_3 | ~spl4_13)),
% 0.21/0.51    inference(subsumption_resolution,[],[f166,f81])).
% 0.21/0.51  fof(f81,plain,(
% 0.21/0.51    ~v2_struct_0(sK0) | spl4_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f80])).
% 0.21/0.51  fof(f80,plain,(
% 0.21/0.51    spl4_1 <=> v2_struct_0(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.51  fof(f166,plain,(
% 0.21/0.51    v2_struct_0(sK0) | (~spl4_3 | ~spl4_13)),
% 0.21/0.51    inference(subsumption_resolution,[],[f165,f90])).
% 0.21/0.51  fof(f90,plain,(
% 0.21/0.51    l1_struct_0(sK0) | ~spl4_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f89])).
% 0.21/0.51  fof(f89,plain,(
% 0.21/0.51    spl4_3 <=> l1_struct_0(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.51  fof(f165,plain,(
% 0.21/0.51    ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~spl4_13),
% 0.21/0.51    inference(resolution,[],[f159,f70])).
% 0.21/0.51  fof(f159,plain,(
% 0.21/0.51    v1_xboole_0(u1_struct_0(sK0)) | ~spl4_13),
% 0.21/0.51    inference(avatar_component_clause,[],[f158])).
% 0.21/0.51  fof(f164,plain,(
% 0.21/0.51    spl4_14 | spl4_13 | ~spl4_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f100,f93,f158,f162])).
% 0.21/0.51  fof(f100,plain,(
% 0.21/0.51    v1_xboole_0(u1_struct_0(sK0)) | k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) | ~spl4_4),
% 0.21/0.51    inference(resolution,[],[f94,f72])).
% 0.21/0.51  fof(f72,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | v1_xboole_0(X0) | k6_domain_1(X0,X1) = k1_tarski(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f45])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.51    inference(flattening,[],[f44])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,axiom,(
% 0.21/0.51    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.21/0.51  fof(f153,plain,(
% 0.21/0.51    spl4_11 | ~spl4_2 | ~spl4_10),
% 0.21/0.51    inference(avatar_split_clause,[],[f144,f137,f84,f151])).
% 0.21/0.51  fof(f144,plain,(
% 0.21/0.51    l1_pre_topc(k1_tex_2(sK0,sK1)) | (~spl4_2 | ~spl4_10)),
% 0.21/0.51    inference(subsumption_resolution,[],[f140,f85])).
% 0.21/0.51  fof(f140,plain,(
% 0.21/0.51    ~l1_pre_topc(sK0) | l1_pre_topc(k1_tex_2(sK0,sK1)) | ~spl4_10),
% 0.21/0.51    inference(resolution,[],[f138,f69])).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.51  fof(f139,plain,(
% 0.21/0.51    spl4_10 | spl4_1 | ~spl4_2 | ~spl4_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f107,f93,f84,f80,f137])).
% 0.21/0.51  fof(f107,plain,(
% 0.21/0.51    m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | (spl4_1 | ~spl4_2 | ~spl4_4)),
% 0.21/0.51    inference(subsumption_resolution,[],[f106,f81])).
% 0.21/0.51  fof(f106,plain,(
% 0.21/0.51    v2_struct_0(sK0) | m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | (~spl4_2 | ~spl4_4)),
% 0.21/0.51    inference(subsumption_resolution,[],[f99,f85])).
% 0.21/0.51  fof(f99,plain,(
% 0.21/0.51    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | ~spl4_4),
% 0.21/0.51    inference(resolution,[],[f94,f65])).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0) | m1_pre_topc(k1_tex_2(X0,X1),X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.21/0.51    inference(pure_predicate_removal,[],[f14])).
% 0.21/0.51  fof(f14,axiom,(
% 0.21/0.51    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).
% 0.21/0.51  fof(f123,plain,(
% 0.21/0.51    spl4_8 | spl4_1 | ~spl4_2 | ~spl4_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f105,f93,f84,f80,f121])).
% 0.21/0.51  fof(f105,plain,(
% 0.21/0.51    v7_struct_0(k1_tex_2(sK0,sK1)) | (spl4_1 | ~spl4_2 | ~spl4_4)),
% 0.21/0.51    inference(subsumption_resolution,[],[f104,f81])).
% 0.21/0.51  fof(f104,plain,(
% 0.21/0.51    v2_struct_0(sK0) | v7_struct_0(k1_tex_2(sK0,sK1)) | (~spl4_2 | ~spl4_4)),
% 0.21/0.51    inference(subsumption_resolution,[],[f97,f85])).
% 0.21/0.51  fof(f97,plain,(
% 0.21/0.51    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v7_struct_0(k1_tex_2(sK0,sK1)) | ~spl4_4),
% 0.21/0.51    inference(resolution,[],[f94,f67])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v7_struct_0(k1_tex_2(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ! [X0,X1] : ((v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ! [X0,X1] : ((v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.21/0.51    inference(pure_predicate_removal,[],[f15])).
% 0.21/0.51  fof(f15,axiom,(
% 0.21/0.51    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).
% 0.21/0.51  fof(f118,plain,(
% 0.21/0.51    spl4_6 | spl4_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f50,f116,f113])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f111,plain,(
% 0.21/0.51    ~spl4_5 | spl4_1 | ~spl4_2 | ~spl4_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f103,f93,f84,f80,f109])).
% 0.21/0.51  fof(f103,plain,(
% 0.21/0.51    ~v2_struct_0(k1_tex_2(sK0,sK1)) | (spl4_1 | ~spl4_2 | ~spl4_4)),
% 0.21/0.51    inference(subsumption_resolution,[],[f102,f81])).
% 0.21/0.51  fof(f102,plain,(
% 0.21/0.51    v2_struct_0(sK0) | ~v2_struct_0(k1_tex_2(sK0,sK1)) | (~spl4_2 | ~spl4_4)),
% 0.21/0.51    inference(subsumption_resolution,[],[f96,f85])).
% 0.21/0.51  fof(f96,plain,(
% 0.21/0.51    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~v2_struct_0(k1_tex_2(sK0,sK1)) | ~spl4_4),
% 0.21/0.51    inference(resolution,[],[f94,f66])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~v2_struct_0(k1_tex_2(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f37])).
% 0.21/0.51  fof(f95,plain,(
% 0.21/0.51    spl4_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f52,f93])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f91,plain,(
% 0.21/0.51    spl4_3 | ~spl4_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f87,f84,f89])).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    l1_struct_0(sK0) | ~spl4_2),
% 0.21/0.51    inference(resolution,[],[f85,f76])).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    spl4_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f54,f84])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    l1_pre_topc(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f82,plain,(
% 0.21/0.51    ~spl4_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f53,f80])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    ~v2_struct_0(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (17615)------------------------------
% 0.21/0.51  % (17615)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (17615)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (17615)Memory used [KB]: 6268
% 0.21/0.51  % (17615)Time elapsed: 0.095 s
% 0.21/0.51  % (17615)------------------------------
% 0.21/0.51  % (17615)------------------------------
% 0.21/0.51  % (17632)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.51  % (17622)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.51  % (17612)Success in time 0.159 s
%------------------------------------------------------------------------------
