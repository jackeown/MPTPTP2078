%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:27 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :  218 ( 432 expanded)
%              Number of leaves         :   38 ( 152 expanded)
%              Depth                    :   20
%              Number of atoms          : 1033 (2440 expanded)
%              Number of equality atoms :   55 ( 193 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f415,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f97,f102,f107,f112,f117,f122,f138,f143,f148,f153,f158,f163,f168,f173,f183,f192,f207,f211,f228,f237,f267,f278,f287,f313,f323,f328,f402,f414])).

fof(f414,plain,
    ( spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_13
    | spl8_17
    | spl8_35 ),
    inference(avatar_contradiction_clause,[],[f413])).

fof(f413,plain,
    ( $false
    | spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_13
    | spl8_17
    | spl8_35 ),
    inference(trivial_inequality_removal,[],[f411])).

fof(f411,plain,
    ( k2_pre_topc(sK0,k1_tarski(sK3)) != k2_pre_topc(sK0,k1_tarski(sK3))
    | spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_13
    | spl8_17
    | spl8_35 ),
    inference(backward_demodulation,[],[f401,f410])).

fof(f410,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK3) = k1_tarski(sK3)
    | spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_13
    | spl8_17 ),
    inference(resolution,[],[f357,f162])).

fof(f162,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl8_13
  <=> m1_subset_1(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f357,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k1_tarski(X2) = k6_domain_1(u1_struct_0(sK0),X2) )
    | spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | spl8_17 ),
    inference(subsumption_resolution,[],[f356,f106])).

fof(f106,plain,
    ( ~ v2_struct_0(sK0)
    | spl8_3 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl8_3
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f356,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k1_tarski(X2) = k6_domain_1(u1_struct_0(sK0),X2)
        | v2_struct_0(sK0) )
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | spl8_17 ),
    inference(subsumption_resolution,[],[f355,f121])).

fof(f121,plain,
    ( l1_pre_topc(sK0)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl8_6
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f355,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k1_tarski(X2) = k6_domain_1(u1_struct_0(sK0),X2)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_4
    | ~ spl8_5
    | spl8_17 ),
    inference(subsumption_resolution,[],[f354,f116])).

fof(f116,plain,
    ( v3_tdlat_3(sK0)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl8_5
  <=> v3_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f354,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k1_tarski(X2) = k6_domain_1(u1_struct_0(sK0),X2)
        | ~ v3_tdlat_3(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_4
    | spl8_17 ),
    inference(subsumption_resolution,[],[f351,f111])).

fof(f111,plain,
    ( v2_pre_topc(sK0)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl8_4
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f351,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k1_tarski(X2) = k6_domain_1(u1_struct_0(sK0),X2)
        | ~ v2_pre_topc(sK0)
        | ~ v3_tdlat_3(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl8_17 ),
    inference(resolution,[],[f252,f70])).

fof(f70,plain,(
    ! [X0] :
      ( m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_tex_2)).

fof(f252,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK5(sK0),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,X0)
        | k6_domain_1(X0,X1) = k1_tarski(X1) )
    | spl8_17 ),
    inference(resolution,[],[f231,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f231,plain,
    ( ! [X1] :
        ( ~ v1_xboole_0(X1)
        | ~ m1_subset_1(sK5(sK0),k1_zfmisc_1(X1)) )
    | spl8_17 ),
    inference(resolution,[],[f187,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f187,plain,
    ( ~ v1_xboole_0(sK5(sK0))
    | spl8_17 ),
    inference(avatar_component_clause,[],[f185])).

fof(f185,plain,
    ( spl8_17
  <=> v1_xboole_0(sK5(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f401,plain,
    ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK3)) != k2_pre_topc(sK0,k1_tarski(sK3))
    | spl8_35 ),
    inference(avatar_component_clause,[],[f399])).

fof(f399,plain,
    ( spl8_35
  <=> k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK3)) = k2_pre_topc(sK0,k1_tarski(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).

fof(f402,plain,
    ( ~ spl8_35
    | ~ spl8_10
    | spl8_28
    | spl8_29 ),
    inference(avatar_split_clause,[],[f377,f320,f310,f145,f399])).

fof(f145,plain,
    ( spl8_10
  <=> m1_subset_1(sK3,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f310,plain,
    ( spl8_28
  <=> k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK3)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK1),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

% (17139)Refutation not found, incomplete strategy% (17139)------------------------------
% (17139)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (17139)Termination reason: Refutation not found, incomplete strategy

% (17139)Memory used [KB]: 10746
% (17139)Time elapsed: 0.148 s
% (17139)------------------------------
% (17139)------------------------------
fof(f320,plain,
    ( spl8_29
  <=> v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).

fof(f377,plain,
    ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK3)) != k2_pre_topc(sK0,k1_tarski(sK3))
    | ~ spl8_10
    | spl8_28
    | spl8_29 ),
    inference(backward_demodulation,[],[f312,f375])).

fof(f375,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK3) = k1_tarski(sK3)
    | ~ spl8_10
    | spl8_29 ),
    inference(resolution,[],[f329,f147])).

fof(f147,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f145])).

fof(f329,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | k1_tarski(X0) = k6_domain_1(u1_struct_0(sK1),X0) )
    | spl8_29 ),
    inference(resolution,[],[f321,f77])).

fof(f321,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | spl8_29 ),
    inference(avatar_component_clause,[],[f320])).

fof(f312,plain,
    ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK3)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK1),sK3))
    | spl8_28 ),
    inference(avatar_component_clause,[],[f310])).

fof(f328,plain,
    ( ~ spl8_24
    | spl8_25
    | ~ spl8_29 ),
    inference(avatar_contradiction_clause,[],[f327])).

fof(f327,plain,
    ( $false
    | ~ spl8_24
    | spl8_25
    | ~ spl8_29 ),
    inference(subsumption_resolution,[],[f324,f261])).

fof(f261,plain,
    ( m1_subset_1(sK5(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl8_24 ),
    inference(avatar_component_clause,[],[f260])).

fof(f260,plain,
    ( spl8_24
  <=> m1_subset_1(sK5(sK1),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f324,plain,
    ( ~ m1_subset_1(sK5(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | spl8_25
    | ~ spl8_29 ),
    inference(resolution,[],[f322,f290])).

fof(f290,plain,
    ( ! [X1] :
        ( ~ v1_xboole_0(X1)
        | ~ m1_subset_1(sK5(sK1),k1_zfmisc_1(X1)) )
    | spl8_25 ),
    inference(resolution,[],[f266,f67])).

fof(f266,plain,
    ( ~ v1_xboole_0(sK5(sK1))
    | spl8_25 ),
    inference(avatar_component_clause,[],[f264])).

fof(f264,plain,
    ( spl8_25
  <=> v1_xboole_0(sK5(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f322,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ spl8_29 ),
    inference(avatar_component_clause,[],[f320])).

fof(f323,plain,
    ( spl8_29
    | ~ spl8_10
    | spl8_27 ),
    inference(avatar_split_clause,[],[f318,f306,f145,f320])).

fof(f306,plain,
    ( spl8_27
  <=> m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f318,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ spl8_10
    | spl8_27 ),
    inference(subsumption_resolution,[],[f315,f147])).

fof(f315,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1))
    | spl8_27 ),
    inference(resolution,[],[f308,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f308,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | spl8_27 ),
    inference(avatar_component_clause,[],[f306])).

fof(f313,plain,
    ( ~ spl8_27
    | ~ spl8_28
    | ~ spl8_1
    | spl8_2
    | spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_11
    | ~ spl8_12
    | ~ spl8_14
    | ~ spl8_15
    | spl8_16 ),
    inference(avatar_split_clause,[],[f270,f180,f170,f165,f155,f150,f140,f135,f119,f114,f109,f104,f99,f94,f310,f306])).

fof(f94,plain,
    ( spl8_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f99,plain,
    ( spl8_2
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f135,plain,
    ( spl8_8
  <=> v4_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f140,plain,
    ( spl8_9
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f150,plain,
    ( spl8_11
  <=> v5_pre_topc(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f155,plain,
    ( spl8_12
  <=> v3_borsuk_1(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f165,plain,
    ( spl8_14
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f170,plain,
    ( spl8_15
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f180,plain,
    ( spl8_16
  <=> k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK3)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f270,plain,
    ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK3)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK1),sK3))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl8_1
    | spl8_2
    | spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_11
    | ~ spl8_12
    | ~ spl8_14
    | ~ spl8_15
    | spl8_16 ),
    inference(superposition,[],[f182,f247])).

fof(f247,plain,
    ( ! [X0] :
        ( k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) )
    | ~ spl8_1
    | spl8_2
    | spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_11
    | ~ spl8_12
    | ~ spl8_14
    | ~ spl8_15 ),
    inference(subsumption_resolution,[],[f246,f157])).

fof(f157,plain,
    ( v3_borsuk_1(sK2,sK0,sK1)
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f155])).

fof(f246,plain,
    ( ! [X0] :
        ( ~ v3_borsuk_1(sK2,sK0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) )
    | ~ spl8_1
    | spl8_2
    | spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_11
    | ~ spl8_14
    | ~ spl8_15 ),
    inference(subsumption_resolution,[],[f245,f172])).

fof(f172,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f170])).

fof(f245,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v3_borsuk_1(sK2,sK0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) )
    | ~ spl8_1
    | spl8_2
    | spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_11
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f244,f152])).

fof(f152,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f150])).

fof(f244,plain,
    ( ! [X0] :
        ( ~ v5_pre_topc(sK2,sK0,sK1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v3_borsuk_1(sK2,sK0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) )
    | ~ spl8_1
    | spl8_2
    | spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f243,f111])).

fof(f243,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK0)
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v3_borsuk_1(sK2,sK0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) )
    | ~ spl8_1
    | spl8_2
    | spl8_3
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f242,f106])).

fof(f242,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v3_borsuk_1(sK2,sK0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) )
    | ~ spl8_1
    | spl8_2
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f241,f142])).

fof(f142,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f140])).

fof(f241,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK1,sK0)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v3_borsuk_1(sK2,sK0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) )
    | ~ spl8_1
    | spl8_2
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f240,f137])).

fof(f137,plain,
    ( v4_tex_2(sK1,sK0)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f135])).

fof(f240,plain,
    ( ! [X0] :
        ( ~ v4_tex_2(sK1,sK0)
        | ~ m1_pre_topc(sK1,sK0)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v3_borsuk_1(sK2,sK0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) )
    | ~ spl8_1
    | spl8_2
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f239,f101])).

fof(f101,plain,
    ( ~ v2_struct_0(sK1)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f99])).

fof(f239,plain,
    ( ! [X0] :
        ( v2_struct_0(sK1)
        | ~ v4_tex_2(sK1,sK0)
        | ~ m1_pre_topc(sK1,sK0)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v3_borsuk_1(sK2,sK0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) )
    | ~ spl8_1
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f238,f121])).

fof(f238,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v4_tex_2(sK1,sK0)
        | ~ m1_pre_topc(sK1,sK0)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v3_borsuk_1(sK2,sK0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) )
    | ~ spl8_1
    | ~ spl8_5
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f213,f116])).

fof(f213,plain,
    ( ! [X0] :
        ( ~ v3_tdlat_3(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v4_tex_2(sK1,sK0)
        | ~ m1_pre_topc(sK1,sK0)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v3_borsuk_1(sK2,sK0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) )
    | ~ spl8_1
    | ~ spl8_14 ),
    inference(resolution,[],[f124,f167])).

fof(f167,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f165])).

fof(f124,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ v3_tdlat_3(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v4_tex_2(X1,X0)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ v5_pre_topc(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v3_borsuk_1(sK2,X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        | k2_pre_topc(X0,X2) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2,X2) )
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f123,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).

fof(f123,plain,
    ( ! [X2,X0,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ v3_tdlat_3(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v4_tex_2(X1,X0)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X0)
        | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ v5_pre_topc(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v3_borsuk_1(sK2,X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | k2_pre_topc(X0,X2) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2,X2) )
    | ~ spl8_1 ),
    inference(resolution,[],[f96,f90])).

fof(f90,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v2_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v4_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v3_borsuk_1(X2,X0,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X4) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v4_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v3_borsuk_1(X2,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | X3 != X4
      | k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4)
                      | X3 != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ v3_borsuk_1(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v5_pre_topc(X2,X0,X1)
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v4_tex_2(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4)
                      | X3 != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ v3_borsuk_1(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v5_pre_topc(X2,X0,X1)
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v4_tex_2(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & v4_tex_2(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v5_pre_topc(X2,X0,X1)
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v3_borsuk_1(X2,X0,X1)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                       => ( X3 = X4
                         => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tex_2)).

fof(f96,plain,
    ( v1_funct_1(sK2)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f94])).

fof(f182,plain,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK3)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK3))
    | spl8_16 ),
    inference(avatar_component_clause,[],[f180])).

fof(f287,plain,
    ( spl8_2
    | ~ spl8_20
    | ~ spl8_21
    | ~ spl8_23
    | spl8_24 ),
    inference(avatar_contradiction_clause,[],[f286])).

fof(f286,plain,
    ( $false
    | spl8_2
    | ~ spl8_20
    | ~ spl8_21
    | ~ spl8_23
    | spl8_24 ),
    inference(subsumption_resolution,[],[f285,f101])).

fof(f285,plain,
    ( v2_struct_0(sK1)
    | ~ spl8_20
    | ~ spl8_21
    | ~ spl8_23
    | spl8_24 ),
    inference(subsumption_resolution,[],[f284,f201])).

fof(f201,plain,
    ( l1_pre_topc(sK1)
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f200])).

fof(f200,plain,
    ( spl8_20
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f284,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl8_21
    | ~ spl8_23
    | spl8_24 ),
    inference(subsumption_resolution,[],[f283,f257])).

fof(f257,plain,
    ( v3_tdlat_3(sK1)
    | ~ spl8_23 ),
    inference(avatar_component_clause,[],[f256])).

fof(f256,plain,
    ( spl8_23
  <=> v3_tdlat_3(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f283,plain,
    ( ~ v3_tdlat_3(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl8_21
    | spl8_24 ),
    inference(subsumption_resolution,[],[f280,f205])).

fof(f205,plain,
    ( v2_pre_topc(sK1)
    | ~ spl8_21 ),
    inference(avatar_component_clause,[],[f204])).

fof(f204,plain,
    ( spl8_21
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f280,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ v3_tdlat_3(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | spl8_24 ),
    inference(resolution,[],[f262,f70])).

fof(f262,plain,
    ( ~ m1_subset_1(sK5(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | spl8_24 ),
    inference(avatar_component_clause,[],[f260])).

fof(f278,plain,
    ( spl8_2
    | spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_9
    | spl8_23 ),
    inference(avatar_contradiction_clause,[],[f277])).

fof(f277,plain,
    ( $false
    | spl8_2
    | spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_9
    | spl8_23 ),
    inference(subsumption_resolution,[],[f276,f106])).

fof(f276,plain,
    ( v2_struct_0(sK0)
    | spl8_2
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_9
    | spl8_23 ),
    inference(subsumption_resolution,[],[f275,f111])).

fof(f275,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_2
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_9
    | spl8_23 ),
    inference(subsumption_resolution,[],[f274,f121])).

fof(f274,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_2
    | ~ spl8_5
    | ~ spl8_9
    | spl8_23 ),
    inference(subsumption_resolution,[],[f273,f116])).

fof(f273,plain,
    ( ~ v3_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_2
    | ~ spl8_9
    | spl8_23 ),
    inference(resolution,[],[f269,f142])).

fof(f269,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK1,X0)
        | ~ v3_tdlat_3(X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | spl8_2
    | spl8_23 ),
    inference(subsumption_resolution,[],[f268,f101])).

fof(f268,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(X0)
        | ~ v3_tdlat_3(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK1,X0)
        | v2_struct_0(sK1)
        | v2_struct_0(X0) )
    | spl8_23 ),
    inference(resolution,[],[f258,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v3_tdlat_3(X1)
      | ~ v2_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tdlat_3(X1)
            & ~ v2_struct_0(X1) )
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tdlat_3(X1)
            & ~ v2_struct_0(X1) )
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( ~ v2_struct_0(X1)
           => ( v3_tdlat_3(X1)
              & ~ v2_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc9_tdlat_3)).

fof(f258,plain,
    ( ~ v3_tdlat_3(sK1)
    | spl8_23 ),
    inference(avatar_component_clause,[],[f256])).

fof(f267,plain,
    ( ~ spl8_23
    | ~ spl8_24
    | ~ spl8_25
    | spl8_2
    | ~ spl8_19
    | ~ spl8_20
    | ~ spl8_21 ),
    inference(avatar_split_clause,[],[f251,f204,f200,f197,f99,f264,f260,f256])).

fof(f197,plain,
    ( spl8_19
  <=> ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ v3_tex_2(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f251,plain,
    ( ~ v1_xboole_0(sK5(sK1))
    | ~ m1_subset_1(sK5(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v3_tdlat_3(sK1)
    | spl8_2
    | ~ spl8_19
    | ~ spl8_20
    | ~ spl8_21 ),
    inference(subsumption_resolution,[],[f250,f101])).

fof(f250,plain,
    ( ~ v1_xboole_0(sK5(sK1))
    | ~ m1_subset_1(sK5(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v3_tdlat_3(sK1)
    | v2_struct_0(sK1)
    | ~ spl8_19
    | ~ spl8_20
    | ~ spl8_21 ),
    inference(subsumption_resolution,[],[f249,f201])).

fof(f249,plain,
    ( ~ v1_xboole_0(sK5(sK1))
    | ~ m1_subset_1(sK5(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v3_tdlat_3(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl8_19
    | ~ spl8_21 ),
    inference(subsumption_resolution,[],[f248,f205])).

fof(f248,plain,
    ( ~ v1_xboole_0(sK5(sK1))
    | ~ m1_subset_1(sK5(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ v3_tdlat_3(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl8_19 ),
    inference(resolution,[],[f198,f71])).

fof(f71,plain,(
    ! [X0] :
      ( v3_tex_2(sK5(X0),X0)
      | ~ v2_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f198,plain,
    ( ! [X0] :
        ( ~ v3_tex_2(X0,sK1)
        | ~ v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) )
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f197])).

fof(f237,plain,
    ( ~ spl8_4
    | ~ spl8_6
    | ~ spl8_9
    | spl8_21 ),
    inference(avatar_contradiction_clause,[],[f236])).

fof(f236,plain,
    ( $false
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_9
    | spl8_21 ),
    inference(subsumption_resolution,[],[f235,f111])).

fof(f235,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ spl8_6
    | ~ spl8_9
    | spl8_21 ),
    inference(subsumption_resolution,[],[f234,f121])).

fof(f234,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl8_9
    | spl8_21 ),
    inference(resolution,[],[f212,f142])).

fof(f212,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK1,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | spl8_21 ),
    inference(resolution,[],[f206,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f206,plain,
    ( ~ v2_pre_topc(sK1)
    | spl8_21 ),
    inference(avatar_component_clause,[],[f204])).

fof(f228,plain,
    ( spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | spl8_18 ),
    inference(avatar_contradiction_clause,[],[f227])).

fof(f227,plain,
    ( $false
    | spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | spl8_18 ),
    inference(subsumption_resolution,[],[f226,f106])).

fof(f226,plain,
    ( v2_struct_0(sK0)
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | spl8_18 ),
    inference(subsumption_resolution,[],[f225,f121])).

fof(f225,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_4
    | ~ spl8_5
    | spl8_18 ),
    inference(subsumption_resolution,[],[f224,f116])).

fof(f224,plain,
    ( ~ v3_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_4
    | spl8_18 ),
    inference(subsumption_resolution,[],[f221,f111])).

fof(f221,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ v3_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_18 ),
    inference(resolution,[],[f191,f70])).

fof(f191,plain,
    ( ~ m1_subset_1(sK5(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl8_18 ),
    inference(avatar_component_clause,[],[f189])).

fof(f189,plain,
    ( spl8_18
  <=> m1_subset_1(sK5(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f211,plain,
    ( ~ spl8_6
    | ~ spl8_9
    | spl8_20 ),
    inference(avatar_contradiction_clause,[],[f210])).

fof(f210,plain,
    ( $false
    | ~ spl8_6
    | ~ spl8_9
    | spl8_20 ),
    inference(subsumption_resolution,[],[f209,f121])).

fof(f209,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl8_9
    | spl8_20 ),
    inference(resolution,[],[f208,f142])).

fof(f208,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK1,X0)
        | ~ l1_pre_topc(X0) )
    | spl8_20 ),
    inference(resolution,[],[f202,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f202,plain,
    ( ~ l1_pre_topc(sK1)
    | spl8_20 ),
    inference(avatar_component_clause,[],[f200])).

fof(f207,plain,
    ( spl8_19
    | ~ spl8_20
    | ~ spl8_21
    | spl8_2 ),
    inference(avatar_split_clause,[],[f125,f99,f204,f200,f197])).

fof(f125,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v3_tex_2(X0,sK1) )
    | spl8_2 ),
    inference(resolution,[],[f101,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => ~ v3_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_tex_2)).

fof(f192,plain,
    ( ~ spl8_17
    | ~ spl8_18
    | spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f178,f119,f114,f109,f104,f189,f185])).

fof(f178,plain,
    ( ~ m1_subset_1(sK5(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(sK5(sK0))
    | spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f177,f106])).

fof(f177,plain,
    ( ~ m1_subset_1(sK5(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(sK5(sK0))
    | v2_struct_0(sK0)
    | spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f176,f121])).

fof(f176,plain,
    ( ~ m1_subset_1(sK5(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(sK5(sK0))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f175,f116])).

fof(f175,plain,
    ( ~ m1_subset_1(sK5(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(sK5(sK0))
    | ~ v3_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_3
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f174,f111])).

fof(f174,plain,
    ( ~ m1_subset_1(sK5(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(sK5(sK0))
    | ~ v2_pre_topc(sK0)
    | ~ v3_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl8_3
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(resolution,[],[f128,f71])).

fof(f128,plain,
    ( ! [X0] :
        ( ~ v3_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_xboole_0(X0) )
    | spl8_3
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f127,f121])).

fof(f127,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_tex_2(X0,sK0) )
    | spl8_3
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f126,f111])).

fof(f126,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_tex_2(X0,sK0) )
    | spl8_3 ),
    inference(resolution,[],[f106,f72])).

fof(f183,plain,(
    ~ spl8_16 ),
    inference(avatar_split_clause,[],[f91,f180])).

fof(f91,plain,(
    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK3)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK3)) ),
    inference(forward_demodulation,[],[f49,f48])).

fof(f48,plain,(
    sK3 = sK4 ),
    inference(cnf_transformation,[],[f26])).

% (17138)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4))
                      & X3 = X4
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & v3_borsuk_1(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v5_pre_topc(X2,X0,X1)
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & m1_pre_topc(X1,X0)
          & v4_tex_2(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4))
                      & X3 = X4
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & v3_borsuk_1(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v5_pre_topc(X2,X0,X1)
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & m1_pre_topc(X1,X0)
          & v4_tex_2(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v3_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & v4_tex_2(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v5_pre_topc(X2,X0,X1)
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( v3_borsuk_1(X2,X0,X1)
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X1))
                     => ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( X3 = X4
                           => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & v4_tex_2(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v5_pre_topc(X2,X0,X1)
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v3_borsuk_1(X2,X0,X1)
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X1))
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ( X3 = X4
                         => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tex_2)).

fof(f49,plain,(
    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK3)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) ),
    inference(cnf_transformation,[],[f26])).

fof(f173,plain,(
    spl8_15 ),
    inference(avatar_split_clause,[],[f54,f170])).

fof(f54,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f26])).

fof(f168,plain,(
    spl8_14 ),
    inference(avatar_split_clause,[],[f52,f165])).

fof(f52,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f26])).

fof(f163,plain,(
    spl8_13 ),
    inference(avatar_split_clause,[],[f92,f160])).

fof(f92,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f47,f48])).

fof(f47,plain,(
    m1_subset_1(sK4,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f158,plain,(
    spl8_12 ),
    inference(avatar_split_clause,[],[f55,f155])).

fof(f55,plain,(
    v3_borsuk_1(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f153,plain,(
    spl8_11 ),
    inference(avatar_split_clause,[],[f53,f150])).

fof(f53,plain,(
    v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f148,plain,(
    spl8_10 ),
    inference(avatar_split_clause,[],[f50,f145])).

fof(f50,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f26])).

fof(f143,plain,(
    spl8_9 ),
    inference(avatar_split_clause,[],[f58,f140])).

fof(f58,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f138,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f57,f135])).

fof(f57,plain,(
    v4_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f122,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f62,f119])).

fof(f62,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f117,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f61,f114])).

fof(f61,plain,(
    v3_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f112,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f60,f109])).

fof(f60,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f107,plain,(
    ~ spl8_3 ),
    inference(avatar_split_clause,[],[f59,f104])).

fof(f59,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f102,plain,(
    ~ spl8_2 ),
    inference(avatar_split_clause,[],[f56,f99])).

fof(f56,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f97,plain,(
    spl8_1 ),
    inference(avatar_split_clause,[],[f51,f94])).

fof(f51,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:42:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (17125)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (17142)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.52  % (17129)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (17134)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (17144)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (17136)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (17145)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (17148)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (17126)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (17122)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (17131)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (17128)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (17142)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % (17149)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (17127)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (17139)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (17124)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (17133)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (17144)Refutation not found, incomplete strategy% (17144)------------------------------
% 0.21/0.54  % (17144)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (17144)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (17144)Memory used [KB]: 10874
% 0.21/0.54  % (17144)Time elapsed: 0.084 s
% 0.21/0.54  % (17144)------------------------------
% 0.21/0.54  % (17144)------------------------------
% 0.21/0.54  % (17123)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.55  % (17130)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.55  % (17150)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.55  % (17152)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.55  % (17141)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (17146)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.55  % (17143)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (17140)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (17135)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.55  % (17132)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.55  % (17151)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.56  % (17137)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.50/0.56  % SZS output start Proof for theBenchmark
% 1.50/0.56  fof(f415,plain,(
% 1.50/0.56    $false),
% 1.50/0.56    inference(avatar_sat_refutation,[],[f97,f102,f107,f112,f117,f122,f138,f143,f148,f153,f158,f163,f168,f173,f183,f192,f207,f211,f228,f237,f267,f278,f287,f313,f323,f328,f402,f414])).
% 1.50/0.56  fof(f414,plain,(
% 1.50/0.56    spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_13 | spl8_17 | spl8_35),
% 1.50/0.56    inference(avatar_contradiction_clause,[],[f413])).
% 1.50/0.56  fof(f413,plain,(
% 1.50/0.56    $false | (spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_13 | spl8_17 | spl8_35)),
% 1.50/0.56    inference(trivial_inequality_removal,[],[f411])).
% 1.50/0.56  fof(f411,plain,(
% 1.50/0.56    k2_pre_topc(sK0,k1_tarski(sK3)) != k2_pre_topc(sK0,k1_tarski(sK3)) | (spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_13 | spl8_17 | spl8_35)),
% 1.50/0.56    inference(backward_demodulation,[],[f401,f410])).
% 1.50/0.56  fof(f410,plain,(
% 1.50/0.56    k6_domain_1(u1_struct_0(sK0),sK3) = k1_tarski(sK3) | (spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_13 | spl8_17)),
% 1.50/0.56    inference(resolution,[],[f357,f162])).
% 1.50/0.56  fof(f162,plain,(
% 1.50/0.56    m1_subset_1(sK3,u1_struct_0(sK0)) | ~spl8_13),
% 1.50/0.56    inference(avatar_component_clause,[],[f160])).
% 1.50/0.56  fof(f160,plain,(
% 1.50/0.56    spl8_13 <=> m1_subset_1(sK3,u1_struct_0(sK0))),
% 1.50/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 1.50/0.56  fof(f357,plain,(
% 1.50/0.56    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | k1_tarski(X2) = k6_domain_1(u1_struct_0(sK0),X2)) ) | (spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_6 | spl8_17)),
% 1.50/0.56    inference(subsumption_resolution,[],[f356,f106])).
% 1.50/0.56  fof(f106,plain,(
% 1.50/0.56    ~v2_struct_0(sK0) | spl8_3),
% 1.50/0.56    inference(avatar_component_clause,[],[f104])).
% 1.50/0.56  fof(f104,plain,(
% 1.50/0.56    spl8_3 <=> v2_struct_0(sK0)),
% 1.50/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 1.50/0.56  fof(f356,plain,(
% 1.50/0.56    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | k1_tarski(X2) = k6_domain_1(u1_struct_0(sK0),X2) | v2_struct_0(sK0)) ) | (~spl8_4 | ~spl8_5 | ~spl8_6 | spl8_17)),
% 1.50/0.56    inference(subsumption_resolution,[],[f355,f121])).
% 1.50/0.56  fof(f121,plain,(
% 1.50/0.56    l1_pre_topc(sK0) | ~spl8_6),
% 1.50/0.56    inference(avatar_component_clause,[],[f119])).
% 1.50/0.56  fof(f119,plain,(
% 1.50/0.56    spl8_6 <=> l1_pre_topc(sK0)),
% 1.50/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 1.50/0.56  fof(f355,plain,(
% 1.50/0.56    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | k1_tarski(X2) = k6_domain_1(u1_struct_0(sK0),X2) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl8_4 | ~spl8_5 | spl8_17)),
% 1.50/0.56    inference(subsumption_resolution,[],[f354,f116])).
% 1.50/0.56  fof(f116,plain,(
% 1.50/0.56    v3_tdlat_3(sK0) | ~spl8_5),
% 1.50/0.56    inference(avatar_component_clause,[],[f114])).
% 1.50/0.56  fof(f114,plain,(
% 1.50/0.56    spl8_5 <=> v3_tdlat_3(sK0)),
% 1.50/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 1.50/0.56  fof(f354,plain,(
% 1.50/0.56    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | k1_tarski(X2) = k6_domain_1(u1_struct_0(sK0),X2) | ~v3_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl8_4 | spl8_17)),
% 1.50/0.56    inference(subsumption_resolution,[],[f351,f111])).
% 1.50/0.56  fof(f111,plain,(
% 1.50/0.56    v2_pre_topc(sK0) | ~spl8_4),
% 1.50/0.56    inference(avatar_component_clause,[],[f109])).
% 1.50/0.56  fof(f109,plain,(
% 1.50/0.56    spl8_4 <=> v2_pre_topc(sK0)),
% 1.50/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 1.50/0.56  fof(f351,plain,(
% 1.50/0.56    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | k1_tarski(X2) = k6_domain_1(u1_struct_0(sK0),X2) | ~v2_pre_topc(sK0) | ~v3_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) ) | spl8_17),
% 1.50/0.56    inference(resolution,[],[f252,f70])).
% 1.50/0.56  fof(f70,plain,(
% 1.50/0.56    ( ! [X0] : (m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f36])).
% 1.50/0.56  fof(f36,plain,(
% 1.50/0.56    ! [X0] : (? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.50/0.56    inference(flattening,[],[f35])).
% 1.50/0.56  fof(f35,plain,(
% 1.50/0.56    ! [X0] : (? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.50/0.56    inference(ennf_transformation,[],[f21])).
% 1.50/0.56  fof(f21,axiom,(
% 1.50/0.56    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_tex_2)).
% 1.50/0.56  fof(f252,plain,(
% 1.50/0.56    ( ! [X0,X1] : (~m1_subset_1(sK5(sK0),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1)) ) | spl8_17),
% 1.50/0.56    inference(resolution,[],[f231,f77])).
% 1.50/0.56  fof(f77,plain,(
% 1.50/0.56    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f42])).
% 1.50/0.56  fof(f42,plain,(
% 1.50/0.56    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.50/0.56    inference(flattening,[],[f41])).
% 1.50/0.56  fof(f41,plain,(
% 1.50/0.56    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.50/0.56    inference(ennf_transformation,[],[f17])).
% 1.50/0.56  fof(f17,axiom,(
% 1.50/0.56    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 1.50/0.56  fof(f231,plain,(
% 1.50/0.56    ( ! [X1] : (~v1_xboole_0(X1) | ~m1_subset_1(sK5(sK0),k1_zfmisc_1(X1))) ) | spl8_17),
% 1.50/0.56    inference(resolution,[],[f187,f67])).
% 1.50/0.56  fof(f67,plain,(
% 1.50/0.56    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f30])).
% 1.50/0.56  fof(f30,plain,(
% 1.50/0.56    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 1.50/0.56    inference(ennf_transformation,[],[f11])).
% 1.50/0.56  fof(f11,axiom,(
% 1.50/0.56    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 1.50/0.56  fof(f187,plain,(
% 1.50/0.56    ~v1_xboole_0(sK5(sK0)) | spl8_17),
% 1.50/0.56    inference(avatar_component_clause,[],[f185])).
% 1.50/0.56  fof(f185,plain,(
% 1.50/0.56    spl8_17 <=> v1_xboole_0(sK5(sK0))),
% 1.50/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 1.50/0.56  fof(f401,plain,(
% 1.50/0.56    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK3)) != k2_pre_topc(sK0,k1_tarski(sK3)) | spl8_35),
% 1.50/0.56    inference(avatar_component_clause,[],[f399])).
% 1.50/0.56  fof(f399,plain,(
% 1.50/0.56    spl8_35 <=> k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK3)) = k2_pre_topc(sK0,k1_tarski(sK3))),
% 1.50/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).
% 1.50/0.56  fof(f402,plain,(
% 1.50/0.56    ~spl8_35 | ~spl8_10 | spl8_28 | spl8_29),
% 1.50/0.56    inference(avatar_split_clause,[],[f377,f320,f310,f145,f399])).
% 1.50/0.56  fof(f145,plain,(
% 1.50/0.56    spl8_10 <=> m1_subset_1(sK3,u1_struct_0(sK1))),
% 1.50/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 1.50/0.56  fof(f310,plain,(
% 1.50/0.56    spl8_28 <=> k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK3)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK1),sK3))),
% 1.50/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).
% 1.50/0.56  % (17139)Refutation not found, incomplete strategy% (17139)------------------------------
% 1.50/0.56  % (17139)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.56  % (17139)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.56  
% 1.50/0.56  % (17139)Memory used [KB]: 10746
% 1.50/0.56  % (17139)Time elapsed: 0.148 s
% 1.50/0.56  % (17139)------------------------------
% 1.50/0.56  % (17139)------------------------------
% 1.50/0.56  fof(f320,plain,(
% 1.50/0.56    spl8_29 <=> v1_xboole_0(u1_struct_0(sK1))),
% 1.50/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).
% 1.50/0.56  fof(f377,plain,(
% 1.50/0.56    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK3)) != k2_pre_topc(sK0,k1_tarski(sK3)) | (~spl8_10 | spl8_28 | spl8_29)),
% 1.50/0.56    inference(backward_demodulation,[],[f312,f375])).
% 1.50/0.56  fof(f375,plain,(
% 1.50/0.56    k6_domain_1(u1_struct_0(sK1),sK3) = k1_tarski(sK3) | (~spl8_10 | spl8_29)),
% 1.50/0.56    inference(resolution,[],[f329,f147])).
% 1.50/0.56  fof(f147,plain,(
% 1.50/0.56    m1_subset_1(sK3,u1_struct_0(sK1)) | ~spl8_10),
% 1.50/0.56    inference(avatar_component_clause,[],[f145])).
% 1.50/0.56  fof(f329,plain,(
% 1.50/0.56    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | k1_tarski(X0) = k6_domain_1(u1_struct_0(sK1),X0)) ) | spl8_29),
% 1.50/0.56    inference(resolution,[],[f321,f77])).
% 1.50/0.56  fof(f321,plain,(
% 1.50/0.56    ~v1_xboole_0(u1_struct_0(sK1)) | spl8_29),
% 1.50/0.56    inference(avatar_component_clause,[],[f320])).
% 1.50/0.56  fof(f312,plain,(
% 1.50/0.56    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK3)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK1),sK3)) | spl8_28),
% 1.50/0.56    inference(avatar_component_clause,[],[f310])).
% 1.50/0.56  fof(f328,plain,(
% 1.50/0.56    ~spl8_24 | spl8_25 | ~spl8_29),
% 1.50/0.56    inference(avatar_contradiction_clause,[],[f327])).
% 1.50/0.56  fof(f327,plain,(
% 1.50/0.56    $false | (~spl8_24 | spl8_25 | ~spl8_29)),
% 1.50/0.56    inference(subsumption_resolution,[],[f324,f261])).
% 1.50/0.56  fof(f261,plain,(
% 1.50/0.56    m1_subset_1(sK5(sK1),k1_zfmisc_1(u1_struct_0(sK1))) | ~spl8_24),
% 1.50/0.56    inference(avatar_component_clause,[],[f260])).
% 1.50/0.56  fof(f260,plain,(
% 1.50/0.56    spl8_24 <=> m1_subset_1(sK5(sK1),k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.50/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).
% 1.50/0.56  fof(f324,plain,(
% 1.50/0.56    ~m1_subset_1(sK5(sK1),k1_zfmisc_1(u1_struct_0(sK1))) | (spl8_25 | ~spl8_29)),
% 1.50/0.56    inference(resolution,[],[f322,f290])).
% 1.50/0.56  fof(f290,plain,(
% 1.50/0.56    ( ! [X1] : (~v1_xboole_0(X1) | ~m1_subset_1(sK5(sK1),k1_zfmisc_1(X1))) ) | spl8_25),
% 1.50/0.56    inference(resolution,[],[f266,f67])).
% 1.50/0.56  fof(f266,plain,(
% 1.50/0.56    ~v1_xboole_0(sK5(sK1)) | spl8_25),
% 1.50/0.56    inference(avatar_component_clause,[],[f264])).
% 1.50/0.56  fof(f264,plain,(
% 1.50/0.56    spl8_25 <=> v1_xboole_0(sK5(sK1))),
% 1.50/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).
% 1.50/0.56  fof(f322,plain,(
% 1.50/0.56    v1_xboole_0(u1_struct_0(sK1)) | ~spl8_29),
% 1.50/0.56    inference(avatar_component_clause,[],[f320])).
% 1.50/0.56  fof(f323,plain,(
% 1.50/0.56    spl8_29 | ~spl8_10 | spl8_27),
% 1.50/0.56    inference(avatar_split_clause,[],[f318,f306,f145,f320])).
% 1.50/0.56  fof(f306,plain,(
% 1.50/0.56    spl8_27 <=> m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK3),k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.50/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).
% 1.50/0.56  fof(f318,plain,(
% 1.50/0.56    v1_xboole_0(u1_struct_0(sK1)) | (~spl8_10 | spl8_27)),
% 1.50/0.56    inference(subsumption_resolution,[],[f315,f147])).
% 1.50/0.56  fof(f315,plain,(
% 1.50/0.56    ~m1_subset_1(sK3,u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK1)) | spl8_27),
% 1.50/0.56    inference(resolution,[],[f308,f78])).
% 1.50/0.56  fof(f78,plain,(
% 1.50/0.56    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f44])).
% 1.50/0.56  fof(f44,plain,(
% 1.50/0.56    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.50/0.56    inference(flattening,[],[f43])).
% 1.50/0.56  fof(f43,plain,(
% 1.50/0.56    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.50/0.56    inference(ennf_transformation,[],[f16])).
% 1.50/0.56  fof(f16,axiom,(
% 1.50/0.56    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 1.50/0.56  fof(f308,plain,(
% 1.50/0.56    ~m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK3),k1_zfmisc_1(u1_struct_0(sK1))) | spl8_27),
% 1.50/0.56    inference(avatar_component_clause,[],[f306])).
% 1.50/0.56  fof(f313,plain,(
% 1.50/0.56    ~spl8_27 | ~spl8_28 | ~spl8_1 | spl8_2 | spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_8 | ~spl8_9 | ~spl8_11 | ~spl8_12 | ~spl8_14 | ~spl8_15 | spl8_16),
% 1.50/0.56    inference(avatar_split_clause,[],[f270,f180,f170,f165,f155,f150,f140,f135,f119,f114,f109,f104,f99,f94,f310,f306])).
% 1.50/0.56  fof(f94,plain,(
% 1.50/0.56    spl8_1 <=> v1_funct_1(sK2)),
% 1.50/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.50/0.56  fof(f99,plain,(
% 1.50/0.56    spl8_2 <=> v2_struct_0(sK1)),
% 1.50/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 1.50/0.56  fof(f135,plain,(
% 1.50/0.56    spl8_8 <=> v4_tex_2(sK1,sK0)),
% 1.50/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 1.50/0.56  fof(f140,plain,(
% 1.50/0.56    spl8_9 <=> m1_pre_topc(sK1,sK0)),
% 1.50/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 1.50/0.56  fof(f150,plain,(
% 1.50/0.56    spl8_11 <=> v5_pre_topc(sK2,sK0,sK1)),
% 1.50/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 1.50/0.56  fof(f155,plain,(
% 1.50/0.56    spl8_12 <=> v3_borsuk_1(sK2,sK0,sK1)),
% 1.50/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 1.50/0.56  fof(f165,plain,(
% 1.50/0.56    spl8_14 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.50/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 1.50/0.56  fof(f170,plain,(
% 1.50/0.56    spl8_15 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 1.50/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 1.50/0.56  fof(f180,plain,(
% 1.50/0.56    spl8_16 <=> k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK3)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK3))),
% 1.50/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 1.50/0.56  fof(f270,plain,(
% 1.50/0.56    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK3)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK1),sK3)) | ~m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK3),k1_zfmisc_1(u1_struct_0(sK1))) | (~spl8_1 | spl8_2 | spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_8 | ~spl8_9 | ~spl8_11 | ~spl8_12 | ~spl8_14 | ~spl8_15 | spl8_16)),
% 1.50/0.56    inference(superposition,[],[f182,f247])).
% 1.50/0.56  fof(f247,plain,(
% 1.50/0.56    ( ! [X0] : (k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))) ) | (~spl8_1 | spl8_2 | spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_8 | ~spl8_9 | ~spl8_11 | ~spl8_12 | ~spl8_14 | ~spl8_15)),
% 1.50/0.56    inference(subsumption_resolution,[],[f246,f157])).
% 1.50/0.56  fof(f157,plain,(
% 1.50/0.56    v3_borsuk_1(sK2,sK0,sK1) | ~spl8_12),
% 1.50/0.56    inference(avatar_component_clause,[],[f155])).
% 1.50/0.56  fof(f246,plain,(
% 1.50/0.56    ( ! [X0] : (~v3_borsuk_1(sK2,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)) ) | (~spl8_1 | spl8_2 | spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_8 | ~spl8_9 | ~spl8_11 | ~spl8_14 | ~spl8_15)),
% 1.50/0.56    inference(subsumption_resolution,[],[f245,f172])).
% 1.50/0.56  fof(f172,plain,(
% 1.50/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl8_15),
% 1.50/0.56    inference(avatar_component_clause,[],[f170])).
% 1.50/0.56  fof(f245,plain,(
% 1.50/0.56    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v3_borsuk_1(sK2,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)) ) | (~spl8_1 | spl8_2 | spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_8 | ~spl8_9 | ~spl8_11 | ~spl8_14)),
% 1.50/0.56    inference(subsumption_resolution,[],[f244,f152])).
% 1.50/0.56  fof(f152,plain,(
% 1.50/0.56    v5_pre_topc(sK2,sK0,sK1) | ~spl8_11),
% 1.50/0.56    inference(avatar_component_clause,[],[f150])).
% 1.50/0.56  fof(f244,plain,(
% 1.50/0.56    ( ! [X0] : (~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v3_borsuk_1(sK2,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)) ) | (~spl8_1 | spl8_2 | spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_8 | ~spl8_9 | ~spl8_14)),
% 1.50/0.56    inference(subsumption_resolution,[],[f243,f111])).
% 1.50/0.56  fof(f243,plain,(
% 1.50/0.56    ( ! [X0] : (~v2_pre_topc(sK0) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v3_borsuk_1(sK2,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)) ) | (~spl8_1 | spl8_2 | spl8_3 | ~spl8_5 | ~spl8_6 | ~spl8_8 | ~spl8_9 | ~spl8_14)),
% 1.50/0.56    inference(subsumption_resolution,[],[f242,f106])).
% 1.50/0.56  fof(f242,plain,(
% 1.50/0.56    ( ! [X0] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v3_borsuk_1(sK2,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)) ) | (~spl8_1 | spl8_2 | ~spl8_5 | ~spl8_6 | ~spl8_8 | ~spl8_9 | ~spl8_14)),
% 1.50/0.56    inference(subsumption_resolution,[],[f241,f142])).
% 1.50/0.56  fof(f142,plain,(
% 1.50/0.56    m1_pre_topc(sK1,sK0) | ~spl8_9),
% 1.50/0.56    inference(avatar_component_clause,[],[f140])).
% 1.50/0.56  fof(f241,plain,(
% 1.50/0.56    ( ! [X0] : (~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v3_borsuk_1(sK2,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)) ) | (~spl8_1 | spl8_2 | ~spl8_5 | ~spl8_6 | ~spl8_8 | ~spl8_14)),
% 1.50/0.56    inference(subsumption_resolution,[],[f240,f137])).
% 1.50/0.56  fof(f137,plain,(
% 1.50/0.56    v4_tex_2(sK1,sK0) | ~spl8_8),
% 1.50/0.56    inference(avatar_component_clause,[],[f135])).
% 1.50/0.56  fof(f240,plain,(
% 1.50/0.56    ( ! [X0] : (~v4_tex_2(sK1,sK0) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v3_borsuk_1(sK2,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)) ) | (~spl8_1 | spl8_2 | ~spl8_5 | ~spl8_6 | ~spl8_14)),
% 1.50/0.56    inference(subsumption_resolution,[],[f239,f101])).
% 1.50/0.56  fof(f101,plain,(
% 1.50/0.56    ~v2_struct_0(sK1) | spl8_2),
% 1.50/0.56    inference(avatar_component_clause,[],[f99])).
% 1.50/0.56  fof(f239,plain,(
% 1.50/0.56    ( ! [X0] : (v2_struct_0(sK1) | ~v4_tex_2(sK1,sK0) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v3_borsuk_1(sK2,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)) ) | (~spl8_1 | ~spl8_5 | ~spl8_6 | ~spl8_14)),
% 1.50/0.56    inference(subsumption_resolution,[],[f238,f121])).
% 1.50/0.56  fof(f238,plain,(
% 1.50/0.56    ( ! [X0] : (~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v4_tex_2(sK1,sK0) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v3_borsuk_1(sK2,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)) ) | (~spl8_1 | ~spl8_5 | ~spl8_14)),
% 1.50/0.56    inference(subsumption_resolution,[],[f213,f116])).
% 1.50/0.56  fof(f213,plain,(
% 1.50/0.56    ( ! [X0] : (~v3_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v4_tex_2(sK1,sK0) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v3_borsuk_1(sK2,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)) ) | (~spl8_1 | ~spl8_14)),
% 1.50/0.56    inference(resolution,[],[f124,f167])).
% 1.50/0.56  fof(f167,plain,(
% 1.50/0.56    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl8_14),
% 1.50/0.56    inference(avatar_component_clause,[],[f165])).
% 1.50/0.56  fof(f124,plain,(
% 1.50/0.56    ( ! [X2,X0,X1] : (~v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~v5_pre_topc(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v3_borsuk_1(sK2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | k2_pre_topc(X0,X2) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2,X2)) ) | ~spl8_1),
% 1.50/0.56    inference(subsumption_resolution,[],[f123,f66])).
% 1.50/0.56  fof(f66,plain,(
% 1.50/0.56    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X0)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f29])).
% 1.50/0.56  fof(f29,plain,(
% 1.50/0.56    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.50/0.56    inference(ennf_transformation,[],[f15])).
% 1.50/0.56  fof(f15,axiom,(
% 1.50/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).
% 1.50/0.56  fof(f123,plain,(
% 1.50/0.56    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X0) | ~v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) | ~v5_pre_topc(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v3_borsuk_1(sK2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X2) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2,X2)) ) | ~spl8_1),
% 1.50/0.56    inference(resolution,[],[f96,f90])).
% 1.50/0.56  fof(f90,plain,(
% 1.50/0.56    ( ! [X4,X2,X0,X1] : (~v1_funct_1(X2) | ~v2_pre_topc(X0) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X0) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v5_pre_topc(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X4) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)) )),
% 1.50/0.56    inference(equality_resolution,[],[f69])).
% 1.50/0.56  fof(f69,plain,(
% 1.50/0.56    ( ! [X4,X2,X0,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v5_pre_topc(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | X3 != X4 | k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f34])).
% 1.50/0.56  fof(f34,plain,(
% 1.50/0.56    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) | X3 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.50/0.56    inference(flattening,[],[f33])).
% 1.50/0.56  fof(f33,plain,(
% 1.50/0.56    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : (! [X4] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) | X3 != X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v3_borsuk_1(X2,X0,X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.50/0.56    inference(ennf_transformation,[],[f22])).
% 1.50/0.56  fof(f22,axiom,(
% 1.50/0.56    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4))))))))),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tex_2)).
% 1.50/0.56  fof(f96,plain,(
% 1.50/0.56    v1_funct_1(sK2) | ~spl8_1),
% 1.50/0.56    inference(avatar_component_clause,[],[f94])).
% 1.50/0.56  fof(f182,plain,(
% 1.50/0.56    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK3)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK3)) | spl8_16),
% 1.50/0.56    inference(avatar_component_clause,[],[f180])).
% 1.50/0.56  fof(f287,plain,(
% 1.50/0.56    spl8_2 | ~spl8_20 | ~spl8_21 | ~spl8_23 | spl8_24),
% 1.50/0.56    inference(avatar_contradiction_clause,[],[f286])).
% 1.50/0.56  fof(f286,plain,(
% 1.50/0.56    $false | (spl8_2 | ~spl8_20 | ~spl8_21 | ~spl8_23 | spl8_24)),
% 1.50/0.56    inference(subsumption_resolution,[],[f285,f101])).
% 1.50/0.56  fof(f285,plain,(
% 1.50/0.56    v2_struct_0(sK1) | (~spl8_20 | ~spl8_21 | ~spl8_23 | spl8_24)),
% 1.50/0.56    inference(subsumption_resolution,[],[f284,f201])).
% 1.50/0.56  fof(f201,plain,(
% 1.50/0.56    l1_pre_topc(sK1) | ~spl8_20),
% 1.50/0.56    inference(avatar_component_clause,[],[f200])).
% 1.50/0.56  fof(f200,plain,(
% 1.50/0.56    spl8_20 <=> l1_pre_topc(sK1)),
% 1.50/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).
% 1.50/0.56  fof(f284,plain,(
% 1.50/0.56    ~l1_pre_topc(sK1) | v2_struct_0(sK1) | (~spl8_21 | ~spl8_23 | spl8_24)),
% 1.50/0.56    inference(subsumption_resolution,[],[f283,f257])).
% 1.50/0.56  fof(f257,plain,(
% 1.50/0.56    v3_tdlat_3(sK1) | ~spl8_23),
% 1.50/0.56    inference(avatar_component_clause,[],[f256])).
% 1.50/0.56  fof(f256,plain,(
% 1.50/0.56    spl8_23 <=> v3_tdlat_3(sK1)),
% 1.50/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).
% 1.50/0.56  fof(f283,plain,(
% 1.50/0.56    ~v3_tdlat_3(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK1) | (~spl8_21 | spl8_24)),
% 1.50/0.56    inference(subsumption_resolution,[],[f280,f205])).
% 1.50/0.56  fof(f205,plain,(
% 1.50/0.56    v2_pre_topc(sK1) | ~spl8_21),
% 1.50/0.56    inference(avatar_component_clause,[],[f204])).
% 1.50/0.56  fof(f204,plain,(
% 1.50/0.56    spl8_21 <=> v2_pre_topc(sK1)),
% 1.50/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).
% 1.50/0.56  fof(f280,plain,(
% 1.50/0.56    ~v2_pre_topc(sK1) | ~v3_tdlat_3(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK1) | spl8_24),
% 1.50/0.56    inference(resolution,[],[f262,f70])).
% 1.50/0.56  fof(f262,plain,(
% 1.50/0.56    ~m1_subset_1(sK5(sK1),k1_zfmisc_1(u1_struct_0(sK1))) | spl8_24),
% 1.50/0.56    inference(avatar_component_clause,[],[f260])).
% 1.50/0.56  fof(f278,plain,(
% 1.50/0.56    spl8_2 | spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_9 | spl8_23),
% 1.50/0.56    inference(avatar_contradiction_clause,[],[f277])).
% 1.50/0.56  fof(f277,plain,(
% 1.50/0.56    $false | (spl8_2 | spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_9 | spl8_23)),
% 1.50/0.56    inference(subsumption_resolution,[],[f276,f106])).
% 1.50/0.56  fof(f276,plain,(
% 1.50/0.56    v2_struct_0(sK0) | (spl8_2 | ~spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_9 | spl8_23)),
% 1.50/0.56    inference(subsumption_resolution,[],[f275,f111])).
% 1.50/0.56  fof(f275,plain,(
% 1.50/0.56    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl8_2 | ~spl8_5 | ~spl8_6 | ~spl8_9 | spl8_23)),
% 1.50/0.56    inference(subsumption_resolution,[],[f274,f121])).
% 1.50/0.56  fof(f274,plain,(
% 1.50/0.56    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl8_2 | ~spl8_5 | ~spl8_9 | spl8_23)),
% 1.50/0.56    inference(subsumption_resolution,[],[f273,f116])).
% 1.50/0.56  fof(f273,plain,(
% 1.50/0.56    ~v3_tdlat_3(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl8_2 | ~spl8_9 | spl8_23)),
% 1.50/0.56    inference(resolution,[],[f269,f142])).
% 1.50/0.56  fof(f269,plain,(
% 1.50/0.56    ( ! [X0] : (~m1_pre_topc(sK1,X0) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | (spl8_2 | spl8_23)),
% 1.50/0.56    inference(subsumption_resolution,[],[f268,f101])).
% 1.50/0.56  fof(f268,plain,(
% 1.50/0.56    ( ! [X0] : (~v2_pre_topc(X0) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK1,X0) | v2_struct_0(sK1) | v2_struct_0(X0)) ) | spl8_23),
% 1.50/0.56    inference(resolution,[],[f258,f68])).
% 1.50/0.56  fof(f68,plain,(
% 1.50/0.56    ( ! [X0,X1] : (v3_tdlat_3(X1) | ~v2_pre_topc(X0) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | v2_struct_0(X0)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f32])).
% 1.50/0.56  fof(f32,plain,(
% 1.50/0.56    ! [X0] : (! [X1] : ((v3_tdlat_3(X1) & ~v2_struct_0(X1)) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.50/0.56    inference(flattening,[],[f31])).
% 1.50/0.56  fof(f31,plain,(
% 1.50/0.56    ! [X0] : (! [X1] : (((v3_tdlat_3(X1) & ~v2_struct_0(X1)) | v2_struct_0(X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.50/0.56    inference(ennf_transformation,[],[f19])).
% 1.50/0.56  fof(f19,axiom,(
% 1.50/0.56    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (~v2_struct_0(X1) => (v3_tdlat_3(X1) & ~v2_struct_0(X1)))))),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc9_tdlat_3)).
% 1.50/0.56  fof(f258,plain,(
% 1.50/0.56    ~v3_tdlat_3(sK1) | spl8_23),
% 1.50/0.56    inference(avatar_component_clause,[],[f256])).
% 1.50/0.56  fof(f267,plain,(
% 1.50/0.56    ~spl8_23 | ~spl8_24 | ~spl8_25 | spl8_2 | ~spl8_19 | ~spl8_20 | ~spl8_21),
% 1.50/0.56    inference(avatar_split_clause,[],[f251,f204,f200,f197,f99,f264,f260,f256])).
% 1.50/0.56  fof(f197,plain,(
% 1.50/0.56    spl8_19 <=> ! [X0] : (~v1_xboole_0(X0) | ~v3_tex_2(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))))),
% 1.50/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).
% 1.50/0.56  fof(f251,plain,(
% 1.50/0.56    ~v1_xboole_0(sK5(sK1)) | ~m1_subset_1(sK5(sK1),k1_zfmisc_1(u1_struct_0(sK1))) | ~v3_tdlat_3(sK1) | (spl8_2 | ~spl8_19 | ~spl8_20 | ~spl8_21)),
% 1.50/0.56    inference(subsumption_resolution,[],[f250,f101])).
% 1.50/0.56  fof(f250,plain,(
% 1.50/0.56    ~v1_xboole_0(sK5(sK1)) | ~m1_subset_1(sK5(sK1),k1_zfmisc_1(u1_struct_0(sK1))) | ~v3_tdlat_3(sK1) | v2_struct_0(sK1) | (~spl8_19 | ~spl8_20 | ~spl8_21)),
% 1.50/0.56    inference(subsumption_resolution,[],[f249,f201])).
% 1.50/0.56  fof(f249,plain,(
% 1.50/0.56    ~v1_xboole_0(sK5(sK1)) | ~m1_subset_1(sK5(sK1),k1_zfmisc_1(u1_struct_0(sK1))) | ~v3_tdlat_3(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK1) | (~spl8_19 | ~spl8_21)),
% 1.50/0.56    inference(subsumption_resolution,[],[f248,f205])).
% 1.50/0.56  fof(f248,plain,(
% 1.50/0.56    ~v1_xboole_0(sK5(sK1)) | ~m1_subset_1(sK5(sK1),k1_zfmisc_1(u1_struct_0(sK1))) | ~v2_pre_topc(sK1) | ~v3_tdlat_3(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK1) | ~spl8_19),
% 1.50/0.56    inference(resolution,[],[f198,f71])).
% 1.50/0.56  fof(f71,plain,(
% 1.50/0.56    ( ! [X0] : (v3_tex_2(sK5(X0),X0) | ~v2_pre_topc(X0) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f36])).
% 1.50/0.56  fof(f198,plain,(
% 1.50/0.56    ( ! [X0] : (~v3_tex_2(X0,sK1) | ~v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))) ) | ~spl8_19),
% 1.50/0.56    inference(avatar_component_clause,[],[f197])).
% 1.50/0.56  fof(f237,plain,(
% 1.50/0.56    ~spl8_4 | ~spl8_6 | ~spl8_9 | spl8_21),
% 1.50/0.56    inference(avatar_contradiction_clause,[],[f236])).
% 1.50/0.56  fof(f236,plain,(
% 1.50/0.56    $false | (~spl8_4 | ~spl8_6 | ~spl8_9 | spl8_21)),
% 1.50/0.56    inference(subsumption_resolution,[],[f235,f111])).
% 1.50/0.56  fof(f235,plain,(
% 1.50/0.56    ~v2_pre_topc(sK0) | (~spl8_6 | ~spl8_9 | spl8_21)),
% 1.50/0.56    inference(subsumption_resolution,[],[f234,f121])).
% 1.50/0.56  fof(f234,plain,(
% 1.50/0.56    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl8_9 | spl8_21)),
% 1.50/0.56    inference(resolution,[],[f212,f142])).
% 1.50/0.56  fof(f212,plain,(
% 1.50/0.56    ( ! [X0] : (~m1_pre_topc(sK1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | spl8_21),
% 1.50/0.56    inference(resolution,[],[f206,f73])).
% 1.50/0.56  fof(f73,plain,(
% 1.50/0.56    ( ! [X0,X1] : (v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f40])).
% 1.50/0.56  fof(f40,plain,(
% 1.50/0.56    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.50/0.56    inference(flattening,[],[f39])).
% 1.50/0.56  fof(f39,plain,(
% 1.50/0.56    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.50/0.56    inference(ennf_transformation,[],[f13])).
% 1.50/0.56  fof(f13,axiom,(
% 1.50/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).
% 1.50/0.56  fof(f206,plain,(
% 1.50/0.56    ~v2_pre_topc(sK1) | spl8_21),
% 1.50/0.56    inference(avatar_component_clause,[],[f204])).
% 1.50/0.56  fof(f228,plain,(
% 1.50/0.56    spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_6 | spl8_18),
% 1.50/0.56    inference(avatar_contradiction_clause,[],[f227])).
% 1.50/0.56  fof(f227,plain,(
% 1.50/0.56    $false | (spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_6 | spl8_18)),
% 1.50/0.56    inference(subsumption_resolution,[],[f226,f106])).
% 1.50/0.56  fof(f226,plain,(
% 1.50/0.56    v2_struct_0(sK0) | (~spl8_4 | ~spl8_5 | ~spl8_6 | spl8_18)),
% 1.50/0.56    inference(subsumption_resolution,[],[f225,f121])).
% 1.50/0.56  fof(f225,plain,(
% 1.50/0.56    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_4 | ~spl8_5 | spl8_18)),
% 1.50/0.56    inference(subsumption_resolution,[],[f224,f116])).
% 1.50/0.56  fof(f224,plain,(
% 1.50/0.56    ~v3_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | (~spl8_4 | spl8_18)),
% 1.50/0.56    inference(subsumption_resolution,[],[f221,f111])).
% 1.50/0.56  fof(f221,plain,(
% 1.50/0.56    ~v2_pre_topc(sK0) | ~v3_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | spl8_18),
% 1.50/0.56    inference(resolution,[],[f191,f70])).
% 1.50/0.56  fof(f191,plain,(
% 1.50/0.56    ~m1_subset_1(sK5(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | spl8_18),
% 1.50/0.56    inference(avatar_component_clause,[],[f189])).
% 1.50/0.56  fof(f189,plain,(
% 1.50/0.56    spl8_18 <=> m1_subset_1(sK5(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.50/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 1.50/0.56  fof(f211,plain,(
% 1.50/0.56    ~spl8_6 | ~spl8_9 | spl8_20),
% 1.50/0.56    inference(avatar_contradiction_clause,[],[f210])).
% 1.50/0.56  fof(f210,plain,(
% 1.50/0.56    $false | (~spl8_6 | ~spl8_9 | spl8_20)),
% 1.50/0.56    inference(subsumption_resolution,[],[f209,f121])).
% 1.50/0.56  fof(f209,plain,(
% 1.50/0.56    ~l1_pre_topc(sK0) | (~spl8_9 | spl8_20)),
% 1.50/0.56    inference(resolution,[],[f208,f142])).
% 1.50/0.56  fof(f208,plain,(
% 1.50/0.56    ( ! [X0] : (~m1_pre_topc(sK1,X0) | ~l1_pre_topc(X0)) ) | spl8_20),
% 1.50/0.56    inference(resolution,[],[f202,f64])).
% 1.50/0.56  fof(f64,plain,(
% 1.50/0.56    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f27])).
% 1.50/0.56  fof(f27,plain,(
% 1.50/0.56    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.50/0.56    inference(ennf_transformation,[],[f14])).
% 1.50/0.56  fof(f14,axiom,(
% 1.50/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.50/0.56  fof(f202,plain,(
% 1.50/0.56    ~l1_pre_topc(sK1) | spl8_20),
% 1.50/0.56    inference(avatar_component_clause,[],[f200])).
% 1.50/0.56  fof(f207,plain,(
% 1.50/0.56    spl8_19 | ~spl8_20 | ~spl8_21 | spl8_2),
% 1.50/0.56    inference(avatar_split_clause,[],[f125,f99,f204,f200,f197])).
% 1.50/0.56  fof(f125,plain,(
% 1.50/0.56    ( ! [X0] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~v3_tex_2(X0,sK1)) ) | spl8_2),
% 1.50/0.56    inference(resolution,[],[f101,f72])).
% 1.50/0.56  fof(f72,plain,(
% 1.50/0.56    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tex_2(X1,X0)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f38])).
% 1.50/0.56  fof(f38,plain,(
% 1.50/0.56    ! [X0] : (! [X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.50/0.56    inference(flattening,[],[f37])).
% 1.50/0.56  fof(f37,plain,(
% 1.50/0.56    ! [X0] : (! [X1] : (~v3_tex_2(X1,X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.50/0.56    inference(ennf_transformation,[],[f20])).
% 1.50/0.56  fof(f20,axiom,(
% 1.50/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => ~v3_tex_2(X1,X0)))),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_tex_2)).
% 1.50/0.56  fof(f192,plain,(
% 1.50/0.56    ~spl8_17 | ~spl8_18 | spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_6),
% 1.50/0.56    inference(avatar_split_clause,[],[f178,f119,f114,f109,f104,f189,f185])).
% 1.50/0.56  fof(f178,plain,(
% 1.50/0.56    ~m1_subset_1(sK5(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_xboole_0(sK5(sK0)) | (spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_6)),
% 1.50/0.56    inference(subsumption_resolution,[],[f177,f106])).
% 1.50/0.56  fof(f177,plain,(
% 1.50/0.56    ~m1_subset_1(sK5(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_xboole_0(sK5(sK0)) | v2_struct_0(sK0) | (spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_6)),
% 1.50/0.56    inference(subsumption_resolution,[],[f176,f121])).
% 1.50/0.56  fof(f176,plain,(
% 1.50/0.56    ~m1_subset_1(sK5(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_xboole_0(sK5(sK0)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | (spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_6)),
% 1.50/0.56    inference(subsumption_resolution,[],[f175,f116])).
% 1.50/0.56  fof(f175,plain,(
% 1.50/0.56    ~m1_subset_1(sK5(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_xboole_0(sK5(sK0)) | ~v3_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | (spl8_3 | ~spl8_4 | ~spl8_6)),
% 1.50/0.56    inference(subsumption_resolution,[],[f174,f111])).
% 1.50/0.56  fof(f174,plain,(
% 1.50/0.56    ~m1_subset_1(sK5(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_xboole_0(sK5(sK0)) | ~v2_pre_topc(sK0) | ~v3_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | (spl8_3 | ~spl8_4 | ~spl8_6)),
% 1.50/0.56    inference(resolution,[],[f128,f71])).
% 1.50/0.56  fof(f128,plain,(
% 1.50/0.56    ( ! [X0] : (~v3_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_xboole_0(X0)) ) | (spl8_3 | ~spl8_4 | ~spl8_6)),
% 1.50/0.56    inference(subsumption_resolution,[],[f127,f121])).
% 1.50/0.56  fof(f127,plain,(
% 1.50/0.56    ( ! [X0] : (~l1_pre_topc(sK0) | ~v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_tex_2(X0,sK0)) ) | (spl8_3 | ~spl8_4)),
% 1.50/0.56    inference(subsumption_resolution,[],[f126,f111])).
% 1.50/0.56  fof(f126,plain,(
% 1.50/0.56    ( ! [X0] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_tex_2(X0,sK0)) ) | spl8_3),
% 1.50/0.56    inference(resolution,[],[f106,f72])).
% 1.50/0.56  fof(f183,plain,(
% 1.50/0.56    ~spl8_16),
% 1.50/0.56    inference(avatar_split_clause,[],[f91,f180])).
% 1.50/0.56  fof(f91,plain,(
% 1.50/0.56    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK3)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK3))),
% 1.50/0.56    inference(forward_demodulation,[],[f49,f48])).
% 1.50/0.56  fof(f48,plain,(
% 1.50/0.56    sK3 = sK4),
% 1.50/0.56    inference(cnf_transformation,[],[f26])).
% 1.50/0.56  % (17138)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.50/0.56  fof(f26,plain,(
% 1.50/0.56    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.50/0.56    inference(flattening,[],[f25])).
% 1.50/0.56  fof(f25,plain,(
% 1.50/0.56    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (? [X4] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4) & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.50/0.56    inference(ennf_transformation,[],[f24])).
% 1.50/0.56  fof(f24,negated_conjecture,(
% 1.50/0.56    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)))))))))),
% 1.50/0.56    inference(negated_conjecture,[],[f23])).
% 1.50/0.56  fof(f23,conjecture,(
% 1.50/0.56    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)))))))))),
% 1.50/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tex_2)).
% 1.50/0.56  fof(f49,plain,(
% 1.50/0.56    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK3)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4))),
% 1.50/0.56    inference(cnf_transformation,[],[f26])).
% 1.50/0.56  fof(f173,plain,(
% 1.50/0.56    spl8_15),
% 1.50/0.56    inference(avatar_split_clause,[],[f54,f170])).
% 1.50/0.56  fof(f54,plain,(
% 1.50/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 1.50/0.56    inference(cnf_transformation,[],[f26])).
% 1.50/0.56  fof(f168,plain,(
% 1.50/0.56    spl8_14),
% 1.50/0.56    inference(avatar_split_clause,[],[f52,f165])).
% 1.50/0.56  fof(f52,plain,(
% 1.50/0.56    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.50/0.56    inference(cnf_transformation,[],[f26])).
% 1.50/0.56  fof(f163,plain,(
% 1.50/0.56    spl8_13),
% 1.50/0.56    inference(avatar_split_clause,[],[f92,f160])).
% 1.50/0.56  fof(f92,plain,(
% 1.50/0.56    m1_subset_1(sK3,u1_struct_0(sK0))),
% 1.50/0.56    inference(forward_demodulation,[],[f47,f48])).
% 1.50/0.56  fof(f47,plain,(
% 1.50/0.56    m1_subset_1(sK4,u1_struct_0(sK0))),
% 1.50/0.56    inference(cnf_transformation,[],[f26])).
% 1.50/0.56  fof(f158,plain,(
% 1.50/0.56    spl8_12),
% 1.50/0.56    inference(avatar_split_clause,[],[f55,f155])).
% 1.50/0.56  fof(f55,plain,(
% 1.50/0.56    v3_borsuk_1(sK2,sK0,sK1)),
% 1.50/0.56    inference(cnf_transformation,[],[f26])).
% 1.50/0.56  fof(f153,plain,(
% 1.50/0.56    spl8_11),
% 1.50/0.56    inference(avatar_split_clause,[],[f53,f150])).
% 1.50/0.56  fof(f53,plain,(
% 1.50/0.56    v5_pre_topc(sK2,sK0,sK1)),
% 1.50/0.56    inference(cnf_transformation,[],[f26])).
% 1.50/0.56  fof(f148,plain,(
% 1.50/0.56    spl8_10),
% 1.50/0.56    inference(avatar_split_clause,[],[f50,f145])).
% 1.50/0.56  fof(f50,plain,(
% 1.50/0.56    m1_subset_1(sK3,u1_struct_0(sK1))),
% 1.50/0.56    inference(cnf_transformation,[],[f26])).
% 1.50/0.56  fof(f143,plain,(
% 1.50/0.56    spl8_9),
% 1.50/0.56    inference(avatar_split_clause,[],[f58,f140])).
% 1.50/0.56  fof(f58,plain,(
% 1.50/0.56    m1_pre_topc(sK1,sK0)),
% 1.50/0.56    inference(cnf_transformation,[],[f26])).
% 1.50/0.56  fof(f138,plain,(
% 1.50/0.56    spl8_8),
% 1.50/0.56    inference(avatar_split_clause,[],[f57,f135])).
% 1.50/0.56  fof(f57,plain,(
% 1.50/0.56    v4_tex_2(sK1,sK0)),
% 1.50/0.56    inference(cnf_transformation,[],[f26])).
% 1.50/0.56  fof(f122,plain,(
% 1.50/0.56    spl8_6),
% 1.50/0.56    inference(avatar_split_clause,[],[f62,f119])).
% 1.50/0.56  fof(f62,plain,(
% 1.50/0.56    l1_pre_topc(sK0)),
% 1.50/0.56    inference(cnf_transformation,[],[f26])).
% 1.50/0.56  fof(f117,plain,(
% 1.50/0.56    spl8_5),
% 1.50/0.56    inference(avatar_split_clause,[],[f61,f114])).
% 1.50/0.56  fof(f61,plain,(
% 1.50/0.56    v3_tdlat_3(sK0)),
% 1.50/0.56    inference(cnf_transformation,[],[f26])).
% 1.50/0.56  fof(f112,plain,(
% 1.50/0.56    spl8_4),
% 1.50/0.56    inference(avatar_split_clause,[],[f60,f109])).
% 1.50/0.56  fof(f60,plain,(
% 1.50/0.56    v2_pre_topc(sK0)),
% 1.50/0.56    inference(cnf_transformation,[],[f26])).
% 1.50/0.56  fof(f107,plain,(
% 1.50/0.56    ~spl8_3),
% 1.50/0.56    inference(avatar_split_clause,[],[f59,f104])).
% 1.50/0.56  fof(f59,plain,(
% 1.50/0.56    ~v2_struct_0(sK0)),
% 1.50/0.56    inference(cnf_transformation,[],[f26])).
% 1.50/0.56  fof(f102,plain,(
% 1.50/0.56    ~spl8_2),
% 1.50/0.56    inference(avatar_split_clause,[],[f56,f99])).
% 1.50/0.56  fof(f56,plain,(
% 1.50/0.56    ~v2_struct_0(sK1)),
% 1.50/0.56    inference(cnf_transformation,[],[f26])).
% 1.50/0.56  fof(f97,plain,(
% 1.50/0.56    spl8_1),
% 1.50/0.56    inference(avatar_split_clause,[],[f51,f94])).
% 1.50/0.56  fof(f51,plain,(
% 1.50/0.56    v1_funct_1(sK2)),
% 1.50/0.56    inference(cnf_transformation,[],[f26])).
% 1.50/0.56  % SZS output end Proof for theBenchmark
% 1.50/0.56  % (17142)------------------------------
% 1.50/0.56  % (17142)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.56  % (17142)Termination reason: Refutation
% 1.50/0.56  
% 1.50/0.56  % (17142)Memory used [KB]: 11129
% 1.50/0.56  % (17142)Time elapsed: 0.131 s
% 1.50/0.56  % (17142)------------------------------
% 1.50/0.56  % (17142)------------------------------
% 1.50/0.57  % (17118)Success in time 0.201 s
%------------------------------------------------------------------------------
